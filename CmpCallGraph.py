#!/usr/bin/env python3

import json
import argparse
import re
import math
from collections import defaultdict
from typing import Dict, List, Set, Tuple, Optional, FrozenSet
from dataclasses import dataclass, field
from concurrent.futures import ProcessPoolExecutor
import multiprocessing
from functools import lru_cache
import pickle

# ============================================================================
# WEIGHTS CONFIGURATION
# ============================================================================

DEFAULT_WEIGHTS = {
    "in_degree_exact": 0.08,
    "in_degree_close": 0.04,
    "out_degree_exact": 0.08,
    "out_degree_close": 0.04,
    "params_count": 0.08,
    "params_types": 0.08,
    "return_type": 0.06,
    "size": 0.10,
    "local_vars": 0.04,
    "calling_convention": 0.04,
    "called_funcs": 0.12,
    "strings": 0.12,
    "constants": 0.06,
    "basic_blocks": 0.04,
    "context": 0.02,
}

# ============================================================================
# PRECOMPILED PATTERNS
# ============================================================================

_LEADING_UNDERSCORES = re.compile(r'^_+')
_POINTER_PATTERN = re.compile(r'\*|ptr|pointer', re.IGNORECASE)
_INT_TYPES = frozenset({'int', 'long', 'short', 'char', 'byte', 'dword', 'qword', 'word'})

_AUTO_NAME_PATTERNS = (
    re.compile(r'^FUN_[0-9a-fA-F]+$'),
    re.compile(r'^sub_[0-9a-fA-F]+$'),
    re.compile(r'^LAB_[0-9a-fA-F]+$'),
    re.compile(r'^DAT_[0-9a-fA-F]+$'),
    re.compile(r'^thunk_'),
    re.compile(r'^[0-9a-fA-F]+$'),
)

# Type equivalence groups for enhanced matching
TYPE_EQUIVALENCES = [
    frozenset({'void*', 'pvoid', 'lpvoid', 'pointer', 'ptr'}),
    frozenset({'char*', 'pchar', 'lpstr', 'pcstr', 'lpcstr'}),
    frozenset({'wchar*', 'pwchar', 'lpwstr', 'pcwstr', 'lpcwstr'}),
    frozenset({'int', 'int32', 'long', 'dword', 'uint', 'uint32', 'ulong'}),
    frozenset({'int64', 'longlong', 'qword', 'uint64', 'ulonglong', '__int64'}),
    frozenset({'int16', 'short', 'word', 'uint16', 'ushort'}),
    frozenset({'int8', 'char', 'byte', 'uint8', 'uchar', 'schar'}),
    frozenset({'handle', 'hwnd', 'hmodule', 'hinstance', 'hkey', 'hdc'}),
    frozenset({'bool', 'boolean', '_bool', 'winbool'}),
    frozenset({'size_t', 'uintptr', 'uintptr_t', 'size'}),
    frozenset({'float', 'single', 'float32'}),
    frozenset({'double', 'float64', 'longdouble'}),
]

# ============================================================================
# GLOBAL WORKER DATA (for multiprocessing)
# ============================================================================

_worker_data = {}


def _init_worker(funcs2_bytes: bytes, index2_bytes: bytes, 
                 by_norm_name1_bytes: bytes, by_norm_name2_bytes: bytes,
                 weights_bytes: bytes):
    """Initialize worker process with shared data"""
    global _worker_data
    _worker_data['funcs2'] = pickle.loads(funcs2_bytes)
    _worker_data['index2'] = pickle.loads(index2_bytes)
    _worker_data['by_norm_name1'] = pickle.loads(by_norm_name1_bytes)
    _worker_data['by_norm_name2'] = pickle.loads(by_norm_name2_bytes)
    _worker_data['weights'] = pickle.loads(weights_bytes)


# ============================================================================
# CACHING AND NORMALIZATION
# ============================================================================

@lru_cache(maxsize=131072)
def normalize_function_name(name: str) -> str:
    """Normalize function name for comparison"""
    normalized = name.replace("::", "__")
    normalized = _LEADING_UNDERSCORES.sub('', normalized)
    return normalized.lower()


@lru_cache(maxsize=131072)
def normalize_string(s: str) -> str:
    """Normalize string for comparison"""
    return s.lower().strip()


@lru_cache(maxsize=131072)
def normalize_type(type_str: str) -> str:
    """Normalize type string for comparison"""
    t = type_str.lower().strip()
    t = re.sub(r'\s+', '', t)
    t = re.sub(r'unsigned\s*', 'u', t)
    t = re.sub(r'signed\s*', '', t)
    t = re.sub(r'const\s*', '', t)
    t = re.sub(r'struct\s*', '', t)
    return t


@lru_cache(maxsize=65536)
def is_auto_name(name: str) -> bool:
    """Check if function name is auto-generated"""
    for pattern in _AUTO_NAME_PATTERNS:
        if pattern.match(name):
            return True
    return False


# ============================================================================
# DATA CLASSES
# ============================================================================

@dataclass
class FunctionInfo:
    address: str
    name: str
    normalized_name: str
    is_renamed: bool
    is_thunk: bool
    is_external: bool
    out_degree: int
    in_degree: int
    called_names: List[str]
    caller_names: List[str]
    signature: dict
    strings: List[str] = field(default_factory=list)
    constants: List[int] = field(default_factory=list)
    basic_block_count: int = 0


# ============================================================================
# FUNCTION INDEX FOR FAST CANDIDATE FILTERING
# ============================================================================

class FunctionIndex:
    """Index for fast candidate filtering based on function characteristics"""
    
    def __init__(self):
        self.by_params: Dict[int, Set[str]] = defaultdict(set)
        self.by_size_bucket: Dict[int, Set[str]] = defaultdict(set)
        self.by_degree_bucket: Dict[Tuple[int, int], Set[str]] = defaultdict(set)
        self.by_calling_conv: Dict[str, Set[str]] = defaultdict(set)
        self.by_string_hash: Dict[int, Set[str]] = defaultdict(set)
        self.all_addrs: Set[str] = set()
        
    def add(self, addr: str, func_dict: dict):
        """Add function to index"""
        self.all_addrs.add(addr)
        sig = func_dict['signature']
        
        # Index by params count (exact)
        self.by_params[sig['params_count']].add(addr)
        
        # Index by size bucket (logarithmic)
        size = sig.get('size', 0)
        bucket = self._size_bucket(size)
        self.by_size_bucket[bucket].add(addr)
        
        # Index by degree bucket
        deg_key = (
            func_dict['in_degree'] // 3,
            func_dict['out_degree'] // 3
        )
        self.by_degree_bucket[deg_key].add(addr)
        
        # Index by calling convention
        cc = sig.get('calling_convention', '')
        if cc:
            self.by_calling_conv[cc].add(addr)
        
        # Index by string content hash (for quick filtering)
        strings = func_dict.get('strings_set', frozenset())
        if strings:
            # Use hash of sorted strings for bucketing
            str_hash = hash(frozenset(list(strings)[:5])) % 1000
            self.by_string_hash[str_hash].add(addr)
    
    def _size_bucket(self, size: int) -> int:
        """Get logarithmic size bucket"""
        if size <= 0:
            return 0
        return int(math.log2(size + 1))
    
    def get_candidates(self, func_dict: dict, matched: Set[str], 
                       max_candidates: int = 500) -> Set[str]:
        """Get filtered candidate set for matching"""
        sig = func_dict['signature']
        size = sig.get('size', 0)
        bucket = self._size_bucket(size)
        
        # Start with size-similar functions (current and adjacent buckets)
        candidates = set()
        for b in [bucket - 1, bucket, bucket + 1]:
            candidates |= self.by_size_bucket.get(b, set())
        
        # If too many candidates, filter by params
        if len(candidates) > max_candidates:
            params = sig['params_count']
            params_filter = set()
            for p in range(max(0, params - 1), params + 2):
                params_filter |= self.by_params.get(p, set())
            if params_filter:
                candidates &= params_filter
        
        # If still too many, filter by degree
        if len(candidates) > max_candidates:
            in_deg = func_dict['in_degree'] // 3
            out_deg = func_dict['out_degree'] // 3
            deg_filter = set()
            for i in range(in_deg - 1, in_deg + 2):
                for o in range(out_deg - 1, out_deg + 2):
                    deg_filter |= self.by_degree_bucket.get((i, o), set())
            if deg_filter:
                candidates &= deg_filter
        
        # If too few candidates, fall back to all
        if len(candidates) < 10:
            candidates = set(self.all_addrs)
        
        # Remove already matched
        candidates -= matched
        
        return candidates
    
    def to_bytes(self) -> bytes:
        """Serialize for multiprocessing"""
        return pickle.dumps(self)
    
    @staticmethod
    def from_bytes(data: bytes) -> 'FunctionIndex':
        """Deserialize"""
        return pickle.loads(data)


# ============================================================================
# ADAPTIVE WEIGHTS
# ============================================================================

class AdaptiveWeights:
    """Adaptive weights based on data characteristics"""
    
    def __init__(self, funcs1: Dict[str, dict], funcs2: Dict[str, dict]):
        self.weights = dict(DEFAULT_WEIGHTS)
        self._analyze_and_adapt(funcs1, funcs2)
        self._normalize()
    
    def _analyze_and_adapt(self, funcs1: dict, funcs2: dict):
        """Analyze data and adapt weights accordingly"""
        # Check string availability
        strings_ratio1 = sum(1 for f in funcs1.values() 
                            if f.get('strings_set')) / max(len(funcs1), 1)
        strings_ratio2 = sum(1 for f in funcs2.values() 
                            if f.get('strings_set')) / max(len(funcs2), 1)
        
        # If few strings, reduce string weight
        if strings_ratio1 < 0.15 or strings_ratio2 < 0.15:
            self.weights['strings'] *= 0.4
            self.weights['size'] *= 1.3
            self.weights['called_funcs'] *= 1.3
        
        # Check constants availability
        const_ratio1 = sum(1 for f in funcs1.values() 
                          if f.get('constants_set')) / max(len(funcs1), 1)
        const_ratio2 = sum(1 for f in funcs2.values() 
                          if f.get('constants_set')) / max(len(funcs2), 1)
        
        if const_ratio1 < 0.1 or const_ratio2 < 0.1:
            self.weights['constants'] *= 0.3
            self.weights['size'] *= 1.1
        
        # Check signature quality
        has_good_sigs1 = sum(1 for f in funcs1.values() 
                            if f['signature'].get('params_count', 0) > 0) / max(len(funcs1), 1)
        has_good_sigs2 = sum(1 for f in funcs2.values() 
                            if f['signature'].get('params_count', 0) > 0) / max(len(funcs2), 1)
        
        if has_good_sigs1 < 0.3 or has_good_sigs2 < 0.3:
            self.weights['params_count'] *= 0.5
            self.weights['params_types'] *= 0.5
            self.weights['return_type'] *= 0.5
    
    def _normalize(self):
        """Normalize weights to sum to 1.0"""
        total = sum(self.weights.values())
        if total > 0:
            self.weights = {k: v / total for k, v in self.weights.items()}
    
    def get(self, key: str) -> float:
        return self.weights.get(key, 0.0)
    
    def to_dict(self) -> dict:
        return dict(self.weights)


# ============================================================================
# SIMILARITY CALCULATION
# ============================================================================

def types_compatible(type1: str, type2: str) -> float:
    """Check type compatibility with score 0-1"""
    t1 = normalize_type(type1)
    t2 = normalize_type(type2)
    
    if t1 == t2:
        return 1.0
    
    # Check equivalence groups
    for equiv_set in TYPE_EQUIVALENCES:
        if t1 in equiv_set and t2 in equiv_set:
            return 0.9
    
    # Both pointers?
    is_ptr1 = '*' in t1 or 'ptr' in t1 or t1.startswith('p')
    is_ptr2 = '*' in t2 or 'ptr' in t2 or t2.startswith('p')
    if is_ptr1 and is_ptr2:
        return 0.7
    
    # Both integers?
    t1_is_int = any(it in t1 for it in _INT_TYPES)
    t2_is_int = any(it in t2 for it in _INT_TYPES)
    if t1_is_int and t2_is_int:
        return 0.5
    
    return 0.0


def jaccard_similarity(set1: FrozenSet, set2: FrozenSet) -> float:
    """Calculate Jaccard similarity between two sets"""
    if not set1 and not set2:
        return 0.0
    intersection = len(set1 & set2)
    union = len(set1 | set2)
    if union == 0:
        return 0.0
    return intersection / union


def calculate_string_similarity(strings1: FrozenSet[str], 
                                  strings2: FrozenSet[str]) -> float:
    """Calculate similarity between string sets"""
    if not strings1 or not strings2:
        return 0.0
    
    # Exact Jaccard
    exact_jaccard = jaccard_similarity(strings1, strings2)
    
    # Substring matching for longer strings
    long_strings1 = {s for s in strings1 if len(s) >= 8}
    long_strings2 = {s for s in strings2 if len(s) >= 8}
    
    substring_score = 0.0
    if long_strings1 and long_strings2:
        matches = 0
        total = 0
        for s1 in long_strings1:
            for s2 in long_strings2:
                total += 1
                if s1 in s2 or s2 in s1:
                    matches += 1
                elif len(set(s1.split()) & set(s2.split())) > 0:
                    matches += 0.5
        if total > 0:
            substring_score = min(matches / total, 1.0)
    
    return exact_jaccard * 0.7 + substring_score * 0.3


def calculate_param_type_similarity(params1: List[dict], 
                                     params2: List[dict]) -> float:
    """Calculate parameter type similarity"""
    if not params1 and not params2:
        return 1.0
    if not params1 or not params2:
        return 0.0
    if len(params1) != len(params2):
        return 0.0
    
    total_score = 0.0
    for p1, p2 in zip(params1, params2):
        type1 = p1.get("type", "")
        type2 = p2.get("type", "")
        total_score += types_compatible(type1, type2)
    
    return total_score / len(params1)


def calculate_size_similarity(size1: int, size2: int) -> float:
    """Calculate size similarity using logarithmic scale"""
    if size1 <= 0 or size2 <= 0:
        return 0.0
    
    if size1 == size2:
        return 1.0
    
    # Use ratio for small functions, log ratio for large
    min_size = min(size1, size2)
    max_size = max(size1, size2)
    
    ratio = min_size / max_size
    
    # Bonus for similar sizes
    if ratio > 0.9:
        return 0.95
    elif ratio > 0.7:
        return 0.8
    elif ratio > 0.5:
        return 0.6
    elif ratio > 0.3:
        return 0.4
    else:
        return ratio


def calculate_degree_similarity(deg1: int, deg2: int) -> Tuple[float, bool]:
    """Calculate degree similarity, returns (score, is_exact)"""
    if deg1 == deg2:
        return (1.0, True)
    
    max_deg = max(deg1, deg2)
    if max_deg == 0:
        return (1.0, True)
    
    diff = abs(deg1 - deg2)
    relative_diff = diff / max_deg
    
    if relative_diff <= 0.1:
        return (0.8, False)
    elif relative_diff <= 0.25:
        return (0.5, False)
    elif relative_diff <= 0.5:
        return (0.2, False)
    
    return (0.0, False)


def calculate_similarity(func1: dict, func2: dict, weights: dict) -> float:
    """Calculate overall similarity between two functions"""
    score = 0.0
    
    # Quick size check for early exit
    size1 = func1['signature'].get('size', 0)
    size2 = func2['signature'].get('size', 0)
    if size1 > 0 and size2 > 0:
        size_ratio = min(size1, size2) / max(size1, size2)
        if size_ratio < 0.2:
            return 0.0  # Too different in size
    
    # In-degree
    in_sim, in_exact = calculate_degree_similarity(
        func1['in_degree'], func2['in_degree']
    )
    if in_exact:
        score += weights.get('in_degree_exact', 0)
    else:
        score += in_sim * weights.get('in_degree_close', 0)
    
    # Out-degree
    out_sim, out_exact = calculate_degree_similarity(
        func1['out_degree'], func2['out_degree']
    )
    if out_exact:
        score += weights.get('out_degree_exact', 0)
    else:
        score += out_sim * weights.get('out_degree_close', 0)
    
    sig1, sig2 = func1['signature'], func2['signature']
    
    # Params count
    if sig1['params_count'] == sig2['params_count']:
        score += weights.get('params_count', 0)
        
        # Param types (only if count matches)
        params1 = sig1.get('params', [])
        params2 = sig2.get('params', [])
        if params1 and params2:
            param_sim = calculate_param_type_similarity(params1, params2)
            score += param_sim * weights.get('params_types', 0)
    elif abs(sig1['params_count'] - sig2['params_count']) == 1:
        score += weights.get('params_count', 0) * 0.3
    
    # Return type
    ret_sim = types_compatible(sig1.get('return_type', ''), 
                                sig2.get('return_type', ''))
    score += ret_sim * weights.get('return_type', 0)
    
    # Size
    size_sim = calculate_size_similarity(size1, size2)
    score += size_sim * weights.get('size', 0)
    
    # Local vars
    lv1 = sig1.get('local_vars_count', 0)
    lv2 = sig2.get('local_vars_count', 0)
    if lv1 == lv2:
        score += weights.get('local_vars', 0)
    elif abs(lv1 - lv2) <= 2:
        score += weights.get('local_vars', 0) * 0.5
    elif abs(lv1 - lv2) <= 5:
        score += weights.get('local_vars', 0) * 0.2
    
    # Calling convention
    cc1 = sig1.get('calling_convention', '')
    cc2 = sig2.get('calling_convention', '')
    if cc1 and cc2 and cc1 == cc2:
        score += weights.get('calling_convention', 0)
    
    # Called functions
    called1 = func1.get('called_names_normalized', frozenset())
    called2 = func2.get('called_names_normalized', frozenset())
    if called1 or called2:
        called_sim = jaccard_similarity(called1, called2)
        score += called_sim * weights.get('called_funcs', 0)
    
    # Strings
    strings1 = func1.get('strings_set', frozenset())
    strings2 = func2.get('strings_set', frozenset())
    if strings1 and strings2:
        string_sim = calculate_string_similarity(strings1, strings2)
        score += string_sim * weights.get('strings', 0)
    
    # Constants
    const1 = func1.get('constants_set', frozenset())
    const2 = func2.get('constants_set', frozenset())
    if const1 and const2:
        const_sim = jaccard_similarity(const1, const2)
        score += const_sim * weights.get('constants', 0)
    
    # Basic blocks
    bb1 = func1.get('basic_block_count', 0)
    bb2 = func2.get('basic_block_count', 0)
    if bb1 > 0 and bb2 > 0:
        bb_ratio = min(bb1, bb2) / max(bb1, bb2)
        score += bb_ratio * weights.get('basic_blocks', 0)
    
    return min(score, 1.0)


# ============================================================================
# WORKER FUNCTIONS
# ============================================================================

def _process_signature_match(args):
    """Worker function for signature-based matching"""
    addr1, func1_dict, matched_addrs2, thunk_external_filter = args
    
    global _worker_data
    funcs2_dict = _worker_data['funcs2']
    index2 = _worker_data['index2']
    weights = _worker_data['weights']
    
    if thunk_external_filter:
        if func1_dict.get('is_thunk') or func1_dict.get('is_external'):
            return None
    
    # Get filtered candidates using index
    candidates_addrs = index2.get_candidates(func1_dict, matched_addrs2)
    
    candidates = []
    for addr2 in candidates_addrs:
        func2_dict = funcs2_dict.get(addr2)
        if func2_dict is None:
            continue
        
        if thunk_external_filter:
            if func2_dict.get('is_thunk') or func2_dict.get('is_external'):
                continue
        
        score = calculate_similarity(func1_dict, func2_dict, weights)
        if score > 0.35:
            candidates.append((addr2, score))
    
    if candidates:
        candidates.sort(key=lambda x: x[1], reverse=True)
        best = candidates[0]
        
        # Require significant margin over second best
        if len(candidates) == 1:
            if best[1] > 0.5:
                return (addr1, best[0], best[1])
        elif best[1] > candidates[1][1] * 1.15:
            if best[1] > 0.5:
                return (addr1, best[0], best[1])
    
    return None


def _process_string_match(args):
    """Worker function for string-based matching"""
    addr1, func1_dict, matched_addrs2, min_string_count = args
    
    global _worker_data
    funcs2_dict = _worker_data['funcs2']
    weights = _worker_data['weights']
    
    strings1 = func1_dict.get('strings_set', frozenset())
    if len(strings1) < min_string_count:
        return None
    
    candidates = []
    
    for addr2, func2_dict in funcs2_dict.items():
        if addr2 in matched_addrs2:
            continue
        
        strings2 = func2_dict.get('strings_set', frozenset())
        if len(strings2) < min_string_count:
            continue
        
        string_sim = calculate_string_similarity(strings1, strings2)
        
        if string_sim > 0.5:
            struct_sim = calculate_similarity(func1_dict, func2_dict, weights)
            combined_score = string_sim * 0.55 + struct_sim * 0.45
            candidates.append((addr2, combined_score, string_sim))
    
    if candidates:
        candidates.sort(key=lambda x: x[1], reverse=True)
        best = candidates[0]
        
        if len(candidates) == 1 or best[1] > candidates[1][1] * 1.12:
            if best[1] > 0.55:
                return (addr1, best[0], best[1], best[2])
    
    return None


def _process_propagation(args):
    """Worker function for match propagation"""
    addr1, func1_dict, matches_dict, matched_addrs2 = args
    
    global _worker_data
    funcs2_dict = _worker_data['funcs2']
    by_norm_name1 = _worker_data['by_norm_name1']
    weights = _worker_data['weights']
    
    candidates = defaultdict(float)
    
    # Check called functions
    for called_name in func1_dict['called_names_normalized']:
        if called_name in by_norm_name1:
            called_info = by_norm_name1[called_name]
            called_addr1 = called_info['address']
            if called_addr1 in matches_dict:
                matched_addr2 = matches_dict[called_addr1]
                matched_func2 = funcs2_dict.get(matched_addr2)
                if matched_func2:
                    matched_normalized = matched_func2['normalized_name']
                    for addr2, func2_dict in funcs2_dict.items():
                        if addr2 in matched_addrs2:
                            continue
                        if matched_normalized in func2_dict['called_names_normalized']:
                            candidates[addr2] += 1.0
    
    # Check caller functions
    for caller_name in func1_dict['caller_names_normalized']:
        if caller_name in by_norm_name1:
            caller_info = by_norm_name1[caller_name]
            caller_addr1 = caller_info['address']
            if caller_addr1 in matches_dict:
                matched_addr2 = matches_dict[caller_addr1]
                matched_func2 = funcs2_dict.get(matched_addr2)
                if matched_func2:
                    matched_normalized = matched_func2['normalized_name']
                    for addr2, func2_dict in funcs2_dict.items():
                        if addr2 in matched_addrs2:
                            continue
                        if matched_normalized in func2_dict['caller_names_normalized']:
                            candidates[addr2] += 1.0
    
    if candidates:
        # Add structural similarity
        for addr2 in list(candidates.keys()):
            func2_dict = funcs2_dict[addr2]
            struct_score = calculate_similarity(func1_dict, func2_dict, weights)
            candidates[addr2] += struct_score * 2.5
        
        sorted_candidates = sorted(candidates.items(), key=lambda x: x[1], reverse=True)
        best_addr2, best_score = sorted_candidates[0]
        
        # Require margin
        if len(sorted_candidates) >= 2:
            if sorted_candidates[0][1] > sorted_candidates[1][1] * 1.25:
                if best_score >= 2.0:
                    return (addr1, best_addr2, best_score / 5.0)
        elif best_score >= 1.8:
            return (addr1, best_addr2, best_score / 5.0)
    
    return None


def _process_candidates(args):
    """Worker function for finding candidates for unknown functions"""
    addr1, func1_dict, matches_dict, matched_addrs2, min_score = args
    
    global _worker_data
    funcs2_dict = _worker_data['funcs2']
    by_norm_name1 = _worker_data['by_norm_name1']
    index2 = _worker_data['index2']
    weights = _worker_data['weights']
    
    # Get filtered candidates
    candidates_addrs = index2.get_candidates(func1_dict, matched_addrs2)
    
    candidates = []
    for addr2 in candidates_addrs:
        func2_dict = funcs2_dict.get(addr2)
        if func2_dict is None:
            continue
        
        score = calculate_similarity(func1_dict, func2_dict, weights)
        link_score = _calculate_link_score(
            func1_dict, func2_dict, by_norm_name1, funcs2_dict, matches_dict
        )
        total_score = score * 0.45 + link_score * 0.55
        
        if total_score > min_score:
            candidates.append((addr2, func2_dict['name'], total_score))
    
    if candidates:
        candidates.sort(key=lambda x: x[2], reverse=True)
        best = candidates[0]
        return (addr1, func1_dict['name'], best[0], best[1], best[2])
    
    return None


def _calculate_link_score(func1_dict: dict, func2_dict: dict,
                          by_norm_name1: dict, funcs2_dict: dict,
                          matches_dict: dict) -> float:
    """Calculate link-based similarity score"""
    score = 0.0
    max_score = 0.0
    
    # Check called functions
    for called_name in func1_dict['called_names_normalized']:
        max_score += 1.0
        if called_name in by_norm_name1:
            called_info = by_norm_name1[called_name]
            called_addr1 = called_info['address']
            if called_addr1 in matches_dict:
                matched_addr2 = matches_dict[called_addr1]
                matched_func2 = funcs2_dict.get(matched_addr2)
                if matched_func2:
                    if matched_func2['normalized_name'] in func2_dict['called_names_normalized']:
                        score += 1.0
    
    # Check caller functions
    for caller_name in func1_dict['caller_names_normalized']:
        max_score += 1.0
        if caller_name in by_norm_name1:
            caller_info = by_norm_name1[caller_name]
            caller_addr1 = caller_info['address']
            if caller_addr1 in matches_dict:
                matched_addr2 = matches_dict[caller_addr1]
                matched_func2 = funcs2_dict.get(matched_addr2)
                if matched_func2:
                    if matched_func2['normalized_name'] in func2_dict['caller_names_normalized']:
                        score += 1.0
    
    if max_score > 0:
        return score / max_score
    return 0.0


# ============================================================================
# MAIN MATCHER CLASS
# ============================================================================

class CallGraphMatcher:
    def __init__(self, graph1_path: str, graph2_path: str, num_workers: int = None):
        print(f"[*] Loading graphs...")
        
        with open(graph1_path, 'r', encoding='utf-8') as f:
            self.graph1 = json.load(f)
        with open(graph2_path, 'r', encoding='utf-8') as f:
            self.graph2 = json.load(f)
        
        self.num_workers = num_workers or max(1, multiprocessing.cpu_count() - 1)
        
        # Parse functions
        self.funcs1 = self._parse_functions(self.graph1)
        self.funcs2 = self._parse_functions(self.graph2)
        
        # Create optimized dict representations
        self.funcs1_dict = {addr: self._func_to_dict(f) for addr, f in self.funcs1.items()}
        self.funcs2_dict = {addr: self._func_to_dict(f) for addr, f in self.funcs2.items()}
        
        # Build indexes
        print(f"[*] Building indexes...")
        self.index2 = FunctionIndex()
        for addr, func_dict in self.funcs2_dict.items():
            self.index2.add(addr, func_dict)
        
        # Name lookups
        self.by_name1 = {f.name: f for f in self.funcs1.values()}
        self.by_name2 = {f.name: f for f in self.funcs2.values()}
        
        self.by_normalized_name1 = {f.normalized_name: f for f in self.funcs1.values()}
        self.by_normalized_name2 = {f.normalized_name: f for f in self.funcs2.values()}
        
        self.by_normalized_name1_dict = {
            name: self._func_to_dict(f) for name, f in self.by_normalized_name1.items()
        }
        self.by_normalized_name2_dict = {
            name: self._func_to_dict(f) for name, f in self.by_normalized_name2.items()
        }
        
        # Adaptive weights
        self.adaptive_weights = AdaptiveWeights(self.funcs1_dict, self.funcs2_dict)
        self.weights = self.adaptive_weights.to_dict()
        
        # Results
        self.matches: Dict[str, str] = {}
        self.match_scores: Dict[str, float] = {}
        self.match_reasons: Dict[str, str] = {}
        
        # Precompute serialized data for workers
        self._prepare_worker_data()
    
    def _prepare_worker_data(self):
        """Prepare serialized data for worker processes"""
        print(f"[*] Preparing worker data...")
        self._funcs2_bytes = pickle.dumps(self.funcs2_dict)
        self._index2_bytes = pickle.dumps(self.index2)
        self._by_norm_name1_bytes = pickle.dumps(self.by_normalized_name1_dict)
        self._by_norm_name2_bytes = pickle.dumps(self.by_normalized_name2_dict)
        self._weights_bytes = pickle.dumps(self.weights)
    
    def _extract_strings(self, data: dict) -> List[str]:
        """Extract strings from function data"""
        strings_data = data.get("strings", [])
        result = []
        for item in strings_data:
            if isinstance(item, str):
                result.append(item)
            elif isinstance(item, dict):
                value = item.get("value", "")
                if value:
                    result.append(value)
        return result
    
    def _extract_constants(self, data: dict) -> List[int]:
        """Extract numeric constants from function data"""
        constants = data.get("constants", [])
        result = []
        for c in constants:
            if isinstance(c, int):
                result.append(c)
            elif isinstance(c, str):
                try:
                    result.append(int(c, 0))
                except ValueError:
                    pass
        return result
    
    def _func_to_dict(self, func: FunctionInfo) -> dict:
        """Convert FunctionInfo to optimized dict"""
        strings_list = func.strings
        strings_set = frozenset(
            normalize_string(s) for s in strings_list if len(s) >= 3
        )
        
        constants_set = frozenset(
            c for c in func.constants if abs(c) > 255
        )
        
        called_normalized = frozenset(
            normalize_function_name(n) for n in func.called_names
        )
        caller_normalized = frozenset(
            normalize_function_name(n) for n in func.caller_names
        )
        
        return {
            "address": func.address,
            "name": func.name,
            "normalized_name": func.normalized_name,
            "is_renamed": func.is_renamed,
            "is_thunk": func.is_thunk,
            "is_external": func.is_external,
            "out_degree": func.out_degree,
            "in_degree": func.in_degree,
            "called_names": func.called_names,
            "caller_names": func.caller_names,
            "called_names_normalized": called_normalized,
            "caller_names_normalized": caller_normalized,
            "signature": func.signature,
            "strings": strings_list,
            "strings_set": strings_set,
            "constants": func.constants,
            "constants_set": constants_set,
            "basic_block_count": func.basic_block_count,
        }
    
    def _parse_functions(self, graph) -> Dict[str, FunctionInfo]:
        """Parse functions from graph data"""
        result = {}
        
        if isinstance(graph, list):
            functions = graph
        elif isinstance(graph, dict):
            functions = graph.get("functions", [])
        else:
            functions = []
        
        items = functions if isinstance(functions, list) else list(functions.items())
        
        for item in items:
            if isinstance(functions, list):
                data = item
                addr = data.get("address", data.get("addr", ""))
            else:
                addr, data = item
            
            name = data.get("name", "")
            normalized_name = normalize_function_name(name)
            
            if "is_renamed" in data:
                is_renamed = data["is_renamed"]
            else:
                is_renamed = not is_auto_name(name)
            
            default_sig = {
                "params_count": 0,
                "return_type": "undefined",
                "size": 0,
                "local_vars_count": 0,
                "calling_convention": "",
                "params": []
            }
            sig = data.get("signature", default_sig)
            if not isinstance(sig, dict):
                sig = default_sig
            
            result[addr] = FunctionInfo(
                address=addr,
                name=name,
                normalized_name=normalized_name,
                is_renamed=is_renamed,
                is_thunk=data.get("is_thunk", False),
                is_external=data.get("is_external", False),
                out_degree=data.get("out_degree", 0),
                in_degree=data.get("in_degree", 0),
                called_names=data.get("called_names", []),
                caller_names=data.get("caller_names", []),
                signature={
                    "params_count": sig.get("params_count", 0),
                    "return_type": sig.get("return_type", "undefined"),
                    "size": sig.get("size", 0),
                    "local_vars_count": sig.get("local_vars_count", 0),
                    "calling_convention": sig.get("calling_convention", ""),
                    "params": sig.get("params", [])
                },
                strings=self._extract_strings(data),
                constants=self._extract_constants(data),
                basic_block_count=data.get("basic_block_count", 
                                          data.get("bb_count", 0))
            )
        
        return result
    
    def _calculate_chunksize(self, n_tasks: int) -> int:
        """Calculate optimal chunksize for task distribution"""
        if n_tasks < 100:
            return 1
        elif n_tasks < 1000:
            return max(1, n_tasks // (self.num_workers * 8))
        else:
            return max(5, n_tasks // (self.num_workers * 16))
    
    def _resolve_conflicts(self, results: List[Tuple]) -> List[Tuple]:
        """Resolve conflicts when multiple functions match to the same target"""
        addr2_to_candidates = defaultdict(list)
        
        for result in results:
            if result is None:
                continue
            if len(result) >= 3:
                addr1, addr2, score = result[0], result[1], result[2]
                addr2_to_candidates[addr2].append((addr1, score, result))
        
        resolved = []
        for addr2, candidates in addr2_to_candidates.items():
            # Choose best match for each target
            best = max(candidates, key=lambda x: x[1])
            resolved.append(best[2])
        
        return resolved
       
    def match_by_unique_strings(self):
        """Match functions by unique string literals"""
        print("[*] Matching by unique string literals...")
        
        initial_count = len(self.matches)
        matched_addrs2 = set(self.matches.values())
        
        # Build string-to-function maps
        string_to_funcs1 = defaultdict(list)
        string_to_funcs2 = defaultdict(list)
        
        for addr, func in self.funcs1.items():
            if addr in self.matches:
                continue
            for s in func.strings:
                normalized = normalize_string(s)
                if len(normalized) >= 6:
                    string_to_funcs1[normalized].append(addr)
        
        for addr, func in self.funcs2.items():
            if addr in matched_addrs2:
                continue
            for s in func.strings:
                normalized = normalize_string(s)
                if len(normalized) >= 6:
                    string_to_funcs2[normalized].append(addr)
        
        # Find unique string matches
        for string, addrs1 in string_to_funcs1.items():
            if len(addrs1) != 1:
                continue
            if string not in string_to_funcs2:
                continue
            addrs2 = string_to_funcs2[string]
            if len(addrs2) != 1:
                continue
            
            addr1 = addrs1[0]
            addr2 = addrs2[0]
            
            if addr1 in self.matches or addr2 in matched_addrs2:
                continue
            
            func1_dict = self.funcs1_dict[addr1]
            func2_dict = self.funcs2_dict[addr2]
            struct_sim = calculate_similarity(func1_dict, func2_dict, self.weights)
            
            if struct_sim > 0.25:
                self.matches[addr1] = addr2
                self.match_scores[addr1] = 0.85 + struct_sim * 0.1
                self.match_reasons[addr1] = "unique_string"
                matched_addrs2.add(addr2)
        
        print(f"    Found {len(self.matches) - initial_count} unique string matches")
    
    def match_by_string_similarity(self):
        """Match functions by string set similarity"""
        print(f"[*] Matching by string similarity (using {self.num_workers} workers)...")
        
        initial_count = len(self.matches)
        matched_addrs2 = set(self.matches.values())
        
        tasks = []
        for addr1, func1 in self.funcs1.items():
            if addr1 in self.matches:
                continue
            if func1.is_thunk or func1.is_external:
                continue
            tasks.append((addr1, self.funcs1_dict[addr1], matched_addrs2, 2))
        
        if not tasks:
            print(f"    Found 0 new matches")
            return
        
        chunksize = self._calculate_chunksize(len(tasks))
        
        with ProcessPoolExecutor(
            max_workers=self.num_workers,
            initializer=_init_worker,
            initargs=(self._funcs2_bytes, self._index2_bytes,
                     self._by_norm_name1_bytes, self._by_norm_name2_bytes,
                     self._weights_bytes)
        ) as executor:
            results = list(executor.map(_process_string_match, tasks, chunksize=chunksize))
        
        # Resolve conflicts
        resolved = self._resolve_conflicts(results)
        
        new_matches = 0
        for result in resolved:
            addr1, addr2, score, string_sim = result
            if addr2 not in matched_addrs2 and addr1 not in self.matches:
                self.matches[addr1] = addr2
                self.match_scores[addr1] = score
                self.match_reasons[addr1] = f"string_similarity({string_sim:.2f})"
                matched_addrs2.add(addr2)
                new_matches += 1
        
        print(f"    Found {new_matches} new matches")
    
    def match_by_signature_and_structure(self):
        """Match functions by signature and structural similarity"""
        print(f"[*] Matching by signature and structure (using {self.num_workers} workers)...")
        
        matched_addrs2 = set(self.matches.values())
        
        tasks = []
        for addr1, func1 in self.funcs1.items():
            if addr1 in self.matches:
                continue
            tasks.append((addr1, self.funcs1_dict[addr1], matched_addrs2, True))
        
        if not tasks:
            print(f"    Found 0 new matches")
            return
        
        chunksize = self._calculate_chunksize(len(tasks))
        
        with ProcessPoolExecutor(
            max_workers=self.num_workers,
            initializer=_init_worker,
            initargs=(self._funcs2_bytes, self._index2_bytes,
                     self._by_norm_name1_bytes, self._by_norm_name2_bytes,
                     self._weights_bytes)
        ) as executor:
            results = list(executor.map(_process_signature_match, tasks, chunksize=chunksize))
        
        # Resolve conflicts
        resolved = self._resolve_conflicts(results)
        
        new_matches = 0
        for result in resolved:
            addr1, addr2, score = result
            if addr2 not in matched_addrs2 and addr1 not in self.matches:
                self.matches[addr1] = addr2
                self.match_scores[addr1] = score
                self.match_reasons[addr1] = "structure"
                matched_addrs2.add(addr2)
                new_matches += 1
        
        print(f"    Found {new_matches} new matches")
    
    def propagate_matches(self, iterations: int = 8):
        """Propagate matches through call graph"""
        print("[*] Propagating matches...")
        
        for i in range(iterations):
            new_matches = self._propagate_once()
            print(f"    Iteration {i+1}: {new_matches} new matches")
            if new_matches == 0:
                break
    
    def _propagate_once(self) -> int:
        """Single iteration of match propagation"""
        matched_addrs2 = set(self.matches.values())
        matches_dict = dict(self.matches)
        
        tasks = []
        for addr1, func1 in self.funcs1.items():
            if addr1 in self.matches:
                continue
            tasks.append((addr1, self.funcs1_dict[addr1], matches_dict, matched_addrs2))
        
        if not tasks:
            return 0
        
        chunksize = self._calculate_chunksize(len(tasks))
        
        with ProcessPoolExecutor(
            max_workers=self.num_workers,
            initializer=_init_worker,
            initargs=(self._funcs2_bytes, self._index2_bytes,
                     self._by_norm_name1_bytes, self._by_norm_name2_bytes,
                     self._weights_bytes)
        ) as executor:
            results = list(executor.map(_process_propagation, tasks, chunksize=chunksize))
        
        # Resolve conflicts
        resolved = self._resolve_conflicts(results)
        
        new_matches = {}
        for result in resolved:
            addr1, addr2, score = result
            if addr2 not in matched_addrs2:
                new_matches[addr1] = (addr2, score)
                matched_addrs2.add(addr2)
        
        for addr1, (addr2, score) in new_matches.items():
            self.matches[addr1] = addr2
            self.match_scores[addr1] = min(score, 1.0)
            self.match_reasons[addr1] = "propagation"
        
        return len(new_matches)
    
    def verify_matches(self):
        """Verify matches using mutual best match criterion"""
        print("[*] Verifying matches...")
        
        removed = 0
        to_remove = []
        
        for addr1, addr2 in list(self.matches.items()):
            reason = self.match_reasons.get(addr1, "")
            
            # Don't verify exact name matches
            if reason in ("exact_name", "normalized_name"):
                continue
            
            score = self.match_scores.get(addr1, 0)
            
            # Only verify lower confidence matches
            if score > 0.85:
                continue
            
            func2_dict = self.funcs2_dict[addr2]
            
            # Check if there's a better candidate for func2
            best_score = 0
            best_addr1 = None
            
            for other_addr1, other_func1_dict in self.funcs1_dict.items():
                if other_addr1 in self.matches and other_addr1 != addr1:
                    continue
                
                sim = calculate_similarity(other_func1_dict, func2_dict, self.weights)
                if sim > best_score:
                    best_score = sim
                    best_addr1 = other_addr1
            
            # If current match is not the best, mark for removal
            if best_addr1 != addr1 and best_score > score * 1.15:
                to_remove.append(addr1)
                removed += 1
        
        for addr1 in to_remove:
            del self.matches[addr1]
            del self.match_scores[addr1]
            del self.match_reasons[addr1]
        
        print(f"    Removed {removed} low-confidence matches")
    
    def find_candidates_for_unknown(self, min_score: float = 0.3) -> List[Tuple]:
        """Find match candidates for remaining unknown functions"""
        print(f"[*] Finding candidates for unknown functions (using {self.num_workers} workers)...")
        
        matched_addrs2 = set(self.matches.values())
        matches_dict = dict(self.matches)
        
        tasks = []
        for addr1, func1 in self.funcs1.items():
            if addr1 in self.matches:
                continue
            tasks.append((
                addr1,
                self.funcs1_dict[addr1],
                matches_dict,
                matched_addrs2,
                min_score
            ))
        
        if not tasks:
            return []
        
        chunksize = self._calculate_chunksize(len(tasks))
        
        with ProcessPoolExecutor(
            max_workers=self.num_workers,
            initializer=_init_worker,
            initargs=(self._funcs2_bytes, self._index2_bytes,
                     self._by_norm_name1_bytes, self._by_norm_name2_bytes,
                     self._weights_bytes)
        ) as executor:
            results = list(executor.map(_process_candidates, tasks, chunksize=chunksize))
        
        candidates_list = [r for r in results if r is not None]
        candidates_list.sort(key=lambda x: x[4], reverse=True)
        
        return candidates_list
    
    def run(self):
        """Run the full matching pipeline"""
        print(f"[*] Graph 1: {len(self.funcs1)} functions")
        print(f"[*] Graph 2: {len(self.funcs2)} functions")
        print(f"[*] Using {self.num_workers} worker processes")
        
        # Statistics
        funcs_with_strings1 = sum(1 for f in self.funcs1.values() if f.strings)
        funcs_with_strings2 = sum(1 for f in self.funcs2.values() if f.strings)
        print(f"[*] Functions with strings: {funcs_with_strings1} / {funcs_with_strings2}")
        
        renamed1 = sum(1 for f in self.funcs1.values() if f.is_renamed)
        renamed2 = sum(1 for f in self.funcs2.values() if f.is_renamed)
        print(f"[*] Named functions: {renamed1} / {renamed2}")
        print()
        
        self.match_by_unique_strings()
        self.match_by_string_similarity()
        self.match_by_signature_and_structure()
        self.propagate_matches(iterations=10)
        self.verify_matches()
        
        print()
        print(f"[*] Total matches: {len(self.matches)}")
        
        # Statistics by reason
        reason_counts = defaultdict(int)
        for reason in self.match_reasons.values():
            base_reason = reason.split("(")[0]
            reason_counts[base_reason] += 1
        
        print("[*] Matches by reason:")
        for reason, count in sorted(reason_counts.items(), key=lambda x: -x[1]):
            print(f"    {reason}: {count}")
        
        # Score distribution
        scores = list(self.match_scores.values())
        if scores:
            avg_score = sum(scores) / len(scores)
            high_conf = sum(1 for s in scores if s >= 0.8)
            med_conf = sum(1 for s in scores if 0.5 <= s < 0.8)
            low_conf = sum(1 for s in scores if s < 0.5)
            print(f"[*] Average confidence: {avg_score:.2f}")
            print(f"[*] High (>=0.8): {high_conf}, Medium (0.5-0.8): {med_conf}, Low (<0.5): {low_conf}")
    
    def export_results(self, output_path: str, include_candidates: bool = True):
        """Export results to file"""
        with open(output_path, 'w', encoding='utf-8') as f:            
            sorted_matches = sorted(
                self.matches.items(),
                key=lambda x: self.match_scores.get(x[0], 0),
                reverse=True
            )
            
            for addr1, addr2 in sorted_matches:
                func1 = self.funcs1[addr1]
                func2 = self.funcs2[addr2]
                score = self.match_scores.get(addr1, 0)

                if not is_auto_name(func1.name) or is_auto_name(func2.name):
                    continue
                
                f.write(f"{func1.name}, {func2.name}, {addr1}, {addr2}, {score:.2f}\n")
            
            if include_candidates:                
                candidates = self.find_candidates_for_unknown(min_score=0.79)
                
                for addr1, name1, addr2, name2, score in candidates[:300]:
                    if not is_auto_name(func1.name) or is_auto_name(func2.name):
                        continue
                    f.write(f"{name1}, {name2}, {addr1}, {addr2}, {score:.2f}\n")
        
        print(f"[*] Results saved to {output_path}")
    
    def export_grouped(self, output_path: str):
        """Export grouped by class names with only unknown functions from graph1
        
        Format:
        [ClassName]
        - 0076c7b0 ClassName::method_name
        - 0076c890 ClassName::another_method
        
        [unnamed namespace]
        - 005ca490 function_name
        """
        grouped_matches = defaultdict(list)
        
        for addr1, addr2 in self.matches.items():
            func1 = self.funcs1[addr1]
            func2 = self.funcs2[addr2]
            
            if not is_auto_name(func1.name):
                continue
            if is_auto_name(func2.name):
                continue
            
            if "::" in func2.name:
                class_name = func2.name.split("::")[0]
                grouped_matches[class_name].append((addr1, func2.name))
            else:
                grouped_matches["unnamed namespace"].append((addr1, func2.name))
        
        sorted_groups = sorted(grouped_matches.items())
        
        with open(output_path, 'w', encoding='utf-8') as f:
            for group_name, functions in sorted_groups:
                f.write(f"[{group_name}]\n")
                
                sorted_funcs = sorted(functions, key=lambda x: x[0])
                
                for addr1, func_name in sorted_funcs:
                    f.write(f"- {addr1} {func_name}\n")
                
                f.write("\n")
        
        total_count = sum(len(funcs) for funcs in grouped_matches.values())
        print(f"[*] Grouped results saved to {output_path}")
        print(f"[*] Total unknown functions identified: {total_count}")
        print(f"[*] Number of groups: {len(grouped_matches)}")

def main():
    parser = argparse.ArgumentParser(
        description='Match function call graphs from two Ghidra projects'
    )
    parser.add_argument('graph1', help='First call graph JSON')
    parser.add_argument('graph2', help='Second call graph JSON')
    parser.add_argument('-o', '--output', default='matches.txt', help='Output file')
    parser.add_argument('--grouped', action='store_true', help='Export grouped by class names (only unknown functions from graph1)')
    parser.add_argument('-j', '--jobs', type=int, default=None, help='Number of parallel workers (default: CPU count - 1)')
    parser.add_argument('--no-candidates', action='store_true', help='Skip candidate generation for faster execution')
    
    args = parser.parse_args()
    
    matcher = CallGraphMatcher(args.graph1, args.graph2, num_workers=args.jobs)
    matcher.run()
    matcher.export_results(args.output, include_candidates=not args.no_candidates)
    
    if args.grouped:
        grouped_path = args.output.replace('.txt', '_grouped.txt')
        matcher.export_grouped(grouped_path)

if __name__ == '__main__':
    main()