import json
import io
from ghidra.program.model.symbol import SourceType
from ghidra.program.model.listing import Function

def get_full_function_name(func):
    name = func.getName()
    namespace = func.getParentNamespace()
    parts = []
    while namespace is not None and not namespace.isGlobal():
        parts.append(namespace.getName())
        namespace = namespace.getParentNamespace()
    if parts:
        parts.reverse()
        return "::".join(parts) + "::" + name
    return name

def is_renamed(func):
    source = func.getSymbol().getSource()
    if source == SourceType.USER_DEFINED:
        return True
    if source == SourceType.IMPORTED:
        return True
    if source == SourceType.ANALYSIS:
        name = func.getName()
        if not name.startswith("FUN_") and not name.startswith("thunk_"):
            return True
    return False

def get_function_signature(func):
    sig = {
        "return_type": str(func.getReturnType()),
        "params_count": func.getParameterCount(),
        "params": [],
        "calling_convention": str(func.getCallingConventionName()),
        "size": func.getBody().getNumAddresses(),
        "local_vars_count": len(func.getLocalVariables())
    }
    for param in func.getParameters():
        sig["params"].append({
            "name": param.getName(),
            "type": str(param.getDataType()),
            "ordinal": param.getOrdinal()
        })
    return sig

def get_related_functions(func, get_outgoing):
    result = []
    if get_outgoing:
        related = func.getCalledFunctions(monitor)
    else:
        related = func.getCallingFunctions(monitor)
    for f in related:
        result.append(get_full_function_name(f))
    return result

def get_referenced_strings(func):
    strings = []
    listing = currentProgram.getListing()
    address_set = func.getBody()
    seen = set()
    instruction_iter = listing.getInstructions(address_set, True)
    for instr in instruction_iter:
        for ref in instr.getReferencesFrom():
            to_addr = ref.getToAddress()
            addr_str = str(to_addr)
            if addr_str in seen:
                continue
            data = listing.getDataAt(to_addr)
            if data is None:
                data = listing.getDataContaining(to_addr)
            if data is not None and data.hasStringValue():
                str_value = data.getValue()
                if str_value is not None:
                    seen.add(addr_str)
                    strings.append({
                        "address": addr_str,
                        "value": u"{}".format(str_value) if str_value is not None else u""
                    })
    return strings

def export_call_graph():
    program = currentProgram
    func_manager = program.getFunctionManager()
    result = {
        "program_name": program.getName(),
        "image_base": str(program.getImageBase()),
        "language": str(program.getLanguageID()),
        "functions": []
    }
    functions = func_manager.getFunctions(True)
    total = func_manager.getFunctionCount()
    count = 0
    for func in functions:
        if monitor.isCancelled():
            break
        count += 1
        if count % 100 == 0:
            monitor.setMessage("Processing function {} of {}".format(count, total))
        full_name = get_full_function_name(func)
        called_names = get_related_functions(func, True)
        caller_names = get_related_functions(func, False)
        referenced_strings = get_referenced_strings(func)
        parent_ns = func.getParentNamespace()
        namespace_str = str(parent_ns.getName(True)) if not parent_ns.isGlobal() else ""
        func_info = {
            "address": str(func.getEntryPoint()),
            "name": full_name,
            "short_name": func.getName(),
            "namespace": namespace_str,
            "is_renamed": is_renamed(func),
            "is_thunk": func.isThunk(),
            "is_external": func.isExternal(),
            "out_degree": len(called_names),
            "in_degree": len(caller_names),
            "called_names": called_names,
            "caller_names": caller_names,
            "signature": get_function_signature(func),
            "strings": referenced_strings,
            "strings_count": len(referenced_strings)
        }
        result["functions"].append(func_info)
    output_path = str(askFile("Save Call Graph", "Save"))
    
    with open(output_path, 'w') as f:
        json.dump(result, f, separators=(',', ':'))
    
    println("Exported {} functions to {}".format(len(result["functions"]), output_path))

export_call_graph()
