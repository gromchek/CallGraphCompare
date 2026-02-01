## Usage Instructions

Follow these steps to process your data:

### Step 1: Extract Data from Ghidra
1. Open the **Script Manager** (`Window` -> `Script Manager`).
2. Add `ExportCallgraph.py` to scripts and run it.
3. When the script finishes, save the output result as a file named **`335_call_graph.json`** in the project root directory.

### Step 2: Run the Processing Script
Execute the shell script:

```bash
./run.sh all # or you can run the specific version: ./run.sh 410
```