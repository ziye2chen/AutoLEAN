# AutoLEAN: Automatic Lean4 Code Generation using Gemini API

AutoLEAN is an intelligent system that automatically generates Lean4 code from mathematical problems and solutions using Google's Gemini AI. It follows a step-by-step approach to break down complex mathematical proofs and convert them into executable Lean4 code.

## Features

- **Automatic Problem Analysis**: Divides complex mathematical solutions into logical parts
- **Step-by-Step Code Generation**: Generates Lean4 code for each part incrementally
- **Error Detection and Correction**: Automatically detects and fixes Lean4 compilation errors
- **Iterative Refinement**: Continuously improves the generated code based on error messages
- **Batch Processing**: Can process multiple problems from a CSV file
- **Kimina Prover Support**: Generate Lean4 code using AI-MO/Kimina-Prover-72B via vLLM

## Prerequisites

1. **Python 3.8+** installed on your system
2. **Lean4** and **Lake** build system installed
3. **Google Gemini API Key** - Get one from [Google AI Studio](https://makersuite.google.com/app/apikey)
4. **OpenRouter API Key** - Get one from [OpenRouter](https://openrouter.ai/) for DeepSeek Prover v2 access

## Installation

1. **Clone or navigate to the AutoLEAN directory**
   ```bash
   cd /path/to/AutoLEAN
   ```

2. **Install Python dependencies**
   ```bash
   pip install -r requirements.txt
   ```

   For Kimina Prover with vLLM, ensure a compatible CUDA + GPUs setup. On Windows, vLLM is not officially supported; use WSL/Linux.

3. **Set up your API keys** (choose one method):

    **Option A: Environment Variables (Recommended)**
    ```bash
    # On Windows
    set GEMINI_API_KEY=your_gemini_api_key_here
    set OPENROUTER_API_KEY=your_openrouter_api_key_here

    # On Linux/Mac
    export GEMINI_API_KEY=your_gemini_api_key_here
    export OPENROUTER_API_KEY=your_openrouter_api_key_here
    ```

    **Option B: Direct input when running the program**

## Running in Google Colab

If you want to run the project in Google Colab, follow these steps:

### Step 1: Clone the Repository
```python
!git clone https://github.com/ziye2chen/AutoLEAN.git
```

### Step 2: Install Lean4 and Lake
```python
# Run the elan (Lean version manager) installer non-interactively
!curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
```

### Step 3: Set Environment Variables
```python
import os
os.environ['PATH'] = f"/root/.elan/bin:{os.environ['PATH']}"
```

### Step 4: Verify Installation
```python
# Check the versions to confirm the installation worked
!lean --version
!lake --version
```

### Step 5: Navigate to Project Directory and Setup
```python
%cd AutoLEAN
!lake exe cache get
```

### Step 6: Run AutoLEAN
```python
!python auto_lean.py
```

### Important Notes for Colab Users:
- **Runtime Type**: Use a GPU runtime for better performance, especially if using Kimina Prover
- **Session Duration**: Colab sessions have time limits, so long-running processes may be interrupted
- **File Persistence**: Files created in Colab will be lost when the session ends unless you download them
- **API Key**: You'll need to input your Gemini API key when prompted, or set it as an environment variable
- **Dependencies**: The `lake exe cache get` command downloads necessary Lean4 dependencies

### Alternative: Set API Keys as Environment Variables in Colab
```python
import os
os.environ['GEMINI_API_KEY'] = 'your_actual_gemini_api_key_here'
os.environ['OPENROUTER_API_KEY'] = 'your_actual_openrouter_api_key_here'
```

## Usage

### Basic Usage

Run the AutoLEAN system:

```bash
python auto_lean.py
```
### Kimina Prover Usage (vLLM)

Generate Lean4 code with Kimina Prover:

```bash
python kimina_prover.py
```

Environment variables:

- `AUTOLEAN_CSV` (optional): path to CSV (default `TestExample.csv`)
- `KIMINA_TP` (optional): tensor parallel size (default `1`)
- `KIMINA_MAX_LEN` (optional): max model length (default `131072`)

Notes:

- Model: `AI-MO/Kimina-Prover-72B`
- Requires multiple GPUs for best performance; adjust `KIMINA_TP` accordingly
- Output is saved to `solutionProcess.lean`, logs to `all_messages.txt`, and successful solutions to `leanSolutions.csv`


The system will:
1. Load problems from `TestExample.csv`
2. Process each problem through the complete pipeline
3. Generate Lean4 code step by step
4. Save results to `solutionProcess.lean`

### Input Format

The system expects a CSV file (`TestExample.csv`) with the following columns:
- `problem_id`: Unique identifier for the problem
- `problem`: The mathematical problem statement (LaTeX format)
- `solution`: The solution to the problem (LaTeX format)

Example:
```csv
problem_id,problem,solution
2023a3,"Let x₁, x₂, ..., x₂₀₂₃ be distinct real positive numbers...","We start with some basic observations..."
```

### Output CSV Format

The system generates `leanSolutions.csv` containing successfully compiled Lean4 code:

```csv
problem_id,lean_code
2023a3,"import Mathlib.Data.Real.Basic...\ntheorem main_result...\n..."
```

### Output Files

- `solutionProcess.lean`: The generated Lean4 code
- `all_messages.txt`: All Lean4 compilation output and error messages
- `leanSolutions.csv`: Successful Lean4 solutions with columns `problem_id` and `lean_code`

## How It Works

### Pipeline Overview

1. **Solution Division**: Uses Gemini 2.5 Pro to break down the mathematical solution into logical parts
2. **Library Dependency Resolution**: Uses Gemini 2.5 Pro to identify and validate required Mathlib4 imports
3. **Incremental Code Generation**: Uses DeepSeek Prover v2 to generate Lean4 code for each part sequentially
4. **Error Detection**: Runs the Lean4 code and captures any compilation errors
5. **Iterative Refinement**: Uses DeepSeek Prover v2 to fix errors and improve the code
6. **Final Validation**: Ensures the complete code compiles successfully

### Detailed Process

#### Step 1: Solution Analysis
```
Input: Problem + Solution
Output: Number of parts + Part descriptions
```

#### Step 2: Library Dependency Resolution
```
Input: Solution + Part descriptions + Mathlib4 structure
Output: Validated import statements
```

#### Step 3: Part-by-Part Code Generation
For each part:
```
Input: Part description + Previous code + Error messages + Library imports
Output: Lean4 code for current part (using DeepSeek Prover v2)
```

#### Step 4: Code Refinement
```
Input: Complete code + Error messages + Library imports
Output: Refined and corrected Lean4 code (using DeepSeek Prover v2)
```

## Configuration

### API Settings

- **Gemini Model**: Uses `gemini-2.5-pro` by default (better reasoning capabilities)
- **DeepSeek Model**: Uses `deepseek/deepseek-prover-v2` via OpenRouter
- **Rate Limiting**: Includes 5-second delays between problems
- **Timeout**: 60 seconds for Lean4 execution

### Refinement Settings

- **Maximum Refinements**: 10 rounds per problem
- **Maximum Refinement Loops**: 10 loops for complete code (configurable)
- **Error Threshold**: Continues until no compilation errors or max loops reached

## Troubleshooting

### Common Issues

1. **API Key Errors**
   - Ensure your Gemini API key is valid and has sufficient quota
   - Ensure your OpenRouter API key is valid for DeepSeek Prover v2 access
   - Check environment variable settings

2. **Lean4 Compilation Errors**
   - The system automatically attempts to fix these
   - Check `all_messages.txt` for detailed error information

3. **Timeout Errors**
   - Complex problems may take longer to process
   - Consider breaking down very large solutions manually

### Debug Mode

To see detailed output, the system provides verbose logging of:
- Gemini API responses
- Lean4 compilation results
- Error messages and fixes

## Example Output

```
🚀 Starting AutoLEAN Pipeline
============================================================
Loaded 3 problems from TestExample.csv

============================================================
PROCESSING PROBLEM: 2023a3
============================================================
=== DIVIDING SOLUTION INTO PARTS ===
PARTS: 4
PART 1: Basic observations and initial setup
PART 2: Main argument and claim statement
PART 3: Proof of the claim
PART 4: Final contradiction and conclusion
==================================================

--- Resolving Library Dependencies ---
=== RESOLVING LIBRARY DEPENDENCIES ===
[Gemini response with import statements]
==================================================
✅ Library imports validated successfully!

--- Processing Part 1/4 ---
=== GENERATING LEAN4 CODE FOR PART 1 (DeepSeek Prover v2) ===
[DeepSeek Prover v2 response with Lean4 code]
==================================================
Saved Lean4 code to solutionProcess.lean
Running Lean4 code for Part 1...
Part 1 completed successfully!

--- Refinement Round 1 ---
=== REFINING COMPLETE CODE (DeepSeek Prover v2) ===
[DeepSeek Prover v2 response with refined Lean4 code]
==================================================

✅ Problem 2023a3 processed successfully
```

## Advanced Usage

### Custom Problem Files

To use a different CSV file:
```python
auto_lean = AutoLEAN(api_key)
auto_lean.run("your_custom_file.csv")
```

### Single Problem Processing

To process just one problem:
```python
problems = auto_lean.load_problems("TestExample.csv")
auto_lean.process_problem(problems[0])  # Process first problem only
```

### Customizing Refinement Loops

To set a custom number of maximum refinement loops:
```python
auto_lean = AutoLEAN(api_key, max_refinement_loops=20)  # Allow up to 20 refinement attempts
# Or change at runtime:
auto_lean.set_max_refinement_loops(15)
```

## Contributing

The AutoLEAN system is designed to be extensible. Key areas for improvement:

1. **Prompt Engineering**: Optimize Gemini prompts for better code generation
2. **Error Handling**: Improve error detection and correction strategies
3. **Code Quality**: Enhance the quality of generated Lean4 code
4. **Performance**: Optimize processing speed and API usage

## License

This project is part of the AutoLEAN system and follows the same license as the parent repository.

## Support

For issues and questions:
1. Check the troubleshooting section above
2. Review the error messages in `all_messages.txt`
3. Ensure your Lean4 environment is properly configured
4. Verify your Gemini API key has sufficient quota

---

**Note**: AutoLEAN is designed to assist with mathematical proof formalization but may require manual review and refinement for complex proofs. Always verify the generated code before using it in production environments.
