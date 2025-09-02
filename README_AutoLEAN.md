# AutoLEAN: Automatic Lean4 Code Generation using Gemini API

AutoLEAN is an intelligent system that automatically generates Lean4 code from mathematical problems and solutions using Google's Gemini AI. It follows a step-by-step approach to break down complex mathematical proofs and convert them into executable Lean4 code.

## Features

- **Section-based Proof Planning (New)**: Uses Gemini to divide each solution into up to 3 sections (lemmas) and writes them to `sections.csv`
- **Per-Section Code Generation**: Generates Lean4 code section-by-section using the section problem and its natural-language solution
- **Automatic Import Repair with LeanExplore**: Detects missing Mathlib modules and queries LeanExplore to suggest replacement imports
- **Iterative Error-Driven Refinement**: Refines Lean code up to 5 times per section using Gemini, preserving the import list
- **Per-Section Output CSV**: Saves Lean code per section in `lean_sections.csv` with `[fail]` markers when a section fails
- **Batch Processing**: Processes multiple problems from a CSV file
- **Kimina Prover Support**: Generate Lean4 code using AI-MO/Kimina-Prover-72B via vLLM

## Prerequisites

1. **Python 3.8+** installed on your system
2. **Lean4** and **Lake** build system installed
3. **Google Gemini API Key** - Get one from [Google AI Studio](https://makersuite.google.com/app/apikey)
4. **LeanExplore API Key** (optional but recommended) - Obtain an API key and set `LEANEXPLORE_API_KEY` for automatic import repair

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

3. **Set up LeanExplore API key (optional)**
   ```bash
   # Windows
   set LEANEXPLORE_API_KEY=your_leanexplore_api_key_here
   # Linux/Mac
   export LEANEXPLORE_API_KEY=your_leanexplore_api_key_here
   ```

3. **Set up your Gemini API key** (choose one method):

    **Option A: Environment Variable (Recommended)**
    ```bash
    # On Windows
    set GEMINI_API_KEY=your_gemini_api_key_here

    # On Linux/Mac
    export GEMINI_API_KEY=your_gemini_api_key_here
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

### Alternative: Set API Key as Environment Variable in Colab
```python
import os
os.environ['GEMINI_API_KEY'] = 'your_actual_gemini_api_key_here'
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

### Output CSV Formats

1) `sections.csv` (new): sections created per problem
```csv
problem_id,problem,section_number,Problem for Section 1,Solution1,Problem for Section 2,Solution2,Problem for Section 3,Solution3
```

2) `lean_sections.csv` (new): Lean code per section
```csv
problem_id,section_number,lean_section1,lean_section2,lean_section3
```

3) `leanSolutions.csv`: combined Lean code when all sections succeed

```csv
problem_id,lean_code
2023a3,"import Mathlib.Data.Real.Basic...\ntheorem main_result...\n..."
```

### Output Files

- `solutionProcess.lean`: The generated Lean4 code
- `all_messages.txt`: All Lean4 compilation output and error messages
- `leanSolutions.csv`: Successful Lean4 solutions with columns `problem_id` and `lean_code`

## How It Works

### Pipeline Overview (New)

1. **Section Creation**: Gemini divides each problem+solution into at most 3 sections and writes to `sections.csv`.
2. **Per-Section Code Generation**: For each section, generate Lean4 code using the prompt:
   - "Now, I have a proof problem: {Problem for section i} ... Now, solve the proof problem with LEAN4 code."
3. **Run & Import Repair**: Run Lean. If error shows "of module X does not exist", query LeanExplore, replace the missing import with top results.
4. **Error-Guided Refinement**: Ask Gemini to refine code using the current imports. Up to 5 attempts per section.
5. **Per-Section Recording**: Save each section's Lean code to `lean_sections.csv`. If failure occurs at a section, prefix that section with `[fail]`, and set subsequent sections to `None`.
6. **Optional Combine**: If all sections succeed, write combined code to `leanSolutions.csv` for convenience.

### Gemini Prompts Used

1) Section division prompt:
```text
You are an expert mathematician and proof strategist. Your task is to analyze a given mathematical proof problem and its correct solution. Your goal is to break down the solution's logic into a sequence of smaller, self-contained "lemmas" or "theorems" that can be proven sequentially.

## Instructions

Analyze Complexity: First, carefully review the [Correct Solution]. Determine if the proof is complex enough to warrant a breakdown. A complex proof might involve multiple distinct steps, a proof by cases, a key construction, or the use of a significant intermediate result.

Decision to Divide:

- If the solution is simple and short (e.g., a direct application of a definition), do not divide it. Present it as a single part.

- If the solution is complex, divide it into at most 3 logical parts. Each part should be a self-contained statement (a lemma) that builds towards the final proof. The proof of a later part may assume the previous parts have been proven.

Formulate Sub-Problems: For each part, clearly state the theorem or lemma that needs to be proven. Frame it as a precise mathematical statement with latex.

Provide Rationale: Briefly explain the strategy behind your division. Describe how proving these smaller parts in sequence logically leads to the final result.

## Input

Problem to Prove:
{problem}

Correct Solution:
{solution}

Format your response as:
PARTS: [number]
PART 1: [description]
PART 1 Solution: [description]
...
```

2) Section code generation prompt:
```text
Now, I have a proof problem:
{Problem for section 1}

I need to solve the proof problem with LEAN4 code.
For your reference, I have a correct solution with natural language and latex:
{Answer 1 with latex}

Now, solve the proof problem with LEAN4 code.
```

3) Error-driven refinement prompt (imports frozen):
```text
I refine the libraries importing and delete the libraries that do not exist. When I run the code:
{current_lean_code}
I got such error:
{error_message}

Please refine your code according to the error message. Solve the error and provide complete, corrected Lean4 code.

IMPORTANT: You must use ONLY the provided library imports above. Do not add or change any import statements.
```

## Configuration

### API Settings

- **Gemini Model**: Uses `gemini-2.5-pro` by default (better reasoning capabilities)
- **Model Selection**: Can switch between `gemini-2.5-pro` and `gemini-2.5-flash`
- **Multi-turn Conversations**: Each problem uses a new chat session for context retention
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
   - Check environment variable settings

2. **Lean4 Compilation Errors**
   - The system automatically attempts to fix these. For missing module errors, LeanExplore is queried to replace imports.
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
=== GENERATING LEAN4 CODE FOR PART 1 (Gemini) ===
[Gemini response with Lean4 code]
==================================================
Saved Lean4 code to solutionProcess.lean
Running Lean4 code for Part 1...
Part 1 completed successfully!

--- Refinement Round 1 ---
=== REFINING COMPLETE CODE (Gemini) ===
[Gemini response with refined Lean4 code]
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

### Model Selection

The system supports both Gemini models:

```python
# Use Gemini 2.5 Pro (default, better reasoning)
auto_lean = AutoLEAN(api_key, model="gemini-2.5-pro")

# Use Gemini 2.5 Flash (faster, good for simpler tasks)
auto_lean = AutoLEAN(api_key, model="gemini-2.5-flash")
```

**Model Comparison:**
- **Gemini 2.5 Pro**: Better for complex mathematical reasoning, more accurate code generation
- **Gemini 2.5 Flash**: Faster response times, good for simpler problems, lower cost

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
