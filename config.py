"""
Configuration file for AutoLEAN system
Modify these settings to customize the behavior of the system.
"""

# Gemini API Configuration
GEMINI_MODEL = "gemini-2.5-pro"  # Default model: "gemini-2.5-pro", Alternative: "gemini-2.5-flash"
GEMINI_TIMEOUT = 60  # seconds
GEMINI_MAX_RETRIES = 3

# Lean4 Configuration
LEAN_TIMEOUT = 60  # seconds for Lean4 execution
LEAN_COMMAND = ["lake", "env", "lean"]
LEAN_ARGS = ["-E", "*"]

# File Configuration
SOLUTION_FILE = "solutionProcess.lean"
ERROR_FILE = "all_messages.txt"
DEFAULT_CSV_FILE = "TestExample.csv"

# Processing Configuration
MAX_REFINEMENTS = 10  # Maximum refinement rounds per problem
MAX_REFINEMENT_LOOPS = 10  # Maximum refinement loops for complete code
DELAY_BETWEEN_PROBLEMS = 5  # seconds between processing different problems
DELAY_BETWEEN_API_CALLS = 1  # seconds between API calls

# Prompt Templates
PROMPTS = {
    "divide_solution": """I have a proof problem:
{problem}

And its solution with latex:
{solution}

Do not change the solution. Please divide the solution into some parts, according to its process.
Please respond with:
1. The number of parts
2. A clear description of each part

Format your response as:
PARTS: [number]
PART 1: [description]
PART 2: [description]
...
""",

    "generate_part1": """From the original solution:
{solution}

We divide the solution into {num_parts} parts:
{part_descriptions}

Now, I want to use Lean4 code to represent the process. Let's translate the process into Lean4 code step by step.
Firstly, transfer the process Part 1 into correct and runnable Lean4 code.

Please provide complete, runnable Lean4 code that can be executed. Include all necessary imports and structure.
""",

    "generate_part_n": """We divide the solution into {num_parts} parts:
{part_descriptions}

The code until part {current_part - 1} is:
{existing_code}

When I run the code, I got such error:
{error_message}

Please solve it, and transfer the process Part {current_part} into correct and runnable Lean4 code.
And combine the code together with the previous parts.

Please provide complete, runnable Lean4 code that can be executed. Include all necessary imports and structure.
""",

    "refine_complete": """From the original solution:
{solution}

We got the solution with Lean4 Code:
{current_code}

When I run the code I got such error:
{error_message}

Please refine your code according to the error message. Provide complete, corrected Lean4 code.
"""
}

# Logging Configuration
LOG_LEVEL = "INFO"  # DEBUG, INFO, WARNING, ERROR
LOG_FORMAT = "%(asctime)s - %(levelname)s - %(message)s"
LOG_FILE = "auto_lean.log"

# Error Handling
IGNORE_ERRORS = [
    "warning",  # Ignore warnings
    "info",     # Ignore info messages
]

# Lean4 Import Suggestions
DEFAULT_IMPORTS = [
    "import Mathlib.Data.Real.Basic",
    "import Mathlib.Data.Nat.Basic",
    "import Mathlib.Algebra.Ring.Basic",
    "import Mathlib.Tactic.NormNum",
    "import Mathlib.Tactic.Ring",
    "import Mathlib.Tactic.Linarith",
]

# Problem Processing
PROBLEM_BATCH_SIZE = 1  # Process problems one at a time
SKIP_COMPLETED = True   # Skip problems that already have solutions
SAVE_INTERMEDIATE = True # Save intermediate results
