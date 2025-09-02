#!/usr/bin/env python3
"""
AutoLEAN: Automatic Lean4 Code Generation using Gemini API
This program takes problems and solutions from TestExample.csv and generates Lean4 code step by step.
"""

import csv
import os
import subprocess
import time
from typing import List, Dict, Tuple
from google import genai
import json

class AutoLEAN:
    def __init__(self, gemini_api_key: str, model: str = "gemini-2.5-pro", max_refinement_loops: int = 10):
        """Initialize the AutoLEAN system with Gemini API key and model selection."""
        self.gemini_client = genai.Client(api_key=gemini_api_key)
        self.gemini_model = model
        self.solution_file = "solutionProcess.lean"
        self.error_file = "all_messages.txt"
        self.error_log_file = "error_log.txt"
        self.solutions_csv = "leanSolutions.csv"
        self.max_refinement_loops = max_refinement_loops

        # Initialize chat session (will be created for each problem)
        self.current_chat = None

        # Load mathlib structure
        self.mathlib_structure = self.load_mathlib_structure()
        self._init_error_log()

    # ===================== Sections CSV helpers =====================
    def write_sections_csv(self, problem_row: Dict[str, str], parts: List[Dict[str, str]], out_path: str = "sections.csv") -> None:
        """Append sections info for a problem to sections.csv with specified columns."""
        header = [
            "problem_id", "problem", "section_number",
            "Problem for Section 1", "Solution1",
            "Problem for Section 2", "Solution2",
            "Problem for Section 3", "Solution3",
        ]
        row = {
            "problem_id": problem_row.get("id", ""),
            "problem": problem_row.get("problem", ""),
            "section_number": str(len(parts)),
            "Problem for Section 1": parts[0]["problem"] if len(parts) >= 1 else "None",
            "Solution1": parts[0]["solution"] if len(parts) >= 1 else "None",
            "Problem for Section 2": parts[1]["problem"] if len(parts) >= 2 else "None",
            "Solution2": parts[1]["solution"] if len(parts) >= 2 else "None",
            "Problem for Section 3": parts[2]["problem"] if len(parts) >= 3 else "None",
            "Solution3": parts[2]["solution"] if len(parts) >= 3 else "None",
        }
        file_exists = os.path.exists(out_path)
        with open(out_path, mode='a', encoding='utf-8', newline='') as f:
            w = csv.DictWriter(f, fieldnames=header)
            if not file_exists:
                w.writeheader()
            w.writerow(row)

    def parse_sections_from_response(self, response: str) -> List[Dict[str, str]]:
        """Parse the PARTS/PART i and PART i Solution blocks into list of dicts."""
        lines = [l.strip() for l in response.splitlines()]
        parts: List[Dict[str, str]] = []
        cur: Dict[str, str] = {}
        expecting = None
        for ln in lines:
            if ln.upper().startswith("PART ") and ":" in ln and "Solution" not in ln:
                if cur:
                    parts.append(cur)
                cur = {"problem": ln.split(":", 1)[1].strip(), "solution": ""}
                expecting = "problem"
            elif ("Solution:" in ln) and ":" in ln:
                if not cur:
                    cur = {"problem": "", "solution": ""}
                cur["solution"] = ln.split(":", 1)[1].strip()
                expecting = "solution"
            else:
                if cur and expecting == "solution" and ln:
                    cur["solution"] += ("\n" + ln if cur["solution"] else ln)
                elif cur and expecting == "problem" and ln and not ln.upper().startswith("PARTS:"):
                    cur["problem"] += ("\n" + ln if cur["problem"] else ln)
        if cur:
            parts.append(cur)
        # Trim to at most 3 as required
        return parts[:3] if parts else []

    def divide_solution_into_sections(self, problem_id: str, problem: str, solution: str) -> List[Dict[str, str]]:
        """Use Gemini to divide solution into up to 3 sections and return structured parts."""
        prompt = (
            "You are an expert mathematician and proof strategist. Your task is to analyze a given mathematical proof problem and its correct solution. Your goal is to break down the solution's logic into a sequence of smaller, self-contained \"lemmas\" or \"theorems\" that can be proven sequentially.\n\n"
            "## Instructions\n\n"
            "Analyze Complexity: First, carefully review the [Correct Solution]. Determine if the proof is complex enough to warrant a breakdown. A complex proof might involve multiple distinct steps, a proof by cases, a key construction, or the use of a significant intermediate result.\n\n"
            "Decision to Divide:\n\n- If the solution is simple and short (e.g., a direct application of a definition), do not divide it. Present it as a single part.\n\n- If the solution is complex, divide it into at most 3 logical parts. Each part should be a self-contained statement (a lemma) that builds towards the final proof. The proof of a later part may assume the previous parts have been proven.\n\n"
            "Formulate Sub-Problems: For each part, clearly state the theorem or lemma that needs to be proven. Frame it as a precise mathematical statement with latex.\n\n"
            "Provide Rationale: Briefly explain the strategy behind your division. Describe how proving these smaller parts in sequence logically leads to the final result.\n\n"
            "## Input\n\n"
            f"Problem to Prove:\n{problem}\n\n"
            f"Correct Solution:\n{solution}\n\n"
            "Format your response as:\nPARTS: [number]\nPART 1: [description]\nPART 1 Solution: [description]\nPART 2: [description]\nPART 2 Solution: [description]\nPART 3: [description]\nPART 3 Solution: [description]\n"
        )
        # fresh chat for this call has already been created per problem
        resp = self.call_gemini(prompt)
        parts = self.parse_sections_from_response(resp)
        if not parts:
            parts = [{"problem": problem, "solution": solution}]
        self.write_sections_csv({"id": problem_id, "problem": problem}, parts)
        return parts

    # ===================== Section code pipeline =====================
    def generate_section_code_prompt(self, section_problem: str, section_solution: str) -> str:
        return f"""Now, I have a proof problem:
{section_problem}

I need to solve the proof problem with LEAN4 code.
For your reference, I have a correct solution with natural language and latex:
{section_solution}

Now, solve the proof problem with LEAN4 code.
"""

    def generate_section_lean_code(self, section_problem: str, section_solution: str) -> str:
        """Use Gemini to generate Lean4 code for a given section (problem + solution)."""
        prompt = self.generate_section_code_prompt(section_problem, section_solution)
        response = self.call_gemini(prompt)
        return self._extract_and_clean_lean_code(response)

    # ===================== LeanExplore integration for missing imports =====================
    def extract_missing_module(self, error_output: str) -> str:
        """Extract missing module path from Lean error text."""
        marker = " of module "
        if marker in error_output and " does not exist" in error_output:
            start = error_output.find(marker) + len(marker)
            end = error_output.find(" does not exist", start)
            return error_output[start:end].strip()
        return ""

    def fix_missing_imports_with_lean_explore(self, code: str, missing_module: str) -> str:
        """Use lean-explore to suggest replacement imports for a missing module path and update code."""
        try:
            import asyncio
            from lean_explore.api.client import Client
            from lean_explore.cli import config_utils
        except Exception:
            return code
        try:
            api_key = config_utils.load_api_key()
        except Exception:
            api_key = os.getenv("LEANEXPLORE_API_KEY")
        try:
            async def _do_search(q: str):
                client = Client(api_key=api_key)
                return await client.search(query=q)
            query = (
                "Suggest exact Mathlib import paths that replace missing module '" + missing_module +
                "' and cover equivalent functionality. Return files as Mathlib.X.Y paths."
            )
            res = asyncio.get_event_loop().run_until_complete(_do_search(query))
            results = getattr(res, 'results', []) or []
            # Build candidate import lines from top 20 results
            candidates: List[str] = []
            for item in results[:20]:
                try:
                    src = item.source_file.replace("/", ".").replace("\\", ".")
                    if src.endswith(".lean"):
                        src = src[:-5]
                    if not src.startswith("Mathlib."):
                        src = f"Mathlib.{src}"
                    imp = f"import {src}"
                    if imp not in candidates:
                        candidates.append(imp)
                except Exception:
                    continue
            if not candidates:
                return code
            # Remove the missing import line and insert candidates
            lines = code.splitlines()
            new_lines: List[str] = []
            removed = False
            for ln in lines:
                if not removed and ln.strip().startswith("import ") and missing_module in ln:
                    removed = True
                    continue
                new_lines.append(ln)
            insert_idx = 0
            while insert_idx < len(new_lines) and new_lines[insert_idx].strip().startswith("import "):
                insert_idx += 1
            updated = new_lines[:insert_idx] + candidates + new_lines[insert_idx:]
            return "\n".join(updated)
        except Exception:
            return code

    # ===================== Section results CSV =====================
    def write_lean_sections_csv(self, problem_id: str, section_count: int, section_codes: List[str], failed_idx: int | None, out_path: str = "lean_sections.csv") -> None:
        """Write per-problem lean sections CSV row, with [fail] prefix on failed section and None for unreached sections."""
        header = [
            "problem_id", "section_number", "lean_section1", "lean_section2", "lean_section3"
        ]
        codes = [None, None, None]
        for i in range(min(3, len(section_codes))):
            codes[i] = section_codes[i]
        # Prefix failed section with [fail]
        if failed_idx is not None and 1 <= failed_idx <= 3 and codes[failed_idx-1] is not None:
            codes[failed_idx-1] = f"[fail]\n{codes[failed_idx-1]}"
        row = {
            "problem_id": problem_id,
            "section_number": str(section_count),
            "lean_section1": codes[0] if codes[0] is not None else "None",
            "lean_section2": codes[1] if codes[1] is not None else "None",
            "lean_section3": codes[2] if codes[2] is not None else "None",
        }
        file_exists = os.path.exists(out_path)
        with open(out_path, mode='a', encoding='utf-8', newline='') as f:
            w = csv.DictWriter(f, fieldnames=header)
            if not file_exists:
                w.writeheader()
            w.writerow(row)

    def _init_error_log(self):
        """Initialize the error log file with a header."""
        try:
            with open(self.error_log_file, 'w', encoding='utf-8') as log_file:
                log_file.write("AutoLEAN Error Log\n")
                log_file.write("=" * 60 + "\n")
                log_file.write(f"Started at: {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
                log_file.write("=" * 60 + "\n\n")
        except Exception as e:
            print(f"Warning: Could not initialize error log file: {e}")

    def load_mathlib_structure(self) -> str:
        """Load the mathlib structure from file."""
        try:
            with open("mathlib_structure.txt", 'r', encoding='utf-8') as f:
                return f.read()
        except FileNotFoundError:
            print("Warning: mathlib_structure.txt not found. Using empty structure.")
            return ""
        except Exception as e:
            print(f"Warning: Could not load mathlib structure: {e}")
            return ""

    def load_problems(self, csv_file: str) -> List[Dict[str, str]]:
        """Load problems and solutions from CSV file."""
        problems = []
        with open(csv_file, 'r', encoding='utf-8') as file:
            reader = csv.DictReader(file)
            for row in reader:
                problems.append({
                    'id': row['problem_id'],
                    'problem': row['problem'],
                    'solution': row['solution']
                })
        return problems

    def create_new_chat(self):
        """Create a new chat session for a new problem."""
        self.current_chat = self.gemini_client.chats.create(model=self.gemini_model)
        print(f"🆕 Created new chat session with {self.gemini_model}")

    def send_chat_message(self, message: str) -> str:
        """Send a message to the current chat session and return the response."""
        if not self.current_chat:
            self.create_new_chat()

        try:
            response = self.current_chat.send_message(message)
            return response.text
        except Exception as e:
            print(f"Error sending chat message: {e}")
            return ""

    def get_chat_history(self) -> list:
        """Get the chat history for debugging purposes."""
        if not self.current_chat:
            return []

        try:
            history = []
            for message in self.current_chat.get_history():
                role = message.role
                text = message.parts[0].text if message.parts else ""
                history.append({"role": role, "text": text})
            return history
        except Exception as e:
            print(f"Error getting chat history: {e}")
            return []

    def call_gemini(self, prompt: str, max_retries: int = 3) -> str:
        """Call Gemini API using multi-turn chat and retry on errors."""
        for attempt in range(max_retries):
            try:
                response = self.send_chat_message(prompt)
                if response:
                    return response
                else:
                    raise Exception("Empty response from chat")
            except Exception as e:
                print(f"Error calling Gemini API (attempt {attempt + 1}/{max_retries}): {e}")
                if attempt < max_retries - 1:
                    print("Retrying in 2 seconds...")
                    time.sleep(2)
                else:
                    print("All retry attempts failed. Please check your API key and connection.")
                    return ""
        return ""



    def divide_solution_into_parts(self, problem: str, solution: str) -> Tuple[int, str]:
        """Step 1: Divide the solution into parts using Gemini."""
        prompt = f"""I have a proof problem:
{problem}

And its solution with latex:
{solution}

Do not change the solution. Please divide the solution into some parts, according to its process.
Please respond with:
1. The number of parts
2. A clear description of each part (you can add some equations from the original solution if needed)

Format your response as:
PARTS: [number]
PART 1: [description]
PART 2: [description]
...
"""

        response = self.call_gemini(prompt)
        print("=== DIVIDING SOLUTION INTO PARTS ===")
        print(response)
        print("=" * 50)

        # Check if we got a valid response
        if not response or not response.strip():
            print("❌ Gemini API returned empty response for solution division")
            return 0, ""

        # Parse the response to extract number of parts and descriptions
        lines = response.split('\n')
        num_parts = 0
        part_descriptions = []

        for line in lines:
            if line.startswith('PARTS:'):
                try:
                    num_parts = int(line.split(':')[1].strip())
                except:
                    num_parts = 3  # Default fallback
            elif line.startswith('PART '):
                part_desc = line.split(':', 1)[1].strip() if ':' in line else line
                part_descriptions.append(part_desc)

        if num_parts == 0:
            num_parts = len(part_descriptions) if part_descriptions else 3

        # Validate that we have meaningful part descriptions
        if not part_descriptions or all(not desc.strip() for desc in part_descriptions):
            print("❌ No valid part descriptions found in Gemini response")
            return 0, ""

        return num_parts, '\n'.join(part_descriptions)

    def resolve_library_dependencies(self, solution: str, num_parts: int, part_descriptions: str) -> str:
        """Step 2: Resolve library dependencies using Gemini."""
        prompt = f"""We divide the original solution into {num_parts} parts:
{part_descriptions}

I now need to convert the solution into LEAN4 code with latest Mathlib4. Please analyze and identify all required libraries. And give the libraries with Lean4 code. The libraries dependence should follow the latest mathlib4 structure below:
{self.mathlib_structure}

CRITICAL: All import statements MUST start with "import Mathlib." (not just "import ").
For example, use "import Mathlib.Data.Nat.Basic" not "import Data.Nat.Basic".

Please provide only the import statements that are needed for this solution. Each import should be on a separate line and MUST include the "Mathlib." prefix.
"""

        response = self.call_gemini(prompt)
        print("=== RESOLVING LIBRARY DEPENDENCIES ===")
        print(response)
        print("=" * 50)

        # Extract import statements from the response
        import_lines = []
        for line in response.split('\n'):
            line = line.strip()
            if line.startswith('import '):
                # Fix imports that are missing Mathlib prefix
                if not line.startswith('import Mathlib.') and not line.startswith('import .'):
                    # Add Mathlib prefix
                    module_path = line[7:]  # Remove 'import '
                    line = f"import Mathlib.{module_path}"
                    print(f"Fixed import: {line}")
                import_lines.append(line)

        if not import_lines:
            # Fallback to basic imports if none found
            import_lines = [
                "import Mathlib.Data.Real.Basic",
                "import Mathlib.Data.Nat.Basic",
                "import Mathlib.Algebra.Ring.Basic"
            ]

        return '\n'.join(import_lines)

    def validate_library_imports(self, import_code: str) -> Tuple[bool, str]:
        """Validate library imports by running Lean4."""
        test_code = f"""{import_code}

-- Test theorem to validate imports
theorem test_imports : True := by trivial
"""

        # Save test code
        with open(self.solution_file, 'w', encoding='utf-8') as file:
            file.write(test_code)

        # Run Lean4 to check imports
        error_message = self.run_lean_code()

        if "error" not in error_message.lower():
            return True, ""
        else:
            return False, error_message

    def refine_library_imports(self, solution: str, num_parts: int, part_descriptions: str,
                              current_imports: str, error_message: str) -> str:
        """Refine library imports based on error messages."""
        prompt = f"""From the original solution:
{solution}

We divide the solution into {num_parts} parts:
{part_descriptions}

I tried to use these library imports:
{current_imports}

But when I run the Lean4 code, I got this error:
{error_message}

The mathlib4 structure is:
{self.mathlib_structure}

CRITICAL: All import statements MUST start with "import Mathlib." (not just "import ").
For example, use "import Mathlib.Data.Nat.Basic" not "import Data.Nat.Basic".

Please fix the import statements. Provide only the corrected import statements, one per line, and MUST include the "Mathlib." prefix.
"""

        response = self.call_gemini(prompt)
        print("=== REFINING LIBRARY IMPORTS ===")
        print(response)
        print("=" * 50)

        # Extract import statements from the response
        import_lines = []
        for line in response.split('\n'):
            line = line.strip()
            if line.startswith('import '):
                # Fix imports that are missing Mathlib prefix
                if not line.startswith('import Mathlib.') and not line.startswith('import .'):
                    # Add Mathlib prefix
                    module_path = line[7:]  # Remove 'import '
                    line = f"import Mathlib.{module_path}"
                    print(f"Fixed import: {line}")
                import_lines.append(line)

        return '\n'.join(import_lines) if import_lines else current_imports

    def generate_lean_code_for_part(self, solution: str, num_parts: int,
                                  part_descriptions: str, current_part: int,
                                  existing_code: str = "", error_message: str = "",
                                  library_imports: str = "") -> str:
        """Generate Lean4 code for a specific part using Gemini."""
        if current_part == 1:
            prompt = f"""Since we divide the original solution into {num_parts} parts:
{part_descriptions}

The required library imports are:
{library_imports}

Now, I want to use Lean4 code to represent the process. Let's translate the process into Lean4 code step by step.
Firstly, transfer the process Part 1 into correct and runnable Lean4 code.

IMPORTANT: Try to use the provided library imports above.

Please provide complete, runnable Lean4 code that can be executed. Include the exact import statements provided above.
"""
        else:
            prompt = f"""When I run the Lean4 code you generated, I got such error:
{error_message}

Please solve the error so far. Next, transfer the process Part {current_part} into correct and runnable Lean4 code.
And combine the code together with the previous parts.

IMPORTANT: Try to use the provided library imports above.

Please provide complete, runnable Lean4 code that can be executed. Include the exact import statements provided above.
"""

        response = self.call_gemini(prompt)
        print(f"=== GENERATING LEAN4 CODE FOR PART {current_part} (Gemini) ===")
        print(response)
        print("=" * 50)

        # Check if we got a valid response
        if not response or not response.strip():
            print(f"❌ Gemini returned empty response for Part {current_part}")
            return ""

        # Extract Lean4 code from the response and clean it up
        extracted_code = self._extract_and_clean_lean_code(response)
        return extracted_code

    def _extract_and_clean_lean_code(self, response: str) -> str:
        """Extract Lean4 code from response and clean it up."""
        # Look for code blocks or specific markers
        if "```lean" in response:
            start = response.find("```lean") + 7
            end = response.find("```", start)
            if end != -1:
                code = response[start:end].strip()
            else:
                code = response[start:].strip()
        elif "```" in response:
            start = response.find("```") + 3
            end = response.find("```", start)
            if end != -1:
                code = response[start:end].strip()
            else:
                code = response[start:].strip()
        else:
            # If no code blocks found, return the whole response
            code = response.strip()

        # Clean up the extracted code
        return self._clean_lean_code(code)

    def _clean_lean_code(self, code: str) -> str:
        """Clean up Lean4 code by removing stray characters and ensuring proper structure."""
        if not code:
            return code

        # Split into lines and process
        lines = code.split('\n')
        cleaned_lines = []

        for i, line in enumerate(lines):
            line = line.strip()

            # Skip empty lines at the beginning
            if not line and i == 0:
                continue

            # Skip lines that are just numbers or stray characters at the beginning
            if i == 0 and (line.isdigit() or len(line) == 1 and not line.isalpha()):
                continue

            # Add the line
            cleaned_lines.append(line)

        # Join lines back together
        cleaned_code = '\n'.join(cleaned_lines)

        # Remove any leading/trailing whitespace
        cleaned_code = cleaned_code.strip()

        return cleaned_code

    def save_lean_solution_csv(self, problem_id: str, lean_code: str) -> None:
        """Append the final Lean4 solution to leanSolutions.csv with headers if new."""
        file_exists = os.path.exists(self.solutions_csv)
        with open(self.solutions_csv, mode='a', encoding='utf-8', newline='') as csvfile:
            writer = csv.DictWriter(csvfile, fieldnames=["problem_id", "lean_code"])
            if not file_exists:
                writer.writeheader()
            writer.writerow({"problem_id": problem_id, "lean_code": lean_code})

    def save_lean_code(self, code: str):
        """Save Lean4 code to solutionProcess.lean file."""
        with open(self.solution_file, 'w', encoding='utf-8') as file:
            file.write(code)
        print(f"Saved Lean4 code to {self.solution_file}")

    def run_lean_code(self) -> str:
        """Run the Lean4 code and capture error messages."""
        try:
            # Run the Lean4 code using lake (equivalent to: lake env lean ./solutionProcess.lean > ./all_messages.txt 2>&1)
            result = subprocess.run(
                ["lake", "env", "lean", self.solution_file],
                capture_output=True,
                text=True,
                cwd=".",
                timeout=60
            )

            combined_output = (result.stdout or "") + (result.stderr or "")

            # Save combined stdout and stderr to all_messages.txt
            with open(self.error_file, 'w', encoding='utf-8') as file:
                file.write(combined_output)

            # Log errors to error_log.txt if there are any
            if result.stderr and "error" in result.stderr.lower():
                with open(self.error_log_file, 'a', encoding='utf-8') as log_file:
                    log_file.write(f"\n{'='*60}\n")
                    log_file.write(f"Timestamp: {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
                    log_file.write(f"File: {self.solution_file}\n")
                    log_file.write(f"Error Output:\n{result.stderr}\n")
                    log_file.write(f"{'='*60}\n")

            # Return combined output for downstream error detection
            return combined_output
        except subprocess.TimeoutExpired:
            timeout_msg = "Timeout: Lean4 execution took too long"
            # Log timeout to error log
            with open(self.error_log_file, 'a', encoding='utf-8') as log_file:
                log_file.write(f"\n{'='*60}\n")
                log_file.write(f"Timestamp: {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
                log_file.write(f"File: {self.solution_file}\n")
                log_file.write(f"Error: {timeout_msg}\n")
                log_file.write(f"{'='*60}\n")
            return timeout_msg
        except Exception as e:
            error_msg = f"Error running Lean4: {e}"
            # Log error to error log
            with open(self.error_log_file, 'a', encoding='utf-8') as log_file:
                log_file.write(f"\n{'='*60}\n")
                log_file.write(f"Timestamp: {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
                log_file.write(f"File: {self.solution_file}\n")
                log_file.write(f"Error: {error_msg}\n")
                log_file.write(f"{'='*60}\n")
            return error_msg

    def refine_complete_code(self, solution: str, current_code: str, error_message: str, library_imports: str = "") -> str:
        """Refine the complete code based on error messages using Gemini."""
        prompt = f"""From the original solution:
{solution}

We transfer the solution into Lean4 Code:
{current_code}

When I run the code I got such error:
{error_message}

Please refine your code according to the error message. Solve the error and provide complete, corrected Lean4 code.

IMPORTANT: You must use ONLY the provided library imports above. Do not add or change any import statements.
"""

        response = self.call_gemini(prompt)
        print("=== REFINING COMPLETE CODE (Gemini) ===")
        print(response)
        print("=" * 50)

        # Check if we got a valid response
        if not response or not response.strip():
            print("❌ Gemini returned empty response for code refinement")
            return ""

        # Extract and clean the Lean4 code from the response
        extracted_code = self._extract_and_clean_lean_code(response)
        return extracted_code

    def process_problem(self, problem_data: Dict[str, str]) -> bool:
        """Process a single problem using the new section-based pipeline."""
        print(f"\n{'='*60}")
        print(f"PROCESSING PROBLEM: {problem_data['id']}")
        print(f"{'='*60}")

        # Create a new chat session for this problem
        self.create_new_chat()

        problem = problem_data['problem']
        solution = problem_data['solution']

        # Step 1: Divide into sections using the new prompt and write to sections.csv
        parts = self.divide_solution_into_sections(problem_data['id'], problem, solution)
        if not parts:
            print("❌ Failed to divide into sections. Skipping this problem.")
            return False

        print(f"Section count: {len(parts)}")

        # Step 2: For each section, generate Lean code, run, and refine up to 5 times
        section_codes: List[str] = []
        failed_idx: int | None = None

        for idx, part in enumerate(parts, start=1):
            print(f"\n--- Processing Section {idx}/{len(parts)} ---")
            section_problem = part.get("problem", "")
            section_solution = part.get("solution", "")

            # Initial generation
            current_code = self.generate_section_lean_code(section_problem, section_solution)
            if not current_code:
                print("❌ Empty code generated for this section.")
                failed_idx = idx
                section_codes.append("")
                break

            # Save and run
            self.save_lean_code(current_code)
            output = self.run_lean_code()

            # Up to 5 refinement attempts per section
            max_attempts = 5
            attempts = 0
            while attempts < max_attempts and (output and "error" in output.lower()):
                attempts += 1
                print(f"Refinement attempt {attempts}/{max_attempts} for Section {idx}")

                # Step 3: If missing module error, fix imports using LeanExplore
                missing_module = self.extract_missing_module(output)
                if missing_module:
                    print(f"Detected missing module: {missing_module}. Trying LeanExplore suggestions...")
                    updated = self.fix_missing_imports_with_lean_explore(current_code, missing_module)
                    if updated != current_code:
                        current_code = updated
                        self.save_lean_code(current_code)
                        output = self.run_lean_code()
                        continue

                # Step 4: Use Gemini to refine code, but do not change imports
                # Extract current imports from code
                import_lines = []
                for ln in current_code.splitlines():
                    if ln.strip().startswith("import "):
                        import_lines.append(ln.strip())
                    else:
                        # stop at first non-import once imports are gathered
                        if import_lines:
                            break
                library_imports = "\n".join(import_lines)

                prompt = (
                    "I refine the libraries importing and delete the libraries that do not exist. When I run the code:\n"
                    f"{current_code}\n"
                    "I got such error:\n"
                    f"{output}\n\n"
                    "Please refine your code according to the error message. Solve the error and provide complete, corrected Lean4 code.\n\n"
                    "IMPORTANT: You must use ONLY the provided library imports above. Do not add or change any import statements."
                )
                refined = self.call_gemini(prompt)
                refined_code = self._extract_and_clean_lean_code(refined)
                if refined_code and refined_code != current_code:
                    # Ensure imports are unchanged
                    refined_imports = []
                    for ln in refined_code.splitlines():
                        if ln.strip().startswith("import "):
                            refined_imports.append(ln.strip())
                        else:
                            if refined_imports:
                                break
                    if "\n".join(refined_imports) != library_imports:
                        # Restore original imports
                        rest = refined_code.split("\n")
                        # Remove refined import block
                        i = 0
                        while i < len(rest) and rest[i].strip().startswith("import "):
                            i += 1
                        refined_code = library_imports + "\n" + "\n".join(rest[i:])

                    current_code = refined_code
                    self.save_lean_code(current_code)
                    output = self.run_lean_code()
                else:
                    # No useful refinement; stop early
                    break

            # After attempts, check success
            if output and "error" in output.lower():
                print(f"❌ Section {idx} failed after {max_attempts} attempts.")
                failed_idx = idx
                section_codes.append(current_code)
                break
            else:
                print(f"✅ Section {idx} succeeded.")
                section_codes.append(current_code)
                # proceed to next section

        # Write per-problem lean sections CSV row
        self.write_lean_sections_csv(problem_data['id'], len(parts), section_codes, failed_idx)

        # If all sections succeeded, also save to leanSolutions.csv as combined code
        if failed_idx is None:
            try:
                combined_code = "\n\n/-- Combined sections below --/\n\n" + "\n\n".join(section_codes)
                self.save_lean_solution_csv(problem_data['id'], combined_code)
            except Exception as e:
                print(f"⚠️  Failed to save combined solution: {e}")

        return failed_idx is None

    def set_max_refinement_loops(self, max_loops: int) -> None:
        """Set the maximum number of refinement loops for complete code."""
        if max_loops < 1:
            raise ValueError("Maximum refinement loops must be at least 1")
        self.max_refinement_loops = max_loops
        print(f"Maximum refinement loops set to: {max_loops}")

    def run(self, csv_file: str = "TestExample.csv"):
        """Run the complete AutoLEAN pipeline."""
        print("🚀 Starting AutoLEAN Pipeline")
        print("=" * 60)

        # Load problems
        problems = self.load_problems(csv_file)
        print(f"Loaded {len(problems)} problems from {csv_file}")

        # Process each problem
        for i, problem_data in enumerate(problems, 1):
            print(f"\n📝 Problem {i}/{len(problems)}")
            try:
                success = self.process_problem(problem_data)
                if success:
                    print(f"✅ Problem {problem_data['id']} processed successfully")
                else:
                    print(f"❌ Problem {problem_data['id']} failed")

                # Add delay between problems to avoid API rate limits
                if i < len(problems):
                    print("Waiting 5 seconds before next problem...")
                    time.sleep(5)

            except Exception as e:
                print(f"❌ Error processing problem {problem_data['id']}: {e}")
                continue

        print("\n🎉 AutoLEAN Pipeline completed!")

def main():
    """Main function to run AutoLEAN."""
    # Get API key from environment variable or user input
    gemini_api_key = os.getenv("GEMINI_API_KEY")
    if not gemini_api_key:
        gemini_api_key = input("Please enter your Gemini API key: ").strip()

    if not gemini_api_key:
        print("❌ No Gemini API key provided. Exiting.")
        return

    # Model selection
    print("\n🤖 Model Selection:")
    print("1. Gemini 2.5 Pro (Recommended for complex reasoning)")
    print("2. Gemini 2.5 Flash (Faster, good for simpler tasks)")

    model_choice = input("Select model (1 or 2, default: 1): ").strip()

    if model_choice == "2":
        model = "gemini-2.5-flash"
        print("✅ Selected: Gemini 2.5 Flash")
    else:
        model = "gemini-2.5-pro"
        print("✅ Selected: Gemini 2.5 Pro")

    # Initialize and run AutoLEAN
    auto_lean = AutoLEAN(gemini_api_key, model, max_refinement_loops=20)
    auto_lean.run()

if __name__ == "__main__":
    main()
