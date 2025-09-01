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
        """Process a single problem through the complete pipeline."""
        print(f"\n{'='*60}")
        print(f"PROCESSING PROBLEM: {problem_data['id']}")
        print(f"{'='*60}")

        # Create a new chat session for this problem
        self.create_new_chat()

        problem = problem_data['problem']
        solution = problem_data['solution']

        # Step 1: Divide solution into parts
        num_parts, part_descriptions = self.divide_solution_into_parts(problem, solution)
        if not part_descriptions:
            print("❌ Failed to divide solution into parts. Skipping this problem.")
            return False
        print(f"Solution divided into {num_parts} parts")

        # Step 2: Resolve library dependencies
        print("\n--- Resolving Library Dependencies ---")
        library_imports = self.resolve_library_dependencies(solution, num_parts, part_descriptions)

        # Validate and refine library imports
        max_import_retries = 5
        import_retry_count = 0

        while import_retry_count < max_import_retries:
            is_valid, error_message = self.validate_library_imports(library_imports)

            if is_valid:
                print("✅ Library imports validated successfully!")
                break
            else:
                print(f"❌ Library import validation failed: {error_message}")
                if import_retry_count < max_import_retries - 1:
                    print("Refining library imports...")
                    library_imports = self.refine_library_imports(
                        solution, num_parts, part_descriptions, library_imports, error_message
                    )
                    import_retry_count += 1
                else:
                    print("⚠️  Max library import retries reached. Using current imports.")
                    break

        # Step 3: Generate code for each part
        current_code = ""
        for part_num in range(1, num_parts + 1):
            print(f"\n--- Processing Part {part_num}/{num_parts} ---")

            # Keep trying to generate code for this part until successful or max retries reached
            max_part_retries = 3
            part_success = False

            for part_attempt in range(max_part_retries):
                if part_attempt > 0:
                    print(f"Retrying Part {part_num} (attempt {part_attempt + 1}/{max_part_retries})...")

                # Generate code for this part
                new_code = self.generate_lean_code_for_part(
                    solution, num_parts, part_descriptions, part_num,
                    current_code, "", library_imports
                )

                # Check if we got valid code from Gemini
                if new_code and new_code.strip():
                    # Combine with previous code
                    if current_code:
                        current_code = new_code  # The new code should already include previous parts
                    else:
                        current_code = new_code

                    # Save and run the code
                    self.save_lean_code(current_code)
                    print(f"Running Lean4 code for Part {part_num}...")
                    error_message = self.run_lean_code()

                    if error_message and "error" in error_message.lower():
                        print(f"Error in Part {part_num}: {error_message}")

                        # If this is not the last part, continue to next part
                        if part_num < num_parts:
                            part_success = True  # Mark as successful even with errors for non-final parts
                            break
                        else:
                            # For the last part, try to refine the complete code
                            print("Attempting to refine the complete code...")
                            refined_code = self.refine_complete_code(solution, current_code, error_message, library_imports)
                            if refined_code and refined_code != current_code:
                                current_code = refined_code
                                self.save_lean_code(current_code)
                                error_message = self.run_lean_code()
                                part_success = True
                                break
                            else:
                                print("Refinement failed or no changes made.")
                                if part_attempt < max_part_retries - 1:
                                    continue  # Try again
                                else:
                                    print(f"Failed to generate valid code for Part {part_num} after {max_part_retries} attempts.")
                                    break
                    else:
                        print(f"Part {part_num} completed successfully!")
                        part_success = True
                        break
                else:
                    print(f"Gemini API returned empty code for Part {part_num}")
                    if part_attempt < max_part_retries - 1:
                        print("Retrying...")
                        time.sleep(2)
                        continue
                    else:
                        print(f"Failed to get valid code for Part {part_num} after {max_part_retries} attempts.")
                        break

            if not part_success:
                print(f"❌ Failed to process Part {part_num}. Stopping processing for this problem.")
                return False

        # Step 3: Final refinement loop
        refinement_count = 0

        while refinement_count < self.max_refinement_loops:
            error_message = self.run_lean_code()

            if not error_message or "error" not in error_message.lower():
                print("✅ Lean4 code generated successfully!")
                # Save to leanSolutions.csv
                try:
                    self.save_lean_solution_csv(problem_data['id'], current_code)
                except Exception as e:
                    print(f"⚠️  Failed to save to leanSolutions.csv: {e}")
                return True

            print(f"\n--- Refinement Round {refinement_count + 1} ---")
            print(f"Error: {error_message}")

            refined_code = self.refine_complete_code(solution, current_code, error_message, library_imports)
            if not refined_code or refined_code == current_code:
                print("No changes made in refinement, stopping.")
                break

            current_code = refined_code
            self.save_lean_code(current_code)
            refinement_count += 1

        if refinement_count >= self.max_refinement_loops:
            print(f"⚠️  Maximum refinements ({self.max_refinement_loops}) reached. Code may still have issues.")

        return True

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
