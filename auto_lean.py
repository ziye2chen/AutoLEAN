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
    def __init__(self, api_key: str, max_refinement_loops: int = 10):
        """Initialize the AutoLEAN system with Gemini API key."""
        self.client = genai.Client(api_key=api_key)
        self.model = "gemini-2.5-pro"
        self.solution_file = "solutionProcess.lean"
        self.error_file = "all_messages.txt"
        self.error_log_file = "error_log.txt"
        self.solutions_csv = "leanSolutions.csv"
        self.max_refinement_loops = max_refinement_loops
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

    def call_gemini(self, prompt: str, max_retries: int = 3) -> str:
        """Call Gemini API with the given prompt and retry on errors."""
        for attempt in range(max_retries):
            try:
                response = self.client.models.generate_content(
                    model=self.model,
                    contents=prompt
                )
                return response.text
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
2. A clear description of each part

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

    def generate_lean_code_for_part(self, solution: str, num_parts: int,
                                  part_descriptions: str, current_part: int,
                                  existing_code: str = "", error_message: str = "") -> str:
        """Generate Lean4 code for a specific part."""
        if current_part == 1:
            prompt = f"""From the original solution:
{solution}

We divide the solution into {num_parts} parts:
{part_descriptions}

Now, I want to use Lean4 code to represent the process. Let's translate the process into Lean4 code step by step.
Firstly, transfer the process Part 1 into correct and runnable Lean4 code.

Please provide complete, runnable Lean4 code that can be executed. Include all necessary imports and structure.
"""
        else:
            prompt = f"""We divide the solution into {num_parts} parts:
{part_descriptions}

The code until part {current_part - 1} is:
{existing_code}

When I run the code, I got such error:
{error_message}

Please solve it, and transfer the process Part {current_part} into correct and runnable Lean4 code.
And combine the code together with the previous parts.

Please provide complete, runnable Lean4 code that can be executed. Include all necessary imports and structure.
"""

        response = self.call_gemini(prompt)
        print(f"=== GENERATING LEAN4 CODE FOR PART {current_part} ===")
        print(response)
        print("=" * 50)

        # Check if we got a valid response
        if not response or not response.strip():
            print(f"❌ Gemini API returned empty response for Part {current_part}")
            return ""

        # Extract Lean4 code from the response
        # Look for code blocks or specific markers
        if "```lean" in response:
            start = response.find("```lean") + 7
            end = response.find("```", start)
            if end != -1:
                return response[start:end].strip()
        elif "```" in response:
            start = response.find("```") + 3
            end = response.find("```", start)
            if end != -1:
                return response[start:end].strip()

        # If no code blocks found, return the whole response
        return response

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

    def refine_complete_code(self, solution: str, current_code: str, error_message: str) -> str:
        """Refine the complete code based on error messages."""
        prompt = f"""From the original solution:
{solution}

We got the solution with Lean4 Code:
{current_code}

When I run the code I got such error:
{error_message}

Please refine your code according to the error message. Provide complete, corrected Lean4 code.
"""

        response = self.call_gemini(prompt)
        print("=== REFINING COMPLETE CODE ===")
        print(response)
        print("=" * 50)

        # Check if we got a valid response
        if not response or not response.strip():
            print("❌ Gemini API returned empty response for code refinement")
            return ""

        # Extract Lean4 code from the response
        if "```lean" in response:
            start = response.find("```lean") + 7
            end = response.find("```", start)
            if end != -1:
                return response[start:end].strip()
        elif "```" in response:
            start = response.find("```") + 3
            end = response.find("```", start)
            if end != -1:
                return response[start:end].strip()

        return response

    def process_problem(self, problem_data: Dict[str, str]) -> bool:
        """Process a single problem through the complete pipeline."""
        print(f"\n{'='*60}")
        print(f"PROCESSING PROBLEM: {problem_data['id']}")
        print(f"{'='*60}")

        problem = problem_data['problem']
        solution = problem_data['solution']

        # Step 1: Divide solution into parts
        num_parts, part_descriptions = self.divide_solution_into_parts(problem, solution)
        if not part_descriptions:
            print("❌ Failed to divide solution into parts. Skipping this problem.")
            return False
        print(f"Solution divided into {num_parts} parts")

        # Step 2: Generate code for each part
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
                    current_code, ""
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
                            refined_code = self.refine_complete_code(solution, current_code, error_message)
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

            refined_code = self.refine_complete_code(solution, current_code, error_message)
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
    api_key = os.getenv("GEMINI_API_KEY")
    if not api_key:
        api_key = input("Please enter your Gemini API key: ").strip()

    if not api_key:
        print("❌ No API key provided. Exiting.")
        return

    # Initialize and run AutoLEAN
    auto_lean = AutoLEAN(api_key, max_refinement_loops=20)  # Customize max refinement loops
    auto_lean.run()

if __name__ == "__main__":
    main()
