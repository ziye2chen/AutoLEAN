#!/usr/bin/env python3
"""
Batch processing script for AutoLEAN
Processes multiple problems with progress tracking and resume capability.
"""

import os
import json
import time
from datetime import datetime
from auto_lean import AutoLEAN
from config import *

class BatchProcessor:
    def __init__(self, api_key: str):
        """Initialize the batch processor."""
        self.auto_lean = AutoLEAN(api_key)
        self.progress_file = "progress.json"
        self.results_dir = "results"
        self.progress = self.load_progress()

        # Create results directory if it doesn't exist
        os.makedirs(self.results_dir, exist_ok=True)

    def load_progress(self) -> dict:
        """Load progress from file."""
        if os.path.exists(self.progress_file):
            try:
                with open(self.progress_file, 'r', encoding='utf-8') as f:
                    return json.load(f)
            except:
                pass
        return {
            "started": datetime.now().isoformat(),
            "problems": {},
            "completed": [],
            "failed": [],
            "current_problem": None
        }

    def save_progress(self):
        """Save progress to file."""
        with open(self.progress_file, 'w', encoding='utf-8') as f:
            json.dump(self.progress, f, indent=2)

    def update_problem_status(self, problem_id: str, status: str, details: str = ""):
        """Update the status of a problem."""
        if problem_id not in self.progress["problems"]:
            self.progress["problems"][problem_id] = {}

        self.progress["problems"][problem_id].update({
            "status": status,
            "last_updated": datetime.now().isoformat(),
            "details": details
        })

        if status == "completed":
            if problem_id not in self.progress["completed"]:
                self.progress["completed"].append(problem_id)
            if problem_id in self.progress["failed"]:
                self.progress["failed"].remove(problem_id)
        elif status == "failed":
            if problem_id not in self.progress["failed"]:
                self.progress["failed"].append(problem_id)

        self.save_progress()

    def save_problem_result(self, problem_id: str, lean_code: str, error_log: str = ""):
        """Save the Lean4 code and error log for a problem."""
        problem_dir = os.path.join(self.results_dir, problem_id)
        os.makedirs(problem_dir, exist_ok=True)

        # Save Lean4 code
        lean_file = os.path.join(problem_dir, "solution.lean")
        with open(lean_file, 'w', encoding='utf-8') as f:
            f.write(lean_code)

        # Save error log
        if error_log:
            error_file = os.path.join(problem_dir, "errors.txt")
            with open(error_file, 'w', encoding='utf-8') as f:
                f.write(error_log)

        # Save metadata
        metadata = {
            "problem_id": problem_id,
            "processed_at": datetime.now().isoformat(),
            "lean_file": lean_file,
            "error_file": error_file if error_log else None
        }

        meta_file = os.path.join(problem_dir, "metadata.json")
        with open(meta_file, 'w', encoding='utf-8') as f:
            json.dump(metadata, f, indent=2)

    def get_problem_summary(self) -> str:
        """Get a summary of processing progress."""
        total = len(self.progress["problems"])
        completed = len(self.progress["completed"])
        failed = len(self.progress["failed"])
        in_progress = total - completed - failed

        return f"""
📊 Processing Summary:
   Total Problems: {total}
   Completed: {completed} ✅
   Failed: {failed} ❌
   In Progress: {in_progress} 🔄
   Progress: {completed/total*100:.1f}% complete
"""

    def process_problem_with_tracking(self, problem_data: dict) -> bool:
        """Process a single problem with progress tracking."""
        problem_id = problem_data['id']

        print(f"\n{'='*60}")
        print(f"PROCESSING PROBLEM: {problem_id}")
        print(f"{'='*60}")

        try:
            # Update status to in progress
            self.progress["current_problem"] = problem_id
            self.update_problem_status(problem_id, "in_progress", "Processing started")
            self.save_progress()

            # Process the problem using AutoLEAN
            success = self.auto_lean.process_problem(problem_data)

            if success:
                # Read the generated code and error log
                lean_code = ""
                error_log = ""

                if os.path.exists(self.auto_lean.solution_file):
                    with open(self.auto_lean.solution_file, 'r', encoding='utf-8') as f:
                        lean_code = f.read()

                if os.path.exists(self.auto_lean.error_file):
                    with open(self.auto_lean.error_file, 'r', encoding='utf-8') as f:
                        error_log = f.read()

                # Save results
                self.save_problem_result(problem_id, lean_code, error_log)

                # Update status
                self.update_problem_status(problem_id, "completed", "Successfully processed")
                print(f"✅ Problem {problem_id} processed successfully")
                return True
            else:
                self.update_problem_status(problem_id, "failed", "Processing failed")
                print(f"❌ Problem {problem_id} failed")
                return False

        except Exception as e:
            error_msg = f"Error: {str(e)}"
            self.update_problem_status(problem_id, "failed", error_msg)
            print(f"❌ Error processing problem {problem_id}: {e}")
            return False

    def run_batch(self, csv_file: str = DEFAULT_CSV_FILE, resume: bool = True):
        """Run batch processing with resume capability."""
        print("🚀 Starting AutoLEAN Batch Processing")
        print("=" * 60)

        # Load problems
        problems = self.auto_lean.load_problems(csv_file)
        print(f"Loaded {len(problems)} problems from {csv_file}")

        # Filter problems based on resume setting
        if resume:
            # Skip completed problems
            problems_to_process = [p for p in problems if p['id'] not in self.progress["completed"]]
            print(f"Resuming: {len(problems_to_process)} problems remaining to process")
        else:
            problems_to_process = problems
            print("Starting fresh: processing all problems")

        # Process problems
        for i, problem_data in enumerate(problems_to_process, 1):
            print(f"\n📝 Problem {i}/{len(problems_to_process)}")

            # Check if we should skip this problem
            if resume and problem_data['id'] in self.progress["completed"]:
                print(f"⏭️  Skipping completed problem {problem_data['id']}")
                continue

            try:
                success = self.process_problem_with_tracking(problem_data)

                # Print summary after each problem
                print(self.get_problem_summary())

                # Add delay between problems
                if i < len(problems_to_process):
                    print(f"Waiting {DELAY_BETWEEN_PROBLEMS} seconds before next problem...")
                    time.sleep(DELAY_BETWEEN_PROBLEMS)

            except KeyboardInterrupt:
                print("\n⚠️  Processing interrupted by user")
                self.progress["current_problem"] = None
                self.save_progress()
                break
            except Exception as e:
                print(f"❌ Unexpected error: {e}")
                continue

        # Final summary
        print("\n🎉 Batch processing completed!")
        print(self.get_problem_summary())

        # Save final progress
        self.progress["current_problem"] = None
        self.save_progress()

    def resume_processing(self, csv_file: str = DEFAULT_CSV_FILE):
        """Resume processing from where it left off."""
        print("🔄 Resuming batch processing...")
        self.run_batch(csv_file, resume=True)

    def restart_processing(self, csv_file: str = DEFAULT_CSV_FILE):
        """Restart processing from the beginning."""
        print("🔄 Restarting batch processing...")
        # Clear progress
        self.progress = {
            "started": datetime.now().isoformat(),
            "problems": {},
            "completed": [],
            "failed": [],
            "current_problem": None
        }
        self.save_progress()
        self.run_batch(csv_file, resume=False)

def main():
    """Main function for batch processing."""
    # Get API key
    api_key = os.getenv("GEMINI_API_KEY")
    if not api_key:
        api_key = input("Please enter your Gemini API key: ").strip()

    if not api_key:
        print("❌ No API key provided. Exiting.")
        return

    # Initialize batch processor
    processor = BatchProcessor(api_key)

    # Show current progress
    print(processor.get_problem_summary())

    # Ask user what to do
    print("\nOptions:")
    print("1. Resume processing (skip completed problems)")
    print("2. Restart processing (process all problems)")
    print("3. Exit")

    choice = input("\nEnter your choice (1-3): ").strip()

    if choice == "1":
        processor.resume_processing()
    elif choice == "2":
        processor.restart_processing()
    elif choice == "3":
        print("Exiting...")
    else:
        print("Invalid choice. Exiting...")

if __name__ == "__main__":
    main()
