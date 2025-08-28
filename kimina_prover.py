#!/usr/bin/env python3
"""
Kimina Prover Lean4 code generation using vLLM

This script uses AI-MO/Kimina-Prover-72B to generate Lean4 code for problems
from TestExample.csv, runs Lean, and writes outputs to all_messages.txt.

It mirrors the prompt structure in the provided template, and saves successful
solutions to leanSolutions.csv (problem_id, lean_code).
"""

import csv
import os
import time
import subprocess
from typing import Dict, List, Optional

from vllm import LLM, SamplingParams
from transformers import AutoTokenizer


MODEL_NAME = "AI-MO/Kimina-Prover-72B"


def load_problems(csv_file: str) -> List[Dict[str, str]]:
    problems: List[Dict[str, str]] = []
    with open(csv_file, 'r', encoding='utf-8') as file:
        reader = csv.DictReader(file)
        for row in reader:
            problems.append({
                'id': row.get('problem_id', '').strip(),
                'problem': row.get('problem', '').strip(),
                'solution': row.get('solution', '').strip(),
                # Optional column 'formal_statement' if present
                'formal_statement': row.get('formal_statement', '').strip() if 'formal_statement' in row else ''
            })
    return problems


def build_formal_statement(problem_id: str, problem_text: str, given_statement: Optional[str]) -> str:
    """Use provided formal statement if available; otherwise create a generic skeleton."""
    if given_statement:
        return given_statement

    theorem_name = f"auto_problem_{problem_id}" if problem_id else "auto_problem"
    return f"""import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/-- {problem_text} -/
theorem {theorem_name} : True := by
  sorry
"""


def build_prompt(problem_text: str, formal_statement: str) -> str:
    prompt = "Think about and solve the following problem step by step in Lean 4."
    prompt += f"\n# Problem:{problem_text}"
    prompt += f"\n# Formal statement:\n```lean4\n{formal_statement}\n```\n"
    return prompt


def extract_lean_code(generation: str) -> str:
    """Extract Lean code from fenced blocks if present; fallback to full text."""
    for fence in ("```lean4", "```lean", "```"):
        if fence in generation:
            start = generation.find(fence) + len(fence)
            end = generation.find("```", start)
            if end != -1:
                return generation[start:end].strip()
    return generation.strip()


def save_solution_file(lean_code: str, path: str = "solutionProcess.lean") -> None:
    with open(path, 'w', encoding='utf-8') as f:
        f.write(lean_code)


def run_lean(solution_path: str = "solutionProcess.lean", log_path: str = "all_messages.txt", timeout_sec: int = 120) -> str:
    try:
        result = subprocess.run(
            ["lake", "env", "lean", solution_path],
            capture_output=True,
            text=True,
            cwd=".",
            timeout=timeout_sec
        )
        combined = (result.stdout or "") + (result.stderr or "")
        with open(log_path, 'w', encoding='utf-8') as f:
            f.write(combined)
        return combined
    except subprocess.TimeoutExpired:
        msg = "Timeout: Lean4 execution took too long"
        with open(log_path, 'w', encoding='utf-8') as f:
            f.write(msg)
        return msg
    except Exception as e:
        msg = f"Error running Lean4: {e}"
        with open(log_path, 'w', encoding='utf-8') as f:
            f.write(msg)
        return msg


def append_success_csv(problem_id: str, lean_code: str, solutions_csv: str = "leanSolutions.csv") -> None:
    file_exists = os.path.exists(solutions_csv)
    with open(solutions_csv, mode='a', encoding='utf-8', newline='') as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=["problem_id", "lean_code"])
        if not file_exists:
            writer.writeheader()
        writer.writerow({"problem_id": problem_id, "lean_code": lean_code})


def generate_with_kimina(problem_text: str, formal_statement: str, temperature: float = 0.6, top_p: float = 0.95, max_tokens: int = 8096) -> str:
    # Initialize model and tokenizer
    model = LLM(
        model=MODEL_NAME,
        # Adjust these settings based on your environment
        tensor_parallel_size=int(os.getenv("KIMINA_TP", "1")),
        max_model_len=int(os.getenv("KIMINA_MAX_LEN", "131072")),
    )
    tokenizer = AutoTokenizer.from_pretrained(MODEL_NAME, trust_remote_code=True)

    messages = [
        {"role": "system", "content": "You are an expert in mathematics and proving theorems in Lean 4."},
        {"role": "user", "content": build_prompt(problem_text, formal_statement)},
    ]
    text = tokenizer.apply_chat_template(messages, tokenize=False, add_generation_prompt=True)
    sampling_params = SamplingParams(temperature=temperature, top_p=top_p, max_tokens=max_tokens)
    outputs = model.generate(text, sampling_params=sampling_params)
    return outputs[0].outputs[0].text


def process_problem(problem: Dict[str, str]) -> bool:
    problem_id = problem['id']
    problem_text = problem['problem']
    formal = build_formal_statement(problem_id, problem_text, problem.get('formal_statement', ''))

    print(f"\nProcessing problem {problem_id} with Kimina Prover...")
    generation = generate_with_kimina(problem_text, formal)
    lean_code = extract_lean_code(generation)

    save_solution_file(lean_code)
    log = run_lean()

    if "error" not in log.lower():
        print("✅ Lean4 code compiled successfully.")
        try:
            append_success_csv(problem_id, lean_code)
        except Exception as e:
            print(f"⚠️  Failed to append to leanSolutions.csv: {e}")
        return True

    print("❌ Compilation errors detected. See all_messages.txt.")
    return False


def main():
    csv_file = os.getenv("AUTOLEAN_CSV", "TestExample.csv")
    problems = load_problems(csv_file)
    print(f"Loaded {len(problems)} problems from {csv_file}")

    for i, p in enumerate(problems, 1):
        print(f"\n—— Problem {i}/{len(problems)}: {p['id']} ——")
        try:
            process_problem(p)
            # small pause to avoid overwhelming the system
            time.sleep(1)
        except KeyboardInterrupt:
            print("Interrupted by user.")
            break
        except Exception as e:
            print(f"Unexpected error: {e}")
            continue

    print("\nDone.")


if __name__ == "__main__":
    main()
