-- Import necessary libraries from Mathlib for numbers, finite sets, and sums.
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

/-!
### Part 1: Generalizing the Problem and Defining "Score"

This section sets up the formal context for the proof. It generalizes the
problem to use a variable `N` and defines the `score` function. In the
original problem, `2 * N - 1 = 2023`, so `N = 1012`.
-/

-- We declare `N` as a variable representing any positive natural number.
variable (N : ℕ) (hN : 0 < N)

/-- The score of a number `x` is its absolute distance from the central value `N`.
This corresponds to `s(x) := |x - N|` in the proof. -/
def score (x : ℕ) : ℕ := Nat.dist x N

-- This theorem statement formalizes the generalized problem.
theorem generalized_problem :
  -- Let `a` be a sequence of `2N-1` natural numbers.
  ∀ (a : Fin (2 * N - 1) → ℕ),

  -- Condition 1: `a` is a permutation of `1, 2, ..., 2N-1`.
  (h_perm_a : Finset.image a Finset.univ = Finset.Icc 1 (2 * N - 1)) →

  -- Condition 2: The absolute differences `|aᵢ - aᵢ₊₁|` form a permutation of `1, ..., 2N-2`.
  (h_perm_diffs :
    let diffs := fun (i : Fin (2 * N - 2)) => Nat.dist (a i.castSucc) (a (i.castSucc.succ))
    Finset.image diffs Finset.univ = Finset.Icc 1 (2 * N - 2)) →

  -- Conclusion: The sum of the first and last terms is at least `N + 1`.
  a 0 + a (Fin.last (2 * N - 2)) ≥ N + 1 := by
  -- We introduce the hypotheses into the proof context.
  intros a h_perm_a h_perm_diffs

  /-!
  ### Part 2: The Core Inequality using Triangle Inequality

  This part of the proof establishes a crucial link between the absolute
  difference of two numbers and the sum of their scores. The mathematical
  statement is `|a - b| ≤ s(a) + s(b)`. In Lean, we prove this as a local
  helper lemma using `Nat.dist_triangle`.
  -/

  have triangle_inequality_with_score : ∀ x y, Nat.dist x y ≤ score N x + score N y := by
    -- Let x and y be any two natural numbers.
    intros x y
    -- The proof follows from the triangle inequality for natural numbers: dist(a, c) ≤ dist(a, b) + dist(b, c)
    -- We apply this with a=x, b=N, c=y.
    calc
      -- `Nat.dist x y` is `|x - y|`
      Nat.dist x y ≤ Nat.dist x N + Nat.dist N y := Nat.dist_triangle x N y
      -- By commutativity of distance, `dist(N, y) = dist(y, N)`.
      _ = Nat.dist x N + Nat.dist y N           := by rw [Nat.dist_comm N y]
      -- By definition, `dist(x, N)` is `score N x`.
      _ = score N x + score N y                 := by rfl

  -- The rest of the proof will continue from here.
  sorry
