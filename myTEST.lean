-- We import libraries for real numbers and common tactics.
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
### Problem Setup
-/
variable {f : ℝ → ℝ}

/-!
### Part 1: Rephrasing the Inequality
-/
theorem rephrased_inequality
    (h : ∀ x y, f (x + y) * f (x - y) ≥ f x ^ 2 - f y ^ 2)
    (s t : ℝ) :
    f s * f t ≥ f ((s + t) / 2) ^ 2 - f ((s - t) / 2) ^ 2 := by
  let x := (s + t) / 2
  let y := (s - t) / 2
  convert h x y
  · ring
  · ring

---

/-!
### Part 2: Generating a Second Inequality
-/
theorem second_inequality
    (h : ∀ x y, f (x + y) * f (x - y) ≥ f x ^ 2 - f y ^ 2)
    (s t : ℝ) :
    f s * f (-t) ≥ f ((s - t) / 2) ^ 2 - f ((s + t) / 2) ^ 2 := by
  have h_rephrased := rephrased_inequality h s (-t)
  have rhs_eq : f ((s + -t) / 2) ^ 2 - f ((s - -t) / 2) ^ 2 =
                f ((s - t) / 2) ^ 2 - f ((s + t) / 2) ^ 2 := by
    have arg1_eq : (s + -t) / 2 = (s - t) / 2 := by ring
    have arg2_eq : (s - -t) / 2 = (s + t) / 2 := by ring
    rw [arg1_eq, arg2_eq]
  rw [rhs_eq] at h_rephrased
  exact h_rephrased

---

/-!
### Part 3: Combining the Inequalities
-/
theorem combined_inequality
    (h : ∀ x y, f (x + y) * f (x - y) ≥ f x ^ 2 - f y ^ 2)
    (s t : ℝ) :
    f s * (f t + f (-t)) ≥ 0 := by
  have h1 := rephrased_inequality h s t
  have h2 := second_inequality h s t
  linarith

---

/-!
### Part 4: Reaching the Conclusion (Corrected)
This final proof is corrected to fix the failing tactics.
-/
theorem final_conclusion
    (h : ∀ x y, f (x + y) * f (x - y) ≥ f x ^ 2 - f y ^ 2)
    (h_strict : ∃ x₀ y₀, f (x₀ + y₀) * f (x₀ - y₀) > f x₀ ^ 2 - f y₀ ^ 2) :
    (∀ x, f x ≥ 0) ∨ (∀ x, f x ≤ 0) := by
  obtain ⟨x₀, y₀, h_strict_xy⟩ := h_strict
  let s₀ := x₀ + y₀
  let t₀ := x₀ - y₀

  have h_strict_combined : f s₀ * (f t₀ + f (-t₀)) > 0 := by
    have h1_strict : f s₀ * f t₀ > f ((s₀ + t₀)/2)^2 - f ((s₀ - t₀)/2)^2 := by
      convert h_strict_xy; ring; ring
    have h2_nonstrict := second_inequality h s₀ t₀
    linarith

  -- Prove that the term `f t₀ + f (-t₀)` is non-zero.
  have C_ne_zero : f t₀ + f (-t₀) ≠ 0 := by
    -- `contrapose!` assumes the negation of the goal (`... = 0`)
    -- and sets out to prove the negation of the hypothesis (`... ≤ 0`).
    contrapose! h_strict_combined
    -- Now `h_strict_combined` is the hypothesis `f t₀ + f (-t₀) = 0`.
    -- We rewrite the goal using this hypothesis.
    rw [h_strict_combined]
    -- The goal becomes `f s₀ * 0 ≤ 0`, which is true.
    simp

  let C := f t₀ + f (-t₀)
  have h_general := combined_inequality h

  rcases lt_or_gt_of_ne C_ne_zero with C_neg | C_pos
  · -- Case 1: C is negative. We prove `∀ x, f x ≤ 0`.
    right; intro x; specialize h_general x t₀
    -- We use `by_contra` (a shorthand for `by_contradiction`).
    by_contra h_fx_pos
    -- `h_fx_pos` is the hypothesis `¬(f x ≤ 0)`, which is equivalent to `f x > 0`.
    push_neg at h_fx_pos
    have h_mul_neg : f x * C < 0 := mul_neg_of_pos_of_neg h_fx_pos C_neg
    -- This contradicts `h_general`, which states `f x * C ≥ 0`.
    linarith
  · -- Case 2: C is positive. We prove `∀ x, f x ≥ 0`.
    left; intro x; specialize h_general x t₀
    by_contra h_fx_neg
    push_neg at h_fx_neg
    have h_mul_neg : f x * C < 0 := mul_neg_of_neg_of_pos h_fx_neg C_pos
    linarith
