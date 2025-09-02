-- We must import `.Sum` to get the necessary theorem about sums of cosines.
-- The `.Basic` file does not contain it.
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sum

-- Open namespaces for easier access to `Real`, `pi`, `cos`, etc.
open Real

-- We state the theorem by writing out each term of the sum explicitly.
theorem cos_sum_over_seven_expanded :
    cos (2 * pi * 1 / 7) + cos (2 * pi * 2 / 7) + cos (2 * pi * 3 / 7) +
    cos (2 * pi * 4 / 7) + cos (2 * pi * 5 / 7) + cos (2 * pi * 6 / 7) = -1 := by

  -- The proof starts with a general theorem from mathlib which states that
  -- for n > 1, the sum of cos(2πk/n) from k=0 to n-1 is zero.
  -- We apply this for n=7 to create a hypothesis `h_sum_zero`.
  have h_sum_zero : (∑ i in Finset.range 7, cos (2 * pi * i / 7)) = 0 := by
    apply sum_cos_mul_two_pi_div_eq_zero
    norm_num -- This tactic proves the side-goal that 1 < 7.

  -- Now, we explicitly expand the sum `∑ i in Finset.range 7` into its seven terms
  -- (from i=0 to i=6) by repeatedly using the `Finset.sum_range_succ` lemma.
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one] at h_sum_zero

  -- After expansion, `h_sum_zero` is the hypothesis:
  -- cos(2π*0/7) + cos(2π*1/7) + ... + cos(2π*6/7) = 0
  -- We now simplify the first term, cos(0), which is 1.
  simp only [mul_zero, zero_div, cos_zero, add_left_inj] at h_sum_zero

  -- `h_sum_zero` has now become:
  -- 1 + (cos(2π*1/7) + cos(2π*2/7) + ... + cos(2π*6/7)) = 0
  -- This is a simple algebraic equation. The lemma `eq_neg_of_add_eq_zero_left`
  -- directly solves for the sum. If `1 + x = 0`, then `x = -1`.
  exact eq_neg_of_add_eq_zero_left h_sum_zero
