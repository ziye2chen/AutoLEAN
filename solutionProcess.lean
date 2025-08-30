import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

open Real BigOperators

-- Define the sequence aₙ
noncomputable def a (x : ℕ → ℝ) (n : ℕ) : ℝ :=
Real.sqrt ((∑ i in Finset.range n, x i) * (∑ i in Finset.range n, 1 / x i))

-- Basic properties
theorem a_nonneg (x : ℕ → ℝ) (hpos : ∀ i, x i > 0) (n : ℕ) : a x n ≥ 0 := by
unfold a
exact Real.sqrt_nonneg _

theorem a_increasing (x : ℕ → ℝ) (hpos : ∀ i, x i > 0) (n : ℕ) : a x (n + 1) ≥ a x n := by
unfold a
refine Real.sqrt_le_sqrt ?_
have h1 : ∑ i in Finset.range (n + 1), x i ≥ ∑ i in Finset.range n, x i := by
simp [Finset.sum_range_succ, le_add_of_nonneg_right (hpos n)]
have h2 : ∑ i in Finset.range (n + 1), 1 / x i ≥ ∑ i in Finset.range n, 1 / x i := by
simp [Finset.sum_range_succ, le_add_of_nonneg_right (by positivity)]
exact mul_le_mul h1 h2 (by positivity) (by positivity)

theorem a1_eq_1 (x : ℕ → ℝ) (hx0 : x 0 > 0) : a x 1 = 1 := by
unfold a
simp [Finset.sum_range_one]
rw [Real.sqrt_eq_one]
field_simp [hx0.ne']

theorem a2_gt_2 (x : ℕ → ℝ) (hx0 : x 0 > 0) (hx1 : x 1 > 0) (hneq : x 0 ≠ x 1) : a x 2 > 2 := by
unfold a
have hsum1 : ∑ i in Finset.range 2, x i = x 0 + x 1 := by
simp [Finset.sum_range_succ, Finset.sum_range_one]
have hsum2 : ∑ i in Finset.range 2, 1 / x i = 1/x 0 + 1/x 1 := by
simp [Finset.sum_range_succ, Finset.sum_range_one]
rw [hsum1, hsum2]
have h : (x 0 + x 1) * (1/x 0 + 1/x 1) > 4 := by
calc
(x 0 + x 1) * (1/x 0 + 1/x 1) = 2 + (x 0/x 1 + x 1/x 0) := by
field_simp [hx0.ne', hx1.ne']
ring
_ > 2 + 2 := by
refine add_lt_add_left ?_ 2
have : x 0/x 1 + x 1/x 0 > 2 := by
refine (div_add_div_gt_two_of_ne hneq.symm ?_ ?_).2
exact hx0
exact hx1
exact this
_ = 4 := by norm_num
exact Real.sqrt_lt_sqrt (by positivity) h

-- Part 3: Key inequality: a_{n+1}² ≥ (aₙ + 1)²
theorem key_inequality (x : ℕ → ℝ) (hpos : ∀ i, x i > 0) (n : ℕ) :
a x (n + 1) ^ 2 ≥ (a x n + 1) ^ 2 := by
unfold a
rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
simp_rw [Finset.sum_range_succ]
set S := ∑ i in Finset.range n, x i
set T := ∑ i in Finset.range n, 1 / x i
have hST : S * T = (Real.sqrt (S * T)) ^ 2 := by
rw [Real.sq_sqrt (mul_nonneg (Finset.sum_nonneg fun _ _ => by linarith [hpos _])
(Finset.sum_nonneg fun _ _ => by positivity))]
calc
(S + x n) * (T + 1 / x n) = S * T + 1 + (S / x n + x n * T) := by
field_simp [(hpos n).ne']
ring
_ ≥ S * T + 1 + 2 * Real.sqrt (S * T) := by
refine add_le_add (le_refl _) ?_
have h : S / x n + x n * T ≥ 2 * Real.sqrt (S * T) := by
calc
S / x n + x n * T ≥ 2 * Real.sqrt ((S / x n) * (x n * T)) :=
by exact two_le_add_of_am_gm (S / x n) (x n * T) (by positivity) (by positivity)
_ = 2 * Real.sqrt (S * T) := by
congr 1
field_simp [(hpos n).ne']
exact h
_ = (Real.sqrt (S * T)) ^ 2 + 1 + 2 * Real.sqrt (S * T) := by rw [hST]
_ = (Real.sqrt (S * T) + 1) ^ 2 := by ring

-- Helper lemma for AM-GM
theorem two_le_add_of_am_gm (a b : ℝ) (ha : a > 0) (hb : b > 0) : a + b ≥ 2 * Real.sqrt (a * b) := by
have h : (a + b) ^ 2 ≥ 4 * (a * b) := by
nlinarith [sq_nonneg (a - b)]
linarith [Real.sqrt_le_sqrt (by nlinarith)]

-- Part 4: Equality condition
theorem equality_condition (x : ℕ → ℝ) (hpos : ∀ i, x i > 0) (n : ℕ)
(heq : a x (n + 1) = a x n + 1) :
(∑ i in Finset.range n, x i) / x n = x n * (∑ i in Finset.range n, 1 / x i) := by
have h := key_inequality x hpos n
rw [heq] at h
unfold a at heq
rw [Real.sqrt_inj (by positivity) (by positivity)] at heq
simp_rw [Finset.sum_range_succ] at heq
set S := ∑ i in Finset.range n, x i
set T := ∑ i in Finset.range n, 1 / x i
have hcalc : (S + x n) * (T + 1 / x n) = (S * T) + 1 + (S / x n + x n * T) := by
field_simp [(hpos n).ne']
ring
rw [hcalc] at heq
nlinarith

-- Main claim: cannot have two consecutive +1 increments
theorem no_two_consecutive_single_increments (x : ℕ → ℝ) (hpos : ∀ i, x i > 0)
(hdistinct : ∀ i j, i ≠ j → x i ≠ x j) (n : ℕ)
(h1 : a x (n + 1) = a x n + 1) (h2 : a x (n + 2) = a x (n + 1) + 1) : False := by
have eq1 := equality_condition x hpos n h1
have eq2 := equality_condition x hpos (n + 1) h2
simp_rw [Finset.sum_range_succ] at eq2
field_simp [(hpos n).ne', (hpos (n + 1)).ne'] at eq1 eq2
have : x (n + 1) = x n := by
nlinarith
exact hdistinct n (n + 1) (by omega) this

-- Final result (placeholder)
theorem main_theorem : ∀ (x : ℕ → ℝ), (∀ i, x i > 0) → (∀ i j, i ≠ j → x i ≠ x j) → a x 2023 ≥ 3034 := by
intro x hpos hdistinct
sorry  -- The full combinatorial argument would go here