/-
# Legendre's chi function χ₂

`chi2 z = ∑_{n ≥ 0} z^(2n+1) / (2n+1)²`, and its summability for `|z| ≤ 1`.
-/
import Mathlib

namespace Chi2U

/-- The `n`-th term of Legendre's chi function `χ₂`. -/
noncomputable def chi2Term (z : ℝ) (n : ℕ) : ℝ := z ^ (2 * n + 1) / (2 * (n : ℝ) + 1) ^ 2

/-- Legendre's chi function `χ₂(z) = ∑_{n ≥ 0} z^(2n+1)/(2n+1)²`. -/
noncomputable def chi2 (z : ℝ) : ℝ := ∑' n : ℕ, chi2Term z n

lemma abs_chi2Term_le {z : ℝ} (hz : |z| ≤ 1) (n : ℕ) :
    |chi2Term z n| ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
  unfold chi2Term
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  have hle : ((n : ℝ) + 1) ^ 2 ≤ (2 * (n : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    nlinarith
  rw [abs_div, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < (2 * (n : ℝ) + 1) ^ 2)]
  calc |z| ^ (2 * n + 1) / (2 * (n : ℝ) + 1) ^ 2
      ≤ 1 / (2 * (n : ℝ) + 1) ^ 2 := by
        gcongr
        exact pow_le_one₀ (abs_nonneg z) hz
    _ ≤ 1 / ((n : ℝ) + 1) ^ 2 := by gcongr

/-- The series defining `χ₂(z)` converges absolutely for `|z| ≤ 1`, so `chi2 z` is its genuine sum. -/
lemma summable_chi2Term {z : ℝ} (hz : |z| ≤ 1) : Summable (chi2Term z) := by
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using this
  exact Summable.of_norm_bounded hs (fun n => by simpa [Real.norm_eq_abs] using abs_chi2Term_le hz n)

end Chi2U
