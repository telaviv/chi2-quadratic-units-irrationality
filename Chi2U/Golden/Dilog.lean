/-
# The dilogarithm on `[-1, 1]` and its link with `χ₂`

`Li2 x = ∑_{n ≥ 0} x^(n+1)/(n+1)²` (the dilogarithm `Li₂`, as a real power series).
This file proves the basic facts used for the golden-ratio closed form of `χ₂(√5 − 2)`:

* `continuousOn_Li2`, `continuousOn_chi2`: both series are continuous on `[-1, 1]` (Weierstrass M-test
  with the summable bound `1/(n+1)²`);
* `Li2_zero`, `Li2_one` (`Li₂(1) = π²/6`, from Mathlib's `hasSum_zeta_two`), `chi2_zero`,
  `chi2_one` (`χ₂(1) = π²/8`, splitting `ζ(2)` into odd and even terms);
* `hasDerivAt_Li2`: `Li₂'(x) = -log(1 - x)/x` for `0 < |x| < 1` (termwise differentiation,
  `hasDerivAt_tsum_of_isPreconnected`, and Mathlib's series for `-log(1 - x)`);
* `chi2_eq_Li2`: `χ₂(x) = ½(Li₂(x) - Li₂(-x))` for `|x| ≤ 1` (even/odd split of the series);
* `hasDerivAt_chi2`: `χ₂'(x) = (log(1 + x) - log(1 - x))/(2x)` for `0 < |x| < 1`.
-/
import Chi2U.Defs

namespace Chi2U
namespace Golden

open Real Filter Topology Set

/-- The `n`-th term of the dilogarithm series. -/
noncomputable def li2Term (x : ℝ) (n : ℕ) : ℝ := x ^ (n + 1) / ((n : ℝ) + 1) ^ 2

/-- The dilogarithm `Li₂(x) = ∑_{n ≥ 0} x^(n+1)/(n+1)²` (meaningful for `|x| ≤ 1`). -/
noncomputable def Li2 (x : ℝ) : ℝ := ∑' n : ℕ, li2Term x n

lemma summable_inv_sq_succ : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa using this

lemma abs_li2Term_le {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) : |li2Term x n| ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
  unfold li2Term
  rw [abs_div, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ 2)]
  gcongr
  exact pow_le_one₀ (abs_nonneg x) hx

lemma summable_li2Term {x : ℝ} (hx : |x| ≤ 1) : Summable (li2Term x) :=
  Summable.of_norm_bounded summable_inv_sq_succ
    (fun n => by simpa [Real.norm_eq_abs] using abs_li2Term_le hx n)

lemma continuousOn_Li2 : ContinuousOn Li2 (Icc (-1) 1) := by
  refine continuousOn_tsum (fun n => ?_) summable_inv_sq_succ (fun n x hx => ?_)
  · exact (by unfold li2Term; fun_prop : Continuous fun x => li2Term x n).continuousOn
  · rw [Real.norm_eq_abs]
    exact abs_li2Term_le (abs_le.mpr hx) n

lemma continuousOn_chi2 : ContinuousOn chi2 (Icc (-1) 1) := by
  refine continuousOn_tsum (fun n => ?_) summable_inv_sq_succ (fun n x hx => ?_)
  · exact (by unfold chi2Term; fun_prop : Continuous fun x => chi2Term x n).continuousOn
  · rw [Real.norm_eq_abs]
    exact abs_chi2Term_le (abs_le.mpr hx) n

lemma continuousAt_Li2 {x : ℝ} (hx : |x| < 1) : ContinuousAt Li2 x :=
  continuousOn_Li2.continuousAt (Icc_mem_nhds (by linarith [neg_abs_le x]) (by linarith [le_abs_self x]))

lemma continuousAt_chi2 {x : ℝ} (hx : |x| < 1) : ContinuousAt chi2 x :=
  continuousOn_chi2.continuousAt (Icc_mem_nhds (by linarith [neg_abs_le x]) (by linarith [le_abs_self x]))

@[simp] lemma Li2_zero : Li2 0 = 0 := by simp [Li2, li2Term]

@[simp] lemma chi2_zero : chi2 0 = 0 := by simp [chi2, chi2Term]

/-- `∑_{n ≥ 0} 1/(n+1)² = π²/6`. -/
lemma hasSum_inv_sq_succ : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
  have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simpa using this

/-- `Li₂(1) = π²/6`. -/
lemma Li2_one : Li2 1 = π ^ 2 / 6 := by
  unfold Li2
  rw [← hasSum_inv_sq_succ.tsum_eq]
  congr 1
  funext n
  simp [li2Term]

/-- `χ₂(1) = ∑ 1/(2n+1)² = π²/8`. -/
lemma chi2_one : chi2 1 = π ^ 2 / 8 := by
  have he : HasSum (fun k : ℕ => 1 / (((2 * k : ℕ) : ℝ) + 1) ^ 2) (chi2 1) := by
    have hfun : (fun k : ℕ => 1 / (((2 * k : ℕ) : ℝ) + 1) ^ 2) = chi2Term 1 := by
      funext k
      simp only [chi2Term, one_pow, Nat.cast_mul, Nat.cast_ofNat]
    rw [hfun]
    exact (summable_chi2Term (z := 1) (by simp)).hasSum
  have ho : HasSum (fun k : ℕ => 1 / (((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2) (π ^ 2 / 6 / 4) := by
    have hfun : (fun k : ℕ => 1 / (((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2) =
        fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 / 4 := by
      funext k
      have : (k : ℝ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    rw [hfun]
    exact hasSum_inv_sq_succ.div_const 4
  have := (HasSum.even_add_odd (f := fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) he ho).unique
    hasSum_inv_sq_succ
  linarith

/-- Termwise derivative of the dilogarithm: `Li₂'(y) = ∑ y^n/(n+1)` for `|y| < 1`. -/
lemma hasDerivAt_Li2_tsum {y : ℝ} (hy : |y| < 1) :
    HasDerivAt Li2 (∑' n : ℕ, y ^ n / ((n : ℝ) + 1)) y := by
  set r : ℝ := (1 + |y|) / 2 with hr
  have hr1 : r < 1 := by rw [hr]; linarith
  have hr0 : |y| < r := by rw [hr]; linarith
  have hrpos' : 0 < r := lt_of_le_of_lt (abs_nonneg y) hr0
  have hrpos : 0 ≤ r := hrpos'.le
  have hmem : y ∈ Ioo (-r) r := ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
  refine hasDerivAt_tsum_of_isPreconnected (g := fun n x => li2Term x n)
    (g' := fun n x => x ^ n / ((n : ℝ) + 1))
    (summable_geometric_of_lt_one hrpos hr1) isOpen_Ioo isPreconnected_Ioo (fun n x _ => ?_)
    (fun n x hx => ?_) (y₀ := 0) ⟨by linarith, by linarith⟩ ?_ hmem
  · have h := (hasDerivAt_pow (n + 1) x).div_const (((n : ℝ) + 1) ^ 2)
    convert h using 1
    · rfl
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    rw [Nat.add_sub_cancel]
    push_cast
    field_simp
  · rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    have hx' : |x| ≤ r := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
    calc |x| ^ n / ((n : ℝ) + 1) ≤ |x| ^ n / 1 := by
          gcongr
          linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      _ ≤ r ^ n := by rw [div_one]; exact pow_le_pow_left₀ (abs_nonneg x) hx' n
  · simp [li2Term]

/-- `Li₂'(y) = -log(1 - y)/y` for `0 < |y| < 1`. -/
lemma hasDerivAt_Li2 {y : ℝ} (hy0 : y ≠ 0) (hy : |y| < 1) :
    HasDerivAt Li2 (-log (1 - y) / y) y := by
  convert hasDerivAt_Li2_tsum hy using 1
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one hy).div_const y
  rw [← h.tsum_eq]
  congr 1
  funext n
  rw [pow_succ]
  field_simp

/-- `χ₂(x) = ½ (Li₂(x) - Li₂(-x))` for `|x| ≤ 1`. -/
lemma chi2_eq_Li2 {x : ℝ} (hx : |x| ≤ 1) : chi2 x = (Li2 x - Li2 (-x)) / 2 := by
  have hx' : |-x| ≤ 1 := by rwa [abs_neg]
  set f : ℕ → ℝ := fun n => li2Term x n - li2Term (-x) n with hf
  have hsum : HasSum f (Li2 x - Li2 (-x)) :=
    (summable_li2Term hx).hasSum.sub (summable_li2Term hx').hasSum
  have he : HasSum (fun k => f (2 * k)) (2 * chi2 x) := by
    have := ((summable_chi2Term hx).hasSum).mul_left 2
    convert this using 1
    swap; · rfl
    funext k
    simp only [hf, li2Term, chi2Term]
    rw [Odd.neg_pow ⟨k, rfl⟩]
    push_cast
    ring
  have ho : HasSum (fun k => f (2 * k + 1)) 0 := by
    convert (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0) using 1
    funext k
    simp only [hf, li2Term]
    rw [Even.neg_pow ⟨k + 1, by ring⟩]
    ring
  have := (he.even_add_odd ho).unique hsum
  linarith

/-- `χ₂'(x) = (log(1 + x) - log(1 - x))/(2x)` for `0 < |x| < 1`. -/
lemma hasDerivAt_chi2 {x : ℝ} (hx0 : x ≠ 0) (hx : |x| < 1) :
    HasDerivAt chi2 ((log (1 + x) - log (1 - x)) / (2 * x)) x := by
  have hx' : |-x| < 1 := by rwa [abs_neg]
  have h1 := hasDerivAt_Li2 hx0 hx
  have h2 := (hasDerivAt_Li2 (neg_ne_zero.mpr hx0) hx').comp x (hasDerivAt_neg x)
  have h := (h1.sub h2).div_const 2
  have hev : (fun t => (Li2 t - (Li2 ∘ fun t => -t) t) / 2) =ᶠ[𝓝 x] chi2 := by
    have hU : Ioo (-1 : ℝ) 1 ∈ 𝓝 x :=
      Ioo_mem_nhds (by linarith [neg_abs_le x]) (by linarith [le_abs_self x])
    filter_upwards [hU] with t ht
    rw [chi2_eq_Li2 (abs_le.mpr ⟨ht.1.le, ht.2.le⟩)]
    rfl
  refine (h.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  rw [sub_neg_eq_add]
  field_simp
  ring

end Golden
end Chi2U
