/-
# The irrationality criterion (Lemma E)

If `P h ∈ ℚ[X]` has degree `≤ h`, `den h • P h` has integer coefficients (`den h > 0` rational),
`den h · |P h(ξ)| ≤ exp(−c h²)` eventually, and for every `a/b` the value `P h (a/b)` is nonzero
for infinitely many `h`, then `ξ` is irrational.
Only infinitely many good `h` are needed.
-/
import Mathlib

namespace Chi2U

open Polynomial Filter Topology

/-- If `d • P` has integer coefficients and `natDegree P ≤ h`, then `b^h · d · P(a/b)` is an integer. -/
lemma exists_int_eval_mul {P : ℚ[X]} {h : ℕ} (hdeg : P.natDegree ≤ h) {d : ℚ}
    (hint : ∀ k, ∃ z : ℤ, d * P.coeff k = z) (a : ℤ) {b : ℕ} (hb : 0 < b) :
    ∃ N : ℤ, (N : ℚ) = (b : ℚ) ^ h * (d * P.eval ((a : ℚ) / b)) := by
  choose z hz using hint
  refine ⟨∑ k ∈ Finset.range (h + 1), z k * a ^ k * (b : ℤ) ^ (h - k), ?_⟩
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hdeg), Finset.mul_sum, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hkh : k ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [← hz k]
  have hpow : (b : ℚ) ^ h = (b : ℚ) ^ (h - k) * (b : ℚ) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hkh]
  rw [hpow, div_pow]
  field_simp

/-- Evaluating a rational polynomial at a rational point commutes with the cast to `ℝ`. -/
lemma aeval_ratCast (P : ℚ[X]) (r : ℚ) : aeval (r : ℝ) P = ((P.eval r : ℚ) : ℝ) := by
  rw [← eq_ratCast (algebraMap ℚ ℝ) r, aeval_algebraMap_apply, eq_ratCast, coe_aeval_eq_eval]

/-- Eventually `b^h · exp(−c h²) < 1`. -/
lemma eventually_pow_mul_exp_lt_one {c : ℝ} (hc : 0 < c) {b : ℕ} (hb : 0 < b) :
    ∀ᶠ h : ℕ in atTop, (b : ℝ) ^ h * Real.exp (-c * (h : ℝ) ^ 2) < 1 := by
  filter_upwards [eventually_gt_atTop ⌈Real.log b / c⌉₊] with h hh
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have hlb : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast hb)
  have hh' : Real.log b / c < h := Nat.lt_of_ceil_lt hh
  have hlog : Real.log b < c * h := by
    have := (div_lt_iff₀ hc).mp hh'
    linarith
  have hh0 : (0 : ℝ) < h := by
    have : (0 : ℝ) ≤ Real.log b / c := div_nonneg hlb hc.le
    linarith
  rw [← Real.exp_log (pow_pos hbpos h), Real.log_pow, ← Real.exp_add, ← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by nlinarith)

/-- **Lemma E.** Small, infinitely often nonzero values of integer polynomials of degree `≤ h`
force irrationality. -/
theorem irrational_of_poly_approx (ξ : ℝ) (P : ℕ → ℚ[X]) (hdeg : ∀ h, (P h).natDegree ≤ h)
    (den : ℕ → ℚ) (hden : ∀ h, 0 < den h)
    (hint : ∀ h k, ∃ z : ℤ, den h * (P h).coeff k = z)
    (c : ℝ) (hc : 0 < c)
    (hsmall : ∀ᶠ h in atTop, (den h : ℝ) * |aeval ξ (P h)| ≤ Real.exp (-c * (h : ℝ) ^ 2))
    (hnv : ∀ (a : ℤ) (b : ℕ), 0 < b → ∃ᶠ h in atTop, (P h).eval ((a : ℚ) / b) ≠ 0) :
    Irrational ξ := by
  rintro ⟨r, rfl⟩
  have hb : 0 < r.den := r.pos
  have hr : (r.num : ℚ) / r.den = r := Rat.num_div_den r
  obtain ⟨h, hnz, hsm, hbg⟩ :=
    ((hnv r.num r.den hb).and_eventually
      (hsmall.and (eventually_pow_mul_exp_lt_one hc hb))).exists
  obtain ⟨N, hN⟩ := exists_int_eval_mul (hdeg h) (hint h) r.num hb
  rw [hr] at hN hnz
  have hN0 : N ≠ 0 := by
    rintro rfl
    have hb0 : (r.den : ℚ) ^ h ≠ 0 := pow_ne_zero _ (by exact_mod_cast hb.ne')
    have hd0 : den h ≠ 0 := (hden h).ne'
    simp only [Int.cast_zero] at hN
    exact hnz ((mul_eq_zero.mp ((mul_eq_zero.mp hN.symm).resolve_left hb0)).resolve_left hd0)
  have h1 : (1 : ℝ) ≤ |(N : ℝ)| := by exact_mod_cast Int.one_le_abs hN0
  have hNR : (N : ℝ) = (r.den : ℝ) ^ h * (((den h : ℚ) : ℝ) * (((P h).eval r : ℚ) : ℝ)) := by
    have := congrArg (fun x : ℚ => (x : ℝ)) hN
    push_cast at this
    exact this
  rw [aeval_ratCast] at hsm
  have : |(N : ℝ)| ≤ (r.den : ℝ) ^ h * Real.exp (-c * (h : ℝ) ^ 2) := by
    rw [hNR, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r.den : ℝ) ^ h),
      abs_of_nonneg (by exact_mod_cast (hden h).le : (0 : ℝ) ≤ ((den h : ℚ) : ℝ))]
    gcongr
  linarith

end Chi2U
