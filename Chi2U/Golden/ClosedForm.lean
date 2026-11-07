/-
# The golden-ratio closed form `χ₂(√5 − 2) = π²/24 − ¾ log²φ`

Let `a = φ⁻¹ = (√5 − 1)/2`, so `a² = 1 − a`, `a/(1 + a) = a²`, `a³ = √5 − 2` and
`(1 − a³)/(1 + a³) = a`; write `ℓ = log a = −log φ`.

* Euler reflection at `t = a²` (`Li2_reflection`): `Li₂(a²) + Li₂(a) = π²/6 − 2ℓ²`;
* Landen for `Li₂` at `s = a` (`Li2_landen`): `Li₂(−a) + Li₂(a²) = −½ℓ²`;
* hence `χ₂(a) = ½(Li₂(a) − Li₂(−a)) = π²/12 − ¾ℓ²` (`chi2_goldenRatio_inv`);
* Landen for `χ₂` at `x = a³` (`chi2_landen`): `χ₂(a³) + χ₂(a) = π²/8 − (3/2)ℓ²`;
* so `χ₂(√5 − 2) = π²/24 − ¾ log²φ` (`chi2_sqrt5_sub_two_eq`).

Standard axioms only.
-/
import Chi2U.Golden.Landen

namespace Chi2U

open Real Set

namespace Golden

/-- `φ⁻¹ = (√5 − 1)/2` and its basic algebra. -/
private lemma golden_facts :
    let a : ℝ := (√5 - 1) / 2
    0 < a ∧ a < 1 ∧ a ^ 2 = 1 - a ∧ a ^ 3 = √5 - 2 ∧ goldenRatio = 1 + a ∧ a * (1 + a) = 1 := by
  intro a
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h2 : 2 < √5 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h3 : √5 < 3 := by nlinarith
  refine ⟨by simp only [a]; linarith, by simp only [a]; linarith, ?_, ?_, ?_, ?_⟩
  · simp only [a]; linear_combination (1 / 4 : ℝ) * h5
  · simp only [a]; linear_combination ((√5 - 3) / 8) * h5
  · simp only [a, goldenRatio]; ring
  · simp only [a]; linear_combination (1 / 4 : ℝ) * h5

end Golden

open Golden

/-- `χ₂(φ⁻¹) = π²/12 − ¾ log²φ`, with `φ⁻¹` written as `(√5 − 1)/2`. -/
theorem chi2_goldenRatio_inv : chi2 ((√5 - 1) / 2) = π ^ 2 / 12 - 3 / 4 * log goldenRatio ^ 2 := by
  obtain ⟨ha0, ha1, ha2, -, hφ, hinv⟩ := golden_facts
  set a : ℝ := (√5 - 1) / 2 with ha
  have hℓφ : log goldenRatio = -log a := by
    rw [hφ, ← Real.log_inv]
    congr 1
    exact (eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hinv))
  have hla2 : log (a ^ 2) = 2 * log a := by rw [Real.log_pow]; norm_num
  have hR := Li2_reflection (t := a ^ 2) ⟨by positivity, by rw [ha2]; linarith⟩
  rw [show 1 - a ^ 2 = a by rw [ha2]; ring, hla2] at hR
  have hL := Li2_landen (s := a) ⟨ha0, ha1⟩
  rw [show a / (1 + a) = a ^ 2 by
      rw [div_eq_iff (by linarith)]; linear_combination -(a * ha2) + hinv - ha2,
    show log (1 + a) = log goldenRatio by rw [hφ], hℓφ] at hL
  have hc := chi2_eq_Li2 (x := a) (by rw [abs_of_pos ha0]; exact ha1.le)
  rw [hc, hℓφ]
  nlinarith [hR, hL]

/-- **The golden-ratio closed form**: `χ₂(√5 − 2) = π²/24 − ¾ log²φ`. -/
theorem chi2_sqrt5_sub_two_eq :
    chi2 (Real.sqrt 5 - 2) = Real.pi ^ 2 / 24 - 3 / 4 * Real.log goldenRatio ^ 2 := by
  obtain ⟨ha0, ha1, ha2, ha3, hφ, hinv⟩ := golden_facts
  set a : ℝ := (√5 - 1) / 2 with ha
  have hℓφ : log goldenRatio = -log a := by
    rw [hφ, ← Real.log_inv]
    congr 1
    exact (eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hinv))
  have hz0 : 0 < a ^ 3 := by positivity
  have hz1 : a ^ 3 < 1 := pow_lt_one₀ ha0.le ha1 (by norm_num)
  have hK := chi2_landen (x := a ^ 3) ⟨hz0, hz1⟩
  have hq : (1 - a ^ 3) / (1 + a ^ 3) = a := by
    rw [div_eq_iff (by linarith)]
    have : a ^ 3 = 2 * a - 1 := by linear_combination a * ha2 - ha2
    rw [this]
    linear_combination (-2 : ℝ) * ha2
  rw [hq, Real.log_pow, chi2_goldenRatio_inv, hℓφ] at hK
  rw [← ha3]
  rw [hℓφ]
  push_cast at hK
  nlinarith [hK]

end Chi2U
