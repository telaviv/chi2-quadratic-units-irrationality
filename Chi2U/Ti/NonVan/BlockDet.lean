/-
# Theorem V_i: the bordered determinant of the block-diagonal reduction (PROOF_TI2 §4, PROOF_U §6 step 5)

**Copy of the `z`-dependent part of `Chi2U/NonVan/BlockDet.lean`.** The generic algebra is reused: `Chi2U.LP.dv`,
`Mblk`, `sum_adjugate_blockB` (`𝟙ᵀ adj(⊕_γ e_γ(c𝟙𝟙ᵀ + diag(d₀, 0, d₂))) 𝟙 = Π_γ e_γ³ c d₀ d₂ · c⁻¹ Σ_γ e_γ⁻¹`).

What changes: `e_γ⁻¹ = −τ z^{3ℓ−1} w^γ` with `w = −z^{−2} = y⁻¹` (χ₂: `w = z^{−2}`), so `Σ_γ e_γ⁻¹ ≠ 0` needs
`w ≠ 1`, i.e. `1 + z̄² = n·z̄ ≠ 0` (`sum_inv_eB_ne_zero`); then `Σ_{γ<ℓ} w^γ ≠ 0` in characteristic `ℓ`
(`geom_ne_zero`, `(Σ w^γ)(w − 1) = (w − 1)^ℓ`). PROOF_TI2 §4: `Σ_γ w^{−2γ} = (1 − w^{−2ℓ})/(1 − w^{−2})`, a unit.
-/
import Chi2U.Ti.NonVan.Gram0
import Chi2U.NonVan.BlockDet

namespace Chi2U
namespace Ti
namespace LP

open Finset Matrix

variable {n : ℕ} [Fact (3 ≤ n)] {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- `Σ_{γ<ℓ} w^γ ≠ 0` for `w ≠ 1` in characteristic `ℓ`. -/
lemma geom_ne_zero {w : Fl n ℓ} (hw : w ≠ 1) : ∑ γ ∈ range ℓ, w ^ γ ≠ 0 := by
  intro h0
  have h := geom_sum_mul w ℓ
  rw [h0, zero_mul] at h
  have h2 : (w - 1) ^ ℓ = w ^ ℓ - 1 := by rw [sub_pow_char, one_pow]
  rw [← h2] at h
  exact sub_ne_zero.mpr hw (pow_eq_zero_iff (hℓ.out.ne_zero) |>.mp h.symm)

/-- `Σ_γ e_γ⁻¹ ≠ 0` for `e_γ = −(−1)^γ τ z^{x_γ}`. -/
lemma sum_inv_eB_ne_zero (hℓm : ¬ ℓ ∣ 2 * n) : ∑ γ ∈ range ℓ, (eB n ℓ γ)⁻¹ ≠ 0 := by
  have hℓ2 : ℓ ≠ 2 := Chi2U.LP.ne_two_of_not_dvd hℓm
  have hz := zb_ne_zero (n := n) (ℓ := ℓ)
  set w : Fl n ℓ := -(zb n ℓ ^ 2)⁻¹ with hw
  set c' : Fl n ℓ := -(tauB n ℓ * zb n ℓ ^ (3 * ℓ) * (zb n ℓ)⁻¹) with hc'
  have hterm : ∀ γ ∈ range ℓ, (eB n ℓ γ)⁻¹ = c' * w ^ γ := by
    intro γ _
    refine inv_eq_of_mul_eq_one_right ?_
    have h1 := zb_poleZ_mul (n := n) hℓ2 γ
    have hτ := tauB_mul_self (n := n) (ℓ := ℓ)
    have hs : ((-1 : Fl n ℓ) ^ γ) * (-1) ^ γ = 1 := by rw [← mul_pow]; norm_num
    have hwγ : w ^ γ = (-1) ^ γ * ((zb n ℓ ^ (2 * γ + 1))⁻¹ * zb n ℓ) := by
      rw [hw, neg_pow, inv_pow, ← pow_mul, pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ hz, mul_one]
    rw [eB, hc', hwγ, ← h1]
    have hA : zb n ℓ ^ poleZ (3 * ℓ - 1) γ ≠ 0 := zpow_ne_zero _ hz
    have hB : zb n ℓ ^ (3 * ℓ) ≠ 0 := pow_ne_zero _ hz
    field_simp
    linear_combination (-1) ^ γ * (-1) ^ γ * hτ + hs
  rw [sum_congr rfl hterm, ← mul_sum]
  refine mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero tauB_ne_zero (pow_ne_zero _ hz))
    (inv_ne_zero hz))) (geom_ne_zero ?_)
  intro h1
  have : zb n ℓ ^ 2 = -1 := by
    rw [hw, neg_eq_iff_eq_neg, inv_eq_iff_eq_inv, inv_neg, inv_one] at h1
    exact h1
  have h4 := one_add_zb_sq (n := n) (ℓ := ℓ)
  rw [this, add_neg_cancel] at h4
  exact mul_ne_zero (n_ne_zero_Fl hℓm) hz h4.symm

end LP
end Ti
end Chi2U
