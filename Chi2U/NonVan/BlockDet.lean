/-
# The bordered determinant of the block-diagonal reduction (PROOF_U §6, step 5)

Generic algebra over a field `K`: for `M_γ = e_γ (c 𝟙𝟙ᵀ + diag(d₀, 0, d₂))` (`γ` in a finite type, `e_γ, c ≠ 0`)
and `B = ⊕_γ M_γ` (Mathlib's `blockDiagonal`, index `Fin 3 × ι`),

    𝟙ᵀ adj(B) 𝟙 = det B · c⁻¹ Σ_γ e_γ⁻¹,   det B = Π_γ e_γ³ c d₀ d₂   (`sum_adjugate_blockB`).

Proof: `B v = 𝟙` for `v = (e_γ⁻¹ c⁻¹ [r = 1])` (column `1` of `M_γ` is `e_γ c 𝟙`, as `d₁ = 0`), so
`adj(B) 𝟙 = adj(B) B v = det B · v`.
Then (`geom_ne_zero`): in characteristic `ℓ`, `Σ_{γ<ℓ} w^γ ≠ 0` for `w ≠ 1`, because `(Σ w^γ)(w − 1) = w^ℓ − 1 = (w − 1)^ℓ`.
-/
import Chi2U.NonVan.Gram0

namespace Chi2U
namespace LP

open Finset Matrix

section Generic

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `d = (d₀, 0, d₂)`. -/
def dv (d0 d2 : K) : Fin 3 → K := ![d0, 0, d2]

/-- `M_γ = e_γ (c 𝟙𝟙ᵀ + diag(d₀, 0, d₂))`. -/
def Mblk (e : ι → K) (c d0 d2 : K) (γ : ι) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun r s => e γ * (c + if r = s then dv d0 d2 r else 0)

omit [Fintype ι] [DecidableEq ι] in
lemma det_Mblk (e : ι → K) (c d0 d2 : K) (γ : ι) : (Mblk e c d0 d2 γ).det = e γ ^ 3 * (c * d0 * d2) := by
  rw [Matrix.det_fin_three]
  simp [Mblk, dv]
  ring

theorem sum_adjugate_blockB (e : ι → K) (c d0 d2 : K) (he : ∀ γ, e γ ≠ 0) (hc : c ≠ 0) :
    ∑ a, ∑ b, (blockDiagonal (Mblk e c d0 d2)).adjugate a b =
      (∏ γ, e γ ^ 3 * (c * d0 * d2)) * (c⁻¹ * ∑ γ, (e γ)⁻¹) := by
  set B := blockDiagonal (Mblk e c d0 d2) with hB
  set v : Fin 3 × ι → K := fun p => if p.1 = 1 then (e p.2)⁻¹ * c⁻¹ else 0 with hv
  have hBv : B *ᵥ v = fun _ => 1 := by
    funext p
    obtain ⟨r, γ⟩ := p
    simp only [hB, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, blockDiagonal_apply]
    rw [Fin.sum_univ_three]
    simp only [hv, Mblk, Matrix.of_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    fin_cases r <;> simp [dv] <;> field_simp [he γ]
  have hsum : ∀ M : Matrix (Fin 3 × ι) (Fin 3 × ι) K, ∑ a, ∑ b, M a b = ∑ a, (M *ᵥ fun _ => 1) a := by
    intro M; simp [Matrix.mulVec, dotProduct]
  rw [hsum, ← hBv, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
    det_blockDiagonal]
  simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum, det_Mblk]
  congr 1
  rw [Fintype.sum_prod_type, Fin.sum_univ_three]
  simp only [hv]
  simp [mul_sum]
  exact sum_congr rfl (fun _ _ => mul_comm _ _)

end Generic

variable {az : ℕ} [Fact (1 ≤ az)] {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- `Σ_{γ<ℓ} w^γ ≠ 0` for `w ≠ 1` in characteristic `ℓ`. -/
lemma geom_ne_zero {w : Fl az ℓ} (hw : w ≠ 1) : ∑ γ ∈ range ℓ, w ^ γ ≠ 0 := by
  intro h0
  have h := geom_sum_mul w ℓ
  rw [h0, zero_mul] at h
  have h2 : (w - 1) ^ ℓ = w ^ ℓ - 1 := by rw [sub_pow_char, one_pow]
  rw [← h2] at h
  exact sub_ne_zero.mpr hw (pow_eq_zero_iff (hℓ.out.ne_zero) |>.mp h.symm)

/-- `Σ_γ e_γ⁻¹ ≠ 0` for `e_γ = −z^{x_γ}`. -/
lemma sum_inv_eB_ne_zero (hℓm : ¬ ℓ ∣ 2 * az) : ∑ γ ∈ range ℓ, (eB az ℓ γ)⁻¹ ≠ 0 := by
  have hℓ2 : ℓ ≠ 2 := ne_two_of_not_dvd hℓm
  have hz := zb_ne_zero (az := az) (ℓ := ℓ)
  set w : Fl az ℓ := (zb az ℓ ^ 2)⁻¹ with hw
  have hterm : ∀ γ ∈ range ℓ, (eB az ℓ γ)⁻¹ = -(zb az ℓ ^ (3 * ℓ) * (zb az ℓ)⁻¹) * w ^ γ := by
    intro γ _
    have h1 := zb_poleZ_mul (az := az) hℓ2 γ
    rw [eB, hw]
    have h3 : zb az ℓ ^ poleZ (3 * ℓ - 1) γ = zb az ℓ ^ (2 * γ + 1) / zb az ℓ ^ (3 * ℓ) := by
      rw [← h1]; field_simp
    rw [h3, inv_pow, ← pow_mul]
    field_simp
    ring
  rw [sum_congr rfl hterm, ← mul_sum]
  refine mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hz) (inv_ne_zero hz))) (geom_ne_zero ?_)
  intro h1
  have : zb az ℓ ^ 2 = 1 := by rw [hw] at h1; exact inv_eq_one.mp h1
  have h4 := one_sub_zb_sq (az := az) (ℓ := ℓ)
  rw [this, sub_self] at h4
  exact mul_ne_zero (az_ne_zero_Fl hℓm) hz h4.symm

end LP
end Chi2U
