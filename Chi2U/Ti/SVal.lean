/-
# Theorem V_i, Lemma S: the local valuation facts (PROOF_TI2 §2 row "§3.2 Lemma S")

**Copy of the `ℚ(√d)`-valued part of `Chi2U/V/SMatrix.lean` (section `VGe`) and of `Chi2U/V/SVal.lean`** for the Ti₂
machine (`Qt n`, trace `n`, `e = v_p(n)`). The `z`-free parts are reused from `Chi2U.V.LS`: `det_expand_rows`, `wT`,
`natAbs_poleZ_le`, `two_padicValNat_le_wT`, `padicNorm_inv_sq_levels`, `vmult`, `vmult_comm`, `padicValRat_pole_sub`,
`padicValRat_dPrime`, `padicValRat_one_div_pow`.

* `vGe_Lmom_special`: the Ti₂ Mahler form `Lmom F = Σ_b Δ^bG(0) (−1)^b z^b/n^{b+1}` (`Ti.Lmom_eq_mahler`) gives, for any
  prime `p` and `F` with `p`-integral values at the odd integers and `F = 0 ∨ deg F < r`, `v_p(Lmom F) ≥ −v_p(n)·r`
  (PROOF_V §3.2 with `1 − y = n z`; the sign `(−1)^b` is a unit).
* `vGe_muPoly_divD`: `v_p(μ(t^e div D)) ≥ −v_p(n)·(e − K)₊`.
* `vGe_Psum_levels`: `v_p(P(x_m)) ≥ −wT(m)` (the signs `χ₄(u)` are units).
-/
import Chi2U.Ti.Lemma8One
import Chi2U.V.LemmaS

set_option linter.unusedSectionVars false

namespace Chi2U
namespace Ti
namespace LS

open Polynomial Finset
open _root_.Chi2U.V.LS

section VGe

variable {n : ℕ} [Fact (3 ≤ n)] {p : ℕ} [Fact p.Prime]

/-- Leibniz with row and column exponents, any finite index type. -/
theorem vGeX_det_rc {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (Qt n)[X]) (ρ κ : ι → ℤ)
    (h : ∀ i j, vGeX p (ρ i + κ j) (M i j)) : vGeX p (∑ i, ρ i + ∑ j, κ j) M.det := by
  rw [Matrix.det_apply]
  refine vGeX_sum _ _ (fun σ _ => ?_)
  have hprod : vGeX p (∑ i, (ρ (σ i) + κ i)) (∏ i, M (σ i) i) := vGeX_prod _ _ _ (fun i _ => h (σ i) i)
  rw [sum_add_distrib, Equiv.sum_comp σ ρ] at hprod
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
  · simpa using hprod
  · simpa using vGeX_neg hprod

lemma vGeX_mono {v w : ℤ} (hmn : w ≤ v) {F : (Qt n)[X]} (hF : vGeX p v F) : vGeX p w F :=
  fun k => vGe_mono hmn (hF k)

lemma vGeX_zero (v : ℤ) : vGeX p v (0 : (Qt n)[X]) := fun k => by
  simpa using vGe_zero (n := n) (p := p) v

lemma vGeX_intCast (z : ℤ) : vGeX p 0 ((z : (Qt n)[X])) := by
  rw [← C_eq_intCast]; exact vGeX_C (vGe_of_pInt (pInt_intCast z))

lemma vGeX_X : vGeX p 0 (X : (Qt n)[X]) := by
  simpa using vGeX_X_mul (vGeX_one (n := n) (p := p))

end VGe

variable {n : ℕ} [Fact (3 ≤ n)] {p : ℕ} [hpF : Fact p.Prime]

/-! ### The polynomial part -/

/-- Mahler form with denominators `n^{b+1}`: `v_p(Lmom F) ≥ −v_p(n)·r`. -/
theorem vGe_Lmom_special (F : ℚ[X]) (r : ℕ)
    (hF : ∀ k : ℕ, padicNorm p (F.eval (2 * (k : ℚ) + 1)) ≤ 1) (hr : F = 0 ∨ F.natDegree < r) :
    vGe p (-(padicValRat p ((n : ℕ) : ℚ) * r)) (Lmom n F) := by
  rcases hr with rfl | hr
  · rw [map_zero]; exact vGe_zero _
  have h2m : (n : ℕ) ≠ 0 := by have := (Fact.out : 3 ≤ n); omega
  have he0 : 0 ≤ padicValRat p ((n : ℕ) : ℚ) := by rw [padicValRat.of_nat]; positivity
  rw [Lmom_eq_mahler]
  refine vGe_sum _ _ (fun b hb => ?_)
  have hbr : b + 1 ≤ r := by have := mem_range.mp hb; omega
  have hm : padicNorm p (mahlerCoeff F b) ≤ 1 := by
    unfold mahlerCoeff
    refine padicNorm.sum_le' (fun k _ => ?_) zero_le_one
    rw [padicNorm.mul]
    have hint : padicNorm p ((-1 : ℚ) ^ (b - k) * (b.choose k : ℚ)) ≤ 1 := by
      have := padicNorm.of_int (p := p) ((-1 : ℤ) ^ (b - k) * (b.choose k : ℤ)); push_cast at this; exact this
    calc padicNorm p ((-1 : ℚ) ^ (b - k) * (b.choose k : ℚ)) * padicNorm p (F.eval (2 * (k : ℚ) + 1))
        ≤ 1 * 1 := mul_le_mul hint (hF k) (padicNorm.nonneg _) zero_le_one
      _ = 1 := one_mul _
  have h1 : vGe p 0 (mahlerCoeff F b : (Qt n)) := vGe_of_pInt (pInt_ratCast hm)
  have h2 : vGe p 0 ((-1 : Qt n) ^ b * (zK n) ^ b) :=
    vGe_of_pInt (pInt_mul (pInt_pow (pInt_neg pInt_one) b) (pInt_pow pInt_zK b))
  have h3 := vGe_ratCast (n := n) (p := p) (1 / ((n : ℕ) : ℚ) ^ (b + 1))
  rw [padicValRat_one_div_pow h2m] at h3
  have e : (mahlerCoeff F b : (Qt n)) * (-1) ^ b * (zK n) ^ b / ((n : ℕ) : Qt n) ^ (b + 1) =
      (mahlerCoeff F b : (Qt n)) * ((-1) ^ b * (zK n) ^ b) * ((1 / ((n : ℕ) : ℚ) ^ (b + 1) : ℚ) : Qt n) := by
    push_cast; ring
  rw [e]
  refine vGe_mono ?_ (vGe_mul (vGe_mul h1 h2) h3)
  have hb' : ((b + 1 : ℕ) : ℤ) ≤ (r : ℤ) := by exact_mod_cast hbr
  have := mul_le_mul_of_nonneg_left hb' he0
  linarith

/-- `v_p(μ(t^e div D)) ≥ −v_p(n)·(e − K)` (truncated subtraction, `K = h + 1`). -/
theorem vGe_muPoly_divD (h e : ℕ) :
    vGe p (-(padicValRat p ((n : ℕ) : ℚ) * ((e - (h + 1) : ℕ) : ℤ)))
      (muPoly n ((X ^ e : ℚ[X]) /ₘ Dpoly h)) := by
  have hQ : (X ^ e : ℚ[X]) /ₘ Dpoly h = ((X ^ e : ℤ[X]) /ₘ l8DZ h).map (Int.castRingHom ℚ) := by
    rw [l8_Dpoly_eq, Polynomial.map_divByMonic _ l8_DZ_monic, Polynomial.map_pow, Polynomial.map_X]
  have hD := Dpoly_monic h
  unfold muPoly
  refine vGe_Lmom_special _ _ (fun k => ?_) ?_
  · rw [hQ, derivative_map]
    have e' : (2 * (k : ℚ) + 1) = (((2 * k + 1 : ℕ) : ℤ) : ℚ) := by push_cast; ring
    rw [e', eval_intCast_map]
    simpa using padicNorm.of_int (p := p) _
  · by_cases hn : e < h + 1
    · left
      have : (X ^ e : ℚ[X]) /ₘ Dpoly h = 0 := by
        rw [divByMonic_eq_zero_iff hD, degree_X_pow, degree_eq_natDegree hD.ne_zero, natDegree_Dpoly]
        exact_mod_cast hn
      rw [this, derivative_zero]
    · have hdeg : ((X ^ e : ℚ[X]) /ₘ Dpoly h).natDegree = e - (h + 1) := by
        rw [natDegree_divByMonic _ hD, natDegree_X_pow, natDegree_Dpoly]
      by_cases h0 : ((X ^ e : ℚ[X]) /ₘ Dpoly h).natDegree = 0
      · left; exact derivative_of_natDegree_zero h0
      · right; rw [← hdeg]; exact natDegree_derivative_lt h0

/-! ### The partial sums, all levels -/

/-- `v_p(P(x_m)) ≥ −wT(m)` (all levels). -/
lemma vGe_Psum_levels {h m : ℕ} (hh : Even h) (hm : m ≤ h) :
    vGe p (-(wT h p m : ℤ)) (Psum n (poleZ h m)) := by
  have hterm : ∀ k ∈ range ((poleZ h m).natAbs / 2), ∀ u : (Qt n), pInt p u →
      vGe p (-(wT h p m : ℤ)) (u / ((2 * k + 1 : ℕ) : (Qt n)) ^ 2) := by
    intro k hk u hu
    have hk' : 2 * k + 1 < (poleZ h m).natAbs := by have := mem_range.mp hk; omega
    have e : u / ((2 * k + 1 : ℕ) : (Qt n)) ^ 2 = u * (((1 / ((2 * k + 1 : ℕ) : ℚ) ^ 2 : ℚ)) : (Qt n)) := by
      push_cast; ring
    rw [e]
    have := vGe_mul (vGe_of_pInt hu) (vGe_ratCast_of_padicNorm (v := -(wT h p m : ℤ))
      (by rw [neg_neg]; exact padicNorm_inv_sq_levels hh hm hk'))
    simpa using this
  unfold Psum
  split_ifs
  · exact vGe_sum _ _ (fun k hk => hterm k hk _ (pInt_mul (pInt_pow (pInt_neg pInt_one) k) (pInt_pow pInt_zK _)))
  · exact vGe_sum _ _ (fun k hk => hterm k hk _ (pInt_mul (pInt_pow (pInt_neg pInt_one) k)
      (by rw [← inv_pow]; exact pInt_pow pInt_zK_inv _)))

end LS
end Ti
end Chi2U
