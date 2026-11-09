/-
# Theorem V_i: Lemma B, the bordered identity (PROOF_TI2 §2 → PROOF_V §3.1 → PROOF_U §3.3)

**Copy of `Chi2U/Arith/LemmaB.lean`** for the Ti₂ machine (`Qt n`, `Ti.Afun`, `Ti.Bfun`). The `z`-free parts are reused
from the χ₂ file: `fLag`, `LB.cPole_add`, the coefficient matrix `LB.coefM` and its lemmas, `LB.adjugate_last`,
`LB.det_coefM_sq`, `LB.eval_fLag`, `LB.dPrime_ne_zero`. With `K = h + 1` and `G^f(X) = (Λ_X(f_i f_j))`:

    Δ_h(X) · Π_i D′(x_i) = (−1)^{K(K−1)/2} · 𝟙ᵀ adj(G^f(X)) 𝟙.

The proof is the χ₂ one verbatim (it never looks inside `A`, `B` beyond additivity).
-/
import Chi2U.Ti.Core

set_option linter.unusedSectionVars false

namespace Chi2U
namespace Ti

variable {n : ℕ} [Fact (3 ≤ n)]

open Polynomial Finset

/-- `Λ_X(g) = A(g) + X·B(g) ∈ ℚ(√d)[X]`. -/
noncomputable def LamX (n : ℕ) [Fact (3 ≤ n)] (h : ℕ) (g : ℚ[X]) : (Qt n)[X] :=
  C (Afun n h g) + X * C (Bfun n h g)

/-- The `K × K` Lagrange Gram matrix `G^f(X)`. -/
noncomputable def GramF (n : ℕ) [Fact (3 ≤ n)] (h : ℕ) : Matrix (Fin (h + 1)) (Fin (h + 1)) (Qt n)[X] :=
  fun i j => LamX n h (fLag h i * fLag h j)

namespace LB

/-! ### Linearity of `Λ_X` -/

lemma Afun_add (h : ℕ) (g₁ g₂ : ℚ[X]) : Afun n h (g₁ + g₂) = Afun n h g₁ + Afun n h g₂ := by
  simp only [Afun, add_divByMonic, muPoly_add, Chi2U.LB.cPole_add, Rat.cast_add, add_mul, sum_add_distrib]
  ring

lemma Bfun_add (h : ℕ) (g₁ g₂ : ℚ[X]) : Bfun n h (g₁ + g₂) = Bfun n h g₁ + Bfun n h g₂ := by
  simp only [Bfun, Chi2U.LB.cPole_add, Rat.cast_add, add_mul, sum_add_distrib]
  ring

lemma LamX_add (h : ℕ) (g₁ g₂ : ℚ[X]) : LamX n h (g₁ + g₂) = LamX n h g₁ + LamX n h g₂ := by
  simp only [LamX, Afun_add, Bfun_add, C_add]; ring

/-- `Λ_X` as an additive map. -/
noncomputable def LamXHom (n : ℕ) [Fact (3 ≤ n)] (h : ℕ) : ℚ[X] →+ (Qt n)[X] :=
  AddMonoidHom.mk' (LamX n h) (LamX_add h)

lemma LamXHom_apply (h : ℕ) (g : ℚ[X]) : LamXHom n h g = LamX n h g := rfl

lemma LamX_C_mul (h : ℕ) (c : ℚ) (g : ℚ[X]) : LamX n h (C c * g) = C (c : (Qt n)) * LamX n h g := by
  have := map_rat_smul (LamXHom n h) c g
  rw [LamXHom_apply, LamXHom_apply] at this
  rw [← smul_eq_C_mul, this, Algebra.smul_def, Polynomial.algebraMap_apply, eq_ratCast]

lemma LamX_sum {ι : Type*} (h : ℕ) (s : Finset ι) (g : ι → ℚ[X]) :
    LamX n h (∑ i ∈ s, g i) = ∑ i ∈ s, LamX n h (g i) :=
  map_sum (LamXHom n h) g s

/-! ### The coefficient matrix (reused from `Chi2U.LB`) -/

/-- The Hankel matrix `H_{h+1} = (Λ_X(t^{a+b}))_{a,b ≤ h}`. -/
noncomputable def Hmat (n : ℕ) [Fact (3 ≤ n)] (h : ℕ) : Matrix (Fin (h + 1)) (Fin (h + 1)) (Qt n)[X] :=
  fun a b => LamX n h (X ^ ((a : ℕ) + b))

/-- `G^f = C' H C'ᵀ`. -/
lemma GramF_eq (h : ℕ) :
    GramF n h = (Chi2U.LB.coefM h).map (algebraMap ℚ (Qt n)[X]) * Hmat n h *
      ((Chi2U.LB.coefM h).map (algebraMap ℚ (Qt n)[X])).transpose := by
  refine Matrix.ext (fun i j => ?_)
  simp only [GramF, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Hmat]
  rw [Chi2U.LB.fLag_eq_sum i, Chi2U.LB.fLag_eq_sum j, sum_mul_sum, LamX_sum]
  simp_rw [LamX_sum, sum_mul]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl (fun a _ => ?_)
  refine sum_congr rfl (fun b _ => ?_)
  rw [show C (Chi2U.LB.coefM h i a) * X ^ (a : ℕ) * (C (Chi2U.LB.coefM h j b) * X ^ (b : ℕ)) =
      C (Chi2U.LB.coefM h i a * Chi2U.LB.coefM h j b) * X ^ ((a : ℕ) + b) by rw [pow_add, C_mul]; ring]
  rw [LamX_C_mul, Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, eq_ratCast, eq_ratCast,
    Rat.cast_mul, C_mul]
  ring

/-! ### The adjugate -/

/-- `𝟙ᵀ adj(G^f) 𝟙 = (det C)² adj(H)_{hh}`. -/
lemma sum_adjugate_GramF (h : ℕ) :
    ∑ a, ∑ b, (GramF n h).adjugate a b =
      C (((Chi2U.LB.coefM h).det : ℚ) : (Qt n)) ^ 2 * (Hmat n h).adjugate (Fin.last h) (Fin.last h) := by
  set C' := (Chi2U.LB.coefM h).map (algebraMap ℚ (Qt n)[X]) with hC'
  set one : Fin (h + 1) → (Qt n)[X] := fun _ => 1 with hone
  set e : Fin (h + 1) → (Qt n)[X] := Pi.single (Fin.last h) 1 with he
  have hcol : C'.mulVec e = one := by
    funext i
    simp only [he, hC', hone, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.single_apply, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Chi2U.LB.coefM_last, map_one]
  have hv : C'.adjugate.mulVec one = C'.det • e := by
    rw [← hcol, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hsum : ∀ M : Matrix (Fin (h + 1)) (Fin (h + 1)) (Qt n)[X], ∑ a, ∑ b, M a b = one ⬝ᵥ M.mulVec one := by
    intro M
    simp [hone, dotProduct, Matrix.mulVec]
  have hdet : C'.det = C (((Chi2U.LB.coefM h).det : ℚ) : (Qt n)) := by
    rw [hC', ← RingHom.mapMatrix_apply, ← RingHom.map_det, Polynomial.algebraMap_apply, eq_ratCast]
  rw [hsum, GramF_eq, ← hC', Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
    ← Matrix.adjugate_transpose, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, hv, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, he, single_dotProduct,
    hdet]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  ring

end LB

/-! ### Assembly -/

open _root_.Chi2U.Ti.LB in
/-- **Lemma B** (bordered identity), Ti₂ version of `Chi2U.lemmaB`. -/
theorem lemmaB {h : ℕ} (hh : Even h) :
    (Delta n h).map (algebraMap ℚ (Qt n)) * C (∏ i ∈ range (h + 1), ((dPrime h i : ℚ) : (Qt n))) =
      C ((-1) ^ ((h + 1) * h / 2)) * ∑ a, ∑ b, (GramF n h).adjugate a b := by
  rw [sum_adjugate_GramF, Chi2U.LB.adjugate_last, Delta_map hh]
  have hsub : (Hmat n h).submatrix Fin.castSucc Fin.castSucc =
      Matrix.of fun i j : Fin h => C (Afun n h (X ^ ((i : ℕ) + j))) + X * C (Bfun n h (X ^ ((i : ℕ) + j))) := by
    refine Matrix.ext (fun i j => ?_)
    simp [Hmat, LamX]
  rw [hsub]
  have hsq : (((Chi2U.LB.coefM h).det : ℚ) : (Qt n)) ^ 2 =
      (-1) ^ ((h + 1) * h / 2) * ∏ i ∈ range (h + 1), ((dPrime h i : ℚ) : (Qt n)) := by
    rw [← Rat.cast_pow, Chi2U.LB.det_coefM_sq, Fin.prod_univ_eq_prod_range (fun i => dPrime h i)]
    push_cast; ring
  have hs : ((-1 : (Qt n)[X]) ^ ((h + 1) * h / 2)) * (-1) ^ ((h + 1) * h / 2) = 1 := by
    rw [← mul_pow]; norm_num
  rw [← C_pow, hsq, C_mul, C_pow, C_neg, C_1, ← mul_assoc, ← mul_assoc, hs, one_mul, mul_comm]

end Ti
end Chi2U
