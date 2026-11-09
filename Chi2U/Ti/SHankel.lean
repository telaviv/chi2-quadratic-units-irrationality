/-
# Theorem V_i, Lemma S: the atom decomposition of the Hankel matrix and its expansion

**Copy of `Chi2U/V/SHankel.lean`** for the Ti₂ machine (`Qt n`). Change: the pole factor is `(−1)^{x_a/2} z^{x_a}`
(`sgnPole`), so `γ_a` carries that sign. `xP`, `botRows`, `det_expand_rows` are reused from `Chi2U.V.LS`.

`H = 𝒫 + Vᵀ diag(γ) V` (PROOF_U Lemma 7′; `𝒫_{ij} = μ(t^{i+j} div D)`, `V_{a i} = x_a^i`,
`γ_a = z^{x_a}(P(x_a) − X)/D′(x_a)`), so `det H = det [[𝒫, Vᵀ], [−diag(γ)V, 1]]` (Schur complement), and the
row expansion of the bottom rows gives `det H = Σ_{T} (Π_{a ∈ S_T} γ_a) · det N_T` (`det_HkM_expand`), where `N_T`
has bottom rows `(−x_a^j | 0)` for `a ∈ S_T` and `(0 | e_a)` otherwise.
-/
import Chi2U.Ti.SVal

set_option linter.unusedSectionVars false

namespace Chi2U
namespace Ti
namespace LS

open Polynomial Finset Matrix
open _root_.Chi2U.V.LS (xP botRows det_expand_rows)

section Setup

variable (n : ℕ) [Fact (3 ≤ n)] (h : ℕ)

/-- The Hankel matrix over `ℚ(√d)[X]` (`Delta_map`). -/
noncomputable def HkM : Matrix (Fin h) (Fin h) (Qt n)[X] :=
  Matrix.of fun i j : Fin h => C (Afun n h (X ^ ((i : ℕ) + j))) + X * C (Bfun n h (X ^ ((i : ℕ) + j)))

/-- The polynomial part `𝒫_{ij} = μ(t^{i+j} div D)`. -/
noncomputable def PmM : Matrix (Fin h) (Fin h) (Qt n)[X] :=
  Matrix.of fun i j : Fin h => C (muPoly n ((X ^ ((i : ℕ) + j) : ℚ[X]) /ₘ Dpoly h))

/-- `V_{a i} = x_a^i`. -/
noncomputable def VmM : Matrix (Fin (h + 1)) (Fin h) (Qt n)[X] :=
  Matrix.of fun a i => ((xP h a ^ (i : ℕ) : ℤ) : (Qt n)[X])

/-- `γ_a = (−1)^{x_a/2} z^{x_a}(P(x_a) − X)/D′(x_a)`. -/
noncomputable def gamF (a : ℕ) : (Qt n)[X] :=
  C ((((dPrime h a)⁻¹ : ℚ) : Qt n) * (sgnPole (poleZ h a) : Qt n) * (zK n) ^ (poleZ h a)) *
    (C (Psum n (poleZ h a)) - X)

lemma HkM_eq : HkM n h = PmM n h + (VmM n h).transpose * diagonal (fun a : Fin (h + 1) => gamF n h a) * VmM n h := by
  refine Matrix.ext (fun i j => ?_)
  rw [Matrix.add_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, HkM, PmM, VmM, Matrix.of_apply, Matrix.transpose_apply, xP]
  rw [Fin.sum_univ_eq_sum_range (fun a => ((poleZ h a ^ (i : ℕ) : ℤ) : (Qt n)[X]) * gamF n h a *
    ((poleZ h a ^ (j : ℕ) : ℤ) : (Qt n)[X])) (h + 1)]
  unfold Afun Bfun
  rw [C_add, add_assoc]
  congr 1
  have hterm : ∀ a ∈ range (h + 1), ((poleZ h a ^ (i : ℕ) : ℤ) : (Qt n)[X]) * gamF n h a *
      ((poleZ h a ^ (j : ℕ) : ℤ) : (Qt n)[X]) =
      C ((cPole h (X ^ ((i : ℕ) + j)) a : Qt n) * (sgnPole (poleZ h a) : Qt n) * zK n ^ poleZ h a *
          Psum n (poleZ h a)) -
        X * C ((cPole h (X ^ ((i : ℕ) + j)) a : Qt n) * (sgnPole (poleZ h a) : Qt n) * zK n ^ poleZ h a) := by
    intro a _
    unfold gamF cPole
    rw [eval_pow, eval_X]
    have e : ((((poleZ h a : ℤ) : ℚ) ^ ((i : ℕ) + j) / dPrime h a : ℚ) : Qt n) =
        ((poleZ h a ^ (i : ℕ) : ℤ) : Qt n) * (((dPrime h a)⁻¹ : ℚ) : Qt n) *
          ((poleZ h a ^ (j : ℕ) : ℤ) : Qt n) := by
      push_cast; ring
    rw [e, ← C_eq_intCast, ← C_eq_intCast]
    simp only [C_mul]
    ring
  rw [sum_congr rfl hterm, sum_sub_distrib, ← mul_sum, map_sum, C_neg, map_sum]
  ring

/-- The bordered matrix `[[𝒫, Vᵀ], [−diag(γ)V, 1]]`. -/
noncomputable def BlkM : Matrix (Fin h ⊕ Fin (h + 1)) (Fin h ⊕ Fin (h + 1)) (Qt n)[X] :=
  fromBlocks (PmM n h) (VmM n h).transpose (-(diagonal (fun a : Fin (h + 1) => gamF n h a) * VmM n h)) 1

lemma det_HkM_eq_BlkM : (HkM n h).det = (BlkM n h).det := by
  rw [BlkM, det_fromBlocks_one₂₂, HkM_eq, Matrix.mul_neg, sub_neg_eq_add, Matrix.mul_assoc]

/-- Row coefficients: `γ_a` on bottom row `a`. -/
noncomputable def aRow : Fin h ⊕ Fin (h + 1) → (Qt n)[X] := Sum.elim (fun _ => 0) (fun a => gamF n h a)

/-- Bottom row `a`, `γ`-part: `(−x_a^j | 0)`. -/
noncomputable def uRow : Fin h ⊕ Fin (h + 1) → Fin h ⊕ Fin (h + 1) → (Qt n)[X] :=
  Sum.elim (fun _ => 0) (fun a => Sum.elim (fun j => -VmM n h a j) (fun _ => 0))

/-- Bottom row `a`, constant part: `(0 | e_a)`. -/
noncomputable def wRow : Fin h ⊕ Fin (h + 1) → Fin h ⊕ Fin (h + 1) → (Qt n)[X] :=
  Sum.elim (fun _ => 0) (fun a => Sum.elim (fun _ => 0) (fun b => if a = b then 1 else 0))

/-- The matrix `N_T` of the term `T ⊆ botRows`. -/
noncomputable def NT (T : Finset (Fin h ⊕ Fin (h + 1))) : Matrix (Fin h ⊕ Fin (h + 1)) (Fin h ⊕ Fin (h + 1)) (Qt n)[X] :=
  Matrix.of fun r => if r ∈ T then uRow n h r else if r ∈ botRows h then wRow n h r else BlkM n h r

lemma det_HkM_expand : (HkM n h).det =
    ∑ T ∈ (botRows h).powerset, (∏ r ∈ T, aRow n h r) * (NT n h T).det := by
  rw [det_HkM_eq_BlkM]
  refine det_expand_rows _ _ _ _ _ (fun r hr => ?_)
  obtain ⟨a, -, rfl⟩ := mem_map.mp hr
  funext c
  rcases c with j | b
  · simp [BlkM, aRow, uRow, wRow, Matrix.diagonal_mul]
  · simp [BlkM, aRow, uRow, wRow, Matrix.one_apply]

end Setup

end LS
end Ti
end Chi2U
