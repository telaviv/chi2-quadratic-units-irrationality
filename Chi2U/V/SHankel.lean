/-
# Lemma S: the atom decomposition of the Hankel matrix and its expansion

`H = 𝒫 + Vᵀ diag(γ) V` (PROOF_U Lemma 7′; `𝒫_{ij} = μ(t^{i+j} div D)`, `V_{a i} = x_a^i`,
`γ_a = z^{x_a}(P(x_a) − X)/D′(x_a)`), so `det H = det [[𝒫, Vᵀ], [−diag(γ)V, 1]]` (Schur complement), and the
row expansion of the bottom rows gives `det H = Σ_{T} (Π_{a ∈ S_T} γ_a) · det N_T` (`det_HkM_expand`), where `N_T`
has bottom rows `(−x_a^j | 0)` for `a ∈ S_T` and `(0 | e_a)` otherwise.
-/
import Chi2U.V.SCount

namespace Chi2U
namespace V
namespace LS

open Polynomial Finset Matrix

section Setup

variable (m : ℕ) [Fact (1 ≤ m)] (h : ℕ)

/-- The poles as integers, indexed by `Fin (h + 1)`. -/
def xP (a : Fin (h + 1)) : ℤ := poleZ h a

/-- The Hankel matrix over `ℚ(√d)[X]` (`Delta_map`). -/
noncomputable def HkM : Matrix (Fin h) (Fin h) (Qd m)[X] :=
  Matrix.of fun i j : Fin h => C (Afun m h (X ^ ((i : ℕ) + j))) + X * C (Bfun m h (X ^ ((i : ℕ) + j)))

/-- The polynomial part `𝒫_{ij} = μ(t^{i+j} div D)`. -/
noncomputable def PmM : Matrix (Fin h) (Fin h) (Qd m)[X] :=
  Matrix.of fun i j : Fin h => C (muPoly m ((X ^ ((i : ℕ) + j) : ℚ[X]) /ₘ Dpoly h))

/-- `V_{a i} = x_a^i`. -/
noncomputable def VmM : Matrix (Fin (h + 1)) (Fin h) (Qd m)[X] :=
  Matrix.of fun a i => ((xP h a ^ (i : ℕ) : ℤ) : (Qd m)[X])

/-- `γ_a = z^{x_a}(P(x_a) − X)/D′(x_a)`. -/
noncomputable def gamF (a : ℕ) : (Qd m)[X] :=
  C ((((dPrime h a)⁻¹ : ℚ) : Qd m) * (zK m) ^ (poleZ h a)) * (C (Psum m (poleZ h a)) - X)

lemma HkM_eq : HkM m h = PmM m h + (VmM m h).transpose * diagonal (fun a : Fin (h + 1) => gamF m h a) * VmM m h := by
  refine Matrix.ext (fun i j => ?_)
  rw [Matrix.add_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, HkM, PmM, VmM, Matrix.of_apply, Matrix.transpose_apply, xP]
  rw [Fin.sum_univ_eq_sum_range (fun a => ((poleZ h a ^ (i : ℕ) : ℤ) : (Qd m)[X]) * gamF m h a *
    ((poleZ h a ^ (j : ℕ) : ℤ) : (Qd m)[X])) (h + 1)]
  unfold Afun Bfun
  rw [C_add, add_assoc]
  congr 1
  have hterm : ∀ a ∈ range (h + 1), ((poleZ h a ^ (i : ℕ) : ℤ) : (Qd m)[X]) * gamF m h a *
      ((poleZ h a ^ (j : ℕ) : ℤ) : (Qd m)[X]) =
      C ((cPole h (X ^ ((i : ℕ) + j)) a : Qd m) * zK m ^ poleZ h a * Psum m (poleZ h a)) -
        X * C ((cPole h (X ^ ((i : ℕ) + j)) a : Qd m) * zK m ^ poleZ h a) := by
    intro a _
    unfold gamF cPole
    rw [eval_pow, eval_X]
    have e : ((((poleZ h a : ℤ) : ℚ) ^ ((i : ℕ) + j) / dPrime h a : ℚ) : Qd m) =
        ((poleZ h a ^ (i : ℕ) : ℤ) : Qd m) * (((dPrime h a)⁻¹ : ℚ) : Qd m) *
          ((poleZ h a ^ (j : ℕ) : ℤ) : Qd m) := by
      push_cast; ring
    rw [e, ← C_eq_intCast, ← C_eq_intCast]
    simp only [C_mul]
    ring
  rw [sum_congr rfl hterm, sum_sub_distrib, ← mul_sum, map_sum, C_neg, map_sum]
  ring

/-- The bordered matrix `[[𝒫, Vᵀ], [−diag(γ)V, 1]]`. -/
noncomputable def BlkM : Matrix (Fin h ⊕ Fin (h + 1)) (Fin h ⊕ Fin (h + 1)) (Qd m)[X] :=
  fromBlocks (PmM m h) (VmM m h).transpose (-(diagonal (fun a : Fin (h + 1) => gamF m h a) * VmM m h)) 1

lemma det_HkM_eq_BlkM : (HkM m h).det = (BlkM m h).det := by
  rw [BlkM, det_fromBlocks_one₂₂, HkM_eq, Matrix.mul_neg, sub_neg_eq_add, Matrix.mul_assoc]

/-- The bottom rows. -/
def botRows : Finset (Fin h ⊕ Fin (h + 1)) := univ.map ⟨Sum.inr, Sum.inr_injective⟩

/-- Row coefficients: `γ_a` on bottom row `a`. -/
noncomputable def aRow : Fin h ⊕ Fin (h + 1) → (Qd m)[X] := Sum.elim (fun _ => 0) (fun a => gamF m h a)

/-- Bottom row `a`, `γ`-part: `(−x_a^j | 0)`. -/
noncomputable def uRow : Fin h ⊕ Fin (h + 1) → Fin h ⊕ Fin (h + 1) → (Qd m)[X] :=
  Sum.elim (fun _ => 0) (fun a => Sum.elim (fun j => -VmM m h a j) (fun _ => 0))

/-- Bottom row `a`, constant part: `(0 | e_a)`. -/
noncomputable def wRow : Fin h ⊕ Fin (h + 1) → Fin h ⊕ Fin (h + 1) → (Qd m)[X] :=
  Sum.elim (fun _ => 0) (fun a => Sum.elim (fun _ => 0) (fun b => if a = b then 1 else 0))

/-- The matrix `N_T` of the term `T ⊆ botRows`. -/
noncomputable def NT (T : Finset (Fin h ⊕ Fin (h + 1))) : Matrix (Fin h ⊕ Fin (h + 1)) (Fin h ⊕ Fin (h + 1)) (Qd m)[X] :=
  Matrix.of fun r => if r ∈ T then uRow m h r else if r ∈ botRows h then wRow m h r else BlkM m h r

lemma det_HkM_expand : (HkM m h).det =
    ∑ T ∈ (botRows h).powerset, (∏ r ∈ T, aRow m h r) * (NT m h T).det := by
  rw [det_HkM_eq_BlkM]
  refine det_expand_rows _ _ _ _ _ (fun r hr => ?_)
  obtain ⟨a, -, rfl⟩ := mem_map.mp hr
  funext c
  rcases c with j | b
  · simp [BlkM, aRow, uRow, wRow, Matrix.diagonal_mul]
  · simp [BlkM, aRow, uRow, wRow, Matrix.one_apply]

end Setup

end LS
end V
end Chi2U
