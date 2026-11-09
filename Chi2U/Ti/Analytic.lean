/-
# Theorem V_i: the analytic bound `analytic_T` (PROOF_TI2 §2, rows "§5.1 Theorem B′_z" and "§5.2 shift lemma")

`analytic_T_proof` (the stub `analytic_T` of `Ti/Interface.lean`, same statement): for `n ≥ 5`, `δ, ε > 0`, eventually
in even `h`, `|Δ_h(T)| ≤ exp((betaT n + δ + ε) h²)`, `T = Ti₂(zT n)`, `betaT n = Φ_L − L(n)/2`.

Route (the χ₂ Theorem V's, `V/Interface.lean`): Theorem U's certificate `exists_certU'` (`Φ < Φ_L = −1.3538792`) is
moved to `z = zT n ≤ zU 4` by the shift lemma (`Ti/Analytic/ShiftT.lean`, a copy of `V/Shift.lean`), and Theorem B′_z
(`DualCertT.analytic`, `Ti/Analytic/TheoremBT.lean`, a copy of `Analytic/TheoremBU.lean` with the signed node weights
`χ₄(τ) z^τ` of `Ti/Analytic/NodesT.lean`) gives the bound. No χ₂ file is edited.
-/
import Chi2U.Ti.Analytic.ShiftT

namespace Chi2U
namespace Ti

open Polynomial Filter

/-- **The analytic bound** (Theorem B′_z at `z = zT n` with the shift lemma from Theorem U's certificate; PROOF_TI2 §2,
PROOF_V §5). The statement of `analytic_T` in `Ti/Interface.lean`. -/
theorem analytic_T_proof (n : ℕ) [Fact (3 ≤ n)] (h5 : 5 ≤ n) {δ : ℝ} (hδ : 0 < δ) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    Even h → |aeval (TT n) (Delta n h)| ≤ Real.exp ((betaT n + δ + ε) * (h : ℝ) ^ 2) := by
  intro ε hε
  obtain ⟨C, hC⟩ := exists_certU'
  obtain ⟨C', hC'⟩ := shift_lemma_proof (n := n) C h5 hδ
  have hΦ : C'.Phi ≤ betaT n + δ := by
    unfold betaT V.PhiL
    linarith
  filter_upwards [C'.analytic ε hε] with h hh heven
  refine (hh heven).trans (Real.exp_le_exp.mpr ?_)
  have : (0 : ℝ) ≤ (h : ℝ) ^ 2 := sq_nonneg _
  nlinarith

end Ti
end Chi2U
