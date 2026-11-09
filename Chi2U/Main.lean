/-
# Theorem U: `χ₂(√5 − 2)` is irrational (PROOF_U §7)

`boundsU` supplies the endgame inputs:
* `den = denAll`, `α = 4/3` (Theorem A′ + Lemma 10′: `log_denAll_le`);
* `β = −27/20` (Theorem B′ with a certificate `Φ < −27/20`: `exists_certU`);
* margin `4/3 − 27/20 = −1/60 < 0`;
* nonvanishing along `h = 3ℓ − 1` (Lemma P′: `nonvan_frequently`).
The machine is the `az = 4` instance of the parametric one (`Field.lean`: `Qd 4 = ℚ(√5)`, `zU_four`).
-/
import Chi2U.MainCond
import Chi2U.Statement
import Chi2U.Arith.Assembly
import Chi2U.Cert.CertU
import Chi2U.NonVan.LemmaP

namespace Chi2U

open Polynomial Filter

/-- The endgame inputs for Theorem U. -/
noncomputable def boundsU : MachineBoundsU where
  den := denAll
  den_pos := denAll_pos
  den_int := denAll_int
  α := 4 / 3
  β := -27 / 20
  margin := by norm_num
  arith := log_denAll_le
  analytic := fun ε hε => by
    obtain ⟨C, hC⟩ := exists_certU
    filter_upwards [C.analytic ε hε] with h hh hev
    refine (hh hev).trans (Real.exp_le_exp.mpr ?_)
    have : (0 : ℝ) ≤ (h : ℝ) ^ 2 := by positivity
    nlinarith
  nonvan := nonvan_frequently

/-- **Theorem U.** `χ₂(√5 − 2) = π²/24 − ¾ log²φ` is irrational. -/
theorem chi2_sqrt5_sub_two_irrational : TheoremU := by
  have := irrational_of_boundsU boundsU
  unfold TU at this
  rwa [zU_four] at this

end Chi2U
