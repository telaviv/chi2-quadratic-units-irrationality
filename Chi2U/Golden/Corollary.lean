/-
# Golden-ratio corollaries of Theorem U

From `chi2_sqrt5_sub_two_irrational : TheoremU` (`χ₂(√5 − 2) ∉ ℚ`, `Chi2U/Main.lean`) and the closed form
`chi2_sqrt5_sub_two_eq : χ₂(√5 − 2) = π²/24 − ¾ log²φ` (`Chi2U/Golden/ClosedForm.lean`):
* `golden_irrational`: `π²/24 − ¾ log²φ` is irrational;
* `golden_irrational'`: `π² − 18 log²φ` is irrational (it is `24` times the previous number).

These inherit the axioms of `chi2_sqrt5_sub_two_irrational`; the closed form itself uses only the
standard axioms.
-/
import Chi2U.Main
import Chi2U.Golden.ClosedForm

namespace Chi2U

open Real

/-- `π²/24 − ¾ log²φ` is irrational (Theorem U in golden-ratio form). -/
theorem golden_irrational : Irrational (Real.pi ^ 2 / 24 - 3 / 4 * Real.log goldenRatio ^ 2) := by
  rw [← chi2_sqrt5_sub_two_eq]
  exact chi2_sqrt5_sub_two_irrational

/-- `π² − 18 log²φ` is irrational. -/
theorem golden_irrational' : Irrational (Real.pi ^ 2 - 18 * Real.log goldenRatio ^ 2) := by
  have h := golden_irrational.ratCast_mul (q := 24) (by norm_num)
  convert h using 1
  push_cast
  ring

end Chi2U
