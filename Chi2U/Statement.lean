/-
# The target statement (Theorem U)

`χ₂(√5 − 2) = Σ_{n ≥ 0} (√5 − 2)^{2n+1}/(2n+1)²` is irrational (`Irrational` from Mathlib).
By Landen's identity `χ₂(√5 − 2) = π²/24 − ¾ log²φ` (proved as `Chi2U.chi2_sqrt5_sub_two_eq` in
`Golden/ClosedForm.lean`), so this says `π² − 18 log²φ ∉ ℚ` (`Chi2U.golden_irrational'` in `Golden/Corollary.lean`).
-/
import Chi2U.Defs

namespace Chi2U

/-- **Theorem U.** `χ₂(√5 − 2)` is irrational. -/
def TheoremU : Prop := Irrational (chi2 (Real.sqrt 5 - 2))

end Chi2U
