/-
# Theorem V_i: definitions and constants (Ti₂ at the norm +1 units)

Source: `../schanuel/four_exp/strong4/pilot_w3/PROOF_TI2.md` (a delta to PROOF_V and PROOF_VODD). For an integer
`n ≥ 3` the unit is `z_n = (n − √(n² − 4))/2 ∈ (0, 1)` (`z² − nz + 1 = 0`, norm `+1`); every quadratic unit in `(0, 1)`
of norm `+1` is some `z_n`, with `n` its trace.

The machine for `Ti₂(z) = Σ (−1)^k z^{2k+1}/(2k+1)²` is χ₂'s machine with `y = −z²` in place of `y = z²`
(`1 − y = 1 + z² = n·z`); it lives in `Chi2U/Ti/*` (a copy of the χ₂ machine with the sign fixed, so that the files of
Theorems U, V and V_odd are untouched).

This file: the inverse tangent integral `Ti2`, the statement `TheoremVi`, the exception set `EOddI`, the real unit
`zT`, and the constants of the margin (`c2T`, `alphaT`, `LshiftT`, `betaT`).
-/
import Chi2U.V.Defs

namespace Chi2U
namespace Ti

open Filter Finset

/-! ## The inverse tangent integral -/

/-- The `k`-th term of `Ti₂`. -/
noncomputable def ti2Term (z : ℝ) (k : ℕ) : ℝ := (-1) ^ k * z ^ (2 * k + 1) / (2 * (k : ℝ) + 1) ^ 2

/-- The inverse tangent integral `Ti₂(z) = Σ_{k ≥ 0} (−1)^k z^{2k+1}/(2k+1)²`. -/
noncomputable def Ti2 (z : ℝ) : ℝ := ∑' k : ℕ, ti2Term z k

/-! ## The statement -/

/-- The odd exceptions `n ≥ 71` of Theorem V_i (17 values, all `≤ 195`). -/
def EOddI : Finset ℕ :=
  {75, 77, 81, 85, 87, 91, 93, 95, 99, 105, 111, 117, 123, 135, 147, 165, 195}

/-- **Theorem V_i.** `Ti₂((n − √(n² − 4))/2)` is irrational
* for every even `n = 2m` with `m ≥ 4`, `m ∉ {5, 7, 9, 15}` (i.e. `Ti₂(m − √(m² − 1)) ∉ ℚ`), and
* for every odd `n ≥ 71` outside `EOddI`. -/
def TheoremVi : Prop :=
  (∀ m : ℕ, 4 ≤ m → m ∉ ({5, 7, 9, 15} : Finset ℕ) → Irrational (Ti2 (m - Real.sqrt ((m : ℝ) ^ 2 - 1)))) ∧
  (∀ n : ℕ, Odd n → 71 ≤ n → n ∉ EOddI → Irrational (Ti2 ((n - Real.sqrt ((n : ℝ) ^ 2 - 4)) / 2)))

/-! ## The real unit -/

/-- `z_n = n/2 − √((n/2)² − 1) = (n − √(n² − 4))/2`. -/
noncomputable def zT (n : ℕ) : ℝ := n / 2 - Real.sqrt (((n : ℝ) / 2) ^ 2 - 1)

lemma zT_eq_half (n : ℕ) : zT n = (n - Real.sqrt ((n : ℝ) ^ 2 - 4)) / 2 := by
  unfold zT
  have h : Real.sqrt (((n : ℝ) / 2) ^ 2 - 1) = Real.sqrt ((n : ℝ) ^ 2 - 4) / 2 := by
    rw [show ((n : ℝ) / 2) ^ 2 - 1 = ((n : ℝ) ^ 2 - 4) / 2 ^ 2 by ring, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq (by norm_num)]
  rw [h]; ring

lemma zT_two_mul (m : ℕ) : zT (2 * m) = m - Real.sqrt ((m : ℝ) ^ 2 - 1) := by
  unfold zT; push_cast; ring_nf

/-! ## Constants of the margin (PROOF_TI2 §0, §6) -/

/-- `c₂`: `½ log 2` for odd `n` (Lemma 10_0), `|ν − 2| log 2 / 4` with `ν = v₂(n)` for even `n` (Lemma 10_ν). -/
noncomputable def c2T (n : ℕ) : ℝ :=
  if n % 2 = 1 then Real.log 2 / 2 else |(padicValNat 2 n : ℝ) - 2| * Real.log 2 / 4

/-- The arithmetic limit constant `α(n) = 4/3 + c₂ + Σ_{p^e ‖ n, p odd} (e/4 + 1/(4(p − 1))) log p`. -/
noncomputable def alphaT (n : ℕ) : ℝ := 4 / 3 + c2T n + V.cSV n

/-- The shift `L(n) = log(z₂/z_n)` from Theorem U's point `z₂ = √5 − 2` to `z_n`. -/
noncomputable def LshiftT (n : ℕ) : ℝ := Real.log (zU 4) - Real.log (zT n)

/-- The analytic constant from the shift lemma: `Φ_L − L(n)/2`. -/
noncomputable def betaT (n : ℕ) : ℝ := V.PhiL - LshiftT n / 2

/-- The traces covered by the margin: `n ≥ 5` outside the exception set (even `n ∈ {6, 10, 14, 18, 30}`, odd `n ≤ 69`,
and `n ∈ EOddI`). -/
def marginOK (n : ℕ) : Prop :=
  5 ≤ n ∧ n ∉ ({6, 10, 14, 18, 30} : Finset ℕ) ∧ ¬ (n % 2 = 1 ∧ n ≤ 69) ∧ n ∉ EOddI

end Ti
end Chi2U
