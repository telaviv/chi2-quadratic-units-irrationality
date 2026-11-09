/-
# Theorem V_odd: definitions and constants

Source: `../handoff/log2log3/pilot_za/PROOF_VODD.md` (a delta to PROOF_V). For odd `a` the unit is
`z_a = (√(a² + 4) − a)/2 = zU a` (the machine at trace `az = a`); `2` is inert in `ℚ(√(a² + 4))`.

The statement `TheoremVOdd`, the exception set `EOdd`, the 2-adic exponent `n2O` (Lemma 10_0), the arithmetic constant
`alphaO`, the list `certA` of traces with a direct certificate and its exponents `PhiC`, and `betaO` (the analytic
constant used at each `a`). The ingredients and the assembly are in `Chi2U/VOdd/Interface.lean`.
-/
import Chi2U.V.Defs

namespace Chi2U
namespace VOdd

open Filter Finset

/-! ## The statement -/

/-- The odd exceptions `a ≥ 5` of Theorem V_odd (39 values). -/
def EOdd : Finset ℕ :=
  {5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33, 35, 37, 39, 41, 43, 45, 47, 49, 51, 53, 55, 57,
    63, 65, 69, 75, 77, 81, 85, 87, 93, 99, 105, 165}

/-- **Theorem V_odd.** `χ₂((√(a² + 4) − a)/2)` is irrational for every odd `a ≥ 5` outside `EOdd`. -/
def TheoremVOdd : Prop :=
  ∀ a : ℕ, Odd a → 5 ≤ a → a ∉ EOdd → Irrational (chi2 ((Real.sqrt ((a : ℝ) ^ 2 + 4) - a) / 2))

/-- `zU a = (√(a² + 4) − a)/2`. -/
lemma zU_eq_half (a : ℕ) : zU a = (Real.sqrt ((a : ℝ) ^ 2 + 4) - a) / 2 := by
  unfold zU
  have h : Real.sqrt (((a : ℝ) / 2) ^ 2 + 1) = Real.sqrt ((a : ℝ) ^ 2 + 4) / 2 := by
    rw [show ((a : ℝ) / 2) ^ 2 + 1 = ((a : ℝ) ^ 2 + 4) / 2 ^ 2 by ring, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq (by norm_num)]
  rw [h]; ring

/-! ## Constants -/

/-- Lemma 10_0's bound on `n₂` at odd `a` (PROOF_VODD §2): `h²/2 + h` (`h` even). -/
def n2O (h : ℕ) : ℕ := h ^ 2 / 2 + h

/-- The arithmetic limit constant at odd `a`: `4/3 + ½ log 2 + Σ_{p^e ‖ a} (e/4 + 1/(4(p − 1))) log p`. -/
noncomputable def alphaO (a : ℕ) : ℝ := 4 / 3 + Real.log 2 / 2 + V.cSV a

/-- The traces with a direct certificate (Lean format; `handoff/log2log3/pilot_za/lean_certza/`). -/
def certA : Finset ℕ := {59, 61, 67, 91, 95, 111, 117, 123, 135, 147, 195}

/-- The certified exponents `Φ(a)` (exact rationals of the generated certificates; `0` off `certA`). -/
def PhiC : ℕ → ℚ
  | 59 => -543651289535819 / 200000000000000
  | 61 => -546976568036957 / 200000000000000
  | 67 => -278174571300181 / 100000000000000
  | 91 => -588872515744563 / 200000000000000
  | 95 => -1185028703313147 / 400000000000000
  | 111 => -121338609879819 / 40000000000000
  | 117 => -306657008537873 / 100000000000000
  | 123 => -308457439547709 / 100000000000000
  | 135 => -10062052121822453 / 3200000000000000
  | 147 => -634659666560277 / 200000000000000
  | 195 => -20713985034247 / 6250000000000
  | _ => 0

/-- The analytic constant used at `a`: the direct certificate on `certA`, else the shift lemma from Theorem U's
certificate, `Φ_L − L(a)/2`. -/
noncomputable def betaO (a : ℕ) : ℝ := if a ∈ certA then (PhiC a : ℝ) else V.PhiL - V.LshiftA a / 2

/-! ## Lemma 10_0, limit form -/

/-- `n2O h · log 2 ≤ (½ log 2 + ε) h²` eventually. -/
theorem lemma10_0_size : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    (n2O h : ℝ) * Real.log 2 ≤ (Real.log 2 / 2 + ε) * (h : ℝ) ^ 2 := by
  intro ε hε
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_ge_atTop (Nat.ceil (Real.log 2 / ε) + 1)] with h hh
  have hdiv : ((h ^ 2 / 2 : ℕ) : ℝ) ≤ (h : ℝ) ^ 2 / 2 := by
    have := Nat.cast_div_le (α := ℝ) (m := h ^ 2) (n := 2); push_cast at this; exact this
  have hn : (n2O h : ℝ) ≤ (h : ℝ) ^ 2 / 2 + h := by unfold n2O; push_cast; linarith
  have hc : Real.log 2 / ε ≤ (h : ℝ) := by
    have := Nat.le_ceil (Real.log 2 / ε)
    have h' : ((Nat.ceil (Real.log 2 / ε) : ℕ) : ℝ) + 1 ≤ h := by exact_mod_cast hh
    linarith
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have hlin : Real.log 2 * h ≤ ε * (h : ℝ) ^ 2 := by
    have := (div_le_iff₀ hε).mp hc
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hn hl2.le]

end VOdd
end Chi2U
