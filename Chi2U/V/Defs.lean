/-
# Theorem V: definitions and constants (PROOF_V, `schanuel/four_exp/strong4/pilot_V/PROOF_V.md`)

The statement `TheoremV`, the constants of the margin (`alphaV`, `Lshift`, `PhiL`), the exponents `n2V`, `eS`, and the
proved size bound `lemma10nu_size`. The ingredients (proved in `Chi2U/V/*`) and the assembly are in `Chi2U/V/Interface.lean`.
-/
import Chi2U.Main

namespace Chi2U
namespace V

open Polynomial Filter Finset

/-! ## The statement and the conditional endgame -/

/-- **Theorem V.** `χ₂(√(m² + 1) − m)` is irrational for every `m ≥ 2` outside `{3, 5, 7, 9, 15}`. -/
def TheoremV : Prop :=
  ∀ m : ℕ, 2 ≤ m → m ∉ ({3, 5, 7, 9, 15} : Finset ℕ) → Irrational (chi2 (Real.sqrt ((m : ℝ) ^ 2 + 1) - m))

/-- The endgame inputs at `z_m` (`α` = arithmetic limit constant, `β` = analytic constant). -/
abbrev MachineBoundsV (m : ℕ) [Fact (1 ≤ m)] : Type := MachineBounds m

/-- The endgame (Lemma E) at `z_m`: proved, generic in `m`. -/
theorem irrational_of_boundsV {m : ℕ} [Fact (1 ≤ m)] (H : MachineBoundsV m) :
    Irrational (chi2 (Real.sqrt ((m : ℝ) ^ 2 + 1) - m)) :=
  irrational_of_bounds H

/-! ## Constants -/

/-- `ν = v₂(1 − y) = 1 + v₂(m)`. -/
def nuV (m : ℕ) : ℕ := 1 + padicValNat 2 m

/-- `c₂(ν) = |ν − 2| log 2 / 4`. -/
noncomputable def c2V (m : ℕ) : ℝ := |(nuV m : ℝ) - 2| * Real.log 2 / 4

/-- The odd prime divisors of `m` (the special primes of Lemma S). -/
def oddDiv (m : ℕ) : Finset ℕ := m.primeFactors.filter (· ≠ 2)

/-- `Σ_{p^e ‖ m, p odd} (e/4 + 1/(4(p − 1))) log p`. -/
noncomputable def cSV (m : ℕ) : ℝ :=
  ∑ p ∈ oddDiv m, ((padicValNat p m : ℝ) / 4 + 1 / (4 * ((p : ℝ) - 1))) * Real.log p

/-- The arithmetic limit constant `α(m) = 4/3 + c₂(ν) + Σ_{p ∣ m odd} c_p(e)`. -/
noncomputable def alphaV (m : ℕ) : ℝ := 4 / 3 + c2V m + cSV m

/-- `L(m) = log(z₂/z_m) = log((m + √(m² + 1))/(2 + √5))`. -/
noncomputable def Lshift (m : ℕ) : ℝ := Real.log (zU 2) - Real.log (zU m)

/-- `Φ_L = −1.3538792`, the exponent of Theorem U's Lean certificate (`exists_certU'`). -/
noncomputable def PhiL : ℝ := -13538792 / 10000000

/-! ## Exponents -/

/-- Lemma 10_ν's bound on `n₂` (PROOF_V §4): `(ν − 1)(h/2 − 1)² − (h/2)² + h⌊log₂ h⌋ + 5h − 1` for `ν ≥ 2`,
`(h/2 − 1)² + 3h` for `ν = 1` (`h` even). -/
def n2V (m h : ℕ) : ℕ :=
  if 2 ≤ nuV m then (nuV m - 1) * (h / 2 - 1) ^ 2 + h * Nat.log 2 h + 5 * h - 1 - (h / 2) ^ 2
  else (h / 2 - 1) ^ 2 + 3 * h

/-- The levels `l ≥ 1` with `p^l < K = h + 1`. -/
def levelsV (h p : ℕ) : Finset ℕ := (Icc 1 h).filter (fun l => p ^ l ≤ h)

/-- Lemma S's bound on `n_p` for odd `p ∣ m`: `Σ_l A_K(p^l) + v_p(m)·(h/2 − 1)²`. -/
def eS (m h p : ℕ) : ℕ := ∑ l ∈ levelsV h p, AK h (p ^ l) + padicValNat p m * (h / 2 - 1) ^ 2

/-- `n2V m h ≤ |ν − 2|·(h/2)² + h⌊log₂ h⌋ + 5h`. -/
lemma n2V_le (m h : ℕ) :
    (n2V m h : ℝ) ≤ |(nuV m : ℝ) - 2| * ((h / 2 : ℕ) : ℝ) ^ 2 + (h : ℝ) * (Nat.log 2 h : ℝ) + 5 * h := by
  set J := h / 2 with hJ
  have hsq : (J - 1) ^ 2 ≤ J ^ 2 := Nat.pow_le_pow_left (Nat.sub_le _ _) 2
  unfold n2V
  split_ifs with hν
  · have hX : (nuV m - 1) * (J - 1) ^ 2 ≤ (nuV m - 2) * J ^ 2 + J ^ 2 := by
      calc (nuV m - 1) * (J - 1) ^ 2 ≤ (nuV m - 1) * J ^ 2 := Nat.mul_le_mul_left _ hsq
        _ = (nuV m - 2) * J ^ 2 + J ^ 2 := by
          rw [show nuV m - 1 = (nuV m - 2) + 1 by omega]; ring
    have hN : (nuV m - 1) * (J - 1) ^ 2 + h * Nat.log 2 h + 5 * h - 1 - J ^ 2 ≤
        (nuV m - 2) * J ^ 2 + h * Nat.log 2 h + 5 * h := by
      generalize (nuV m - 1) * (J - 1) ^ 2 = X at hX ⊢
      generalize (nuV m - 2) * J ^ 2 = Z at hX ⊢
      omega
    have hc : ((nuV m - 2 : ℕ) : ℝ) = |(nuV m : ℝ) - 2| := by
      have h2 : (2 : ℝ) ≤ nuV m := by exact_mod_cast hν
      rw [Nat.cast_sub hν, abs_of_nonneg (by linarith)]; norm_num
    have := (Nat.cast_le (α := ℝ)).mpr hN
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, hc] at this
    push_cast at this ⊢
    linarith
  · have hν1 : nuV m = 1 := by unfold nuV at *; omega
    have h1 : ((J - 1) ^ 2 : ℕ) ≤ J ^ 2 := hsq
    have := (Nat.cast_le (α := ℝ)).mpr h1
    rw [hν1]
    push_cast at this ⊢
    have hL0 : (0 : ℝ) ≤ (h : ℝ) * (Nat.log 2 h : ℝ) := by positivity
    have : |(1 : ℝ) - 2| = 1 := by norm_num
    nlinarith

/-- Lemma 10_ν, limit form: `n2V m h · log 2 ≤ (c₂(ν) + ε) h²` eventually (the `h²` coefficient of `n2V` is
`|ν − 2|/4`, the rest is `O(h log h)`). -/
theorem lemma10nu_size (m : ℕ) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    (n2V m h : ℝ) * Real.log 2 ≤ (c2V m + ε) * (h : ℝ) ^ 2 := by
  intro ε hε
  filter_upwards [eventually_rem_le_U ε hε, eventually_ge_atTop 1] with h hR h1
  have hJh : ((h / 2 : ℕ) : ℝ) ≤ (h : ℝ) / 2 := Nat.cast_div_le
  have hJ0 : (0 : ℝ) ≤ ((h / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hJ2 : ((h / 2 : ℕ) : ℝ) ^ 2 ≤ (h : ℝ) ^ 2 / 4 := by nlinarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hL : (Nat.log 2 h : ℝ) * Real.log 2 ≤ Real.log h := by
    have hp := Nat.pow_log_le_self 2 (by omega : h ≠ 0)
    have : ((2 : ℝ) ^ Nat.log 2 h) ≤ h := by exact_mod_cast hp
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) this
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have hlh : 0 ≤ Real.log h := Real.log_natCast_nonneg h
  have hA : (0 : ℝ) ≤ |(nuV m : ℝ) - 2| := abs_nonneg _
  have key := mul_le_mul_of_nonneg_right (n2V_le m h) hl2.le
  have e1 : |(nuV m : ℝ) - 2| * ((h / 2 : ℕ) : ℝ) ^ 2 * Real.log 2 ≤ c2V m * (h : ℝ) ^ 2 := by
    unfold c2V
    have := mul_le_mul_of_nonneg_left hJ2 (mul_nonneg hA hl2.le)
    nlinarith
  have e2 : (h : ℝ) * (Nat.log 2 h : ℝ) * Real.log 2 ≤ (h : ℝ) * Real.log h := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hL hh0
  have e3 : 5 * (h : ℝ) * Real.log 2 ≤ 5 * h := by nlinarith
  nlinarith

end V
end Chi2U
