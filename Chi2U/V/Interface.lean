/-
# Theorem V: the stage-B2 interface (PROOF_V, `schanuel/four_exp/strong4/pilot_V/PROOF_V.md`)

**Theorem V.** For every `m ≥ 2`, `m ∉ E = {3, 5, 7, 9, 15}`: `χ₂(√(m² + 1) − m) ∉ ℚ` (`TheoremV`).

The machine of Theorem U is parametric in `m` (`Field`, `Moments`, `Machine`, `LemmaR`, `PoleExpansion`, `Mahler`,
`Arith/VGe`, …, all with a parameter `mz`), and so are the endgame (`MainCond.irrational_of_bounds`), the generic
odd primes `p ∤ 2m` (Lemmas 8′, 8A′, 9′: `padicNorm_Delta_odd`; Theorem A′: `theoremA`) and Theorem B′
(`DualCertU.analytic`, any `m`, given a dual certificate at `z_m`). This file states, as `sorry` stubs, exactly what is
still missing (six stubs; `lemma10nu_size` is already proved), and **proves** `TheoremV` from the stubs
(`theoremV`):

| stub | PROOF_V | statement |
|---|---|---|
| `lemma10nu` | §4, Lemma 10_ν | `n₂ ≤ n2V m h` (`ν = 1 + v₂(m)`) |
| `lemma10nu_size` | §4 ("consequently") | `n2V m h · log 2 ≤ (c₂(ν) + ε) h²` eventually — **proved** (`n2V_le`) |
| `lemmaS` | §3.2, Lemma S | odd `p ∣ m`: `n_p ≤ Σ_{l ≥ 1, p^l ≤ h} A_K(p^l) + e·(h/2 − 1)²`, `e = v_p(m)` |
| `AK_levels_size` | §3.2 ("for the limit") | `Σ_l A_K(p^l) ≤ (1/(4(p − 1)) + ε) h²` eventually |
| `shift_lemma` | §5.2 | a certificate at `z₂` gives one at `z_m` with `Φ' ≤ Φ − L(m)/2 + δ` (any `δ > 0`) |
| `margin_V` | §0, §7 | `α(m) + Φ_L − L(m)/2 < 0` for `m ≥ 2`, `m ∉ E` |
| `lemmaP_m` | §6, Lemma P′_m | `Δ_{3ℓ−1}(a/b) ≠ 0` for primes `ℓ ≥ 7`, `ℓ ∤ 2m(m² + 1)`, `ℓ² ∤ b` |

Constants (weaker than PROOF_V where the Lean pieces are weaker):
* `Φ_L = −1.3538792` (the Lean certificate: `exists_certU'`, `data.PhiQ = −1.3538792442…`) instead of PROOF_V's
  `Φ_U = −1.3592161834586374`;
* the shift lemma in the discrete certificate format of `Analytic/TheoremBU.lean` loses `L(m)/(2rL)` when every
  cell is split into `r` subcells (left-endpoint Riemann sum of `(1 − x)₊`); hence the arbitrary `δ > 0`;
* `α(m) = 4/3 + c₂(ν) + Σ_{p^e ‖ m, p odd} (e/4 + 1/(4(p − 1))) log p` exactly as in PROOF_V.
Margins with `Φ_L` (`scripts/margins_lean.py`, 60-digit arithmetic, `m ≤ 3000`, plus the closed form of PROOF_V §7
with `Φ_L`, valid for odd `m > 68` and all even `m ≥ 4`): `M(m) ≥ 0` exactly for `m ∈ E`; tightest `m = 11`
(`M = −0.012571`), `m = 21` (`−0.015023`), `m = 2` (`−0.020546`).

Proof of `theoremV` from the stubs: denominators `denV0 m h = 2^{n2V} · Π_{p ≤ h odd, p ∤ m} p^{eOdd} ·
Π_{p ∣ m odd} p^{eS}` (integrality from `lemma10nu`, `padicNorm_Delta_odd`, `lemmaS`; size from `lemma10nu_size`,
`theoremA`, `AK_levels_size`), `β = Φ` of the shifted certificate, nonvanishing along `h = 3ℓ − 1` for large primes
`ℓ`; then `irrational_of_boundsV`.
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

/-! ## The stubs (stage B2) -/

/-- **Lemma 10_ν** (PROOF_V §4): `n₂(Δ_h) ≤ n2V m h` for even `h ≥ 2`. Generalises Lemma 10′ (`Arith/TwoAdic*`,
`mz = 2`, where `n₂ ≤ h⌊log₂ h⌋ + 3h`). Checked on exact `Δ_h` for `m = 1, 3, 4, 6, 8, 12`, `h ≤ 16` (`scripts/check_defs_v.py`). -/
theorem lemma10nu (m : ℕ) [Fact (1 ≤ m)] {h : ℕ} (hh : Even h) (h2 : 2 ≤ h) (k : ℕ) :
    padicNorm 2 ((Delta m h).coeff k) ≤ (2 : ℚ) ^ n2V m h := by
  sorry

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

/-- **Lemma S** (PROOF_V §3.2): for an odd prime `p ∣ m`, `n_p ≤ Σ_{l ≥ 1, p^l ≤ h} A_K(p^l) + e(h/2 − 1)²`,
`e = v_p(m)`. Needs the multi-level Lemma 8′ (statement in `attic/Lemma8_general_unused.lean`; a class-adapted
proof for a similar machine is in `../lean_chi2/Chi2Irrational/Arith/ClassBound.lean`, `Special.lean`) plus the
polynomial-minor bound `v_p(𝒫_ij) ≥ −e(i + j − K)₊` from the Mahler form (`Mahler.Lmom_eq_mahler`, denominators
`(2m)^{b+1}`). Checked on exact `Δ_h` (`scripts/check_defs_v.py`). -/
theorem lemmaS (m : ℕ) [Fact (1 ≤ m)] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hpm : p ∣ m) {h : ℕ} (hh : Even h)
    (k : ℕ) : padicNorm p ((Delta m h).coeff k) ≤ (p : ℚ) ^ eS m h p := by
  sorry

/-- Lemma S, limit form: `Σ_l A_K(p^l) ≤ (1/(4(p − 1)) + ε) h²` eventually (`A_K(d) ≤ K²/(4d) + O(K)`,
`Σ_l p^{−l} ≤ 1/(p − 1)`). -/
theorem AK_levels_size {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    ((∑ l ∈ levelsV h p, AK h (p ^ l) : ℕ) : ℝ) ≤ (1 / (4 * ((p : ℝ) - 1)) + ε) * (h : ℝ) ^ 2 := by
  sorry

/-- **Shift lemma** (PROOF_V §5.2) in the certificate format of `Analytic/TheoremBU.lean`: from a certificate at
`z₂` build one at `z_m` (same `μ`, `λ' = λ − L(m)`, every cell split into `r` subcells with
`S'_{k'} = S_k − L(m)·k'/(rL)`; the tail conditions only improve since `L(m) ≥ 0`, `X ≥ 4`); then
`Φ' ≤ Φ − L(m)/2 + L(m)/(2rL)`, and `r` is taken large. -/
theorem shift_lemma (C : DualCertU 2) (m : ℕ) [Fact (1 ≤ m)] (hm : 2 ≤ m) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C' : DualCertU m, C'.Phi ≤ C.Phi - Lshift m / 2 + δ := by
  sorry

/-- **The margin inequality** `M(m) < 0` (PROOF_V §0, §7) with Lean's constant `Φ_L`. Numerically: `M(m) ≥ 0`
exactly on `E` for `m ≤ 3000`; closed form beyond (`scripts/margins_lean.py`); tightest `M(11) = −0.012571`. -/
theorem margin_V {m : ℕ} (hm : 2 ≤ m) (hE : m ∉ ({3, 5, 7, 9, 15} : Finset ℕ)) :
    alphaV m + (PhiL - Lshift m / 2) < 0 := by
  sorry

/-- **Lemma P′_m** (PROOF_V §6) for primes `ℓ ≥ 7` with `ℓ ∤ 2m(m² + 1)` (excluding `ℓ ∣ d` avoids the ramified
and index cases; infinitely many `ℓ` remain). The Lean proof of Lemma P′ (`NonVan/**`) is written for `mz = 2`;
its steps use `z`, `1 − y = 2mz·z` and `1 − z^{2ℓ}` only through their being `𝔩`-units. -/
theorem lemmaP_m (m : ℕ) [Fact (1 ≤ m)] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : 7 ≤ ℓ) (hℓm : ¬ ℓ ∣ 2 * m * (m ^ 2 + 1))
    (a : ℤ) {b : ℕ} (hb : 0 < b) (hb2 : ¬ ℓ ^ 2 ∣ b) : (Delta m (3 * ℓ - 1)).eval ((a : ℚ) / b) ≠ 0 := by
  sorry

/-! ## Assembly (proved from the stubs) -/

/-- `|Π_{q ∈ S} q^{f q}|_p = p^{−f p}` if `p ∈ S`, else `1` (`S` a set of primes). -/
lemma padicNorm_prod_primes (p : ℕ) [Fact p.Prime] (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (f : ℕ → ℕ) :
    padicNorm p (∏ q ∈ S, (q : ℚ) ^ f q) = if p ∈ S then ((p : ℚ)⁻¹) ^ f p else 1 := by
  rw [padicNorm_prod_U]
  rw [prod_congr rfl (fun q hq => by rw [padicNorm_pow_U, padicNorm_prime_nat_U (hS q hq)])]
  rw [prod_congr rfl (fun q _ => (show (if q = p then (p : ℚ)⁻¹ else 1) ^ f q =
      if q = p then ((p : ℚ)⁻¹) ^ f p else 1 by split_ifs with he <;> simp [he]))]
  rw [prod_ite_eq']

/-- The generic odd primes `p ≤ h`, `p ∤ m`. -/
def oddGen (m h : ℕ) : Finset ℕ := (oddPrimes h).filter (fun p => ¬ p ∣ m)

lemma prime_of_mem_oddGen {m h q : ℕ} (hq : q ∈ oddGen m h) : q.Prime := (mem_filter.mp (mem_filter.mp hq).1).2.1

lemma prime_of_mem_oddDiv {m q : ℕ} (hq : q ∈ oddDiv m) : q.Prime :=
  Nat.prime_of_mem_primeFactors (mem_filter.mp hq).1

/-- The proved denominator for even `h ≥ 2`. -/
noncomputable def denV0 (m h : ℕ) : ℚ :=
  (2 : ℚ) ^ n2V m h * (∏ p ∈ oddGen m h, (p : ℚ) ^ eOdd h p) * ∏ p ∈ oddDiv m, (p : ℚ) ^ eS m h p

lemma denV0_pos (m h : ℕ) : 0 < denV0 m h := by
  unfold denV0
  refine mul_pos (mul_pos (by positivity) (prod_pos (fun p hp => ?_))) (prod_pos (fun p hp => ?_))
  · have := (prime_of_mem_oddGen hp).pos; positivity
  · have := (prime_of_mem_oddDiv hp).pos; positivity

lemma inv_pow_mul_le_one {p : ℚ} (hp : 0 < p) {e : ℕ} {x : ℚ} (hx0 : 0 ≤ x) (hx : x ≤ p ^ e) :
    (p⁻¹) ^ e * x ≤ 1 := by
  calc (p⁻¹) ^ e * x ≤ (p⁻¹) ^ e * p ^ e := mul_le_mul_of_nonneg_left hx (by positivity)
    _ = 1 := by rw [inv_pow]; field_simp

/-- `denV0 m h · Δ_h ∈ ℤ[X]` for even `h ≥ 2`. -/
theorem denV0_int (m : ℕ) [Fact (1 ≤ m)] {h : ℕ} (hh : Even h) (h2 : 2 ≤ h) (k : ℕ) :
    ∃ z : ℤ, denV0 m h * (Delta m h).coeff k = z := by
  refine exists_int_of_padicNorm_le_U _ (fun p hp => ?_)
  have := Fact.mk hp
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  unfold denV0
  rw [padicNorm.mul, padicNorm.mul, padicNorm.mul, padicNorm_pow_U, padicNorm_two_U,
    padicNorm_prod_primes p _ (fun q hq => prime_of_mem_oddGen hq),
    padicNorm_prod_primes p _ (fun q hq => prime_of_mem_oddDiv hq)]
  have hc0 := padicNorm.nonneg (p := p) ((Delta m h).coeff k)
  by_cases h2p : p = 2
  · subst h2p
    have h1 : (2 : ℕ) ∉ oddGen m h := fun hm => (mem_filter.mp (mem_filter.mp hm).1).2.2 rfl
    have h3 : (2 : ℕ) ∉ oddDiv m := fun hm => (mem_filter.mp hm).2 rfl
    rw [if_pos rfl, if_neg h1, if_neg h3, mul_one, mul_one]
    exact inv_pow_mul_le_one hp0 hc0 (by exact_mod_cast lemma10nu m hh h2 k)
  · rw [if_neg (Ne.symm h2p), one_pow, one_mul]
    by_cases hpm : p ∣ m
    · have hD : p ∈ oddDiv m := mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpm, by
        have := (Fact.out : 1 ≤ m); omega⟩, h2p⟩
      have hG : p ∉ oddGen m h := fun hm => (mem_filter.mp hm).2 hpm
      rw [if_neg hG, if_pos hD, one_mul]
      exact inv_pow_mul_le_one hp0 hc0 (lemmaS m h2p hpm hh k)
    · have hD : p ∉ oddDiv m := fun hm => hpm (Nat.dvd_of_mem_primeFactors (mem_filter.mp hm).1)
      rw [if_neg hD, mul_one]
      have hc := padicNorm_Delta_odd (p := p) h2p hpm hh k
      split_ifs with hG
      · exact inv_pow_mul_le_one hp0 hc0 hc
      · have hph : h < p := by
          by_contra hc'
          exact hG (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega), hp, h2p⟩, hpm⟩)
        rw [eOdd_eq_zero_asm hph, pow_zero] at hc
        simpa using hc

/-- The denominators used by the endgame (odd `h` and `h = 0` are not used). -/
noncomputable def denV (m : ℕ) [Fact (1 ≤ m)] (h : ℕ) : ℚ :=
  if Even h ∧ 2 ≤ h then denV0 m h else Classical.choose (exists_den (Delta m h))

lemma denV_pos (m : ℕ) [Fact (1 ≤ m)] (h : ℕ) : 0 < denV m h := by
  unfold denV
  split_ifs
  · exact denV0_pos m h
  · exact (Classical.choose_spec (exists_den (Delta m h))).1

lemma denV_int (m : ℕ) [Fact (1 ≤ m)] (h k : ℕ) : ∃ z : ℤ, denV m h * (Delta m h).coeff k = z := by
  unfold denV
  split_ifs with hh
  · exact denV0_int m hh.1 hh.2 k
  · exact (Classical.choose_spec (exists_den (Delta m h))).2 k

lemma half_sub_one_sq_le (h : ℕ) : (((h / 2 - 1) ^ 2 : ℕ) : ℝ) ≤ (h : ℝ) ^ 2 / 4 := by
  have h1 : ((h / 2 - 1 : ℕ) : ℝ) ≤ (h : ℝ) / 2 := by
    calc ((h / 2 - 1 : ℕ) : ℝ) ≤ ((h / 2 : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
      _ ≤ (h : ℝ) / 2 := Nat.cast_div_le
  push_cast
  have h0 : (0 : ℝ) ≤ ((h / 2 - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- **The arithmetic bound** at `z_m`: `log den h ≤ (α(m) + ε) h²` for even `h`, eventually. -/
theorem log_denV_le (m : ℕ) [Fact (1 ≤ m)] : ∀ ε > 0, ∀ᶠ h : ℕ in atTop, Even h →
    Real.log (denV m h) ≤ (alphaV m + ε) * (h : ℝ) ^ 2 := by
  intro ε hε
  set W : ℝ := ∑ p ∈ oddDiv m, Real.log p with hW
  have hW0 : 0 ≤ W := sum_nonneg (fun p hp => Real.log_natCast_nonneg p)
  set ε' : ℝ := ε / (3 * (W + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hS := (eventually_all_finset (oddDiv m)).2
    (fun p hp => AK_levels_size (prime_of_mem_oddDiv hp) (mem_filter.mp hp).2 ε' hε'0)
  filter_upwards [theoremA (ε / 3) (by positivity), lemma10nu_size m (ε / 3) (by positivity), hS,
    eventually_ge_atTop 2] with h hA h2 hS' hh2 hev
  have hd : denV m h = denV0 m h := by unfold denV; rw [if_pos ⟨hev, hh2⟩]
  rw [hd]
  have hne1 : ∀ p ∈ oddGen m h, ((p : ℝ)) ^ eOdd h p ≠ 0 := fun p hp =>
    pow_ne_zero _ (by exact_mod_cast (prime_of_mem_oddGen hp).ne_zero)
  have hne2 : ∀ p ∈ oddDiv m, ((p : ℝ)) ^ eS m h p ≠ 0 := fun p hp =>
    pow_ne_zero _ (by exact_mod_cast (prime_of_mem_oddDiv hp).ne_zero)
  have hlog : Real.log ((denV0 m h : ℚ) : ℝ) = (n2V m h : ℝ) * Real.log 2 +
      ∑ p ∈ oddGen m h, (eOdd h p : ℝ) * Real.log p + ∑ p ∈ oddDiv m, (eS m h p : ℝ) * Real.log p := by
    unfold denV0
    push_cast
    rw [Real.log_mul (mul_ne_zero (by positivity) (prod_ne_zero_iff.mpr hne1)) (prod_ne_zero_iff.mpr hne2),
      Real.log_mul (by positivity) (prod_ne_zero_iff.mpr hne1), Real.log_pow, Real.log_prod hne1,
      Real.log_prod hne2]
    simp only [Real.log_pow]
  rw [hlog]
  -- generic odd primes: a subset of the odd primes `≤ h`
  have hG : ∑ p ∈ oddGen m h, (eOdd h p : ℝ) * Real.log p ≤ (4 / 3 + ε / 3) * (h : ℝ) ^ 2 :=
    le_trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p))) hA
  -- special primes
  have hSp : ∑ p ∈ oddDiv m, (eS m h p : ℝ) * Real.log p ≤ (cSV m + ε / 3) * (h : ℝ) ^ 2 := by
    have hterm : ∀ p ∈ oddDiv m, (eS m h p : ℝ) * Real.log p ≤
        ((padicValNat p m : ℝ) / 4 + 1 / (4 * ((p : ℝ) - 1))) * Real.log p * (h : ℝ) ^ 2 +
          ε' * Real.log p * (h : ℝ) ^ 2 := by
      intro p hp
      have hlp := Real.log_natCast_nonneg p
      have h1 := hS' p hp
      have h2 := half_sub_one_sq_le h
      have he : (eS m h p : ℝ) ≤ (1 / (4 * ((p : ℝ) - 1)) + ε') * (h : ℝ) ^ 2 +
          (padicValNat p m : ℝ) * ((h : ℝ) ^ 2 / 4) := by
        unfold eS
        push_cast
        have h1' : ((∑ l ∈ levelsV h p, AK h (p ^ l) : ℕ) : ℝ) = ∑ l ∈ levelsV h p, (AK h (p ^ l) : ℝ) := by
          push_cast; rfl
        rw [h1'] at h1
        have h2' : ((h / 2 - 1 : ℕ) : ℝ) ^ 2 ≤ (h : ℝ) ^ 2 / 4 := by exact_mod_cast h2
        have hv : (0 : ℝ) ≤ padicValNat p m := Nat.cast_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left h2' hv]
      have := mul_le_mul_of_nonneg_right he hlp
      nlinarith
    calc ∑ p ∈ oddDiv m, (eS m h p : ℝ) * Real.log p
        ≤ ∑ p ∈ oddDiv m, (((padicValNat p m : ℝ) / 4 + 1 / (4 * ((p : ℝ) - 1))) * Real.log p * (h : ℝ) ^ 2 +
          ε' * Real.log p * (h : ℝ) ^ 2) := sum_le_sum hterm
      _ = cSV m * (h : ℝ) ^ 2 + ε' * W * (h : ℝ) ^ 2 := by
          simp only [cSV, hW, sum_add_distrib, sum_mul, mul_sum]
      _ ≤ (cSV m + ε / 3) * (h : ℝ) ^ 2 := by
          have : ε' * W ≤ ε / 3 := by
            rw [hε', div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
          nlinarith [sq_nonneg (h : ℝ)]
  unfold alphaV
  nlinarith [sq_nonneg (h : ℝ)]

/-- Infinitely many even `h` with `Δ_h(a/b) ≠ 0` (Lemma P′_m along `h = 3ℓ − 1`, `ℓ` a large prime). -/
theorem nonvan_frequently_V (m : ℕ) [Fact (1 ≤ m)] (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ∃ᶠ h : ℕ in atTop, Even h ∧ (Delta m h).eval ((a : ℚ) / b) ≠ 0 := by
  rw [frequently_atTop]
  intro N
  obtain ⟨ℓ, hℓN, hℓp⟩ := Nat.exists_infinite_primes (N + b + 7 + 2 * m * (m ^ 2 + 1))
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have hℓ7 : 7 ≤ ℓ := by omega
  have hodd : Odd ℓ := hℓp.odd_of_ne_two (by omega)
  have hpos : 0 < 2 * m * (m ^ 2 + 1) := by have := (Fact.out : 1 ≤ m); positivity
  refine ⟨3 * ℓ - 1, by omega, ?_, lemmaP_m m hℓ7 (fun hd => ?_) a hb ?_⟩
  · obtain ⟨k, rfl⟩ := hodd
    exact ⟨3 * k + 1, by omega⟩
  · have := Nat.le_of_dvd hpos hd; omega
  · intro hdvd
    have hle := Nat.le_of_dvd hb hdvd
    have : ℓ ≤ ℓ ^ 2 := Nat.le_self_pow (by norm_num) ℓ
    omega

/-- The endgame inputs at `z_m`, from the stubs. -/
theorem exists_boundsV {m : ℕ} [Fact (1 ≤ m)] (hm : 2 ≤ m) (hE : m ∉ ({3, 5, 7, 9, 15} : Finset ℕ)) :
    Nonempty (MachineBoundsV m) := by
  obtain ⟨C, hC⟩ := exists_certU'
  have hM := margin_V hm hE
  set M : ℝ := alphaV m + (PhiL - Lshift m / 2) with hMdef
  obtain ⟨C', hC'⟩ := shift_lemma C m hm (δ := -M / 2) (by linarith)
  have hCL : C.Phi < PhiL := by rw [PhiL]; exact hC
  exact ⟨{
    den := denV m
    den_pos := denV_pos m
    den_int := denV_int m
    α := alphaV m
    β := C'.Phi
    margin := by linarith
    arith := log_denV_le m
    analytic := C'.analytic
    nonvan := nonvan_frequently_V m }⟩

/-- **Theorem V**, from the stubs. -/
theorem theoremV : TheoremV := by
  intro m hm hE
  have : Fact (1 ≤ m) := ⟨by omega⟩
  obtain ⟨H⟩ := exists_boundsV hm hE
  exact irrational_of_boundsV H

end V
end Chi2U
