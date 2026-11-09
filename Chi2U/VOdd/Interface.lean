/-
# Theorem V_odd: assembly (PROOF_VODD, `../handoff/log2log3/pilot_za/PROOF_VODD.md`)

**Theorem V_odd.** For every odd `a ≥ 5`, `a ∉ EOdd` (39 values, largest 165): `χ₂((√(a² + 4) − a)/2) ∉ ℚ`
(`TheoremVOdd`).

The machine at the trace `az = a` (stage C0) and the trace-generic ingredients of Theorem V are reused:
`padicNorm_Delta_odd` (odd `p ∤ a`, Lemmas 8′, 8A′, 9′), `theoremA`, `V.lemmaS` (odd `p ∣ a`), `V.AK_levels_size`,
`V.shift_lemma` (`a ≥ 4`), `V.lemmaP_m` (`ℓ ∤ a(a² + 4)`), Theorem B′ (`DualCertU.analytic`). New ingredients:

| ingredient | PROOF_VODD | statement (proof) |
|---|---|---|
| `lemma10_0` | §2, Lemma 10_0 | odd `a`: `n₂ ≤ h²/2 + h` |
| `lemma10_0_size` | §2 ("consequently") | **proved** in `VOdd/Defs` |
| `exists_certOdd` | §0, §3 (certificates) | `a ∈ certA` (11 traces): a certificate with `Φ ≤ PhiC a` |
| `margin_VOdd` | §0, §4 | `alphaO a + betaO a < 0` for odd `a ≥ 5`, `a ∉ EOdd` |

Constants: `Φ_L = −1.3538792` (Theorem U's Lean certificate) for the shift lemma, so `a = 123` needs a direct certificate
too (PROOF_VODD's ten plus 123); `c₂ = ½ log 2`; the special primes as in PROOF_VODD (`e/4 + 1/(4(p − 1))`).
-/
import Chi2U.VOdd.Defs
import Chi2U.VOdd.TenZero
import Chi2U.VOdd.Margin
import Chi2U.VOdd.CertOdd
import Chi2U.V.Interface

namespace Chi2U
namespace VOdd

open Polynomial Filter Finset V

/-! ## The new ingredients -/

/-- **Lemma 10_0** (PROOF_VODD §2): at odd `a` (`2` inert), `n₂(Δ_h) ≤ h²/2 + h` for even `h ≥ 2`. -/
theorem lemma10_0 (az : ℕ) [Fact (1 ≤ az)] (ha : Odd az) {h : ℕ} (hh : Even h) (h2 : 2 ≤ h) (k : ℕ) :
    padicNorm 2 ((Delta az h).coeff k) ≤ (2 : ℚ) ^ n2O h :=
  lemma10_0_proof az ha hh h2 k

/-- **Direct certificates** (PROOF_VODD §0, §3) at the 11 traces of `certA`, in the format of `DualCertU`. -/
theorem exists_certOdd {a : ℕ} [Fact (1 ≤ a)] (ha : a ∈ certA) : ∃ C : DualCertU a, C.Phi ≤ PhiC a :=
  exists_certOdd_proof ha

/-- **The margin inequality** (PROOF_VODD §0, §4) with Lean's constants. -/
theorem margin_VOdd {a : ℕ} (ho : Odd a) (h5 : 5 ≤ a) (hE : a ∉ EOdd) : alphaO a + betaO a < 0 :=
  margin_VOdd_proof ho h5 hE

/-! ## Assembly -/

/-- The proved denominator at odd `a` for even `h ≥ 2`. -/
noncomputable def denO0 (a h : ℕ) : ℚ :=
  (2 : ℚ) ^ n2O h * (∏ p ∈ oddGen a h, (p : ℚ) ^ eOdd h p) * ∏ p ∈ oddDiv a, (p : ℚ) ^ eSA a h p

lemma denO0_pos (a h : ℕ) : 0 < denO0 a h := by
  unfold denO0
  refine mul_pos (mul_pos (by positivity) (prod_pos (fun p hp => ?_))) (prod_pos (fun p hp => ?_))
  · have := (prime_of_mem_oddGen hp).pos; positivity
  · have := (prime_of_mem_oddDiv hp).pos; positivity

/-- `denO0 a h · Δ_h ∈ ℤ[X]` for odd `a` and even `h ≥ 2`. -/
theorem denO0_int (a : ℕ) [Fact (1 ≤ a)] (ho : Odd a) {h : ℕ} (hh : Even h) (h2 : 2 ≤ h) (k : ℕ) :
    ∃ z : ℤ, denO0 a h * (Delta a h).coeff k = z := by
  refine exists_int_of_padicNorm_le_U _ (fun p hp => ?_)
  have := Fact.mk hp
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  unfold denO0
  rw [padicNorm.mul, padicNorm.mul, padicNorm.mul, padicNorm_pow_U, padicNorm_two_U,
    padicNorm_prod_primes p _ (fun q hq => prime_of_mem_oddGen hq),
    padicNorm_prod_primes p _ (fun q hq => prime_of_mem_oddDiv hq)]
  have hc0 := padicNorm.nonneg (p := p) ((Delta a h).coeff k)
  by_cases h2p : p = 2
  · subst h2p
    have h1 : (2 : ℕ) ∉ oddGen a h := fun hm => (mem_filter.mp (mem_filter.mp hm).1).2.2 rfl
    have h3 : (2 : ℕ) ∉ oddDiv a := fun hm => (mem_filter.mp hm).2 rfl
    rw [if_pos rfl, if_neg h1, if_neg h3, mul_one, mul_one]
    exact inv_pow_mul_le_one hp0 hc0 (by exact_mod_cast lemma10_0 a ho hh h2 k)
  · rw [if_neg (Ne.symm h2p), one_pow, one_mul]
    by_cases hpa : p ∣ a
    · have hD : p ∈ oddDiv a := mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpa, by
        have := (Fact.out : 1 ≤ a); omega⟩, h2p⟩
      have hG : p ∉ oddGen a h := fun hm => (mem_filter.mp hm).2 hpa
      rw [if_neg hG, if_pos hD, one_mul]
      exact inv_pow_mul_le_one hp0 hc0 (lemmaS a h2p hpa hh k)
    · have hD : p ∉ oddDiv a := fun hm => hpa (Nat.dvd_of_mem_primeFactors (mem_filter.mp hm).1)
      rw [if_neg hD, mul_one]
      have hc := padicNorm_Delta_odd (az := a) (p := p) h2p hpa hh k
      split_ifs with hG
      · exact inv_pow_mul_le_one hp0 hc0 hc
      · have hph : h < p := by
          by_contra hc'
          exact hG (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega), hp, h2p⟩, hpa⟩)
        rw [eOdd_eq_zero_asm hph, pow_zero] at hc
        simpa using hc

/-- The denominators used by the endgame at odd `a` (odd `h` and `h = 0` are not used). -/
noncomputable def denO (a : ℕ) [Fact (1 ≤ a)] (h : ℕ) : ℚ :=
  if Even h ∧ 2 ≤ h then denO0 a h else Classical.choose (exists_den (Delta a h))

lemma denO_pos (a : ℕ) [Fact (1 ≤ a)] (h : ℕ) : 0 < denO a h := by
  unfold denO
  split_ifs
  · exact denO0_pos a h
  · exact (Classical.choose_spec (exists_den (Delta a h))).1

lemma denO_int (a : ℕ) [Fact (1 ≤ a)] (ho : Odd a) (h k : ℕ) : ∃ z : ℤ, denO a h * (Delta a h).coeff k = z := by
  unfold denO
  split_ifs with hh
  · exact denO0_int a ho hh.1 hh.2 k
  · exact (Classical.choose_spec (exists_den (Delta a h))).2 k

/-- **The arithmetic bound** at odd `a`: `log den h ≤ (alphaO a + ε) h²` for even `h`, eventually. -/
theorem log_denO_le (a : ℕ) [Fact (1 ≤ a)] : ∀ ε > 0, ∀ᶠ h : ℕ in atTop, Even h →
    Real.log (denO a h) ≤ (alphaO a + ε) * (h : ℝ) ^ 2 := by
  intro ε hε
  set W : ℝ := ∑ p ∈ oddDiv a, Real.log p with hW
  have hW0 : 0 ≤ W := sum_nonneg (fun p hp => Real.log_natCast_nonneg p)
  set ε' : ℝ := ε / (3 * (W + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hS := (eventually_all_finset (oddDiv a)).2
    (fun p hp => AK_levels_size (prime_of_mem_oddDiv hp) (mem_filter.mp hp).2 ε' hε'0)
  filter_upwards [theoremA (ε / 3) (by positivity), lemma10_0_size (ε / 3) (by positivity), hS,
    eventually_ge_atTop 2] with h hA h2 hS' hh2 hev
  have hd : denO a h = denO0 a h := by unfold denO; rw [if_pos ⟨hev, hh2⟩]
  rw [hd]
  have hne1 : ∀ p ∈ oddGen a h, ((p : ℝ)) ^ eOdd h p ≠ 0 := fun p hp =>
    pow_ne_zero _ (by exact_mod_cast (prime_of_mem_oddGen hp).ne_zero)
  have hne2 : ∀ p ∈ oddDiv a, ((p : ℝ)) ^ eSA a h p ≠ 0 := fun p hp =>
    pow_ne_zero _ (by exact_mod_cast (prime_of_mem_oddDiv hp).ne_zero)
  have hlog : Real.log ((denO0 a h : ℚ) : ℝ) = (n2O h : ℝ) * Real.log 2 +
      ∑ p ∈ oddGen a h, (eOdd h p : ℝ) * Real.log p + ∑ p ∈ oddDiv a, (eSA a h p : ℝ) * Real.log p := by
    unfold denO0
    push_cast
    rw [Real.log_mul (mul_ne_zero (by positivity) (prod_ne_zero_iff.mpr hne1)) (prod_ne_zero_iff.mpr hne2),
      Real.log_mul (by positivity) (prod_ne_zero_iff.mpr hne1), Real.log_pow, Real.log_prod hne1,
      Real.log_prod hne2]
    simp only [Real.log_pow]
  rw [hlog]
  have hG : ∑ p ∈ oddGen a h, (eOdd h p : ℝ) * Real.log p ≤ (4 / 3 + ε / 3) * (h : ℝ) ^ 2 :=
    le_trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p))) hA
  have hSp : ∑ p ∈ oddDiv a, (eSA a h p : ℝ) * Real.log p ≤ (cSV a + ε / 3) * (h : ℝ) ^ 2 := by
    have hterm : ∀ p ∈ oddDiv a, (eSA a h p : ℝ) * Real.log p ≤
        ((padicValNat p a : ℝ) / 4 + 1 / (4 * ((p : ℝ) - 1))) * Real.log p * (h : ℝ) ^ 2 +
          ε' * Real.log p * (h : ℝ) ^ 2 := by
      intro p hp
      have hlp := Real.log_natCast_nonneg p
      have h1 := hS' p hp
      have h2 := half_sub_one_sq_le h
      have he : (eSA a h p : ℝ) ≤ (1 / (4 * ((p : ℝ) - 1)) + ε') * (h : ℝ) ^ 2 +
          (padicValNat p a : ℝ) * ((h : ℝ) ^ 2 / 4) := by
        unfold eSA
        push_cast
        have h1' : ((∑ l ∈ levelsV h p, AK h (p ^ l) : ℕ) : ℝ) = ∑ l ∈ levelsV h p, (AK h (p ^ l) : ℝ) := by
          push_cast; rfl
        rw [h1'] at h1
        have h2' : ((h / 2 - 1 : ℕ) : ℝ) ^ 2 ≤ (h : ℝ) ^ 2 / 4 := by exact_mod_cast h2
        have hv : (0 : ℝ) ≤ padicValNat p a := Nat.cast_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left h2' hv]
      have := mul_le_mul_of_nonneg_right he hlp
      nlinarith
    calc ∑ p ∈ oddDiv a, (eSA a h p : ℝ) * Real.log p
        ≤ ∑ p ∈ oddDiv a, (((padicValNat p a : ℝ) / 4 + 1 / (4 * ((p : ℝ) - 1))) * Real.log p * (h : ℝ) ^ 2 +
          ε' * Real.log p * (h : ℝ) ^ 2) := sum_le_sum hterm
      _ = cSV a * (h : ℝ) ^ 2 + ε' * W * (h : ℝ) ^ 2 := by
          simp only [cSV, hW, sum_add_distrib, sum_mul, mul_sum]
      _ ≤ (cSV a + ε / 3) * (h : ℝ) ^ 2 := by
          have : ε' * W ≤ ε / 3 := by
            rw [hε', div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
          nlinarith [sq_nonneg (h : ℝ)]
  unfold alphaO
  nlinarith [sq_nonneg (h : ℝ)]

/-- Infinitely many even `h` with `Δ_h(x/b) ≠ 0` at the trace `a` (Lemma P′ along `h = 3ℓ − 1`). -/
theorem nonvan_frequently_O (a : ℕ) [Fact (1 ≤ a)] (x : ℤ) (b : ℕ) (hb : 0 < b) :
    ∃ᶠ h : ℕ in atTop, Even h ∧ (Delta a h).eval ((x : ℚ) / b) ≠ 0 := by
  rw [frequently_atTop]
  intro N
  obtain ⟨ℓ, hℓN, hℓp⟩ := Nat.exists_infinite_primes (N + b + 7 + a * (a ^ 2 + 4))
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have hℓ7 : 7 ≤ ℓ := by omega
  have hodd : Odd ℓ := hℓp.odd_of_ne_two (by omega)
  have hpos : 0 < a * (a ^ 2 + 4) := by have := (Fact.out : 1 ≤ a); positivity
  refine ⟨3 * ℓ - 1, by omega, ?_, lemmaP_m a hℓ7 (fun hd => ?_) x hb ?_⟩
  · obtain ⟨k, rfl⟩ := hodd
    exact ⟨3 * k + 1, by omega⟩
  · have := Nat.le_of_dvd hpos hd; omega
  · intro hdvd
    have hle := Nat.le_of_dvd hb hdvd
    have : ℓ ≤ ℓ ^ 2 := Nat.le_self_pow (by norm_num) ℓ
    omega

/-- An analytic certificate at `a` with `Φ < betaO a + δ` (direct, or shifted from Theorem U's). -/
theorem exists_cert_beta {a : ℕ} [Fact (1 ≤ a)] (h4 : 4 ≤ a) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : DualCertU a, C.Phi < betaO a + δ := by
  unfold betaO
  split_ifs with hc
  · obtain ⟨C, hC⟩ := exists_certOdd hc
    exact ⟨C, by linarith⟩
  · obtain ⟨C, hC⟩ := exists_certU'
    obtain ⟨C', hC'⟩ := shift_lemma C a h4 (δ := δ / 2) (by linarith)
    have hCL : C.Phi < PhiL := by rw [PhiL]; exact hC
    exact ⟨C', by linarith⟩

/-- The endgame inputs at odd `a`. -/
theorem exists_boundsO {a : ℕ} [Fact (1 ≤ a)] (ho : Odd a) (h5 : 5 ≤ a) (hE : a ∉ EOdd) :
    Nonempty (MachineBounds a) := by
  have hM := margin_VOdd ho h5 hE
  obtain ⟨C, hC⟩ := exists_cert_beta (a := a) (by omega) (δ := -(alphaO a + betaO a) / 2) (by linarith)
  exact ⟨{
    den := denO a
    den_pos := denO_pos a
    den_int := denO_int a ho
    α := alphaO a
    β := C.Phi
    margin := by linarith
    arith := log_denO_le a
    analytic := C.analytic
    nonvan := nonvan_frequently_O a }⟩

/-- **Theorem V_odd.** -/
theorem theoremVOdd : TheoremVOdd := by
  intro a ho h5 hE
  have : Fact (1 ≤ a) := ⟨by omega⟩
  obtain ⟨H⟩ := exists_boundsO ho h5 hE
  have := irrational_of_bounds H
  unfold TU at this
  rwa [zU_eq_half] at this

end VOdd
end Chi2U
