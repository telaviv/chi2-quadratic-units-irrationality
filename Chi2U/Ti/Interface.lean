/-
# Theorem V_i: the ingredients and the assembly (PROOF_TI2)

**Theorem V_i** (`Chi2U.Ti.TheoremVi`, `Ti/Defs.lean`). The Ti₂ machine is in `Chi2U/Ti/*` (stage C2-core: `Ti/Core.lean`,
endgame `irrational_of_boundsT`); the margin is `Ti/Margin.lean` (`margin_Vi_proof`). This file states the remaining
ingredients at a trace `n ≥ 3`, each proved in its own file (stage C2), and assembles `TheoremVi`.

| ingredient | PROOF_TI2 | statement (proof file) |
|---|---|---|
| `padicNorm_Delta_odd` | §2 (PROOF_V §3.1 verbatim) | odd `p ∤ n`: `n_p ≤ eOdd h p` (Lemmas 8′, 8A′, 9′) |
| `lemmaS` | §2 (PROOF_V §3.2, `e = v_p(n)`) | odd `p ∣ n`: `n_p ≤ eSA n h p` |
| `lemma10nu` | §2 (PROOF_V §4, `ν = v₂(n) ≥ 1`) | even `n`: `n₂ ≤ n2A n h` |
| `lemma10_0` | §3 (PROOF_VODD §2) | odd `n`: `n₂ ≤ n2O h` |
| `lemmaP_n` | §4, Lemma P′_n | `Δ_{3ℓ−1}(a/b) ≠ 0` for primes `ℓ ≥ 7`, `ℓ ∤ n(n² − 4)`, `ℓ² ∤ b` |
| `analytic_T` | §2 (Theorem B′_z + shift lemma) | `n ≥ 5`: `|Δ_h(T)| ≤ exp((betaT n + δ + ε) h²)` eventually, any `δ, ε > 0` |
| `margin_Vi` | §6 | `alphaT n + betaT n < 0` on `marginOK` (`Ti/Margin`) |
-/
import Chi2U.Ti.Core
import Chi2U.Ti.Margin
import Chi2U.VOdd.Defs
import Chi2U.V.Interface
import Chi2U.Ti.Analytic
import Chi2U.Ti.Lemma10nu
import Chi2U.Ti.TenZero

namespace Chi2U
namespace Ti

open Polynomial Filter Finset

/-! ## The ingredients (stubs; each is proved as `<name>_proof` in its own file) -/

/-- **Generic odd primes** (PROOF_V §3.1 verbatim, Lemmas 8′, 8A′, 9′ and the row claim): for an odd prime `p ∤ n`,
`|coeff|_p ≤ p^{eOdd h p}`. The χ₂ version is `Chi2U.padicNorm_Delta_odd` (`Arith/OddExp`). -/
theorem padicNorm_Delta_odd (n : ℕ) [Fact (3 ≤ n)] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hpn : ¬ p ∣ n) {h : ℕ}
    (hh : Even h) (k : ℕ) : padicNorm p ((Delta n h).coeff k) ≤ (p : ℚ) ^ eOdd h p := by
  sorry

/-- **Lemma S** (PROOF_V §3.2 with `e = v_p(n)`): for an odd prime `p ∣ n`, `|coeff|_p ≤ p^{eSA n h p}`. The χ₂ version is
`Chi2U.V.lemmaS`. -/
theorem lemmaS (n : ℕ) [Fact (3 ≤ n)] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hpn : p ∣ n) {h : ℕ} (hh : Even h)
    (k : ℕ) : padicNorm p ((Delta n h).coeff k) ≤ (p : ℚ) ^ V.eSA n h p := by
  sorry

/-- **Lemma 10_ν** (PROOF_V §4) at an even trace `n` (`ν = v₂(n) ≥ 1`). The χ₂ version is `Chi2U.V.lemma10nu`. -/
theorem lemma10nu (n : ℕ) [Fact (3 ≤ n)] (hn : Even n) {h : ℕ} (hh : Even h) (h2 : 2 ≤ h) (k : ℕ) :
    padicNorm 2 ((Delta n h).coeff k) ≤ (2 : ℚ) ^ V.n2A n h :=
  lemma10nu_proof n hn hh h2 k

/-- **Lemma 10_0** (PROOF_VODD §2) at an odd trace `n` (`2` inert in `ℚ(√(n² − 4))`). The χ₂ version is
`Chi2U.VOdd.lemma10_0`. -/
theorem lemma10_0 (n : ℕ) [Fact (3 ≤ n)] (hn : Odd n) {h : ℕ} (hh : Even h) (h2 : 2 ≤ h) (k : ℕ) :
    padicNorm 2 ((Delta n h).coeff k) ≤ (2 : ℚ) ^ VOdd.n2O h :=
  lemma10_0_proof n hn hh h2 k

/-- **Lemma P′_n** (PROOF_TI2 §4). The χ₂ version is `Chi2U.V.lemmaP_m`. -/
theorem lemmaP_n (n : ℕ) [Fact (3 ≤ n)] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : 7 ≤ ℓ) (hℓn : ¬ ℓ ∣ n * (n ^ 2 - 4))
    (a : ℤ) {b : ℕ} (hb : 0 < b) (hb2 : ¬ ℓ ^ 2 ∣ b) : (Delta n (3 * ℓ - 1)).eval ((a : ℚ) / b) ≠ 0 := by
  sorry

/-- **The analytic bound** (Theorem B′ at `z = zT n` with the signed weights `χ₄(t) z^t`, from Theorem U's certificate
`exists_certU'` moved by the shift lemma; PROOF_TI2 §2, PROOF_V §5). -/
theorem analytic_T (n : ℕ) [Fact (3 ≤ n)] (h5 : 5 ≤ n) {δ : ℝ} (hδ : 0 < δ) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    Even h → |aeval (TT n) (Delta n h)| ≤ Real.exp ((betaT n + δ + ε) * (h : ℝ) ^ 2) :=
  analytic_T_proof n h5 hδ

/-- **The margin inequality** (PROOF_TI2 §6) with Lean's constant `Φ_L`. -/
theorem margin_Vi {n : ℕ} (hn : marginOK n) : alphaT n + betaT n < 0 := margin_Vi_proof hn

/-! ## Assembly (adapted from `VOdd/Interface.lean`) -/

/-- The 2-adic exponent: Lemma 10_0 for odd `n`, Lemma 10_ν for even `n`. -/
def n2T (n h : ℕ) : ℕ := if n % 2 = 1 then VOdd.n2O h else V.n2A n h

lemma padicNorm_Delta_two (n : ℕ) [Fact (3 ≤ n)] {h : ℕ} (hh : Even h) (h2 : 2 ≤ h) (k : ℕ) :
    padicNorm 2 ((Delta n h).coeff k) ≤ (2 : ℚ) ^ n2T n h := by
  unfold n2T
  split_ifs with ho
  · exact lemma10_0 n (Nat.odd_iff.mpr ho) hh h2 k
  · exact lemma10nu n (Nat.even_iff.mpr (by omega)) hh h2 k

/-- `n2T n h · log 2 ≤ (c₂ + ε) h²` eventually. -/
theorem n2T_size (n : ℕ) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    (n2T n h : ℝ) * Real.log 2 ≤ (c2T n + ε) * (h : ℝ) ^ 2 := by
  intro ε hε
  by_cases ho : n % 2 = 1
  · filter_upwards [VOdd.lemma10_0_size ε hε] with h hh
    unfold n2T c2T; rw [if_pos ho, if_pos ho]; exact hh
  · rcases Nat.even_iff.mpr (by omega : n % 2 = 0) with ⟨m, rfl⟩
    by_cases hm : m = 0
    · subst hm
      filter_upwards [V.lemma10nu_size 0 ε hε] with h hh
      have e : V.n2A (0 + 0) h = V.n2V 0 h := by unfold V.n2A V.n2V V.nuA V.nuV; simp
      have l2 : 0 < Real.log 2 := Real.log_pos one_lt_two
      have hc : V.c2V 0 ≤ c2T (0 + 0) := by
        unfold V.c2V V.nuV c2T
        rw [if_neg (by norm_num)]
        norm_num
        linarith
      unfold n2T; rw [if_neg ho, e]
      nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg (h : ℝ))]
    · filter_upwards [V.lemma10nu_size m ε hε] with h hh
      have h2m : m + m = 2 * m := by ring
      unfold n2T c2T
      rw [if_neg ho, if_neg ho, h2m, V.n2A_two_mul hm]
      have hv : (padicValNat 2 (2 * m) : ℝ) = (V.nuV m : ℝ) := by
        unfold V.nuV; rw [padicValNat.mul two_ne_zero hm, padicValNat_self]
      rw [hv]; exact hh

/-- The proved denominator for even `h ≥ 2`. -/
noncomputable def denT0 (n h : ℕ) : ℚ :=
  (2 : ℚ) ^ n2T n h * (∏ p ∈ V.oddGen n h, (p : ℚ) ^ eOdd h p) * ∏ p ∈ V.oddDiv n, (p : ℚ) ^ V.eSA n h p

lemma denT0_pos (n h : ℕ) : 0 < denT0 n h := by
  unfold denT0
  refine mul_pos (mul_pos (by positivity) (prod_pos (fun p hp => ?_))) (prod_pos (fun p hp => ?_))
  · have := (V.prime_of_mem_oddGen hp).pos; positivity
  · have := (V.prime_of_mem_oddDiv hp).pos; positivity

/-- `denT0 n h · Δ_h ∈ ℤ[X]` for even `h ≥ 2`. -/
theorem denT0_int (n : ℕ) [Fact (3 ≤ n)] {h : ℕ} (hh : Even h) (h2 : 2 ≤ h) (k : ℕ) :
    ∃ z : ℤ, denT0 n h * (Delta n h).coeff k = z := by
  refine exists_int_of_padicNorm_le_U _ (fun p hp => ?_)
  have := Fact.mk hp
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  unfold denT0
  rw [padicNorm.mul, padicNorm.mul, padicNorm.mul, padicNorm_pow_U, padicNorm_two_U,
    V.padicNorm_prod_primes p _ (fun q hq => V.prime_of_mem_oddGen hq),
    V.padicNorm_prod_primes p _ (fun q hq => V.prime_of_mem_oddDiv hq)]
  have hc0 := padicNorm.nonneg (p := p) ((Delta n h).coeff k)
  by_cases h2p : p = 2
  · subst h2p
    have h1 : (2 : ℕ) ∉ V.oddGen n h := fun hm => (mem_filter.mp (mem_filter.mp hm).1).2.2 rfl
    have h3 : (2 : ℕ) ∉ V.oddDiv n := fun hm => (mem_filter.mp hm).2 rfl
    rw [if_pos rfl, if_neg h1, if_neg h3, mul_one, mul_one]
    exact V.inv_pow_mul_le_one hp0 hc0 (by exact_mod_cast padicNorm_Delta_two n hh h2 k)
  · rw [if_neg (Ne.symm h2p), one_pow, one_mul]
    by_cases hpa : p ∣ n
    · have hD : p ∈ V.oddDiv n := mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpa, by
        have := (Fact.out : 3 ≤ n); omega⟩, h2p⟩
      have hG : p ∉ V.oddGen n h := fun hm => (mem_filter.mp hm).2 hpa
      rw [if_neg hG, if_pos hD, one_mul]
      exact V.inv_pow_mul_le_one hp0 hc0 (lemmaS n h2p hpa hh k)
    · have hD : p ∉ V.oddDiv n := fun hm => hpa (Nat.dvd_of_mem_primeFactors (mem_filter.mp hm).1)
      rw [if_neg hD, mul_one]
      have hc := padicNorm_Delta_odd n (p := p) h2p hpa hh k
      split_ifs with hG
      · exact V.inv_pow_mul_le_one hp0 hc0 hc
      · have hph : h < p := by
          by_contra hc'
          exact hG (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega), hp, h2p⟩, hpa⟩)
        rw [eOdd_eq_zero_asm hph, pow_zero] at hc
        simpa using hc

/-- The denominators used by the endgame (odd `h` and `h = 0` are not used). -/
noncomputable def denT (n : ℕ) [Fact (3 ≤ n)] (h : ℕ) : ℚ :=
  if Even h ∧ 2 ≤ h then denT0 n h else Classical.choose (exists_den (Delta n h))

lemma denT_pos (n : ℕ) [Fact (3 ≤ n)] (h : ℕ) : 0 < denT n h := by
  unfold denT
  split_ifs
  · exact denT0_pos n h
  · exact (Classical.choose_spec (exists_den (Delta n h))).1

lemma denT_int (n : ℕ) [Fact (3 ≤ n)] (h k : ℕ) : ∃ z : ℤ, denT n h * (Delta n h).coeff k = z := by
  unfold denT
  split_ifs with hh
  · exact denT0_int n hh.1 hh.2 k
  · exact (Classical.choose_spec (exists_den (Delta n h))).2 k

/-- **The arithmetic bound**: `log den h ≤ (alphaT n + ε) h²` for even `h`, eventually. -/
theorem log_denT_le (n : ℕ) [Fact (3 ≤ n)] : ∀ ε > 0, ∀ᶠ h : ℕ in atTop, Even h →
    Real.log (denT n h) ≤ (alphaT n + ε) * (h : ℝ) ^ 2 := by
  intro ε hε
  set W : ℝ := ∑ p ∈ V.oddDiv n, Real.log p with hW
  have hW0 : 0 ≤ W := sum_nonneg (fun p hp => Real.log_natCast_nonneg p)
  set ε' : ℝ := ε / (3 * (W + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hS := (eventually_all_finset (V.oddDiv n)).2
    (fun p hp => V.AK_levels_size (V.prime_of_mem_oddDiv hp) (mem_filter.mp hp).2 ε' hε'0)
  filter_upwards [theoremA (ε / 3) (by positivity), n2T_size n (ε / 3) (by positivity), hS,
    eventually_ge_atTop 2] with h hA h2 hS' hh2 hev
  have hd : denT n h = denT0 n h := by unfold denT; rw [if_pos ⟨hev, hh2⟩]
  rw [hd]
  have hne1 : ∀ p ∈ V.oddGen n h, ((p : ℝ)) ^ eOdd h p ≠ 0 := fun p hp =>
    pow_ne_zero _ (by exact_mod_cast (V.prime_of_mem_oddGen hp).ne_zero)
  have hne2 : ∀ p ∈ V.oddDiv n, ((p : ℝ)) ^ V.eSA n h p ≠ 0 := fun p hp =>
    pow_ne_zero _ (by exact_mod_cast (V.prime_of_mem_oddDiv hp).ne_zero)
  have hlog : Real.log ((denT0 n h : ℚ) : ℝ) = (n2T n h : ℝ) * Real.log 2 +
      ∑ p ∈ V.oddGen n h, (eOdd h p : ℝ) * Real.log p + ∑ p ∈ V.oddDiv n, (V.eSA n h p : ℝ) * Real.log p := by
    unfold denT0
    push_cast
    rw [Real.log_mul (mul_ne_zero (by positivity) (prod_ne_zero_iff.mpr hne1)) (prod_ne_zero_iff.mpr hne2),
      Real.log_mul (by positivity) (prod_ne_zero_iff.mpr hne1), Real.log_pow, Real.log_prod hne1,
      Real.log_prod hne2]
    simp only [Real.log_pow]
  rw [hlog]
  have hG : ∑ p ∈ V.oddGen n h, (eOdd h p : ℝ) * Real.log p ≤ (4 / 3 + ε / 3) * (h : ℝ) ^ 2 :=
    le_trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p))) hA
  have hSp : ∑ p ∈ V.oddDiv n, (V.eSA n h p : ℝ) * Real.log p ≤ (V.cSV n + ε / 3) * (h : ℝ) ^ 2 := by
    have hterm : ∀ p ∈ V.oddDiv n, (V.eSA n h p : ℝ) * Real.log p ≤
        ((padicValNat p n : ℝ) / 4 + 1 / (4 * ((p : ℝ) - 1))) * Real.log p * (h : ℝ) ^ 2 +
          ε' * Real.log p * (h : ℝ) ^ 2 := by
      intro p hp
      have hlp := Real.log_natCast_nonneg p
      have h1 := hS' p hp
      have h2 := V.half_sub_one_sq_le h
      have he : (V.eSA n h p : ℝ) ≤ (1 / (4 * ((p : ℝ) - 1)) + ε') * (h : ℝ) ^ 2 +
          (padicValNat p n : ℝ) * ((h : ℝ) ^ 2 / 4) := by
        unfold V.eSA
        push_cast
        have h1' : ((∑ l ∈ V.levelsV h p, AK h (p ^ l) : ℕ) : ℝ) = ∑ l ∈ V.levelsV h p, (AK h (p ^ l) : ℝ) := by
          push_cast; rfl
        rw [h1'] at h1
        have h2' : ((h / 2 - 1 : ℕ) : ℝ) ^ 2 ≤ (h : ℝ) ^ 2 / 4 := by exact_mod_cast h2
        have hv : (0 : ℝ) ≤ padicValNat p n := Nat.cast_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left h2' hv]
      have := mul_le_mul_of_nonneg_right he hlp
      nlinarith
    calc ∑ p ∈ V.oddDiv n, (V.eSA n h p : ℝ) * Real.log p
        ≤ ∑ p ∈ V.oddDiv n, (((padicValNat p n : ℝ) / 4 + 1 / (4 * ((p : ℝ) - 1))) * Real.log p * (h : ℝ) ^ 2 +
          ε' * Real.log p * (h : ℝ) ^ 2) := sum_le_sum hterm
      _ = V.cSV n * (h : ℝ) ^ 2 + ε' * W * (h : ℝ) ^ 2 := by
          simp only [V.cSV, hW, sum_add_distrib, sum_mul, mul_sum]
      _ ≤ (V.cSV n + ε / 3) * (h : ℝ) ^ 2 := by
          have : ε' * W ≤ ε / 3 := by
            rw [hε', div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
          nlinarith [sq_nonneg (h : ℝ)]
  unfold alphaT
  nlinarith [sq_nonneg (h : ℝ)]

/-- Infinitely many even `h` with `Δ_h(x/b) ≠ 0` (Lemma P′_n along `h = 3ℓ − 1`). -/
theorem nonvan_frequently_T (n : ℕ) [Fact (3 ≤ n)] (x : ℤ) (b : ℕ) (hb : 0 < b) :
    ∃ᶠ h : ℕ in atTop, Even h ∧ (Delta n h).eval ((x : ℚ) / b) ≠ 0 := by
  rw [frequently_atTop]
  intro N
  obtain ⟨ℓ, hℓN, hℓp⟩ := Nat.exists_infinite_primes (N + b + 7 + n * (n ^ 2 - 4))
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have hℓ7 : 7 ≤ ℓ := by omega
  have hodd : Odd ℓ := hℓp.odd_of_ne_two (by omega)
  have hn3 := (Fact.out : 3 ≤ n)
  have hsq : 4 < n ^ 2 := by nlinarith
  have hpos : 0 < n * (n ^ 2 - 4) := Nat.mul_pos (by omega) (by omega)
  refine ⟨3 * ℓ - 1, by omega, ?_, lemmaP_n n hℓ7 (fun hd => ?_) x hb ?_⟩
  · obtain ⟨k, rfl⟩ := hodd
    exact ⟨3 * k + 1, by omega⟩
  · have := Nat.le_of_dvd hpos hd; omega
  · intro hdvd
    have hle := Nat.le_of_dvd hb hdvd
    have : ℓ ≤ ℓ ^ 2 := Nat.le_self_pow (by norm_num) ℓ
    omega

/-- The endgame inputs at `n` on `marginOK`. -/
theorem exists_boundsT {n : ℕ} [Fact (3 ≤ n)] (hn : marginOK n) : Nonempty (MachineBoundsT n) := by
  have hM := margin_Vi hn
  set δ : ℝ := -(alphaT n + betaT n) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  exact ⟨{
    den := denT n
    den_pos := denT_pos n
    den_int := denT_int n
    α := alphaT n
    β := betaT n + δ
    margin := by rw [hδ]; linarith
    arith := log_denT_le n
    analytic := analytic_T n hn.1 hδ0
    nonvan := nonvan_frequently_T n }⟩

/-- `Ti₂(z_n) ∉ ℚ` on `marginOK`. -/
theorem irrational_Ti2_zT {n : ℕ} (hn : marginOK n) : Irrational (Ti2 (zT n)) := by
  have : Fact (3 ≤ n) := ⟨by have := hn.1; omega⟩
  obtain ⟨H⟩ := exists_boundsT hn
  exact irrational_of_boundsT H

/-- **Theorem V_i.** -/
theorem theoremVi : TheoremVi := by
  refine ⟨fun m hm hE => ?_, fun n ho h71 hE => ?_⟩
  · have hok : marginOK (2 * m) := by
      refine ⟨by omega, ?_, by omega, ?_⟩
      · intro hmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem hE
        omega
      · intro hmem
        simp only [EOddI, Finset.mem_insert, Finset.mem_singleton] at hmem
        omega
    have := irrational_Ti2_zT hok
    rwa [zT_two_mul] at this
  · have hok : marginOK n := by
      refine ⟨by omega, ?_, ?_, hE⟩
      · intro hmem
        have := Nat.odd_iff.mp ho
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        omega
      · intro ⟨_, h69⟩; omega
    have := irrational_Ti2_zT hok
    rwa [zT_eq_half] at this

end Ti
end Chi2U
