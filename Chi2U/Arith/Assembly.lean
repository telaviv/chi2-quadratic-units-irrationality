/-
# Assembly of the arithmetic bound: the denominators `den h`

* `denU h = 2^{e2 h} · Π_{p odd ≤ h} p^{eOdd h p}` for even `h`; `denU h · Δ_h ∈ ℤ[X]` (`denU_int`, from
  `padicNorm_Delta_odd`, `padicNorm_Delta_two` and the fact that a rational with `|x|_p ≤ 1` for all `p` is an
  integer);
* `denAll h`: `denU h` for even `h`, any positive common denominator (`exists_den`) for odd `h` (odd `h` are not used
  by the endgame);
* `log_denAll_le`: `log den h ≤ (4/3 + ε) h²` for even `h` eventually (Theorem A′ and `e2 h = O(h log h)`).

Proofs: `padicNorm_prod_oddPrimes` computes `|Π_{q odd ≤ h} q^{eOdd h q}|_p = p^{−eOdd h p}` for odd `p` (also for
`p > h`, where `eOdd h p = 0`), and `|2^{e2}|_2 = 2^{−e2}`; `exists_int_of_padicNorm_le_U` is lean_chi2's
`exists_int_of_padicNorm_le` (`Arith/Special.lean`). For the size, `log denU = e2 log 2 + Σ eOdd log p`, and
`e2 log 2 ≤ h log h + 3h ≤ 30h + 6h log h = o(h²)` (`eventually_rem_le_U`, from lean_chi2's `Arith/Assembly.lean`).
-/
import Chi2U.Arith.OddExp
import Chi2U.Arith.TwoAdic
import Chi2U.Arith.PrimeSums

namespace Chi2U

open Polynomial Finset Filter

/-- Every rational polynomial has a positive common denominator. -/
lemma exists_den (P : ℚ[X]) : ∃ d : ℚ, 0 < d ∧ ∀ k, ∃ z : ℤ, d * P.coeff k = z := by
  refine ⟨∏ k ∈ P.support, ((P.coeff k).den : ℚ), Finset.prod_pos (fun k _ => by exact_mod_cast (P.coeff k).pos),
    fun k => ?_⟩
  by_cases hk : k ∈ P.support
  · refine ⟨(∏ j ∈ P.support.erase k, ((P.coeff j).den : ℤ)) * (P.coeff k).num, ?_⟩
    rw [← Finset.mul_prod_erase _ _ hk]
    push_cast
    rw [mul_comm ((P.coeff k).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
  · refine ⟨0, ?_⟩
    rw [Polynomial.notMem_support_iff.mp hk]
    simp

/-- The proved denominator for even `h`. -/
noncomputable def denU (h : ℕ) : ℚ := (2 : ℚ) ^ e2 h * ∏ p ∈ oddPrimes h, (p : ℚ) ^ eOdd h p

lemma denU_pos (h : ℕ) : 0 < denU h := by
  unfold denU
  refine mul_pos (by positivity) (Finset.prod_pos (fun p hp => ?_))
  have := (Finset.mem_filter.mp hp).2.1.pos
  positivity

/-! ### `p`-adic norms of the denominator -/

lemma padicNorm_prod_U (p : ℕ) [Fact p.Prime] {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    padicNorm p (∏ i ∈ s, f i) = ∏ i ∈ s, padicNorm p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [prod_insert ha, prod_insert ha, padicNorm.mul, ih]

lemma padicNorm_pow_U (p : ℕ) [Fact p.Prime] (x : ℚ) (n : ℕ) :
    padicNorm p (x ^ n) = padicNorm p x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, padicNorm.mul, ih, pow_succ]

lemma padicNorm_prime_nat_U {p p' : ℕ} [Fact p.Prime] (hp' : p'.Prime) :
    padicNorm p (p' : ℚ) = if p' = p then (p : ℚ)⁻¹ else 1 := by
  split_ifs with he
  · subst he; exact padicNorm.padicNorm_p_of_prime
  · rw [padicNorm.nat_eq_one_iff]
    intro hd
    exact he ((Nat.prime_dvd_prime_iff_eq (Fact.out) hp').mp hd).symm

lemma padicNorm_two_U (p : ℕ) [Fact p.Prime] :
    padicNorm p (2 : ℚ) = if 2 = p then (p : ℚ)⁻¹ else 1 := by
  have := padicNorm_prime_nat_U (p := p) Nat.prime_two
  exact_mod_cast this

/-- Primes `p > h` do not occur. -/
lemma eOdd_eq_zero_asm {h p : ℕ} (hp : h < p) : eOdd h p = 0 := by
  unfold eOdd
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

lemma padicNorm_prod_oddPrimes (h p : ℕ) [Fact p.Prime] :
    padicNorm p (∏ q ∈ oddPrimes h, (q : ℚ) ^ eOdd h q) =
      if p = 2 then 1 else ((p : ℚ)⁻¹) ^ eOdd h p := by
  rw [padicNorm_prod_U]
  rw [prod_congr rfl (fun q hq => by
    rw [padicNorm_pow_U, padicNorm_prime_nat_U (mem_filter.mp hq).2.1])]
  rw [prod_congr rfl (fun q _ => (show (if q = p then (p : ℚ)⁻¹ else 1) ^ eOdd h q =
      if q = p then ((p : ℚ)⁻¹) ^ eOdd h p else 1 by split_ifs with he <;> simp [he]))]
  rw [prod_ite_eq']
  split_ifs with hS h2 h2
  · exact absurd h2 (mem_filter.mp hS).2.2
  · rfl
  · rfl
  · have : h < p := by
      by_contra hc
      exact hS (mem_filter.mpr ⟨mem_range.mpr (by omega), Fact.out, h2⟩)
    rw [eOdd_eq_zero_asm this, pow_zero]

/-- A rational with `|x|_p ≤ 1` for every prime `p` is an integer (lean_chi2, `exists_int_of_padicNorm_le`). -/
lemma exists_int_of_padicNorm_le_U (x : ℚ) (hx : ∀ p : ℕ, p.Prime → padicNorm p x ≤ 1) :
    ∃ z : ℤ, x = z := by
  refine ⟨x.num, ?_⟩
  by_contra hne
  have hden : x.den ≠ 1 := fun h1 => hne (Rat.coe_int_num_of_den_eq_one h1).symm
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hden
  have := Fact.mk hp
  have hnum : ¬ (p : ℤ) ∣ x.num := fun hn => by
    have h1 : p ∣ x.num.natAbs := Int.ofNat_dvd_left.mp hn
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 x.reduced) hpd)
  have h1 : padicNorm p (x.num : ℚ) = 1 := (padicNorm.int_eq_one_iff _).mpr hnum
  have h2 : padicNorm p (x.den : ℚ) < 1 := (padicNorm.nat_lt_one_iff _).mpr hpd
  have h3 : 0 < padicNorm p (x.den : ℚ) := lt_of_le_of_ne (padicNorm.nonneg _) (fun h0 => by
    have := padicNorm.zero_of_padicNorm_eq_zero h0.symm
    exact x.den_nz (by exact_mod_cast this))
  have := hx p hp
  rw [← Rat.num_div_den x, padicNorm.div, h1, div_le_one h3] at this
  linarith

/-- `denU h · Δ_h ∈ ℤ[X]` for even `h`. -/
theorem denU_int {h : ℕ} (hh : Even h) (k : ℕ) : ∃ z : ℤ, denU h * (Delta 4 h).coeff k = z := by
  refine exists_int_of_padicNorm_le_U _ (fun p hp => ?_)
  have := Fact.mk hp
  unfold denU
  rw [padicNorm.mul, padicNorm.mul, padicNorm_pow_U, padicNorm_two_U, padicNorm_prod_oddPrimes]
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  by_cases h2 : p = 2
  · rw [ite_eq_left h2.symm, ite_eq_left h2, mul_one]
    have hc := padicNorm_Delta_two hh k
    have e : (2 : ℚ) = (p : ℚ) := by rw [h2]; norm_num
    rw [e] at hc
    subst h2
    calc (((2 : ℕ) : ℚ)⁻¹) ^ e2 h * padicNorm 2 ((Delta 4 h).coeff k)
        ≤ (((2 : ℕ) : ℚ)⁻¹) ^ e2 h * ((2 : ℕ) : ℚ) ^ e2 h := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = 1 := by rw [inv_pow]; field_simp
  · rw [ite_eq_right (Ne.symm h2), ite_eq_right h2, one_pow, one_mul]
    have hc := padicNorm_Delta_odd (p := p) h2 (not_dvd_four_of_ne h2) hh k
    calc ((p : ℚ)⁻¹) ^ eOdd h p * padicNorm p ((Delta 4 h).coeff k)
        ≤ ((p : ℚ)⁻¹) ^ eOdd h p * (p : ℚ) ^ eOdd h p := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = 1 := by rw [inv_pow]; field_simp

/-- The denominators used by the endgame. -/
noncomputable def denAll (h : ℕ) : ℚ :=
  if Even h then denU h else Classical.choose (exists_den (Delta 4 h))

lemma denAll_pos (h : ℕ) : 0 < denAll h := by
  unfold denAll
  split_ifs
  · exact denU_pos h
  · exact (Classical.choose_spec (exists_den (Delta 4 h))).1

lemma denAll_int (h k : ℕ) : ∃ z : ℤ, denAll h * (Delta 4 h).coeff k = z := by
  unfold denAll
  split_ifs with hh
  · exact denU_int hh k
  · exact (Classical.choose_spec (exists_den (Delta 4 h))).2 k

/-! ### The size of the denominator -/

/-- `30h + 6h log h = o(h²)` (verbatim from lean_chi2's `Arith/Assembly.lean`, `eventually_rem_le`). -/
lemma eventually_rem_le_U (c : ℝ) (hc : 0 < c) :
    ∀ᶠ h : ℕ in atTop, 30 * (h : ℝ) + 6 * (h : ℝ) * Real.log h ≤ c * (h : ℝ) ^ 2 := by
  filter_upwards [eventually_ge_atTop ⌈(24 / c) ^ 2 + 60 / c + 1⌉₊] with h hh
  have hH : (24 / c) ^ 2 + 60 / c + 1 ≤ (h : ℝ) := Nat.ceil_le.mp hh
  set H : ℝ := (h : ℝ)
  have hc24 : 0 ≤ 24 / c := by positivity
  have hc60 : 0 ≤ 60 / c := by positivity
  have hH0 : 0 < H := by nlinarith
  set s := Real.sqrt H
  have hs2 : s ^ 2 = H := Real.sq_sqrt hH0.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr hH0
  have hs24 : 24 / c ≤ s := Real.le_sqrt_of_sq_le (by nlinarith)
  have hcs : 24 ≤ c * s := by rwa [div_le_iff₀ hc, mul_comm] at hs24
  have hcH : 60 ≤ c * H := by
    have : 60 / c ≤ H := by nlinarith
    rwa [div_le_iff₀ hc, mul_comm] at this
  have hlog : Real.log H ≤ 2 * s := by
    have h1 := Real.log_le_sub_one_of_pos hs0
    have h2 : Real.log H = 2 * Real.log s := by rw [← hs2, Real.log_pow]; push_cast; ring
    linarith
  have h3 : 6 * H * Real.log H ≤ 12 * H * s := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hcs (by positivity : (0 : ℝ) ≤ H * s / 2)]

/-- **The arithmetic bound**: `log den h ≤ (4/3 + ε) h²` for even `h`, eventually. -/
theorem log_denAll_le : ∀ ε > 0, ∀ᶠ h : ℕ in atTop, Even h →
    Real.log (denAll h) ≤ (4 / 3 + ε) * (h : ℝ) ^ 2 := by
  intro ε hε
  filter_upwards [theoremA (ε / 2) (by positivity), eventually_rem_le_U (ε / 2) (by positivity),
    eventually_ge_atTop 1] with h hA hR h1 hh
  have hd : denAll h = denU h := by unfold denAll; rw [ite_eq_left hh]
  rw [hd]
  have hne : ∀ p ∈ oddPrimes h, ((p : ℝ)) ^ eOdd h p ≠ 0 := fun p hp =>
    pow_ne_zero _ (by exact_mod_cast (mem_filter.mp hp).2.1.ne_zero)
  have hlog : Real.log ((denU h : ℚ) : ℝ) =
      (e2 h : ℝ) * Real.log 2 + ∑ p ∈ oddPrimes h, (eOdd h p : ℝ) * Real.log p := by
    unfold denU
    push_cast
    rw [Real.log_mul (by positivity) (prod_ne_zero_iff.mpr hne), Real.log_pow, Real.log_prod hne]
    simp only [Real.log_pow]
  rw [hlog]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hL : (Nat.log 2 h : ℝ) * Real.log 2 ≤ Real.log h := by
    have hp := Nat.pow_log_le_self 2 (by omega : h ≠ 0)
    have : ((2 : ℝ) ^ Nat.log 2 h) ≤ h := by exact_mod_cast hp
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) this
  have he2 : (e2 h : ℝ) * Real.log 2 ≤ 30 * h + 6 * h * Real.log h := by
    unfold e2
    push_cast
    have hh0 : (0 : ℝ) ≤ h := h.cast_nonneg
    have hlh : 0 ≤ Real.log h := Real.log_natCast_nonneg h
    nlinarith [mul_le_mul_of_nonneg_left hL hh0]
  linarith

end Chi2U
