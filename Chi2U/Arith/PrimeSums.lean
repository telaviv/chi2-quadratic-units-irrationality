/-
# Theorem A′: the odd primes contribute `4/3` per `h²` (PROOF_U §3.4)

`K = h + 1`. The odd primes `p ≤ h` split into
* `3p < K` (`sum_small_le`): `eOdd = 2h·lev*(p) + v_p(h!)`, and
  `Σ (2h·lev*(p) + v_p(h!)) log p ≤ 2h (θ(h/3) + (√h + 1) log h) + h log h`
  (`lev* ≤ 1` when `p² > h`, `lev*(p) log p ≤ log h` always (`levU_le_one_A`, `levU_mul_log_le_A`), and
  `Π p^{v_p(h!)} ∣ h! ≤ h^h` (`sum_padicValNat_log_le`)); by the PNT `θ(h/3) ~ h/3` this is `(2/3)h² + o(h²)`;
* `K/3 ≤ p ≤ h` (`sum_large_le`): `eOdd = 3(K − p) = K · gL(K/p)` with `gL(y) = 3(1 − 1/y)`; the prime `p = K/3`
  (if any) costs `2K log K`, the others are a prime sum `Σ_{K/3 < p ≤ K} gL(K/p) log p` which is
  `≤ (2/3 + ε)K` eventually (`eventually_primeSum_gL_le`: upper Riemann sums of `3(1 − x)` on `[1/3, 1]` in `M`
  equal cells, `Σ = (2/3)(1 + 1/M)`, fed into the step-function PNT bound `eventually_primeSum_step_le`).
Total `(4/3 + ε) h²` eventually (`theoremA`). The PNT is `Chi2U.PNT` (ported verbatim from lean_chi2).
Template: `lean_chi2/Chi2Irrational/Arith/PrimeSums.lean` (step weights `φ₁` there).
-/
import Chi2U.PNT.PrimeSums
import Chi2U.Arith.Defs

namespace Chi2U

open Finset Filter
open scoped Chebyshev

open PNT

/-! ### `lev*` -/

/-- `lev*(p) ≤ 1` when `p² > h`. -/
theorem levU_le_one_A {h p : ℕ} (hp : p.Prime) (hpp : h < p * p) : levU h p ≤ 1 := by
  unfold levU
  calc ((Icc 1 h).filter (fun e => p ^ e ≤ h)).card ≤ ({1} : Finset ℕ).card := by
        apply card_le_card
        intro e he
        simp only [mem_filter, mem_Icc] at he
        obtain ⟨⟨he1, _⟩, he2⟩ := he
        rw [mem_singleton]
        by_contra hne
        have h2 : p ^ 2 ≤ p ^ e := Nat.pow_le_pow_right hp.pos (by omega)
        rw [pow_two] at h2
        omega
    _ = 1 := card_singleton 1

/-- `lev*(p) · log p ≤ log h` for a prime `p` and `h ≥ 1`. -/
theorem levU_mul_log_le_A {h p : ℕ} (hp : p.Prime) (hh : 1 ≤ h) :
    (levU h p : ℝ) * Real.log p ≤ Real.log h := by
  set L := Nat.log p h
  have hlev : levU h p ≤ L := by
    unfold levU
    calc ((Icc 1 h).filter (fun e => p ^ e ≤ h)).card ≤ (Icc 1 L).card := by
          apply card_le_card
          intro e he
          simp only [mem_filter, mem_Icc] at he ⊢
          exact ⟨he.1.1, Nat.le_log_of_pow_le hp.one_lt he.2⟩
      _ = L := by simp
  have hpL : p ^ L ≤ h := Nat.pow_log_le_self p (by omega)
  have hp0 : (0 : ℝ) < ((p ^ L : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos L
  calc (levU h p : ℝ) * Real.log p ≤ (L : ℝ) * Real.log p :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hlev) (Real.log_natCast_nonneg p)
    _ = Real.log ((p ^ L : ℕ) : ℝ) := by rw [Nat.cast_pow, Real.log_pow]
    _ ≤ Real.log h := Real.log_le_log hp0 (by exact_mod_cast hpL)

/-- Finite form: `Σ_{p ∈ F} lev*(p) log p ≤ θ(h/3) + (√h + 1) log h` for primes with `3p ≤ h`. -/
theorem sum_levU_log_le {h : ℕ} (hh : 1 ≤ h) (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime ∧ 3 * p ≤ h) :
    ∑ p ∈ F, (levU h p : ℝ) * Real.log p ≤ θ ((h : ℝ) / 3) + (Real.sqrt h + 1) * Real.log h := by
  have hlogh : 0 ≤ Real.log h := Real.log_natCast_nonneg h
  have hpt : ∀ p ∈ F, (levU h p : ℝ) * Real.log p ≤
      Real.log p + (if p * p ≤ h then Real.log h else 0) := by
    intro p hp
    have hp2 := (hF p hp).1
    split_ifs with hpp
    · have := levU_mul_log_le_A (h := h) hp2 hh
      have := Real.log_natCast_nonneg p
      linarith
    · have h1 : (levU h p : ℝ) ≤ 1 := by exact_mod_cast levU_le_one_A hp2 (by omega)
      have := Real.log_natCast_nonneg p
      nlinarith
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib]
  gcongr
  · -- main term
    rw [← primeSum_one_zero, primeSum_eq_sum_filter _ (by positivity) (range (h + 1))]
    · simp only [one_mul]
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hp2, hp3⟩ := hF p hp
        refine mem_filter.mpr ⟨mem_range.mpr (by omega), hp2, by exact_mod_cast hp2.pos, ?_⟩
        rw [le_div_iff₀ (by norm_num)]
        exact_mod_cast (by omega : p * 3 ≤ h)
      · intro p _ _
        exact Real.log_natCast_nonneg p
    · intro p _ _ hpd
      rw [mem_range]
      have : (p : ℝ) * 3 ≤ h := by rwa [le_div_iff₀ (by norm_num)] at hpd
      have : p * 3 ≤ h := by exact_mod_cast this
      omega
  · -- prime powers
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    gcongr
    have hcard : (F.filter (fun p => p * p ≤ h)).card ≤ Nat.sqrt h + 1 := by
      calc (F.filter (fun p => p * p ≤ h)).card ≤ (range (Nat.sqrt h + 1)).card := by
            apply card_le_card
            intro p hp
            rw [mem_filter] at hp
            rw [mem_range, Nat.lt_succ_iff]
            exact Nat.le_sqrt.mpr hp.2
        _ = Nat.sqrt h + 1 := card_range _
    calc ((F.filter (fun p => p * p ≤ h)).card : ℝ) ≤ ((Nat.sqrt h + 1 : ℕ) : ℝ) := by
          exact_mod_cast hcard
      _ ≤ Real.sqrt h + 1 := by
          push_cast
          have := Real.nat_sqrt_le_real_sqrt (a := h)
          linarith

/-! ### `v_p(h!)` -/

/-- `Π_{p ∈ s} p^{v_p(n)} ∣ n` for a finset of primes. -/
theorem prod_pow_padicValNat_dvd (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (n : ℕ) :
    ∏ p ∈ s, p ^ padicValNat p n ∣ n := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a r har ih =>
    rw [prod_insert har]
    have ha := hs a (mem_insert_self a r)
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ pow_padicValNat_dvd
      (ih fun p hp => hs p (mem_insert_of_mem hp))
    refine Nat.Coprime.prod_right fun q hq => ?_
    have hq' := hs q (mem_insert_of_mem hq)
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes ha hq').mpr (fun e => har (e ▸ hq)))

/-- `Σ_{p ∈ s} v_p(h!) log p ≤ log h! ≤ h log h`. -/
theorem sum_padicValNat_log_le (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (h : ℕ) :
    ∑ p ∈ s, (padicValNat p h.factorial : ℝ) * Real.log p ≤ h * Real.log h := by
  have hd := Nat.le_of_dvd (Nat.factorial_pos h) (prod_pow_padicValNat_dvd s hs h.factorial)
  have hpos : 0 < ∏ p ∈ s, p ^ padicValNat p h.factorial :=
    prod_pos fun p hp => pow_pos (hs p hp).pos _
  have e : ∑ p ∈ s, (padicValNat p h.factorial : ℝ) * Real.log p =
      Real.log ((∏ p ∈ s, p ^ padicValNat p h.factorial : ℕ) : ℝ) := by
    push_cast
    rw [Real.log_prod (fun p hp => pow_ne_zero _ (by exact_mod_cast (hs p hp).ne_zero))]
    simp only [Real.log_pow]
  rw [e, ← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast hpos)
  exact_mod_cast hd.trans (Nat.factorial_le_pow h)

/-! ### The small primes `3p < K` -/

/-- Small primes, finite form. -/
theorem sum_small_le {h : ℕ} (hh : 1 ≤ h) :
    ∑ p ∈ (oddPrimes h).filter (fun p => 3 * p < h + 1), (eOdd h p : ℝ) * Real.log p ≤
      2 * h * (θ ((h : ℝ) / 3) + (Real.sqrt h + 1) * Real.log h) + h * Real.log h := by
  have hmem : ∀ p ∈ (oddPrimes h).filter (fun p => 3 * p < h + 1), p.Prime ∧ 3 * p ≤ h := by
    intro p hp
    simp only [oddPrimes, mem_filter, mem_range] at hp
    exact ⟨hp.1.2.1, by omega⟩
  have e : ∀ p ∈ (oddPrimes h).filter (fun p => 3 * p < h + 1), (eOdd h p : ℝ) * Real.log p =
      2 * h * ((levU h p : ℝ) * Real.log p) + (padicValNat p h.factorial : ℝ) * Real.log p := by
    intro p hp
    have := (mem_filter.mp hp).2
    unfold eOdd
    rw [ite_eq_left this]
    push_cast
    ring
  rw [sum_congr rfl e, sum_add_distrib, ← mul_sum]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (sum_levU_log_le hh _ hmem) (by positivity)
  · exact sum_padicValNat_log_le _ (fun p hp => (hmem p hp).1) h

/-! ### The large primes `K/3 ≤ p < K` -/

/-- The large-prime weight as a function of `y = K/p`: `3(K − p) = K · gL(K/p)`. -/
noncomputable def gL (y : ℝ) : ℝ := 3 * (1 - 1 / y)

/-- `Σ_{n/3 < p ≤ n} gL(n/p) log p ≤ (2/3 + ε) n` eventually (PNT, `∫_{1/3}^1 3(1 − x) dx = 2/3`). -/
theorem eventually_primeSum_gL_le (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop,
    primeSum (fun p => gL ((n : ℝ) / p)) ((n : ℝ) / 3) n ≤ (2 / 3 + ε) * n := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, 4 / (3 * ε) < M := exists_nat_gt _
  have hM0' : (0 : ℝ) < M := lt_trans (by positivity) hM
  set Δ : ℝ := 2 / 3 / M with hΔ
  have hΔ0 : 0 < Δ := by positivity
  have hMΔ : (M : ℝ) * Δ = 2 / 3 := by rw [hΔ]; field_simp
  set x : ℕ → ℝ := fun i => 1 / (1 - i * Δ) with hxdef
  set u : ℕ → ℝ := fun i => 3 * ((i + 1) * Δ) with hudef
  have hpos : ∀ i ≤ M, 1 / 3 ≤ 1 - (i : ℝ) * Δ := by
    intro i hi
    have : (i : ℝ) ≤ M := by exact_mod_cast hi
    nlinarith
  have hx0 : 0 < x 0 := by simp [hxdef]
  have hx : ∀ i < M, x i < x (i + 1) := by
    intro i hi
    have h1 := hpos (i + 1) hi
    simp only [hxdef]
    push_cast at h1 ⊢
    apply one_div_lt_one_div_of_lt (by linarith)
    nlinarith
  have hinv : ∀ i, 1 / x i = 1 - i * Δ := by
    intro i
    simp [hxdef]
  have hh : ∀ i < M, ∀ y, x i < y → y < x (i + 1) → gL y ≤ u i := by
    intro i hi y hy1 hy2
    have hy0 : 0 < y := lt_trans hx0 (lt_of_le_of_lt (le_of_chain hx i hi.le) hy1)
    have : 1 / x (i + 1) < 1 / y := one_div_lt_one_div_of_lt hy0 hy2
    rw [hinv (i + 1)] at this
    push_cast at this
    simp only [gL, hudef]
    linarith
  have hstep := eventually_primeSum_step_le gL x u M hx0 hx hh (half_pos hε)
  filter_upwards [hstep] with n hs
  have hsum : ∑ i ∈ range M, u i * (1 / x i - 1 / x (i + 1)) ≤ 2 / 3 + ε / 2 := by
    have e : ∀ i ∈ range M, u i * (1 / x i - 1 / x (i + 1)) = 3 * Δ ^ 2 * ((i : ℝ) + 1) := by
      intro i _
      rw [hinv i, hinv (i + 1)]
      simp only [hudef]
      push_cast
      ring
    rw [sum_congr rfl e, ← mul_sum, sum_range_succ_cast]
    have e2 : 3 * Δ ^ 2 * ((M : ℝ) * (M + 1) / 2) = 2 / 3 + 2 / (3 * M) := by
      rw [hΔ]
      field_simp
    rw [e2]
    have h4 : 4 < (M : ℝ) * (3 * ε) := by rwa [div_lt_iff₀ (by positivity)] at hM
    have : 2 / (3 * (M : ℝ)) ≤ ε / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have e0 : (n : ℝ) / x 0 = n := by simp [hxdef]
  have eM : (n : ℝ) / x M = n / 3 := by
    simp only [hxdef, hMΔ]
    norm_num
  rw [e0, eM] at hs
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  nlinarith [mul_le_mul_of_nonneg_left hsum hn0]

/-- Large primes, finite form (`K = h + 1`). -/
theorem sum_large_le (h : ℕ) :
    ∑ p ∈ (oddPrimes h).filter (fun p => ¬ 3 * p < h + 1), (eOdd h p : ℝ) * Real.log p ≤
      2 * ((h : ℝ) + 1) * Real.log ((h : ℝ) + 1) +
        ((h : ℝ) + 1) * primeSum (fun p => gL (((h : ℝ) + 1) / p)) (((h : ℝ) + 1) / 3) ((h : ℝ) + 1) := by
  have hK0 : (0 : ℝ) < (h : ℝ) + 1 := by positivity
  have hmem : ∀ p ∈ (oddPrimes h).filter (fun p => ¬ 3 * p < h + 1),
      p.Prime ∧ p ≤ h ∧ h + 1 ≤ 3 * p := by
    intro p hp
    simp only [oddPrimes, mem_filter, mem_range] at hp
    exact ⟨hp.1.2.1, by omega, by omega⟩
  have heO : ∀ p ∈ (oddPrimes h).filter (fun p => ¬ 3 * p < h + 1),
      (eOdd h p : ℝ) = 3 * ((h : ℝ) + 1 - p) := by
    intro p hp
    obtain ⟨-, hph, h3⟩ := hmem p hp
    unfold eOdd
    rw [ite_eq_right (by omega), ite_eq_left (by omega), Nat.cast_mul, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [← sum_filter_add_sum_filter_not _ (fun p => 3 * p = h + 1)]
  apply add_le_add
  · -- the prime `p = K/3`
    have hcard : (((oddPrimes h).filter (fun p => ¬ 3 * p < h + 1)).filter
        (fun p => 3 * p = h + 1)).card ≤ 1 := by
      rw [card_le_one]
      intro a ha b hb
      have := (mem_filter.mp ha).2
      have := (mem_filter.mp hb).2
      omega
    have hl1 : 0 ≤ Real.log ((h : ℝ) + 1) := Real.log_nonneg (by have := h.cast_nonneg (α := ℝ); linarith)
    have hterm : ∀ p ∈ ((oddPrimes h).filter (fun p => ¬ 3 * p < h + 1)).filter
        (fun p => 3 * p = h + 1),
        (eOdd h p : ℝ) * Real.log p ≤ 2 * ((h : ℝ) + 1) * Real.log ((h : ℝ) + 1) := by
      intro p hp
      obtain ⟨hpS, h3⟩ := mem_filter.mp hp
      obtain ⟨hpp, hph, -⟩ := hmem p hpS
      rw [heO p hpS]
      have h3' : (3 : ℝ) * p = h + 1 := by exact_mod_cast h3
      have hph' : (p : ℝ) ≤ h := by exact_mod_cast hph
      have hl : Real.log p ≤ Real.log ((h : ℝ) + 1) :=
        Real.log_le_log (by exact_mod_cast hpp.pos) (by linarith)
      have e3 : 3 * ((h : ℝ) + 1 - p) = 2 * ((h : ℝ) + 1) := by linarith
      rw [e3]
      exact mul_le_mul_of_nonneg_left hl (by positivity)
    calc _ ≤ ∑ p ∈ ((oddPrimes h).filter (fun p => ¬ 3 * p < h + 1)).filter (fun p => 3 * p = h + 1),
          2 * ((h : ℝ) + 1) * Real.log ((h : ℝ) + 1) := sum_le_sum hterm
      _ = (((oddPrimes h).filter (fun p => ¬ 3 * p < h + 1)).filter (fun p => 3 * p = h + 1)).card *
          (2 * ((h : ℝ) + 1) * Real.log ((h : ℝ) + 1)) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 1 * (2 * ((h : ℝ) + 1) * Real.log ((h : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = _ := one_mul _
  · -- the primes `K/3 < p ≤ h`
    rw [primeSum_eq_sum_filter _ hK0.le (range (h + 2))]
    · calc ∑ p ∈ ((oddPrimes h).filter (fun p => ¬ 3 * p < h + 1)).filter (fun p => ¬ 3 * p = h + 1),
            (eOdd h p : ℝ) * Real.log p
          = ∑ p ∈ ((oddPrimes h).filter (fun p => ¬ 3 * p < h + 1)).filter (fun p => ¬ 3 * p = h + 1),
            ((h : ℝ) + 1) * (gL (((h : ℝ) + 1) / p) * Real.log p) := by
            apply sum_congr rfl
            intro p hp
            obtain ⟨hpS, -⟩ := mem_filter.mp hp
            have hp0 : (0 : ℝ) < p := by exact_mod_cast (hmem p hpS).1.pos
            rw [heO p hpS]
            unfold gL
            field_simp
        _ ≤ ∑ p ∈ (range (h + 2)).filter (fun p : ℕ => p.Prime ∧ ((h : ℝ) + 1) / 3 < (p : ℝ) ∧
              (p : ℝ) ≤ (h : ℝ) + 1), ((h : ℝ) + 1) * (gL (((h : ℝ) + 1) / p) * Real.log p) := by
            apply sum_le_sum_of_subset_of_nonneg
            · intro p hp
              obtain ⟨hpS, h3⟩ := mem_filter.mp hp
              obtain ⟨hpp, hph, hK3⟩ := hmem p hpS
              have hlt : h + 1 < 3 * p := lt_of_le_of_ne hK3 (Ne.symm h3)
              refine mem_filter.mpr ⟨mem_range.mpr (by omega), hpp, ?_, ?_⟩
              · rw [div_lt_iff₀ (by norm_num)]
                exact_mod_cast (by omega : h + 1 < p * 3)
              · have : (p : ℝ) ≤ h := by exact_mod_cast hph
                linarith
            · intro p hp _
              obtain ⟨-, hpp, -, hpK⟩ := mem_filter.mp hp
              have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
              have hg : 0 ≤ gL (((h : ℝ) + 1) / p) := by
                unfold gL
                rw [one_div_div]
                have : (p : ℝ) / ((h : ℝ) + 1) ≤ 1 := (div_le_one hK0).mpr hpK
                linarith
              have := Real.log_natCast_nonneg p
              positivity
        _ = _ := by rw [mul_sum]
    · intro p _ _ hpd
      rw [mem_range]
      have : (p : ℝ) ≤ ((h + 1 : ℕ) : ℝ) := by push_cast; exact hpd
      have := Nat.cast_le.mp this
      omega

/-! ### Theorem A′ -/

/-- **Theorem A′** (needs the PNT). -/
theorem theoremA : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    ∑ p ∈ oddPrimes h, (eOdd h p : ℝ) * Real.log p ≤ (4 / 3 + ε) * (h : ℝ) ^ 2 := by
  intro ε hε
  set δ : ℝ := min (ε / 16) 1 with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : 16 * δ ≤ ε := by have := min_le_left (ε / 16) 1; linarith
  -- PNT: `θ(h/3) ≤ (1/3 + δ) h`
  have hT := theta_nat_div_tendsto (c := 3) (by norm_num)
  have hlt : 1 / (3 : ℝ) < 1 / 3 + δ := by linarith
  -- `√x log x = o(x)`, `log x = o(x)`
  have hA := tendsto_natCast_atTop_atTop.eventually
    ((Port.isLittleO_sqrt_mul_log).bound (c := δ) hδ0)
  have hB := tendsto_natCast_atTop_atTop.eventually (Real.isLittleO_log_id_atTop.bound (c := δ) hδ0)
  have hL := (tendsto_add_atTop_nat 1).eventually (eventually_primeSum_gL_le δ hδ0)
  have hB1 := (tendsto_add_atTop_nat 1).eventually hB
  filter_upwards [hT.eventually (Iio_mem_nhds hlt), hA, hB, hL, hB1,
    eventually_ge_atTop (⌈3 / δ⌉₊ + 1)] with h hθ hA hB hL hB1 hN
  have h1 : 1 ≤ h := by omega
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hK0 : (0 : ℝ) < (h : ℝ) + 1 := by linarith
  simp only [id, Real.norm_eq_abs] at hA hB hB1
  push_cast at hL hB1
  have hlog : 0 ≤ Real.log h := Real.log_natCast_nonneg h
  have hlog1 : 0 ≤ Real.log ((h : ℝ) + 1) := Real.log_nonneg (by linarith)
  rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hlog), abs_of_pos hh0] at hA
  rw [abs_of_nonneg hlog, abs_of_pos hh0] at hB
  rw [abs_of_nonneg hlog1, abs_of_pos hK0] at hB1
  have hθ' : θ ((h : ℝ) / 3) ≤ (1 / 3 + δ) * h := by
    have := (div_lt_iff₀ hh0).mp hθ
    linarith
  -- `2h + 1 ≤ δ h²`
  have hquad : 2 * (h : ℝ) + 1 ≤ δ * (h : ℝ) ^ 2 := by
    have hc : 3 / δ ≤ (⌈3 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have hN' : ((⌈3 / δ⌉₊ + 1 : ℕ) : ℝ) ≤ h := by exact_mod_cast hN
    push_cast at hN'
    have h3 : 3 ≤ δ * h := by
      have : 3 / δ ≤ h := by linarith
      rwa [div_le_iff₀ hδ0, mul_comm] at this
    have h1' : (1 : ℝ) ≤ h := by exact_mod_cast h1
    nlinarith
  -- the small primes
  have hS := sum_small_le h1
  have hS' : ∑ p ∈ (oddPrimes h).filter (fun p => 3 * p < h + 1), (eOdd h p : ℝ) * Real.log p ≤
      (2 / 3 + 7 * δ) * (h : ℝ) ^ 2 := by
    have hin : θ ((h : ℝ) / 3) + (Real.sqrt h + 1) * Real.log h ≤ (1 / 3 + 3 * δ) * h := by
      have : (Real.sqrt h + 1) * Real.log h = Real.sqrt h * Real.log h + Real.log h := by ring
      linarith
    have e1 := mul_le_mul_of_nonneg_left hin (by positivity : (0 : ℝ) ≤ 2 * h)
    have e2 := mul_le_mul_of_nonneg_left hB hh0.le
    nlinarith
  -- the large primes
  have hLg := sum_large_le h
  have hL' : ∑ p ∈ (oddPrimes h).filter (fun p => ¬ 3 * p < h + 1), (eOdd h p : ℝ) * Real.log p ≤
      (2 / 3 + 7 * δ) * (h : ℝ) ^ 2 := by
    have e1 := mul_le_mul_of_nonneg_left hB1 (by positivity : (0 : ℝ) ≤ 2 * ((h : ℝ) + 1))
    have e2 := mul_le_mul_of_nonneg_left hL hK0.le
    have hsq : ((h : ℝ) + 1) ^ 2 ≤ (1 + δ) * (h : ℝ) ^ 2 := by nlinarith
    have e3 := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 2 / 3 + 3 * δ)
    have hδ2 : δ * δ ≤ δ := by nlinarith
    have e4 := mul_le_mul_of_nonneg_left hδ2 (by positivity : (0 : ℝ) ≤ 3 * (h : ℝ) ^ 2)
    nlinarith
  rw [← sum_filter_add_sum_filter_not (oddPrimes h) (fun p => 3 * p < h + 1)]
  nlinarith

end Chi2U
