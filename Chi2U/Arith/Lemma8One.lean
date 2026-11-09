/-
# Lemma 8′ for one-level primes: `n_p ≤ A_K(p)` when `3p ≥ K` (PROOF_U §3.2, the case used by Theorem A′)

Theorem A′ uses Lemma 8′ only for odd primes `p` with `K/3 ≤ p` (`K = h + 1`), where `p² ≥ 3p ≥ K` leaves the single
level `e = 1` (and for `p ≥ K`, where there is no level). This file proves exactly that case,
`lemma8_one : 3p ≥ K → |c_k|_p ≤ p^{A_K(p)}`, by a route shorter in Lean than the paper's atom expansion.

**Route (Lagrange Gram + Lemma B).** With `f_i = D/(t − x_i)` (`fLag`), `f_i(x_m) = δ_{im} D′(x_i)`, so the pole
coefficients `c_m(f_i f_j) = f_i(x_m) f_j(x_m)/D′(x_m)` vanish except `c_i(f_i²) = D′(x_i)` (`l8_cPole_fLag_mul`). Hence
the `K × K` Gram matrix of Lemma B is `G^f = 𝒫 + diag(d_i)` with
* `𝒫_{ij} = μ(f_i f_j div D)`, `p`-integral (`f_i f_j div D ∈ ℤ[t]` since `D` is monic integral, and
  `vGe_Lmom_odd`), and
* `d_i = −D′(x_i) z^{x_i} (X − P(x_i))`.
If `v_p(P(x_i)) ≥ −w_i`, every entry of row `i` has `v_p ≥ ρ_i := min(0, v_p(D′(x_i)) − w_i)`. An adjugate entry is the
determinant of `G^f` with one row replaced by a unit vector (`Matrix.adjugate_apply`), so it has `v_p ≥ Σ_i ρ_i`; Lemma B
(`Δ_h · Π D′(x_i) = ± 𝟙ᵀ adj(G^f) 𝟙`) gives
  `n_p ≤ Σ_i (v_p(D′(x_i)) − ρ_i) = Σ_i max(v_p(D′(x_i)), w_i)`      (`padicNorm_Delta_crude`).
**Counting for `3p ≥ K`.** Atom differences are `< 3p ≤ p²`, so `v_p(D′(x_m)) ≤ n_c − 1` (`n_c` = size of the class of
`m` mod `p`); odd `n < |x_m| ≤ h < 3p` divisible by `p` is `n = p`, so `w = wU` works (`l8_vGe_Psum`). Classes have
`≤ 3` atoms and at most one atom of weight 0 (two such atoms would be `≥ p` apart inside a window of width `p`), so the
class sum of `max(n_c − 1, w)` is at most the class value at `S = {weight-2 atoms}` (`l8_class_le`): `Σ ≤ A_K(p)`.
-/
import Chi2U.Arith.LemmaB
import Chi2U.Mahler

namespace Chi2U

variable {az : ℕ} [Fact (1 ≤ az)]

open Polynomial Finset

variable {h p : ℕ}

/-! ### Poles and Lagrange polynomials -/

lemma l8_poleZ_inj {m l : ℕ} (e : (poleZ h m : ℚ) = poleZ h l) : m = l := by
  have e' : poleZ h m = poleZ h l := by exact_mod_cast e
  unfold poleZ at e'; omega

lemma l8_dPrime_ne_zero (h m : ℕ) : dPrime h m ≠ 0 := by
  unfold dPrime
  refine prod_ne_zero_iff.mpr (fun l _ => ?_)
  split_ifs with hl
  · exact one_ne_zero
  · exact sub_ne_zero.mpr (fun e => hl (l8_poleZ_inj e).symm)

lemma l8_eval_fLag_self (h i : ℕ) : (fLag h i).eval (poleZ h i : ℚ) = dPrime h i := by
  unfold fLag dPrime
  rw [eval_prod, ← prod_erase (range (h + 1))
    (f := fun l => if l = i then (1 : ℚ) else ((poleZ h i : ℚ) - poleZ h l)) (a := i) (by simp)]
  refine prod_congr rfl (fun l hl => ?_)
  simp [ne_of_mem_erase hl]

lemma l8_eval_fLag_of_ne {i m : ℕ} (hm : m ≤ h) (hmi : m ≠ i) : (fLag h i).eval (poleZ h m : ℚ) = 0 := by
  unfold fLag
  rw [eval_prod]
  exact prod_eq_zero (mem_erase.mpr ⟨hmi, mem_range.mpr (by omega)⟩) (by simp)

lemma l8_cPole_fLag_mul {i j m : ℕ} (hm : m ≤ h) :
    cPole h (fLag h i * fLag h j) m = if i = m ∧ j = m then dPrime h m else 0 := by
  unfold cPole
  rw [eval_mul]
  split_ifs with hc
  · obtain ⟨rfl, rfl⟩ := hc
    rw [l8_eval_fLag_self, mul_div_assoc, div_self (l8_dPrime_ne_zero _ _), mul_one]
  · rcases not_and_or.mp hc with h1 | h1
    · rw [l8_eval_fLag_of_ne hm (Ne.symm h1), zero_mul, zero_div]
    · rw [l8_eval_fLag_of_ne hm (Ne.symm h1), mul_zero, zero_div]

/-! ### Integrality of the polynomial part -/

/-- `D` over `ℤ`. -/
noncomputable def l8DZ (h : ℕ) : ℤ[X] := ∏ m ∈ range (h + 1), (X - C (poleZ h m))

/-- `f_i` over `ℤ`. -/
noncomputable def l8fZ (h i : ℕ) : ℤ[X] := ∏ m ∈ (range (h + 1)).erase i, (X - C (poleZ h m))

lemma l8_Dpoly_eq : Dpoly h = (l8DZ h).map (Int.castRingHom ℚ) := by
  simp [Dpoly, l8DZ, Polynomial.map_prod]

lemma l8_fLag_eq (i : ℕ) : fLag h i = (l8fZ h i).map (Int.castRingHom ℚ) := by
  simp [fLag, l8fZ, Polynomial.map_prod]

lemma l8_DZ_monic : (l8DZ h).Monic := monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

/-- `μ(f_i f_j div D)` is `p`-integral. -/
lemma l8_vGe_muPoly_fLag [Fact p.Prime] (hp : ¬ p ∣ az) (i j : ℕ) :
    vGe p 0 (muPoly az ((fLag h i * fLag h j) /ₘ Dpoly h)) := by
  have hQ : (fLag h i * fLag h j) /ₘ Dpoly h =
      ((l8fZ h i * l8fZ h j) /ₘ l8DZ h).map (Int.castRingHom ℚ) := by
    rw [l8_fLag_eq, l8_fLag_eq, l8_Dpoly_eq, ← Polynomial.map_mul, Polynomial.map_divByMonic _ l8_DZ_monic]
  rw [hQ, muPoly, derivative_map]
  refine vGe_Lmom_odd hp _ 0 (fun k => ?_)
  have e : (2 * (k : ℚ) + 1) = (((2 * k + 1 : ℕ) : ℤ) : ℚ) := by push_cast; ring
  rw [e, eval_intCast_map]
  simpa using padicNorm.of_int (p := p) _

/-! ### The partial sums `P(x_m)` for `3p ≥ K` -/

lemma l8_padicNorm_inv_sq [hpp : Fact p.Prime] (h3 : h + 1 ≤ 3 * p) {m k : ℕ} (hm : m ≤ h)
    (hk : 2 * k + 1 < (poleZ h m).natAbs) :
    padicNorm p (1 / ((2 * k + 1 : ℕ) : ℚ) ^ 2) ≤ (p : ℚ) ^ (wU h p m : ℤ) := by
  have hx : (poleZ h m).natAbs ≤ h + 1 := by simp only [poleZ]; omega
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hpp.out.one_lt.le
  rw [padicNorm.div, padicNorm.one, sq, padicNorm.mul]
  by_cases hd : p ∣ 2 * k + 1
  · obtain ⟨j, hj⟩ := hd
    have hj1 : j = 1 := by
      have hodd : Odd (p * j) := hj ▸ odd_two_mul_add_one k
      have hjodd := (Nat.odd_mul.mp hodd).2
      have hlt : p * j < p * 3 := by omega
      have := Nat.lt_of_mul_lt_mul_left hlt
      obtain ⟨t, ht⟩ := hjodd; omega
    subst hj1
    have hw : wU h p m = 2 := by unfold wU; split_ifs <;> omega
    rw [hw, hj, mul_one, padicNorm.padicNorm_p_of_prime]
    have hp0 : (p : ℚ) ≠ 0 := by positivity
    rw [show ((2 : ℕ) : ℤ) = (2 : ℤ) from rfl, zpow_two]
    field_simp
    exact le_rfl
  · rw [(padicNorm.nat_eq_one_iff _).mpr hd, mul_one, div_one]
    exact one_le_zpow₀ hp1 (by positivity)

/-- `v_p(P(x_m)) ≥ −w(m)` for `3p ≥ K`. -/
lemma l8_vGe_Psum [Fact p.Prime] (h3 : h + 1 ≤ 3 * p) {m : ℕ} (hm : m ≤ h) :
    vGe p (-(wU h p m : ℤ)) (Psum az (poleZ h m)) := by
  have hterm : ∀ k ∈ range ((poleZ h m).natAbs / 2), ∀ u : (Qd az), pInt p u →
      vGe p (-(wU h p m : ℤ)) (u / ((2 * k + 1 : ℕ) : (Qd az)) ^ 2) := by
    intro k hk u hu
    have hk' : 2 * k + 1 < (poleZ h m).natAbs := by have := mem_range.mp hk; omega
    have e : u / ((2 * k + 1 : ℕ) : (Qd az)) ^ 2 = u * (((1 / ((2 * k + 1 : ℕ) : ℚ) ^ 2 : ℚ)) : (Qd az)) := by
      push_cast; ring
    rw [e]
    have := vGe_mul (vGe_of_pInt hu) (vGe_ratCast_of_padicNorm (n := -(wU h p m : ℤ))
      (by rw [neg_neg]; exact l8_padicNorm_inv_sq h3 hm hk'))
    simpa using this
  unfold Psum
  split_ifs
  · exact vGe_sum _ _ (fun k hk => hterm k hk _ (pInt_pow pInt_zK _))
  · exact vGe_neg (vGe_sum _ _ (fun k hk => hterm k hk _ (by rw [← inv_pow]; exact pInt_pow pInt_zK_inv _)))

/-! ### The crude bound `n_p ≤ Σ_i max(v_p(D′(x_i)), w_i)` -/

lemma l8_vGeX_mono {n m : ℤ} [Fact p.Prime] (hmn : m ≤ n) {F : (Qd az)[X]} (hF : vGeX p n F) : vGeX p m F :=
  fun k => vGe_mono hmn (hF k)

lemma l8_vGeX_zero [Fact p.Prime] (n : ℤ) : vGeX p n (0 : (Qd az)[X]) := fun k => by
  simpa using vGe_zero (p := p) n

lemma l8_padicNorm_prod [Fact p.Prime] (s : Finset ℕ) (f : ℕ → ℚ) :
    padicNorm p (∏ i ∈ s, f i) = ∏ i ∈ s, padicNorm p (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [prod_insert ha, prod_insert ha, padicNorm.mul, ih]

lemma l8_zpow_prod {a : ℚ} (ha : a ≠ 0) (s : Finset ℕ) (f : ℕ → ℤ) :
    ∏ i ∈ s, a ^ f i = a ^ (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [prod_insert hx, sum_insert hx, ih, zpow_add₀ ha]

/-- The row exponent `ρ_i = min(0, v_p(D′(x_i)) − w_i)`. -/
noncomputable def l8rho (h p : ℕ) (w : ℕ → ℤ) (i : ℕ) : ℤ := min 0 (padicValRat p (dPrime h i) - w i)

section Crude

variable [Fact p.Prime] (hp : ¬ p ∣ az) (w : ℕ → ℤ) (hw0 : ∀ m, 0 ≤ w m)
  (hw : ∀ m ≤ h, vGe p (-w m) (Psum az (poleZ h m)))
include hp hw0 hw

lemma l8_vGe_A {i : ℕ} (hi : i ≤ h) (j : ℕ) : vGe p (l8rho h p w i) (Afun az h (fLag h i * fLag h j)) := by
  unfold Afun
  refine vGe_add (vGe_mono (min_le_left _ _) (l8_vGe_muPoly_fLag hp _ _)) (vGe_sum _ _ (fun m hm => ?_))
  have hm' : m ≤ h := Nat.lt_succ_iff.mp (mem_range.mp hm)
  rw [l8_cPole_fLag_mul hm']
  split_ifs with hc
  · obtain ⟨rfl, -⟩ := hc
    have := vGe_mul (vGe_mul (vGe_ratCast (p := p) (dPrime h i)) (vGe_zK_zpow (p := p) (poleZ h i))) (hw i hi)
    refine vGe_mono ?_ this
    unfold l8rho; have := hw0 i; omega
  · rw [Rat.cast_zero, zero_mul, zero_mul]; exact vGe_zero _

omit hp hw in
lemma l8_vGe_B {i : ℕ} (j : ℕ) : vGe p (l8rho h p w i) (Bfun az h (fLag h i * fLag h j)) := by
  unfold Bfun
  refine vGe_neg (vGe_sum _ _ (fun m hm => ?_))
  have hm' : m ≤ h := Nat.lt_succ_iff.mp (mem_range.mp hm)
  rw [l8_cPole_fLag_mul hm']
  split_ifs with hc
  · obtain ⟨rfl, -⟩ := hc
    have := vGe_mul (vGe_ratCast (p := p) (dPrime h i)) (vGe_zK_zpow (az := az) (p := p) (poleZ h i))
    refine vGe_mono ?_ this
    unfold l8rho; have := hw0 i; omega
  · rw [Rat.cast_zero, zero_mul]; exact vGe_zero _

lemma l8_vGeX_GramF (i j : Fin (h + 1)) : vGeX p (l8rho h p w i) (GramF az h i j) := by
  have hi : (i : ℕ) ≤ h := Nat.lt_succ_iff.mp i.isLt
  change vGeX p _ (LamX az h (fLag h i * fLag h j))
  unfold LamX
  exact vGeX_add (vGeX_C (l8_vGe_A hp w hw0 hw hi j)) (vGeX_X_mul (vGeX_C (l8_vGe_B w hw0 j)))

lemma l8_vGeX_adj (a b : Fin (h + 1)) :
    vGeX p (∑ i : Fin (h + 1), l8rho h p w i) ((GramF az h).adjugate a b) := by
  rw [Matrix.adjugate_apply]
  refine l8_vGeX_mono ?_ (vGeX_det _ (fun r : Fin (h + 1) => if r = b then 0 else l8rho h p w r) (fun r c => ?_))
  · refine sum_le_sum (fun r _ => ?_)
    split_ifs
    · exact min_le_left _ _
    · exact le_rfl
  · rw [Matrix.updateRow_apply]
    split_ifs with hr
    · rw [Pi.single_apply]
      split_ifs
      · exact vGeX_one
      · exact l8_vGeX_zero 0
    · exact l8_vGeX_GramF hp w hw0 hw r c

/-- **Crude bound** (any odd `p`, any weights `w ≥ 0` with `v_p(P(x_m)) ≥ −w_m`):
`|c_k|_p ≤ p^{Σ_m max(v_p(D′(x_m)), w_m)}` for the coefficients of `Δ_h`. -/
theorem padicNorm_Delta_crude (hh : Even h) (k : ℕ) :
    padicNorm p ((Delta az h).coeff k) ≤
      (p : ℚ) ^ (∑ m ∈ range (h + 1), max (padicValRat p (dPrime h m)) (w m)) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hppos : (0 : ℚ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hS : vGeX p (∑ i : Fin (h + 1), l8rho h p w i)
      (C ((-1 : (Qd az)) ^ ((h + 1) * h / 2)) * ∑ a, ∑ b, (GramF az h).adjugate a b) := by
    have h1 : vGeX p 0 (C ((-1 : (Qd az)) ^ ((h + 1) * h / 2))) :=
      vGeX_C (vGe_of_pInt (pInt_pow (pInt_neg pInt_one) _))
    simpa using vGeX_mul h1 (vGeX_sum _ _ (fun a _ => vGeX_sum _ _ (fun b _ => l8_vGeX_adj hp w hw0 hw a b)))
  rw [← lemmaB hh] at hS
  have hk := padicNorm_le_of_vGe (az := az) (p := p) (r := (Delta az h).coeff k * ∏ i ∈ range (h + 1), dPrime h i) (by
    have := hS k
    rw [coeff_mul_C, coeff_map, eq_ratCast] at this
    push_cast
    exact this)
  rw [padicNorm.mul, l8_padicNorm_prod, prod_congr rfl (fun i _ => padicNorm.eq_zpow_of_nonzero
    (l8_dPrime_ne_zero h i)), l8_zpow_prod hp0] at hk
  have hexp : -(∑ i : Fin (h + 1), l8rho h p w i) + ∑ i ∈ range (h + 1), padicValRat p (dPrime h i) =
      ∑ m ∈ range (h + 1), max (padicValRat p (dPrime h m)) (w m) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => l8rho h p w i) (h + 1), ← sum_neg_distrib, ← sum_add_distrib]
    exact sum_congr rfl (fun m _ => by unfold l8rho; omega)
  rw [← hexp, zpow_add₀ hp0]
  have hpos : (0 : ℚ) < (p : ℚ) ^ (∑ i ∈ range (h + 1), padicValRat p (dPrime h i)) := zpow_pos hppos _
  calc padicNorm p ((Delta az h).coeff k)
      = padicNorm p ((Delta az h).coeff k) * (p : ℚ) ^ (∑ i ∈ range (h + 1), -padicValRat p (dPrime h i)) *
          (p : ℚ) ^ (∑ i ∈ range (h + 1), padicValRat p (dPrime h i)) := by
        rw [mul_assoc, ← zpow_add₀ hp0, sum_neg_distrib, neg_add_cancel, zpow_zero, mul_one]
    _ ≤ _ := by gcongr

end Crude

/-! ### Counting for `3p ≥ K` -/

lemma l8_padicValRat_two_mul_le [Fact p.Prime] (hp : p ≠ 2) {n : ℤ} (hn : n ≠ 0) (hnp : n.natAbs < p * p) :
    padicValRat p (2 * (n : ℚ)) ≤ if (p : ℤ) ∣ n then 1 else 0 := by
  have hpp : p.Prime := Fact.out
  have h2 : padicValRat p 2 = 0 := by
    have : padicValRat p ((2 : ℕ) : ℚ) = 0 := by
      rw [padicValRat.of_nat]
      exact_mod_cast padicValNat.eq_zero_of_not_dvd (fun hd =>
        hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp hd))
    exact_mod_cast this
  rw [padicValRat.mul (by norm_num) (by exact_mod_cast hn), h2, zero_add, padicValRat.of_int]
  have hna : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  unfold padicValInt
  split_ifs with hd
  · have : padicValNat p n.natAbs ≤ 1 := by
      by_contra hc
      have h2le : 2 ≤ padicValNat p n.natAbs := by omega
      have hdv := (padicValNat_dvd_iff_le hna).mpr h2le
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hna) hdv
      rw [sq] at this; omega
    exact_mod_cast this
  · have : ¬ p ∣ n.natAbs := fun h' => hd (Int.ofNat_dvd_left.mpr h')
    rw [padicValNat.eq_zero_of_not_dvd this]; simp

lemma l8_padicValRat_prod [Fact p.Prime] (s : Finset ℕ) (f : ℕ → ℚ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [prod_insert ha, sum_insert ha, padicValRat.mul (hf a (mem_insert_self a s))
        (prod_ne_zero_iff.mpr (fun i hi => hf i (mem_insert_of_mem hi))),
        ih (fun i hi => hf i (mem_insert_of_mem hi))]

/-- `v_p(D′(x_m)) ≤ n_c − 1` for `3p ≥ K`. -/
lemma l8_v_le [Fact p.Prime] (hp : p ≠ 2) (h3 : h + 1 ≤ 3 * p) {m : ℕ} (hm : m ≤ h) :
    padicValRat p (dPrime h m) ≤ (((clU h p (m % p)).card - 1 : ℕ) : ℤ) := by
  have hpp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hpp.two_le; omega
  have hpp3 : 3 * p ≤ p * p := Nat.mul_le_mul_right p hp3
  have hcard : (clU h p (m % p)).card - 1 = ((range (h + 1)).filter (fun l => l ≠ m ∧ l % p = m % p)).card := by
    have hmem : m ∈ clU h p (m % p) := mem_filter.mpr ⟨mem_range.mpr (by omega), rfl⟩
    rw [← card_erase_of_mem hmem]
    congr 1; ext l; simp only [clU, mem_erase, mem_filter]; tauto
  rw [hcard, ← sum_boole]
  unfold dPrime
  rw [l8_padicValRat_prod _ _ (fun l _ => by
    split_ifs with hl
    · exact one_ne_zero
    · exact sub_ne_zero.mpr (fun e => hl (l8_poleZ_inj e).symm))]
  refine sum_le_sum (fun l hl => ?_)
  have hl' : l ≤ h := Nat.lt_succ_iff.mp (mem_range.mp hl)
  by_cases hlm : l = m
  · simp [hlm]
  · simp only [hlm, ↓reduceIte]
    have e : ((poleZ h m : ℚ) - poleZ h l) = 2 * (((m : ℤ) - l : ℤ) : ℚ) := by unfold poleZ; push_cast; ring
    rw [e]
    refine (l8_padicValRat_two_mul_le hp (by omega) (by omega)).trans ?_
    have hiff : ((p : ℤ) ∣ (m : ℤ) - l) ↔ (l ≠ m ∧ l % p = m % p) := by
      rw [← Nat.modEq_iff_dvd]
      exact ⟨fun h' => ⟨hlm, h'⟩, fun h' => h'.2⟩
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact absurd (hiff.mp h1) h2
    · norm_num
    · exact le_rfl

lemma l8_wU_cases (h p m : ℕ) : wU h p m = 0 ∨ wU h p m = 2 := by
  unfold wU; split_ifs <;> simp

/-- Class sum `≤ classVal` for `3p ≥ K`: classes have `≤ 3` atoms and at most one of weight `0`. -/
lemma l8_class_le [Fact p.Prime] (hp : p ≠ 2) (hh : Even h) (h3 : h + 1 ≤ 3 * p) {c : ℕ} (hc : c < p) :
    ∑ m ∈ clU h p c, max ((clU h p (m % p)).card - 1) (wU h p m) ≤ classVal h p c := by
  have hpp : p.Prime := Fact.out
  have hp0 : 0 < p := hpp.pos
  obtain ⟨q, hq⟩ := hpp.odd_of_ne_two hp
  obtain ⟨J, hJ⟩ := hh
  set C := clU h p c with hCdef
  have hmemC : ∀ m ∈ C, m ≤ h ∧ m % p = c := fun m hm => by
    have := mem_filter.mp hm; exact ⟨Nat.lt_succ_iff.mp (mem_range.mp this.1), this.2⟩
  -- at most three atoms
  have hn3 : C.card ≤ 3 := by
    have hsub : C ⊆ (range 3).image (fun j => c + j * p) := by
      intro m hm
      obtain ⟨hmh, hmc⟩ := hmemC m hm
      refine mem_image.mpr ⟨m / p, mem_range.mpr ?_, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hp0]; omega
      · have := Nat.mod_add_div m p; rw [hmc] at this; rw [mul_comm]; omega
    exact (card_le_card hsub).trans (card_image_le.trans (by simp))
  -- at most one atom of weight 0
  set S := C.filter (fun m => wU h p m ≠ 0) with hS
  set Z := C.filter (fun m => ¬ wU h p m ≠ 0) with hZ
  have hz1 : Z.card ≤ 1 := by
    refine card_le_one.mpr (fun a ha b hb => ?_)
    obtain ⟨haC, ha0⟩ := mem_filter.mp ha
    obtain ⟨hbC, hb0⟩ := mem_filter.mp hb
    obtain ⟨hah, hac⟩ := hmemC a haC
    obtain ⟨hbh, hbc⟩ := hmemC b hbC
    have ha' : ¬ p < (poleZ h a).natAbs := by
      intro hlt; apply ha0; unfold wU; simp [hlt]
    have hb' : ¬ p < (poleZ h b).natAbs := by
      intro hlt; apply hb0; unfold wU; simp [hlt]
    unfold poleZ at ha' hb'
    have hdvd : (p : ℤ) ∣ (b : ℤ) - a := (Nat.modEq_iff_dvd).mp (hac.trans hbc.symm)
    obtain ⟨t, ht⟩ := hdvd
    have hJ2 : h / 2 = J := by omega
    rw [hJ2] at ha' hb'
    have hbd : |(b : ℤ) - a| ≤ p := by rw [abs_le]; constructor <;> omega
    have ht1 : t = 0 ∨ t = 1 ∨ t = -1 := by
      rw [ht, abs_mul, abs_of_pos (by exact_mod_cast hp0 : (0 : ℤ) < p)] at hbd
      have : |t| ≤ 1 := by
        by_contra hc'
        have : (2 : ℤ) ≤ |t| := by omega
        nlinarith
      rw [abs_le] at this; omega
    rcases ht1 with rfl | rfl | rfl
    · simp at ht; omega
    · omega
    · omega
  have hSZ : S.card + Z.card = C.card := card_filter_add_card_filter_not _
  -- the class value at `S`
  have hval : S.card * (C.card - S.card) + ∑ m ∈ S, wU h p m ≤ classVal h p c :=
    Finset.le_sup (f := fun S => S.card * ((clU h p c).card - S.card) + ∑ m ∈ S, wU h p m)
      (mem_powerset.mpr (filter_subset _ _))
  have hSw : ∑ m ∈ S, wU h p m = 2 * S.card := by
    rw [sum_congr rfl (fun m hm => ((l8_wU_cases h p m).resolve_left (mem_filter.mp hm).2)), sum_const,
      smul_eq_mul, mul_comm]
  -- the left-hand side
  have hL : ∑ m ∈ C, max ((clU h p (m % p)).card - 1) (wU h p m) = 2 * S.card + Z.card * (C.card - 1) := by
    rw [← sum_filter_add_sum_filter_not C (fun m => wU h p m ≠ 0)]
    have e1 : ∑ m ∈ S, max ((clU h p (m % p)).card - 1) (wU h p m) = 2 * S.card := by
      rw [sum_congr rfl (fun m hm => by
        obtain ⟨hmC, hw⟩ := mem_filter.mp hm
        rw [(hmemC m hmC).2, (l8_wU_cases h p m).resolve_left hw]), sum_const, smul_eq_mul]
      have hmax : max ((clU h p c).card - 1) 2 = 2 := by rw [← hCdef]; omega
      rw [hmax, mul_comm]
    have e2 : ∑ m ∈ Z, max ((clU h p (m % p)).card - 1) (wU h p m) = Z.card * (C.card - 1) := by
      rw [sum_congr rfl (fun m hm => by
        obtain ⟨hmC, hw⟩ := mem_filter.mp hm
        rw [(hmemC m hmC).2, not_not.mp hw]), sum_const, smul_eq_mul]
      have hmax : max ((clU h p c).card - 1) 0 = (clU h p c).card - 1 := by omega
      rw [hmax]
    rw [← hS, ← hZ, e1, e2]
  rw [hL]
  refine le_trans ?_ hval
  rw [hSw]
  have hz : C.card - S.card = Z.card := by omega
  rw [hz]
  interval_cases hzc : Z.card
  · simp
  · have : C.card - 1 = S.card := by omega
    rw [this]; ring_nf; omega

lemma l8_sum_le_AK [Fact p.Prime] (hp : p ≠ 2) (hh : Even h) (h3 : h + 1 ≤ 3 * p) :
    ∑ m ∈ range (h + 1), max ((clU h p (m % p)).card - 1) (wU h p m) ≤ AK h p := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  unfold AK
  rw [← sum_fiberwise_of_maps_to (g := fun m => m % p) (t := range p)
    (fun m _ => mem_range.mpr (Nat.mod_lt _ hp0))]
  exact sum_le_sum (fun c hc => l8_class_le hp hh h3 (mem_range.mp hc))

/-- **Lemma 8′ for `3p ≥ K`** (one level `e = 1` if `p < K`, none if `p ≥ K`): `|c_k|_p ≤ p^{A_K(p)}`. -/
theorem lemma8_one [Fact p.Prime] (hp : p ≠ 2) (hpm : ¬ p ∣ az) (hh : Even h) (h3 : h + 1 ≤ 3 * p) (k : ℕ) :
    padicNorm p ((Delta az h).coeff k) ≤ (p : ℚ) ^ AK h p := by
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  refine (padicNorm_Delta_crude hpm (fun m => (wU h p m : ℤ)) (fun m => by positivity)
    (fun m hm => l8_vGe_Psum h3 hm) hh k).trans ?_
  have hsum : (∑ m ∈ range (h + 1), max (padicValRat p (dPrime h m)) (wU h p m : ℤ)) ≤ (AK h p : ℤ) := by
    calc _ ≤ ∑ m ∈ range (h + 1), ((max ((clU h p (m % p)).card - 1) (wU h p m) : ℕ) : ℤ) :=
          sum_le_sum (fun m hm => by
            have := l8_v_le hp h3 (Nat.lt_succ_iff.mp (mem_range.mp hm))
            push_cast
            exact max_le_max this le_rfl)
      _ ≤ AK h p := by exact_mod_cast l8_sum_le_AK hp hh h3
  rw [← zpow_natCast]
  exact zpow_le_zpow_right₀ hp1 hsum

end Chi2U
