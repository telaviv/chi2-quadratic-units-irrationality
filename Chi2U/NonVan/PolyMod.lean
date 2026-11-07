/-
# The Lagrange products mod `ℓ` along `h = 3ℓ − 1` (PROOF_U §6, steps 3–4, polynomial part)

`h = 3ℓ − 1`, poles `x_m = 2m + 1 − 3ℓ ≡ 2m + 1 (mod ℓ)` (`poleZ_mod`). Integer versions `fZ`, `DZ` of `f_i`, `D` and
`PZ i j := (f_i f_j) div D ∈ ℤ[t]` (the polynomial part of `f_i f_j / D`).

Main result `deriv_PZ_mod`: at the progression points `t = 2γ + 1` (`γ < ℓ`),

    PZ_{ij}′(2γ+1) ≡ −[i ≡ j ≡ γ (mod ℓ)]   (mod ℓ).

Proof (in `(ZMod ℓ)[t]`): mod `ℓ` the poles of a class coincide, so `f̄_i f̄_j div D̄ = Π_{m ≠ i, j′}(t − x̄_m)` with
`j′ = j` for `i ≠ j` and `j′` another member of the class of `i` for `i = j` (`sq_divByMonic_of_eq`). The derivative of
a product at `ρ` is `Σ_k Π_{m ≠ k}(ρ − x̄_m)`; it vanishes when two factors vanish at `ρ`, and otherwise (the class
of `γ` minus `{i, j′}` is one point `q`) equals `U_γ = Π_{m ≢ γ}(2γ+1 − x̄_m) = (2^{ℓ−1} (ℓ−1)!)³ = −1`
(Fermat and Wilson, `Ubar_eq`).
-/
import Chi2U.NonVan.Prog

namespace Chi2U
namespace LP

open Polynomial Finset

/-! ### Generic products -/

section Generic

variable {A : Type*} [CommRing A]

lemma eval_deriv_prod (T : Finset ℕ) (a : ℕ → A) (ρ : A) :
    (derivative (∏ m ∈ T, (X - C (a m)))).eval ρ = ∑ k ∈ T, ∏ m ∈ T.erase k, (ρ - a m) := by
  rw [derivative_prod_finset, eval_finset_sum]
  refine sum_congr rfl (fun k _ => ?_)
  simp [eval_prod]

lemma eval_deriv_prod_one (T : Finset ℕ) (a : ℕ → A) (ρ : A) {q : ℕ} (hq : q ∈ T) (haq : a q = ρ) :
    (derivative (∏ m ∈ T, (X - C (a m)))).eval ρ = ∏ m ∈ T.erase q, (ρ - a m) := by
  rw [eval_deriv_prod, sum_eq_single q]
  · intro k _ hkq
    exact prod_eq_zero (mem_erase.mpr ⟨Ne.symm hkq, hq⟩) (by rw [haq, sub_self])
  · intro h; exact absurd hq h

lemma eval_deriv_prod_two (T : Finset ℕ) (a : ℕ → A) (ρ : A) {q q' : ℕ} (hq : q ∈ T) (hq' : q' ∈ T)
    (hne : q ≠ q') (haq : a q = ρ) (haq' : a q' = ρ) :
    (derivative (∏ m ∈ T, (X - C (a m)))).eval ρ = 0 := by
  rw [eval_deriv_prod_one T a ρ hq haq]
  exact prod_eq_zero (mem_erase.mpr ⟨Ne.symm hne, hq'⟩) (by rw [haq', sub_self])

lemma prod_erase_mul (S : Finset ℕ) (a : ℕ → A) {i : ℕ} (hi : i ∈ S) :
    ∏ m ∈ S, (X - C (a m)) = (X - C (a i)) * ∏ m ∈ S.erase i, (X - C (a m)) :=
  (mul_prod_erase S _ hi).symm

lemma monic_prod_X_sub (S : Finset ℕ) (a : ℕ → A) : (∏ m ∈ S, (X - C (a m))).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

/-- Off-diagonal: `f_i f_j = D · Π_{m ≠ i,j}`. -/
lemma offdiag_divByMonic [Nontrivial A] (S : Finset ℕ) (a : ℕ → A) {i j : ℕ} (hi : i ∈ S) (hj : j ∈ S)
    (hij : i ≠ j) :
    ((∏ m ∈ S.erase i, (X - C (a m))) * ∏ m ∈ S.erase j, (X - C (a m))) /ₘ ∏ m ∈ S, (X - C (a m)) =
      ∏ m ∈ (S.erase i).erase j, (X - C (a m)) := by
  have e1 := prod_erase_mul (S.erase i) a (mem_erase.mpr ⟨Ne.symm hij, hj⟩)
  have e2 := prod_erase_mul (S.erase j) a (mem_erase.mpr ⟨hij, hi⟩)
  have e3 := prod_erase_mul S a hi
  rw [erase_right_comm] at e2
  have : (∏ m ∈ S.erase i, (X - C (a m))) * ∏ m ∈ S.erase j, (X - C (a m)) =
      (∏ m ∈ S, (X - C (a m))) * ∏ m ∈ (S.erase i).erase j, (X - C (a m)) := by
    rw [e3, e2, e1]; ring
  rw [this]
  exact mul_divByMonic_cancel_left _ (monic_prod_X_sub S a)

/-- Diagonal with a colliding pole: if `a i = a i'` (`i ≠ i'`), then `f_i² = D · Π_{m ≠ i,i'}`. -/
lemma sq_divByMonic_of_eq [Nontrivial A] (S : Finset ℕ) (a : ℕ → A) {i i' : ℕ} (hi : i ∈ S) (hi' : i' ∈ S)
    (hii' : i ≠ i') (ha : a i = a i') :
    ((∏ m ∈ S.erase i, (X - C (a m))) * ∏ m ∈ S.erase i, (X - C (a m))) /ₘ ∏ m ∈ S, (X - C (a m)) =
      ∏ m ∈ (S.erase i).erase i', (X - C (a m)) := by
  have e1 := prod_erase_mul (S.erase i) a (mem_erase.mpr ⟨Ne.symm hii', hi'⟩)
  have e3 := prod_erase_mul S a hi
  rw [← ha] at e1
  have : (∏ m ∈ S.erase i, (X - C (a m))) * ∏ m ∈ S.erase i, (X - C (a m)) =
      (∏ m ∈ S, (X - C (a m))) * ∏ m ∈ (S.erase i).erase i', (X - C (a m)) := by
    rw [e3]; nth_rewrite 1 [e1]; ring
  rw [this]
  exact mul_divByMonic_cancel_left _ (monic_prod_X_sub S a)

end Generic

/-! ### Classes mod `ℓ` in `range (3ℓ)` -/

section Classes

variable {ℓ : ℕ}

lemma add_mul_mod_eq {γ k : ℕ} (hγ : γ < ℓ) : (γ + k * ℓ) % ℓ = γ := by
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hγ]

lemma class_cases {m γ : ℕ} (hm : m < 3 * ℓ) (h : m % ℓ = γ) : m = γ ∨ m = γ + ℓ ∨ m = γ + 2 * ℓ := by
  have hd := Nat.div_add_mod m ℓ
  have hpos : 0 < ℓ := by rcases Nat.eq_zero_or_pos ℓ with h0 | h0 <;> [simp [h0] at hm; exact h0]
  have h3 : m / ℓ < 3 := (Nat.div_lt_iff_lt_mul hpos).mpr (by linarith)
  rw [h] at hd
  interval_cases hq : m / ℓ <;> omega

lemma mod_of_class {γ : ℕ} (hγ : γ < ℓ) : γ % ℓ = γ ∧ (γ + ℓ) % ℓ = γ ∧ (γ + 2 * ℓ) % ℓ = γ := by
  refine ⟨Nat.mod_eq_of_lt hγ, ?_, ?_⟩
  · simpa using add_mul_mod_eq (k := 1) hγ
  · exact add_mul_mod_eq (k := 2) hγ

/-- Two members of the class of `γ` avoid `{i, j}` unless both `i, j` are in it. -/
lemma two_in_class {i j γ : ℕ} (hγ : γ < ℓ) (hi3 : i < 3 * ℓ) (hj3 : j < 3 * ℓ)
    (h : ¬ (i % ℓ = γ ∧ j % ℓ = γ)) :
    ∃ m₁ m₂, m₁ ≠ m₂ ∧ m₁ < 3 * ℓ ∧ m₂ < 3 * ℓ ∧ m₁ ≠ i ∧ m₁ ≠ j ∧ m₂ ≠ i ∧ m₂ ≠ j ∧
      m₁ % ℓ = γ ∧ m₂ % ℓ = γ := by
  obtain ⟨h0, h1, h2⟩ := mod_of_class hγ
  have nm : ∀ {m n : ℕ}, m % ℓ = γ → n % ℓ ≠ γ → m ≠ n := fun hm hn e => hn (e ▸ hm)
  by_cases hi : i % ℓ = γ
  · have hj : j % ℓ ≠ γ := fun hj => h ⟨hi, hj⟩
    rcases class_cases hi3 hi with e | e | e
    · exact ⟨γ + ℓ, γ + 2 * ℓ, by omega, by omega, by omega, by omega, nm h1 hj, by omega, nm h2 hj, h1, h2⟩
    · exact ⟨γ, γ + 2 * ℓ, by omega, by omega, by omega, by omega, nm h0 hj, by omega, nm h2 hj, h0, h2⟩
    · exact ⟨γ, γ + ℓ, by omega, by omega, by omega, by omega, nm h0 hj, by omega, nm h1 hj, h0, h1⟩
  · by_cases hj : j % ℓ = γ
    · rcases class_cases hj3 hj with e | e | e
      · exact ⟨γ + ℓ, γ + 2 * ℓ, by omega, by omega, by omega, nm h1 hi, by omega, nm h2 hi, by omega, h1, h2⟩
      · exact ⟨γ, γ + 2 * ℓ, by omega, by omega, by omega, nm h0 hi, by omega, nm h2 hi, by omega, h0, h2⟩
      · exact ⟨γ, γ + ℓ, by omega, by omega, by omega, nm h0 hi, by omega, nm h1 hi, by omega, h0, h1⟩
    · exact ⟨γ, γ + ℓ, by omega, by omega, by omega, nm h0 hi, nm h0 hj, nm h1 hi, nm h1 hj, h0, h1⟩

end Classes

/-! ### The poles mod `ℓ` -/

section Poles

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma poleZ_eq (hodd : Odd ℓ) (m : ℕ) : poleZ (3 * ℓ - 1) m = 2 * (m : ℤ) + 1 - 3 * ℓ := by
  obtain ⟨t, rfl⟩ := hodd
  unfold poleZ
  have : (3 * (2 * t + 1) - 1) / 2 = 3 * t + 1 := by omega
  rw [this]; push_cast; ring

lemma two_ne_zero_ZMod (hℓ2 : ℓ ≠ 2) : (2 : ZMod ℓ) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_two).mp this)

lemma abar (hℓ2 : ℓ ≠ 2) (m : ℕ) : ((poleZ (3 * ℓ - 1) m : ℤ) : ZMod ℓ) = 2 * (m : ZMod ℓ) + 1 := by
  rw [poleZ_eq (hℓ.out.odd_of_ne_two hℓ2)]; push_cast; rw [ZMod.natCast_self]; ring

lemma abar_of_mod (hℓ2 : ℓ ≠ 2) {m γ : ℕ} (hγ : γ < ℓ) (hm : m % ℓ = γ) :
    ((poleZ (3 * ℓ - 1) m : ℤ) : ZMod ℓ) = 2 * (γ : ZMod ℓ) + 1 := by
  rw [abar hℓ2, (ZMod.natCast_eq_natCast_iff' m γ ℓ).mpr (by rw [hm, Nat.mod_eq_of_lt hγ])]

lemma prod_sub_ne {γ : ℕ} (hγ : γ < ℓ) : ∏ m ∈ (range ℓ).erase γ, ((γ : ZMod ℓ) - m) = -1 := by
  rw [← ZMod.prod_Ico_one_prime ℓ]
  refine prod_nbij' (fun m => if m < γ then γ - m else γ + ℓ - m)
    (fun k => if k ≤ γ then γ - k else γ + ℓ - k) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    simp only [mem_erase, mem_range] at hm
    simp only [mem_Ico]
    split_ifs <;> omega
  · intro k hk
    simp only [mem_Ico] at hk
    simp only [mem_erase, mem_range]
    split_ifs <;> omega
  · intro m hm
    simp only [mem_erase, mem_range] at hm
    split_ifs <;> omega
  · intro k hk
    simp only [mem_Ico] at hk
    split_ifs <;> omega
  · intro m hm
    simp only [mem_erase, mem_range] at hm
    split_ifs with h
    · rw [Nat.cast_sub h.le]
    · rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self]; ring

/-- `U_γ = Π_{m ≢ γ}(2γ + 1 − x̄_m) = −1`. -/
lemma Ubar_eq (hℓ2 : ℓ ≠ 2) {γ : ℕ} (hγ : γ < ℓ) :
    ∏ m ∈ (range (3 * ℓ)).filter (fun m => m % ℓ ≠ γ),
      (2 * (γ : ZMod ℓ) + 1 - ((poleZ (3 * ℓ - 1) m : ℤ) : ZMod ℓ)) = -1 := by
  have hfac : ∀ m, (2 * (γ : ZMod ℓ) + 1 - ((poleZ (3 * ℓ - 1) m : ℤ) : ZMod ℓ)) =
      2 * ((γ : ZMod ℓ) - m) := by intro m; rw [abar hℓ2]; ring
  simp_rw [hfac]
  rw [prod_filter]
  set g : ℕ → ZMod ℓ := fun m => if m % ℓ ≠ γ then 2 * ((γ : ZMod ℓ) - m) else 1 with hg
  show ∏ m ∈ range (3 * ℓ), g m = -1
  have hshift : ∀ m, g (ℓ + m) = g m := by
    intro m; simp only [hg, Nat.add_mod_left, Nat.cast_add, ZMod.natCast_self, zero_add]
  have hbase : ∏ m ∈ range ℓ, g m = -1 := by
    have : ∏ m ∈ range ℓ, g m = ∏ m ∈ range ℓ, if m ≠ γ then 2 * ((γ : ZMod ℓ) - m) else 1 := by
      refine prod_congr rfl (fun m hm => ?_)
      simp only [hg, Nat.mod_eq_of_lt (mem_range.mp hm)]
    rw [this, ← prod_filter, filter_ne', prod_mul_distrib, prod_const, prod_sub_ne hγ,
      card_erase_of_mem (mem_range.mpr hγ), card_range,
      ZMod.pow_card_sub_one_eq_one (two_ne_zero_ZMod hℓ2)]
    ring
  rw [show 3 * ℓ = ℓ + (ℓ + ℓ) by ring, prod_range_add, prod_range_add]
  simp only [hshift, hbase]
  norm_num

end Poles

/-! ### The integer polynomials and their reduction -/

/-- `f_i ∈ ℤ[t]`. -/
noncomputable def fZ (h i : ℕ) : ℤ[X] := ∏ m ∈ (range (h + 1)).erase i, (X - C (poleZ h m))

/-- `D ∈ ℤ[t]`. -/
noncomputable def DZ (h : ℕ) : ℤ[X] := ∏ m ∈ range (h + 1), (X - C (poleZ h m))

/-- `(f_i f_j) div D ∈ ℤ[t]`. -/
noncomputable def PZ (h i j : ℕ) : ℤ[X] := (fZ h i * fZ h j) /ₘ DZ h

lemma DZ_monic (h : ℕ) : (DZ h).Monic := monic_prod_X_sub _ _

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem deriv_T_val (hℓ2 : ℓ ≠ 2) {i j γ : ℕ} (hi : i < 3 * ℓ) (hj : j < 3 * ℓ) (hij : i ≠ j) (hγ : γ < ℓ) :
    (derivative (∏ m ∈ ((range (3 * ℓ)).erase i).erase j,
      (X - C ((poleZ (3 * ℓ - 1) m : ℤ) : ZMod ℓ)))).eval (2 * (γ : ZMod ℓ) + 1) =
      if i % ℓ = γ ∧ j % ℓ = γ then -1 else 0 := by
  obtain ⟨h0, h1, h2⟩ := mod_of_class hγ
  split_ifs with h
  · obtain ⟨hiγ, hjγ⟩ := h
    have ci := class_cases hi hiγ
    have cj := class_cases hj hjγ
    obtain ⟨q, hq⟩ : ∃ q, q = 3 * γ + 3 * ℓ - i - j := ⟨_, rfl⟩
    have cq : q = γ ∨ q = γ + ℓ ∨ q = γ + 2 * ℓ := by omega
    have hqγ : q % ℓ = γ := by rcases cq with e | e | e <;> rw [e] <;> assumption
    have hqT : q ∈ ((range (3 * ℓ)).erase i).erase j := by
      simp only [mem_erase, mem_range]; omega
    rw [eval_deriv_prod_one _ (fun m => ((poleZ (3 * ℓ - 1) m : ℤ) : ZMod ℓ)) _ hqT (abar_of_mod hℓ2 hγ hqγ)]
    have hset : (((range (3 * ℓ)).erase i).erase j).erase q =
        (range (3 * ℓ)).filter (fun m => m % ℓ ≠ γ) := by
      ext m
      simp only [mem_erase, mem_range, mem_filter]
      constructor
      · rintro ⟨hmq, hmj, hmi, hm⟩
        refine ⟨hm, fun hmγ => ?_⟩
        have := class_cases hm hmγ
        clear h0 h1 h2 hiγ hjγ hqγ hmγ hqT
        omega
      · rintro ⟨hm, hmγ⟩
        exact ⟨fun e => hmγ (by rw [e]; exact hqγ), fun e => hmγ (by rw [e]; exact hjγ),
          fun e => hmγ (by rw [e]; exact hiγ), hm⟩
    rw [hset, Ubar_eq hℓ2 hγ]
  · obtain ⟨m₁, m₂, hne, hm₁, hm₂, h1i, h1j, h2i, h2j, hm₁γ, hm₂γ⟩ := two_in_class hγ hi hj h
    exact eval_deriv_prod_two _ (fun m => ((poleZ (3 * ℓ - 1) m : ℤ) : ZMod ℓ)) _ (by simp only [mem_erase, mem_range]; omega)
      (by simp only [mem_erase, mem_range]; omega) hne (abar_of_mod hℓ2 hγ hm₁γ) (abar_of_mod hℓ2 hγ hm₂γ)

/-- **The polynomial part mod `ℓ`**: `PZ_{ij}′(2γ+1) ≡ −[i ≡ j ≡ γ]`. -/
theorem deriv_PZ_mod (hℓ2 : ℓ ≠ 2) {i j γ : ℕ} (hi : i < 3 * ℓ) (hj : j < 3 * ℓ) (hγ : γ < ℓ) :
    (((derivative (PZ (3 * ℓ - 1) i j)).eval (2 * (γ : ℤ) + 1) : ℤ) : ZMod ℓ) =
      if i % ℓ = γ ∧ j % ℓ = γ then -1 else 0 := by
  have h3 : 3 * ℓ - 1 + 1 = 3 * ℓ := by have := hℓ.out.pos; omega
  have key : ∀ (P : ℤ[X]) (n : ℤ), ((P.eval n : ℤ) : ZMod ℓ) = (P.map (Int.castRingHom (ZMod ℓ))).eval (n : ZMod ℓ) :=
    fun P n => by
      rw [eval_map, show ((n : ZMod ℓ)) = Int.castRingHom (ZMod ℓ) n from rfl, eval₂_hom]; rfl
  rw [key, ← derivative_map, PZ,
    map_divByMonic _ (DZ_monic _), Polynomial.map_mul]
  simp only [fZ, DZ, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C, Int.coe_castRingHom, h3]
  push_cast
  by_cases hij : i = j
  · subst hij
    set i' := if i + ℓ < 3 * ℓ then i + ℓ else i - 2 * ℓ with hi'
    have hi'3 : i' < 3 * ℓ := by rw [hi']; split_ifs <;> omega
    have hii' : i ≠ i' := by have := hℓ.out.pos; rw [hi']; split_ifs <;> omega
    have hmod : i' % ℓ = i % ℓ := by
      rw [hi']; split_ifs with hc
      · exact Nat.add_mod_right i ℓ
      · have := Nat.add_mul_mod_self_right (i - 2 * ℓ) 2 ℓ
        rw [show i - 2 * ℓ + 2 * ℓ = i by omega] at this
        exact this.symm
    have ha : ((poleZ (3 * ℓ - 1) i : ℤ) : ZMod ℓ) = ((poleZ (3 * ℓ - 1) i' : ℤ) : ZMod ℓ) := by
      rw [abar hℓ2, abar hℓ2, (ZMod.natCast_eq_natCast_iff' i i' ℓ).mpr hmod.symm]
    rw [sq_divByMonic_of_eq _ _ (mem_range.mpr hi) (mem_range.mpr hi'3) hii' ha,
      deriv_T_val hℓ2 hi hi'3 hii' hγ, hmod]
  · rw [offdiag_divByMonic _ _ (mem_range.mpr hi) (mem_range.mpr hj) hij, deriv_T_val hℓ2 hi hj hij hγ]

end LP
end Chi2U
