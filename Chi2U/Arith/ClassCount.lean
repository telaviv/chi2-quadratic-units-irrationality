/-
# Lemma 8A′: the class count `A_K(d) = 3(K − d)` (PROOF_U §3.2)

For `K = h + 1` odd and `d` odd with `K/3 ≤ d < K`: `w_d(m) = 0` iff `|m − J| ≤ (d−1)/2`, a block of `d`
consecutive atoms, so every class has exactly one weight-0 atom and the others have weight 2. With `n ≤ 3` atoms
the class value is `V(1) = 0, V(2) = 3, V(3) = 6`; counting classes gives `3(K − d)`. For `d ≥ K` every class has
at most one atom and `|x_m| ≤ h < d`, so `A_K(d) = 0`.

Lean proof.
* `classVal_eq_of`: a class with `n ≤ 3` atoms, one atom `z` of weight `0` and all others of weight `2` has value
  `3(n − 1)`. Upper bound: `Σ_S w ≤ 2·|S ∖ {z}| ≤ 2 min(|S|, n − 1)` and `s(n − s) + 2 min(s, n − 1) ≤ 3(n − 1)` for
  `s ≤ n ≤ 3` (case check); lower bound: `S = C ∖ {z}`.
* `wU_eq_zero_iff`: for `h = 2J`, `d = 2κ + 1`, `w_d(m) = 0 ↔ J − κ ≤ m ≤ J + κ`.
* For each `c < d` the block `[J − κ, J + κ]` contains exactly one `z ≡ c (mod d)` (write `J − κ = qd + r`); the class
  has `≤ 3` atoms since `h < 3d`; `Σ_c n_c = K` (fibres of `m ↦ m % d`), so `A_K(d) = Σ_c 3(n_c − 1) = 3(K − d)`.
* `AK_eq_zero`: for `d ≥ K` classes have `≤ 1` atom and all weights vanish (`|x_m| ≤ h < d`).
-/
import Chi2U.Arith.Defs

namespace Chi2U

open Finset

lemma wU_le_two (h d m : ℕ) : wU h d m ≤ 2 := by
  unfold wU; split_ifs <;> omega

lemma wU_eq_zero_or_two (h d m : ℕ) : wU h d m = 0 ∨ wU h d m = 2 := by
  unfold wU; split_ifs <;> simp

/-- Weight-0 atoms: for `h = 2J`, `d = 2κ + 1`, `w_d(m) = 0 ↔ J ≤ m + κ ∧ m ≤ J + κ`. -/
lemma wU_eq_zero_iff {h d m J κ : ℕ} (hJ : h = 2 * J) (hκ : d = 2 * κ + 1) :
    wU h d m = 0 ↔ (J ≤ m + κ ∧ m ≤ J + κ) := by
  subst hJ hκ
  have hJ2 : 2 * J / 2 = J := by omega
  unfold wU poleZ
  rw [hJ2]
  split_ifs with H
  · simp only [false_iff, not_and_or, not_le]
    omega
  · simp only [true_iff]
    omega

/-- The class value of a class with `n ≤ 3` atoms, exactly one of weight `0`, the others of weight `2`. -/
lemma classVal_eq_of {h d c z : ℕ} (hz : z ∈ clU h d c) (hwz : wU h d z = 0)
    (hw : ∀ m ∈ clU h d c, m ≠ z → wU h d m = 2) (hn : (clU h d c).card ≤ 3) :
    classVal h d c = 3 * ((clU h d c).card - 1) := by
  have hn1 : 1 ≤ (clU h d c).card := Finset.card_pos.2 ⟨z, hz⟩
  have hCe : (clU h d c |>.erase z).card = (clU h d c).card - 1 := Finset.card_erase_of_mem hz
  unfold classVal
  apply le_antisymm
  · apply Finset.sup_le
    intro S hS
    rw [Finset.mem_powerset] at hS
    have hsum : ∑ m ∈ S, wU h d m ≤ 2 * (S.erase z).card := by
      rw [← Finset.sum_erase S hwz]
      calc ∑ m ∈ S.erase z, wU h d m ≤ ∑ _m ∈ S.erase z, 2 :=
            Finset.sum_le_sum (fun m _ => wU_le_two h d m)
        _ = 2 * (S.erase z).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have he1 : (S.erase z).card ≤ S.card := Finset.card_erase_le
    have he2 : (S.erase z).card ≤ (clU h d c).card - 1 := by
      rw [← hCe]; exact Finset.card_le_card (Finset.erase_subset_erase z hS)
    have hs : S.card ≤ (clU h d c).card := Finset.card_le_card hS
    generalize (clU h d c).card = n at *
    generalize S.card = s at *
    generalize ∑ m ∈ S, wU h d m = W at *
    generalize (S.erase z).card = e at *
    interval_cases n <;> interval_cases s <;> omega
  · have hmem : (clU h d c).erase z ∈ (clU h d c).powerset :=
      Finset.mem_powerset.2 (Finset.erase_subset z _)
    refine le_trans ?_ (Finset.le_sup (f := fun S => S.card * ((clU h d c).card - S.card) +
      ∑ m ∈ S, wU h d m) hmem)
    have hsum : ∑ m ∈ (clU h d c).erase z, wU h d m = 2 * ((clU h d c).card - 1) := by
      rw [Finset.sum_congr rfl (g := fun _ => 2) (fun m hm => hw m (Finset.mem_of_mem_erase hm)
        (Finset.ne_of_mem_erase hm)), Finset.sum_const, smul_eq_mul, hCe, mul_comm]
    change 3 * ((clU h d c).card - 1) ≤ ((clU h d c).erase z).card * ((clU h d c).card -
      ((clU h d c).erase z).card) + ∑ m ∈ (clU h d c).erase z, wU h d m
    rw [hsum, hCe, show (clU h d c).card - ((clU h d c).card - 1) = 1 by omega, mul_one]
    omega

/-- Membership in a class. -/
lemma mem_clU {h d c m : ℕ} : m ∈ clU h d c ↔ m ≤ h ∧ m % d = c := by
  unfold clU; rw [Finset.mem_filter, Finset.mem_range]; omega

/-- Classes have at most three atoms when `h < 3d`. -/
lemma card_clU_le_three {h d c : ℕ} (hd : 0 < d) (h3 : h < 3 * d) : (clU h d c).card ≤ 3 := by
  refine le_trans (Finset.card_le_card (t := {c, c + d, c + 2 * d}) ?_) Finset.card_le_three
  intro m hm
  rw [mem_clU] at hm
  have hq : m / d < 3 := (Nat.div_lt_iff_lt_mul hd).2 (by rw [mul_comm]; omega)
  have hdm := Nat.div_add_mod m d
  rw [hm.2] at hdm
  simp only [Finset.mem_insert, Finset.mem_singleton]
  interval_cases hq' : m / d <;> omega

/-- Two atoms of the same class at distance `< d` coincide. -/
lemma eq_of_mod_eq_of_dist {d m z : ℕ} (hmz : m % d = z % d) (h1 : m < z + d) (h2 : z < m + d) :
    m = z := by
  have hm := Nat.div_add_mod m d
  have hz := Nat.div_add_mod z d
  rcases lt_trichotomy (m / d) (z / d) with H | H | H
  · have := Nat.mul_le_mul_left d (show m / d + 1 ≤ z / d by omega)
    rw [mul_add, mul_one] at this; omega
  · rw [H] at hm; omega
  · have := Nat.mul_le_mul_left d (show z / d + 1 ≤ m / d by omega)
    rw [mul_add, mul_one] at this; omega

/-- **Lemma 8A′.** -/
theorem AK_eq {h d : ℕ} (hh : Even h) (hd : Odd d) (h3 : h + 1 ≤ 3 * d) (hdK : d < h + 1) :
    AK h d = 3 * (h + 1 - d) := by
  obtain ⟨J, hJ⟩ := hh
  obtain ⟨κ, hκ⟩ := hd
  have hJ' : h = 2 * J := by omega
  have hd0 : 0 < d := by omega
  -- each class has value `3(n_c − 1)` and at least one atom
  have hcls : ∀ c ∈ range d, classVal h d c = 3 * ((clU h d c).card - 1) ∧
      1 ≤ (clU h d c).card := by
    intro c hc
    rw [Finset.mem_range] at hc
    -- the weight-0 atom of the class: `J − κ = q d + r`
    have ha := Nat.div_add_mod (J - κ) d
    have hr := Nat.mod_lt (J - κ) hd0
    obtain ⟨z, hzlo, hzhi, hzc⟩ : ∃ z, J - κ ≤ z ∧ z ≤ J + κ ∧ z % d = c := by
      rcases le_or_gt ((J - κ) % d) c with H | H
      · refine ⟨d * ((J - κ) / d) + c, by omega, by omega, ?_⟩
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc]
      · refine ⟨d * ((J - κ) / d + 1) + c, by rw [mul_add]; omega, by rw [mul_add]; omega, ?_⟩
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc]
    have hz : z ∈ clU h d c := mem_clU.2 ⟨by omega, hzc⟩
    have hwz : wU h d z = 0 := (wU_eq_zero_iff hJ' hκ).2 ⟨by omega, by omega⟩
    have hw : ∀ m ∈ clU h d c, m ≠ z → wU h d m = 2 := by
      intro m hm hne
      rcases wU_eq_zero_or_two h d m with H | H
      · exfalso
        rw [wU_eq_zero_iff hJ' hκ] at H
        rw [mem_clU] at hm
        exact hne (eq_of_mod_eq_of_dist (by rw [hm.2, hzc]) (by omega) (by omega))
      · exact H
    exact ⟨classVal_eq_of hz hwz hw (card_clU_le_three hd0 (by omega)),
      Finset.card_pos.2 ⟨z, hz⟩⟩
  -- the classes partition the atoms
  have hpart : ∑ c ∈ range d, (clU h d c).card = h + 1 := by
    have := Finset.card_eq_sum_card_fiberwise (s := range (h + 1)) (t := range d) (f := fun m => m % d)
      (fun m _ => Finset.mem_range.2 (Nat.mod_lt m hd0))
    rw [Finset.card_range] at this
    exact this.symm
  have hsub : ∑ c ∈ range d, ((clU h d c).card - 1) + d = h + 1 := by
    have e : ∑ c ∈ range d, ((clU h d c).card - 1 + 1) = ∑ c ∈ range d, (clU h d c).card :=
      Finset.sum_congr rfl (fun c hc => by have := (hcls c hc).2; omega)
    rw [← hpart, ← e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  unfold AK
  rw [Finset.sum_congr rfl (fun c hc => (hcls c hc).1), ← Finset.mul_sum]
  omega

/-- Levels `d ≥ K` contribute nothing. -/
theorem AK_eq_zero {h d : ℕ} (hd : h + 1 ≤ d) : AK h d = 0 := by
  unfold AK
  apply Finset.sum_eq_zero
  intro c _
  have hw : ∀ m ∈ clU h d c, wU h d m = 0 := by
    intro m hm
    rw [mem_clU] at hm
    have h2 : h / 2 ≤ h := Nat.div_le_self h 2
    unfold wU poleZ
    split_ifs with H <;> omega
  have hcard : (clU h d c).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [mem_clU] at ha hb
    rw [Nat.mod_eq_of_lt (by omega)] at ha hb
    omega
  unfold classVal
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro S hS
  rw [Finset.mem_powerset] at hS
  have hs : S.card ≤ (clU h d c).card := Finset.card_le_card hS
  rw [Finset.sum_eq_zero (fun m hm => hw m (hS hm))]
  have : S.card * ((clU h d c).card - S.card) = 0 := by
    rcases Nat.eq_zero_or_pos S.card with H | H
    · rw [H, zero_mul]
    · rw [show (clU h d c).card - S.card = 0 by omega, mul_zero]
  omega

end Chi2U
