/-
# Lemma S: the counting (PROOF_U §3.2, split over levels and classes)

For a set `S` of atoms (`S ⊆ {0, …, h}`), the cost of the term of the expansion indexed by `S` is
`Σ_{m ∈ S} Σ_{l ∉ S} v_p(x_m − x_l) + Σ_{m ∈ S} wT(m)`; split over levels `d = p^e` and classes mod `d`, a class
`C_c` contributes `|S_c|(n_c − |S_c|) + Σ_{m ∈ S_c} w_d(m) ≤ classVal`, so the cost is `≤ Σ_e A_K(p^e)`
(`cost_le`). Also: `sum_pairs_split` (the cross term `v(cross(S)) = Σ_{m∈S} v(D′(x_m)) − 2 v(Vand(x_S))`) and
`sum_trunc_sq` (`Σ_{i<2J} (i − J)₊ + Σ_{j<2J} (j − J − 1)₊ = (J − 1)²`).
-/
import Chi2U.V.SVal

namespace Chi2U
namespace V
namespace LS

open Finset

/-- One level: `Σ_{m∈S} #{l ∉ S : l ≡ m (d)} + Σ_{m∈S} w_d(m) ≤ A_K(d)`. -/
lemma level_count {h d : ℕ} (hd : 0 < d) (S : Finset ℕ) (hS : S ⊆ range (h + 1)) :
    ∑ m ∈ S, ((range (h + 1) \ S).filter (fun l => m % d = l % d)).card + ∑ m ∈ S, wU h d m ≤ AK h d := by
  rw [← sum_add_distrib]
  unfold AK
  rw [← sum_fiberwise_of_maps_to (s := S) (t := range d) (g := (· % d))
    (fun m _ => mem_range.mpr (Nat.mod_lt _ hd))]
  refine sum_le_sum (fun c _ => ?_)
  set Sc := S.filter (fun m => m % d = c) with hSc
  have hScC : Sc ⊆ clU h d c := fun m hm => by
    obtain ⟨hmS, hmc⟩ := mem_filter.mp hm
    exact mem_clU.mpr ⟨Nat.lt_succ_iff.mp (mem_range.mp (hS hmS)), hmc⟩
  have hcard : ∀ m ∈ Sc, ((range (h + 1) \ S).filter (fun l => m % d = l % d)).card =
      (clU h d c).card - Sc.card := by
    intro m hm
    have hmc := (mem_filter.mp hm).2
    rw [← card_sdiff_of_subset hScC]
    congr 1
    ext l
    simp only [mem_filter, mem_sdiff, mem_range, mem_clU, hSc]
    constructor
    · rintro ⟨⟨hl, hlS⟩, hml⟩; exact ⟨⟨by omega, by omega⟩, fun h' => hlS h'.1⟩
    · rintro ⟨⟨hl, hlc⟩, hlS⟩; exact ⟨⟨by omega, fun h' => hlS ⟨h', hlc⟩⟩, by omega⟩
  rw [sum_add_distrib, sum_congr rfl hcard, sum_const, smul_eq_mul]
  exact Finset.le_sup (f := fun S => S.card * ((clU h d c).card - S.card) + ∑ m ∈ S, wU h d m)
    (mem_powerset.mpr hScC)

/-- All levels: `Σ_{m∈S} Σ_{l∉S} vmult(m, l) + Σ_{m∈S} wT(m) ≤ Σ_e A_K(p^e)`. -/
lemma cost_le {h p : ℕ} (hp : 0 < p) (S : Finset ℕ) (hS : S ⊆ range (h + 1)) :
    ∑ m ∈ S, ∑ l ∈ range (h + 1) \ S, vmult h p m l + ∑ m ∈ S, wT h p m ≤
      ∑ e ∈ levelsV h p, AK h (p ^ e) := by
  have e1 : ∑ m ∈ S, ∑ l ∈ range (h + 1) \ S, vmult h p m l =
      ∑ e ∈ levelsV h p, ∑ m ∈ S, ((range (h + 1) \ S).filter (fun l => m % p ^ e = l % p ^ e)).card := by
    simp only [vmult, card_filter]
    rw [sum_comm (s := levelsV h p)]
    refine sum_congr rfl (fun m _ => ?_)
    rw [sum_comm]
  have e2 : ∑ m ∈ S, wT h p m = ∑ e ∈ levelsV h p, ∑ m ∈ S, wU h (p ^ e) m := by
    simp only [wT]; rw [sum_comm]
  rw [e1, e2, ← sum_add_distrib]
  exact sum_le_sum (fun e _ => level_count (pow_pos hp e) S hS)

/-- The cross term: for symmetric `v`, `Σ_{m∈S} Σ_{l ∈ U, l ≠ m} v = Σ_{m∈S} Σ_{l ∈ U∖S} v + 2 Σ_{a∈S} Σ_{k∈S, k<a} v`. -/
lemma sum_pairs_split (U S : Finset ℕ) (hS : S ⊆ U) (v : ℕ → ℕ → ℕ) (hv : ∀ a b, v a b = v b a) :
    ∑ m ∈ S, ∑ l ∈ U, (if l = m then 0 else v m l) =
      ∑ m ∈ S, ∑ l ∈ U \ S, v m l + 2 * ∑ a ∈ S, ∑ k ∈ S.filter (· < a), v a k := by
  have h1 : ∀ m ∈ S, ∑ l ∈ U, (if l = m then 0 else v m l) =
      ∑ l ∈ U \ S, v m l + (∑ l ∈ S, (if l < m then v m l else 0) + ∑ l ∈ S, (if m < l then v m l else 0)) := by
    intro m hm
    rw [← sum_sdiff hS, ← sum_add_distrib]
    congr 1
    · exact sum_congr rfl (fun l hl => by rw [if_neg (by rintro rfl; exact (mem_sdiff.mp hl).2 hm)])
    · refine sum_congr rfl (fun l _ => ?_)
      rcases lt_trichotomy l m with hlm | hlm | hlm
      · rw [if_neg (ne_of_lt hlm), if_pos hlm, if_neg (not_lt.mpr hlm.le), add_zero]
      · subst hlm; simp
      · rw [if_neg (ne_of_gt hlm), if_neg (not_lt.mpr hlm.le), if_pos hlm, zero_add]
  have h2 : ∑ m ∈ S, ∑ l ∈ S, (if m < l then v m l else 0) = ∑ a ∈ S, ∑ k ∈ S.filter (· < a), v a k := by
    rw [sum_comm]
    refine sum_congr rfl (fun a _ => ?_)
    rw [sum_filter]
    exact sum_congr rfl (fun k _ => by rw [hv])
  rw [sum_congr rfl h1, sum_add_distrib, sum_add_distrib, h2]
  have h3 : ∑ m ∈ S, ∑ l ∈ S, (if l < m then v m l else 0) = ∑ a ∈ S, ∑ k ∈ S.filter (· < a), v a k :=
    sum_congr rfl (fun a _ => by rw [sum_filter])
  rw [h3]; ring

lemma sum_range_sub_eq (J c : ℕ) : ∑ i ∈ range (J + c + J), (i - (J + c)) = ∑ k ∈ range J, k := by
  rw [sum_range_add, sum_eq_zero (fun i hi => by have := mem_range.mp hi; omega), zero_add]
  exact sum_congr rfl (fun k _ => by omega)

/-- `Σ_{i<2J} (i − J)₊ + Σ_{j<2J} (j − J − 1)₊ = (J − 1)²`. -/
lemma sum_trunc_sq (J : ℕ) :
    ∑ i ∈ range (2 * J), (i - J) + ∑ j ∈ range (2 * J), (j - J - 1) = (J - 1) ^ 2 := by
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · simp
  obtain ⟨K, rfl⟩ : ∃ K, J = K + 1 := ⟨J - 1, by omega⟩
  have a1 : ∑ i ∈ range (2 * (K + 1)), (i - (K + 1)) = ∑ k ∈ range (K + 1), k := by
    have := sum_range_sub_eq (K + 1) 0
    simp only [add_zero] at this
    rw [show 2 * (K + 1) = K + 1 + (K + 1) by ring, this]
  have a2 : ∑ j ∈ range (2 * (K + 1)), (j - (K + 1) - 1) = ∑ k ∈ range K, k := by
    rw [show 2 * (K + 1) = K + 2 + K by ring, ← sum_range_sub_eq K 2]
    exact sum_congr rfl (fun j _ => by omega)
  rw [a1, a2, Nat.add_sub_cancel]
  have g1 := sum_range_id_mul_two (K + 1)
  have g2 := sum_range_id_mul_two K
  simp only [Nat.add_sub_cancel] at g1
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  · obtain ⟨L, rfl⟩ : ∃ L, K = L + 1 := ⟨K - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at g2
    nlinarith

end LS
end V
end Chi2U
