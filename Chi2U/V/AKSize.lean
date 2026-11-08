/-
# Lemma S, limit form: `Σ_{l ≥ 1, p^l ≤ h} A_K(p^l) ≤ (1/(4(p − 1)) + ε) h²` (PROOF_V §3.2, "for the limit")

* `four_classVal_le`: a class with `n` atoms has value `≤ (n + 2)²/4` (`s(n − s) + 2s ≤ (n + 2)²/4`);
* `card_clU_le`: a class mod `d` has at most `⌊h/d⌋ + 1` atoms;
* `AK_le_real`: `A_K(d) ≤ h²/(4d) + 4h` for `d ≤ h` (PROOF_V: `≤ K²/(4d) + O(K)`);
* the levels: `Σ_l p^{−l} ≤ 1/(p − 1)`, at most `log h` levels (`p ≥ 3`), and `4h log h = o(h²)`
  (`eventually_rem_le_U`).
-/
import Chi2U.V.Defs

namespace Chi2U
namespace V
namespace LS

open Finset Filter

lemma card_clU_le {h d c : ℕ} (hd : 0 < d) : (clU h d c).card ≤ h / d + 1 := by
  by_cases hc : c < d
  · refine (card_le_card (t := (range (h / d + 1)).image (fun j => c + j * d)) ?_).trans
      (card_image_le.trans (by simp))
    intro m hm
    rw [mem_clU] at hm
    refine mem_image.mpr ⟨m / d, mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hm.1)), ?_⟩
    have := Nat.mod_add_div m d
    rw [hm.2] at this
    linarith [mul_comm d (m / d)]
  · have : clU h d c = ∅ := by
      ext m
      simp only [mem_clU, Finset.notMem_empty, iff_false, not_and]
      intro _ hmc
      have := Nat.mod_lt m hd
      omega
    simp [this]

lemma four_classVal_le (h d c : ℕ) : 4 * classVal h d c ≤ ((clU h d c).card + 2) ^ 2 := by
  unfold classVal
  obtain ⟨S, hS, hSeq⟩ := Finset.exists_mem_eq_sup (clU h d c).powerset (powerset_nonempty _)
    (fun S => S.card * ((clU h d c).card - S.card) + ∑ m ∈ S, wU h d m)
  rw [hSeq]
  have hs : S.card ≤ (clU h d c).card := card_le_card (mem_powerset.mp hS)
  have hw : ∑ m ∈ S, wU h d m ≤ 2 * S.card := by
    calc _ ≤ ∑ _m ∈ S, 2 := sum_le_sum (fun m _ => wU_le_two h d m)
      _ = 2 * S.card := by rw [sum_const, smul_eq_mul, mul_comm]
  generalize (clU h d c).card = n at *
  generalize S.card = s at *
  generalize ∑ m ∈ S, wU h d m = W at *
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [Nat.add_sub_cancel_left]
  zify at hw ⊢
  nlinarith [sq_nonneg ((t : ℤ) - s + 2)]

/-- `A_K(d) ≤ h²/(4d) + 4h` for `0 < d ≤ h`. -/
lemma AK_le_real {h d : ℕ} (hd : 0 < d) (hdh : d ≤ h) : (AK h d : ℝ) ≤ (h : ℝ) ^ 2 / (4 * d) + 4 * h := by
  have h4 : 4 * AK h d ≤ d * (h / d + 3) ^ 2 := by
    unfold AK
    rw [mul_sum]
    calc ∑ c ∈ range d, 4 * classVal h d c ≤ ∑ _c ∈ range d, (h / d + 3) ^ 2 :=
          sum_le_sum (fun c _ => (four_classVal_le h d c).trans
            (Nat.pow_le_pow_left (by have := card_clU_le (h := h) (c := c) hd; omega) 2))
      _ = d * (h / d + 3) ^ 2 := by simp
  set q := h / d
  have hq : (d : ℝ) * q ≤ h := by exact_mod_cast Nat.mul_div_le h d
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h4' : 4 * (AK h d : ℝ) ≤ d * (q + 3) ^ 2 := by exact_mod_cast h4
  have hsq : (d : ℝ) * q ^ 2 ≤ (h : ℝ) ^ 2 / d := by
    rw [le_div_iff₀ hd0]
    have : ((d : ℝ) * q) ^ 2 ≤ (h : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hq 2
    nlinarith
  have hdh' : (d : ℝ) ≤ h := by exact_mod_cast hdh
  have hmain : (d : ℝ) * (q + 3) ^ 2 ≤ (h : ℝ) ^ 2 / d + 15 * h := by nlinarith
  have e : (h : ℝ) ^ 2 / (4 * d) = ((h : ℝ) ^ 2 / d) / 4 := by rw [div_div, mul_comm]
  rw [e]
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  linarith

lemma sum_levels_geom {h p : ℕ} (hp : 2 ≤ p) :
    ∑ l ∈ levelsV h p, (1 / (p : ℝ)) ^ l ≤ 1 / ((p : ℝ) - 1) := by
  set r : ℝ := 1 / (p : ℝ)
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hsub : levelsV h p ⊆ (range h).image (fun k => k + 1) := by
    intro l hl
    have := mem_Icc.mp (mem_filter.mp hl).1
    exact mem_image.mpr ⟨l - 1, mem_range.mpr (by omega), by omega⟩
  calc ∑ l ∈ levelsV h p, r ^ l ≤ ∑ l ∈ (range h).image (fun k => k + 1), r ^ l :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ k ∈ range h, r ^ (k + 1) := sum_image (fun a _ b _ e => by omega)
    _ = r * ∑ k ∈ range h, r ^ k := by rw [mul_sum]; exact sum_congr rfl (fun k _ => by ring)
    _ ≤ r * (1 - r)⁻¹ := by
        gcongr
        rw [← tsum_geometric_of_lt_one hr0 hr1]
        exact Summable.sum_le_tsum _ (fun _ _ => by positivity) (summable_geometric_of_lt_one hr0 hr1)
    _ = 1 / ((p : ℝ) - 1) := by
        have : (p : ℝ) - 1 ≠ 0 := by linarith
        have : (p : ℝ) ≠ 0 := by linarith
        simp only [r]
        field_simp

lemma card_levelsV_le {h p : ℕ} (hp : 3 ≤ p) (h1 : 1 ≤ h) : ((levelsV h p).card : ℝ) ≤ Real.log h := by
  have hsub : levelsV h p ⊆ Icc 1 (Nat.log p h) := by
    intro l hl
    obtain ⟨hl1, hl2⟩ := mem_filter.mp hl
    exact mem_Icc.mpr ⟨(mem_Icc.mp hl1).1, Nat.le_log_of_pow_le (by omega) hl2⟩
  have hc : (levelsV h p).card ≤ Nat.log p h := by
    have := card_le_card hsub
    simpa using this
  have hpow := Nat.pow_log_le_self p (by omega : h ≠ 0)
  have hlog : (Nat.log p h : ℝ) * Real.log p ≤ Real.log h := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
  have hlp : 1 ≤ Real.log p := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp
    have := Real.exp_one_lt_d9
    linarith
  have hn0 : (0 : ℝ) ≤ Nat.log p h := Nat.cast_nonneg _
  calc ((levelsV h p).card : ℝ) ≤ Nat.log p h := by exact_mod_cast hc
    _ ≤ (Nat.log p h : ℝ) * Real.log p := by nlinarith
    _ ≤ Real.log h := hlog

end LS

open LS Finset Filter

/-- Lemma S, limit form: `Σ_l A_K(p^l) ≤ (1/(4(p − 1)) + ε) h²` eventually (`A_K(d) ≤ K²/(4d) + O(K)`,
`Σ_l p^{−l} ≤ 1/(p − 1)`). -/
theorem AK_levels_size_proof {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    ((∑ l ∈ levelsV h p, AK h (p ^ l) : ℕ) : ℝ) ≤ (1 / (4 * ((p : ℝ) - 1)) + ε) * (h : ℝ) ^ 2 := by
  intro ε hε
  filter_upwards [eventually_rem_le_U ε hε, eventually_ge_atTop 1] with h hR h1
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  push_cast
  have hlev : ∀ l ∈ levelsV h p, (AK h (p ^ l) : ℝ) ≤ (h : ℝ) ^ 2 / 4 * (1 / (p : ℝ)) ^ l + 4 * h := by
    intro l hl
    have hl' := (mem_filter.mp hl).2
    have := AK_le_real (pow_pos hp.pos l) hl'
    have e : (h : ℝ) ^ 2 / (4 * ((p ^ l : ℕ) : ℝ)) = (h : ℝ) ^ 2 / 4 * (1 / (p : ℝ)) ^ l := by
      push_cast
      rw [one_div_pow, mul_one_div, div_div]
    rwa [e] at this
  have hgeom := sum_levels_geom (h := h) (by omega : 2 ≤ p)
  have hcard := card_levelsV_le (h := h) hp3 h1
  have hlog0 : 0 ≤ Real.log h := Real.log_natCast_nonneg h
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  calc ∑ l ∈ levelsV h p, (AK h (p ^ l) : ℝ)
      ≤ ∑ l ∈ levelsV h p, ((h : ℝ) ^ 2 / 4 * (1 / (p : ℝ)) ^ l + 4 * h) := sum_le_sum hlev
    _ = (h : ℝ) ^ 2 / 4 * ∑ l ∈ levelsV h p, (1 / (p : ℝ)) ^ l + (levelsV h p).card * (4 * h) := by
        rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
    _ ≤ (h : ℝ) ^ 2 / 4 * (1 / ((p : ℝ) - 1)) + Real.log h * (4 * h) := by gcongr
    _ ≤ (1 / (4 * ((p : ℝ) - 1)) + ε) * (h : ℝ) ^ 2 := by
        have e : 1 / (4 * ((p : ℝ) - 1)) = (1 / 4) * (1 / ((p : ℝ) - 1)) := by
          rw [one_div_mul_one_div]
        rw [e]
        nlinarith

end V
end Chi2U
