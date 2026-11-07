/-
# Level counting for Lemma 9′ (odd primes) (PROOF_U §3.3, χ₂'s Lemma 9 steps 4–7)

Ported from `lean_chi2/Chi2Irrational/Arith/Lemma9.lean` (levels, residue classes, the ranking `rk`, ranked
divided differences) and `NonVan/ClassData.lean`, `NonVan/Counting.lean` (`DD`, products), with these changes:
* `K = h + 1` atoms `m ≤ h`, poles `x_m = 2(m − h/2)` (even integers) instead of half-integers;
* the moment functional sums over odd `t = 2k + 1`, and `t − x_r = c − 2r` with `c = 2(k + h/2) + 1` odd
  (`cT`), so the class of atoms with `p^e ∣ t − x_r` is `{r : r ≡ (d/2 + 1)c mod d}` (`ctF_eq`);
* levels `e ≥ 1` with `p^e ≤ h` (`levSet`, of size `levU h p`), since `|m − i| ≤ h`.

Main outputs (all in namespace `Chi2U.L9`):
* `padicNorm_dPrime_eq`, `padicValRat_dPrime`: `v_p(D′(x_i)) = Σ_e N_e(i)` (`Vexp`);
* `Vexp_le_factorial`: `Σ_e N_e(i) ≤ v_p(h!)`;
* `prod_T_le`, `prod_DD_le`: the derivative terms lose at most `2` per level;
* `DD_prod_rank`: ranked divided differences.
-/
import Chi2U.Mahler

namespace Chi2U
namespace L9

open Polynomial Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Levels and valuations -/

lemma inv_pow_eq_zpow {a : ℚ} (n : ℕ) : a⁻¹ ^ n = a ^ (-(n : ℤ)) := by
  rw [zpow_neg, zpow_natCast, inv_pow]

/-- The level set `L = {e ∈ [1, h] : p^e ≤ h}`. -/
def levSet (h p : ℕ) : Finset ℕ := (Icc 1 h).filter (fun e => p ^ e ≤ h)

lemma card_levSet (h p : ℕ) : (levSet h p).card = levU h p := rfl

/-- `ν(n) = #{e ∈ L : p^e ∣ n}`. -/
def nuL (h p : ℕ) (n : ℤ) : ℕ := ((levSet h p).filter (fun e => ((p ^ e : ℕ) : ℤ) ∣ n)).card

lemma nuL_le (h : ℕ) (n : ℤ) : nuL h p n ≤ levU h p := card_filter_le _ _

lemma padicNorm_int_le (h : ℕ) (n : ℤ) : padicNorm p (n : ℚ) ≤ (p : ℚ)⁻¹ ^ nuL h p n := by
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  by_cases hn : n = 0
  · subst hn; simp only [Int.cast_zero, padicNorm.zero]; positivity
  · have hsub : (levSet h p).filter (fun e => ((p ^ e : ℕ) : ℤ) ∣ n) ⊆ Icc 1 (padicValInt p n) := by
      intro e he
      rw [mem_filter] at he
      obtain ⟨he1, hdvd⟩ := he
      have he1' := (mem_filter.mp he1).1
      rw [mem_Icc] at he1' ⊢
      push_cast at hdvd
      rcases (padicValInt_dvd_iff e n).mp hdvd with h0 | hle
      · exact absurd h0 hn
      · exact ⟨he1'.1, hle⟩
    have hcard := card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard
    rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn), padicValRat.of_int, inv_pow_eq_zpow]
    exact zpow_le_zpow_right₀ hp1 (by unfold nuL; omega)

lemma padicNorm_int_eq {h : ℕ} {n : ℤ} (hn : n ≠ 0) (hn' : n.natAbs ≤ h) :
    padicNorm p (n : ℚ) = (p : ℚ)⁻¹ ^ nuL h p n := by
  have heq : (levSet h p).filter (fun e => ((p ^ e : ℕ) : ℤ) ∣ n) = Icc 1 (padicValInt p n) := by
    ext e
    simp only [levSet, mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨⟨h1, -⟩, -⟩, hdvd⟩
      push_cast at hdvd
      rcases (padicValInt_dvd_iff e n).mp hdvd with h0 | hle
      · exact absurd h0 hn
      · exact ⟨h1, hle⟩
    · rintro ⟨h1, hle⟩
      have hdvd : (p : ℤ) ^ e ∣ n := (padicValInt_dvd_iff e n).mpr (Or.inr hle)
      have hle2 : p ^ e ≤ h := by
        have := Int.natAbs_dvd_natAbs.mpr hdvd
        rw [Int.natAbs_pow, Int.natAbs_natCast] at this
        exact (Nat.le_of_dvd (Int.natAbs_pos.mpr hn) this).trans hn'
      have hlt : e < p ^ e := Nat.lt_pow_self hp.out.one_lt
      exact ⟨⟨⟨h1, by omega⟩, hle2⟩, by push_cast; exact hdvd⟩
  rw [nuL, heq, Nat.card_Icc, Nat.add_sub_cancel, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn),
    padicValRat.of_int, inv_pow_eq_zpow]

/-- `Σ_r ν(g r) = Σ_{e∈L} #{r : p^e ∣ g r}`. -/
lemma sum_nuL (h : ℕ) (T : Finset ℕ) (g : ℕ → ℤ) :
    ∑ r ∈ T, nuL h p (g r) = ∑ e ∈ levSet h p, (T.filter (fun r : ℕ => ((p ^ e : ℕ) : ℤ) ∣ g r)).card := by
  simp only [nuL, card_filter]
  exact sum_comm

lemma padicNorm_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    padicNorm p (∏ i ∈ s, f i) = ∏ i ∈ s, padicNorm p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [prod_insert ha, prod_insert ha, padicNorm.mul, ih]

lemma padicNorm_prod_le_nuL (h : ℕ) (T : Finset ℕ) (f : ℕ → ℚ) (g : ℕ → ℤ)
    (hf : ∀ r ∈ T, padicNorm p (f r) ≤ (p : ℚ)⁻¹ ^ nuL h p (g r)) :
    padicNorm p (∏ r ∈ T, f r) ≤
      (p : ℚ)⁻¹ ^ ∑ e ∈ levSet h p, (T.filter (fun r : ℕ => ((p ^ e : ℕ) : ℤ) ∣ g r)).card := by
  rw [← sum_nuL, padicNorm_prod, ← prod_pow_eq_pow_sum]
  exact prod_le_prod₀ (fun r _ => padicNorm.nonneg _) hf

lemma padicNorm_two (hp2 : p ≠ 2) : padicNorm p (2 : ℚ) = 1 := by
  have hnd : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)
  have := (padicNorm.nat_eq_one_iff (p := p) 2).mpr hnd
  simpa using this

/-! ### The poles -/

/-- `c = 2(k + h/2) + 1`, so that `(2k + 1) − x_r = c − 2r`. -/
def cT (h k : ℕ) : ℕ := 2 * (k + h / 2) + 1

lemma odd_sub_poleZ (h k r : ℕ) :
    (2 * (k : ℚ) + 1) - ((poleZ h r : ℤ) : ℚ) = (((cT h k : ℤ) - 2 * r : ℤ) : ℚ) := by
  unfold poleZ cT; push_cast; ring

lemma padicNorm_odd_sub_pole_le (h k r : ℕ) :
    padicNorm p ((2 * (k : ℚ) + 1) - ((poleZ h r : ℤ) : ℚ)) ≤ (p : ℚ)⁻¹ ^ nuL h p ((cT h k : ℤ) - 2 * r) := by
  rw [odd_sub_poleZ]; exact padicNorm_int_le h _

lemma pole_sub_pole' (h i r : ℕ) :
    ((poleZ h i : ℤ) : ℚ) - ((poleZ h r : ℤ) : ℚ) = (-2 : ℚ) * (((r : ℤ) - i : ℤ) : ℚ) := by
  unfold poleZ; push_cast; ring

lemma padicNorm_neg_two (hp2 : p ≠ 2) : padicNorm p (-2 : ℚ) = 1 := by
  rw [padicNorm.neg, padicNorm_two hp2]

lemma padicNorm_pole_sub_pole_le (hp2 : p ≠ 2) (h i r : ℕ) :
    padicNorm p (((poleZ h i : ℤ) : ℚ) - ((poleZ h r : ℤ) : ℚ)) ≤ (p : ℚ)⁻¹ ^ nuL h p ((r : ℤ) - i) := by
  rw [pole_sub_pole', padicNorm.mul, padicNorm_neg_two hp2, one_mul]
  exact padicNorm_int_le h _

lemma padicNorm_pole_sub_pole_eq (hp2 : p ≠ 2) {h i r : ℕ} (hi : i ≤ h) (hr : r ≤ h) (hne : r ≠ i) :
    padicNorm p (((poleZ h i : ℤ) : ℚ) - ((poleZ h r : ℤ) : ℚ)) = (p : ℚ)⁻¹ ^ nuL h p ((r : ℤ) - i) := by
  rw [pole_sub_pole', padicNorm.mul, padicNorm_neg_two hp2, one_mul]
  exact padicNorm_int_eq (by omega) (by omega)

/-- `N_e(i) = #{m ≤ h, m ≠ i : d ∣ m − i}` (with `K = h + 1`). -/
def Aset (d K i : ℕ) : Finset ℕ := ((range K).erase i).filter (fun m : ℕ => (d : ℤ) ∣ (m : ℤ) - i)

/-- `V_i = Σ_{e∈L} N_e(i) = v_p(D′(x_i))`. -/
def Vexp (h p i : ℕ) : ℕ := ∑ e ∈ levSet h p, (Aset (p ^ e) (h + 1) i).card

lemma dPrime_eq_prod_erase {h i : ℕ} (hi : i ≤ h) :
    dPrime h i = ∏ l ∈ (range (h + 1)).erase i, (((poleZ h i : ℤ) : ℚ) - ((poleZ h l : ℤ) : ℚ)) := by
  unfold dPrime
  rw [← mul_prod_erase (range (h + 1)) _ (mem_range.mpr (Nat.lt_succ_of_le hi)), if_pos rfl, one_mul]
  exact prod_congr rfl (fun l hl => by rw [if_neg (ne_of_mem_erase hl)])

lemma padicNorm_dPrime_eq (hp2 : p ≠ 2) {h i : ℕ} (hi : i ≤ h) :
    padicNorm p (dPrime h i) = (p : ℚ)⁻¹ ^ Vexp h p i := by
  rw [dPrime_eq_prod_erase hi]
  unfold Vexp Aset
  rw [← sum_nuL h _ (fun m => (m : ℤ) - i), padicNorm_prod, ← prod_pow_eq_pow_sum]
  refine prod_congr rfl (fun m hm => ?_)
  obtain ⟨hmi, hmh⟩ := mem_erase.mp hm
  rw [mem_range] at hmh
  exact padicNorm_pole_sub_pole_eq hp2 hi (by omega) hmi

lemma dPrime_ne_zero' (hp2 : p ≠ 2) {h i : ℕ} (hi : i ≤ h) : dPrime h i ≠ 0 := by
  intro h0
  have h1 := padicNorm_dPrime_eq hp2 hi
  rw [h0, padicNorm.zero] at h1
  exact (pow_ne_zero _ (inv_ne_zero (by exact_mod_cast hp.out.ne_zero))) h1.symm

lemma padicValRat_dPrime (hp2 : p ≠ 2) {h i : ℕ} (hi : i ≤ h) :
    padicValRat p (dPrime h i) = (Vexp h p i : ℤ) := by
  have h1 := padicNorm_dPrime_eq hp2 hi
  rw [padicNorm.eq_zpow_of_nonzero (dPrime_ne_zero' hp2 hi), inv_pow, ← zpow_natCast, ← zpow_neg] at h1
  exact neg_injective (zpow_right_injective₀ (by exact_mod_cast hp.out.pos)
    (by exact_mod_cast hp.out.one_lt.ne') h1)

lemma inv_pow_le_dPrime (hp2 : p ≠ 2) {h i : ℕ} (hi : i ≤ h) {c : ℕ} (hc : Vexp h p i ≤ c + 2 * levU h p) :
    (p : ℚ)⁻¹ ^ c ≤ padicNorm p (dPrime h i) * (p : ℚ) ^ (2 * levU h p) := by
  have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hp0 : (0 : ℚ) < p := by linarith
  rw [padicNorm_dPrime_eq hp2 hi, inv_pow_eq_zpow, inv_pow_eq_zpow, ← zpow_natCast (p : ℚ) (2 * levU h p),
    ← zpow_add₀ hp0.ne']
  exact zpow_le_zpow_right₀ hp1 (by push_cast; omega)

lemma pow_mod_two (hp2 : p ≠ 2) (e : ℕ) : p ^ e % 2 = 1 :=
  Nat.odd_iff.mp ((hp.out.odd_of_ne_two hp2).pow)

/-! ### One level: residue classes modulo an odd `d` -/

section Level

lemma dvd_of_dvd_two_mul {d : ℕ} (hd : d % 2 = 1) {x : ℤ} (hx : (d : ℤ) ∣ 2 * x) : (d : ℤ) ∣ x := by
  have e : (d : ℤ) * x - ((d / 2 : ℕ) : ℤ) * (2 * x) = x := by
    have : (d : ℤ) = 2 * ((d / 2 : ℕ) : ℤ) + 1 := by omega
    rw [this]; ring
  rw [← e]
  exact dvd_sub (dvd_mul_right _ _) (dvd_mul_of_dvd_right hx _)

lemma card_filter_mod' {d : ℕ} (hd : 0 < d) {c : ℕ} (hc : c < d) (X : ℕ) :
    ((range X).filter (fun l => l % d = c)).card = (X + d - 1 - c) / d := by
  have himg : (range X).filter (fun l => l % d = c) = (range ((X + d - 1 - c) / d)).image (fun j => c + j * d) := by
    ext l
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hl, hlc⟩
      refine ⟨l / d, ?_, ?_⟩
      · rw [Nat.lt_div_iff_mul_lt hd]
        have := Nat.mod_add_div l d
        rw [hlc] at this
        have e : (l / d + 1) * d = l / d * d + d := by ring
        have e2 : d * (l / d) = l / d * d := by ring
        omega
      · have := Nat.mod_add_div l d
        rw [hlc] at this
        linarith [mul_comm d (l / d)]
    · rintro ⟨j, hj, rfl⟩
      rw [Nat.lt_div_iff_mul_lt hd] at hj
      refine ⟨?_, ?_⟩
      · have e : (j + 1) * d = j * d + d := by ring
        omega
      · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  rw [himg, card_image_of_injective _ (fun a b e => Nat.eq_of_mul_eq_mul_right hd (by omega)), card_range]

lemma card_mod_le {d : ℕ} (hd : 0 < d) {a b : ℕ} (ha : a < d) (hb : b < d) (X : ℕ) :
    ((range X).filter (fun l => l % d = a)).card ≤ ((range X).filter (fun l => l % d = b)).card + 1 := by
  rw [card_filter_mod' hd ha, card_filter_mod' hd hb]
  calc (X + d - 1 - a) / d ≤ (X + d - 1 - b + d) / d := Nat.div_le_div_right (by omega)
    _ = (X + d - 1 - b) / d + 1 := Nat.add_div_right _ hd

/-- The class of `i` in `[0, K)` modulo `d`. -/
def clsF (d K i : ℕ) : Finset ℕ := (range K).filter (fun m : ℕ => (d : ℤ) ∣ (m : ℤ) - i)

/-- The atoms `m < K` with `d ∣ c − 2m`. -/
def ctF (d K c : ℕ) : Finset ℕ := (range K).filter (fun m : ℕ => (d : ℤ) ∣ (c : ℤ) - 2 * m)

lemma clsF_eq (d K i : ℕ) : clsF d K i = (range K).filter (fun m => m % d = i % d) := by
  unfold clsF
  refine filter_congr (fun m _ => ?_)
  rw [← Nat.modEq_iff_dvd]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

lemma ctF_eq {d : ℕ} (hd : d % 2 = 1) (K c : ℕ) :
    ctF d K c = (range K).filter (fun m => m % d = ((d / 2 + 1) * c) % d) := by
  unfold ctF
  refine filter_congr (fun m _ => ?_)
  obtain ⟨w, rfl⟩ : ∃ w, d = 2 * w + 1 := ⟨d / 2, by omega⟩
  have hw : (2 * w + 1) / 2 = w := by omega
  rw [hw]
  show _ ↔ Nat.ModEq (2 * w + 1) m ((w + 1) * c)
  rw [Nat.modEq_iff_dvd]
  push_cast
  constructor
  · intro h1
    have := dvd_add (dvd_mul_of_dvd_right h1 ((w : ℤ) + 1)) (dvd_mul_right (2 * (w : ℤ) + 1) (m : ℤ))
    convert this using 1; ring
  · intro h1
    have := dvd_sub (dvd_mul_of_dvd_right h1 2) (dvd_mul_right (2 * (w : ℤ) + 1) (c : ℤ))
    convert this using 1; ring

lemma ctF_eq_clsF {d : ℕ} (hd : d % 2 = 1) {K c i : ℕ} (hci : (d : ℤ) ∣ (c : ℤ) - 2 * i) :
    ctF d K c = clsF d K i := by
  unfold ctF clsF
  refine filter_congr (fun m _ => ?_)
  constructor
  · intro h1
    have := dvd_sub hci h1
    exact dvd_of_dvd_two_mul hd (by convert this using 1; ring)
  · intro h1
    have := dvd_sub hci (dvd_mul_of_dvd_right h1 2)
    convert this using 1; ring

lemma not_dvd_of_mem_ctF {d : ℕ} {c i m : ℕ} (hci : ¬ (d : ℤ) ∣ (c : ℤ) - 2 * i)
    (hm : (d : ℤ) ∣ (c : ℤ) - 2 * m) : ¬ (d : ℤ) ∣ (m : ℤ) - i := by
  intro h1
  apply hci
  have := dvd_add hm (dvd_mul_of_dvd_right h1 2)
  convert this using 1; ring

lemma card_clsF_le {d : ℕ} (hd : d % 2 = 1) (K c i : ℕ) : (clsF d K i).card ≤ (ctF d K c).card + 1 := by
  have hd0 : 0 < d := by omega
  rw [clsF_eq, ctF_eq hd]
  exact card_mod_le hd0 (Nat.mod_lt _ hd0) (Nat.mod_lt _ hd0) K

lemma card_Aset {d K i : ℕ} (hi : i < K) : (Aset d K i).card + 1 = (clsF d K i).card := by
  unfold Aset clsF
  rw [filter_erase, card_erase_of_mem (mem_filter.mpr ⟨mem_range.mpr hi, by simp⟩)]
  have : 0 < ((range K).filter (fun m : ℕ => (d : ℤ) ∣ (m : ℤ) - i)).card :=
    card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_range.mpr hi, by simp⟩⟩
  omega

/-- `N_e(i) ≤ ⌊h/d⌋`. -/
lemma card_Aset_le {d h i : ℕ} (hd : 0 < d) (hi : i ≤ h) : (Aset d (h + 1) i).card ≤ h / d := by
  have h1 := card_Aset (d := d) (K := h + 1) (show i < h + 1 by omega)
  rw [clsF_eq, card_filter_mod' hd (Nat.mod_lt _ hd)] at h1
  have hr : i % d ≤ h := (Nat.mod_le i d).trans hi
  have h2 : (h + 1 + d - 1 - i % d) / d = (h - i % d) / d + 1 := by
    rw [show h + 1 + d - 1 - i % d = (h - i % d) + d by omega]; exact Nat.add_div_right _ hd
  rw [h2] at h1
  have h3 := Nat.div_le_div_right (c := d) (Nat.sub_le h (i % d))
  omega

/-- **Level count, products over `[0,K) ∖ {i, j, s}`.** -/
lemma level_L1 {d : ℕ} (hd : d % 2 = 1) {K i : ℕ} (hi : i < K) (j s c : ℕ) (T : Finset ℕ)
    (hT : ∀ r < K, r ≠ i → r ≠ j → r ≠ s → r ∈ T) :
    (Aset d K i).card ≤ (T.filter (fun r : ℕ => (d : ℤ) ∣ (c : ℤ) - 2 * r)).card + 2 := by
  have hA := card_Aset (d := d) hi
  have hsub : (((ctF d K c).erase i).erase j).erase s ⊆ T.filter (fun r : ℕ => (d : ℤ) ∣ (c : ℤ) - 2 * r) := by
    intro r hr
    simp only [mem_erase, ctF, mem_filter, mem_range] at hr
    exact mem_filter.mpr ⟨hT r hr.2.2.2.1 hr.2.2.1 hr.2.1 hr.1, hr.2.2.2.2⟩
  have h1 := card_le_card hsub
  have e1 := pred_card_le_card_erase (s := ctF d K c) (a := i)
  have e2 := pred_card_le_card_erase (s := (ctF d K c).erase i) (a := j)
  have e3 := pred_card_le_card_erase (s := ((ctF d K c).erase i).erase j) (a := s)
  by_cases hdi : (d : ℤ) ∣ (c : ℤ) - 2 * i
  · rw [ctF_eq_clsF hd hdi] at e1 h1 e2 e3
    omega
  · have hiC : i ∉ ctF d K c := fun hm => hdi (mem_filter.mp hm).2
    have e0 : ((ctF d K c).erase i).card = (ctF d K c).card := by rw [erase_eq_of_notMem hiC]
    have hK := card_clsF_le hd K c i
    omega

/-- **Level count, ranked divided-difference terms.** -/
lemma level_L2 {d : ℕ} (hd : d % 2 = 1) {K i : ℕ} (hi : i < K) (c l s : ℕ) (ρ : ℕ → ℕ)
    (hl : l ∈ (range K).erase i) (hinj : Set.InjOn ρ ((range K).erase i : Finset ℕ))
    (hρ : ∀ r ∈ (range K).erase i, ∀ r' ∈ (range K).erase i,
      (d : ℤ) ∣ (r : ℤ) - i → ¬ (d : ℤ) ∣ (r' : ℤ) - i → ρ r < ρ r') :
    (Aset d K i).card ≤
      ((((range K).erase i).filter (fun r => ρ r < ρ l)).filter (fun r : ℕ => (d : ℤ) ∣ (r : ℤ) - i)).card +
      (((((range K).erase i).filter (fun r => ρ l < ρ r)).erase s).filter
        (fun r : ℕ => (d : ℤ) ∣ (c : ℤ) - 2 * r)).card + 2 := by
  by_cases hlA : (d : ℤ) ∣ (l : ℤ) - i
  · have hsplit : Aset d K i ⊆ insert l ((Aset d K i).filter (fun r => ρ r < ρ l) ∪
        (Aset d K i).filter (fun r => ρ l < ρ r)) := by
      intro r hr
      by_cases hrl : r = l
      · rw [hrl]; exact mem_insert_self _ _
      · have hne : ρ r ≠ ρ l := fun e => hrl (hinj (mem_coe.mpr (mem_filter.mp hr).1) (mem_coe.mpr hl) e)
        rcases lt_or_gt_of_ne hne with h1 | h1
        · exact mem_insert_of_mem (mem_union_left _ (mem_filter.mpr ⟨hr, h1⟩))
        · exact mem_insert_of_mem (mem_union_right _ (mem_filter.mpr ⟨hr, h1⟩))
    have hcA := (card_le_card hsplit).trans ((card_insert_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) 1))
    have hb : (Aset d K i).filter (fun r => ρ r < ρ l) ⊆
        (((range K).erase i).filter (fun r => ρ r < ρ l)).filter (fun r : ℕ => (d : ℤ) ∣ (r : ℤ) - i) := by
      intro r hr
      simp only [Aset, mem_filter] at hr ⊢
      exact ⟨⟨hr.1.1, hr.2⟩, hr.1.2⟩
    have hb' := card_le_card hb
    by_cases hti : (d : ℤ) ∣ (c : ℤ) - 2 * i
    · have ha : ((Aset d K i).filter (fun r => ρ l < ρ r)).erase s ⊆
          ((((range K).erase i).filter (fun r => ρ l < ρ r)).erase s).filter
            (fun r : ℕ => (d : ℤ) ∣ (c : ℤ) - 2 * r) := by
        intro r hr
        simp only [Aset, mem_erase, mem_filter] at hr
        refine mem_filter.mpr ⟨mem_erase.mpr ⟨hr.1, mem_filter.mpr ⟨mem_erase.mpr hr.2.1.1, hr.2.2⟩⟩, ?_⟩
        have := dvd_sub hti (dvd_mul_of_dvd_right hr.2.1.2 2)
        convert this using 1; ring
      have ha' := card_le_card ha
      have := pred_card_le_card_erase (s := (Aset d K i).filter (fun r => ρ l < ρ r)) (a := s)
      omega
    · have hC : (ctF d K c).erase s ⊆ ((((range K).erase i).filter (fun r => ρ l < ρ r)).erase s).filter
            (fun r : ℕ => (d : ℤ) ∣ (c : ℤ) - 2 * r) := by
        intro r hr
        obtain ⟨hrs, hrC⟩ := mem_erase.mp hr
        have hrC' := mem_filter.mp hrC
        have hri : r ≠ i := fun e => hti (e ▸ hrC'.2)
        have hrM : r ∈ (range K).erase i := mem_erase.mpr ⟨hri, hrC'.1⟩
        have hrA := not_dvd_of_mem_ctF hti hrC'.2
        exact mem_filter.mpr ⟨mem_erase.mpr ⟨hrs, mem_filter.mpr ⟨hrM, hρ l hl r hrM hlA hrA⟩⟩, hrC'.2⟩
      have h1 := card_le_card hC
      have h2 := pred_card_le_card_erase (s := ctF d K c) (a := s)
      have hK := card_clsF_le hd K c i
      have hA := card_Aset (d := d) hi
      omega
  · have hsub : Aset d K i ⊆
        (((range K).erase i).filter (fun r => ρ r < ρ l)).filter (fun r : ℕ => (d : ℤ) ∣ (r : ℤ) - i) := by
      intro r hr
      have hr' := mem_filter.mp hr
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨hr'.1, hρ r hr'.1 l hl hr'.2 hlA⟩, hr'.2⟩
    have := card_le_card hsub
    omega

end Level

/-! ### `Σ_e N_e(i) ≤ v_p(h!)` -/

lemma Vexp_le_factorial {h : ℕ} (i : ℕ) (hi : i ≤ h) : Vexp h p i ≤ padicValNat p h.factorial := by
  rw [padicValNat_factorial (p := p) (b := h + 1) (Nat.lt_succ_of_le (Nat.log_le_self p h))]
  unfold Vexp
  calc ∑ e ∈ levSet h p, (Aset (p ^ e) (h + 1) i).card ≤ ∑ e ∈ levSet h p, h / p ^ e :=
        sum_le_sum (fun e _ => card_Aset_le (pow_pos hp.out.pos e) hi)
    _ ≤ ∑ e ∈ Ico 1 (h + 1), h / p ^ e := by
        refine sum_le_sum_of_subset_of_nonneg (fun e he => ?_) (fun _ _ _ => Nat.zero_le _)
        have := (mem_filter.mp he).1
        rw [mem_Icc] at this
        rw [mem_Ico]; omega

/-! ### The ranking by decreasing valuation -/

/-- `rk(m) = m + K (K − v_p(m − i))`: atoms with larger `v_p(m − i)` come first. -/
noncomputable def rk (p K i m : ℕ) : ℕ := m + K * (K - padicValInt p ((m : ℤ) - i))

lemma rk_injOn (K i : ℕ) : Set.InjOn (rk p K i) ((range K).erase i : Finset ℕ) := by
  intro r hr r' hr' e
  have hr1 : r < K := mem_range.mp (mem_of_mem_erase (mem_coe.mp hr))
  have hr1' : r' < K := mem_range.mp (mem_of_mem_erase (mem_coe.mp hr'))
  have := congrArg (· % K) e
  simp only [rk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr1, Nat.mod_eq_of_lt hr1'] at this
  exact this

lemma rk_lt {K i e : ℕ} (hi : i < K) {r r' : ℕ} (hr : r ∈ (range K).erase i) (hr' : r' ∈ (range K).erase i)
    (h1 : ((p ^ e : ℕ) : ℤ) ∣ (r : ℤ) - i) (h2 : ¬ ((p ^ e : ℕ) : ℤ) ∣ (r' : ℤ) - i) :
    rk p K i r < rk p K i r' := by
  obtain ⟨hri, hrh⟩ := mem_erase.mp hr
  obtain ⟨hri', hrh'⟩ := mem_erase.mp hr'
  rw [mem_range] at hrh hrh'
  push_cast at h1 h2
  have hne : (r : ℤ) - i ≠ 0 := by omega
  have hv1 : e ≤ padicValInt p ((r : ℤ) - i) := ((padicValInt_dvd_iff e _).mp h1).resolve_left hne
  have hv2 : padicValInt p ((r' : ℤ) - i) < e := by
    by_contra hc
    push_neg at hc
    exact h2 ((padicValInt_dvd_iff e _).mpr (Or.inr hc))
  have hv3 : padicValInt p ((r : ℤ) - i) < K := by
    have hd := padicValInt_dvd (p := p) ((r : ℤ) - i)
    have hd' := Int.natAbs_dvd_natAbs.mpr hd
    rw [Int.natAbs_pow, Int.natAbs_natCast] at hd'
    have h3 := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) hd'
    have h4 := Nat.lt_pow_self (n := padicValInt p ((r : ℤ) - i)) hp.out.one_lt
    have h5 : ((r : ℤ) - i).natAbs < K := by omega
    omega
  unfold rk
  generalize padicValInt p ((r : ℤ) - i) = v at *
  generalize padicValInt p ((r' : ℤ) - i) = v' at *
  have hab : K - v + 1 ≤ K - v' := by omega
  have := Nat.mul_le_mul_left K hab
  rw [mul_add, mul_one] at this
  generalize K * (K - v) = A at *
  generalize K * (K - v') = B at *
  omega

/-! ### Divided differences -/

/-- `DD x P = (P − P(x)) / (X − x)`. -/
noncomputable def DD (x : ℚ) (P : ℚ[X]) : ℚ[X] := (P - C (P.eval x)) /ₘ (X - C x)

lemma X_sub_C_mul_DD (x : ℚ) (P : ℚ[X]) : (X - C x) * DD x P = P - C (P.eval x) := by
  unfold DD
  rw [mul_divByMonic_eq_iff_isRoot.mpr (by simp [IsRoot])]

lemma DD_eq_of_mul {x : ℚ} {P Q : ℚ[X]} (H : (X - C x) * Q = P - C (P.eval x)) : DD x P = Q := by
  have := X_sub_C_mul_DD x P
  rw [← H] at this
  exact mul_left_cancel₀ (X_sub_C_ne_zero x) this

lemma DD_mul (x : ℚ) (P R : ℚ[X]) : DD x (P * R) = DD x P * R + C (P.eval x) * DD x R := by
  apply DD_eq_of_mul
  have hP := X_sub_C_mul_DD x P
  have hR := X_sub_C_mul_DD x R
  rw [eval_mul, C_mul]
  linear_combination R * hP + C (P.eval x) * hR

lemma DD_X_sub_C (x a : ℚ) : DD x (X - C a) = 1 := by
  apply DD_eq_of_mul
  simp only [eval_sub, eval_X, eval_C, mul_one, map_sub]
  ring

lemma DD_one (x : ℚ) : DD x 1 = 0 := by
  apply DD_eq_of_mul
  simp

/-- `DD_x ∏_{m∈M}(X − a_m) = Σ_ℓ ∏_{ρr<ρℓ}(x − a_r) · ∏_{ρℓ<ρr}(X − a_r)` for a ranking `ρ` injective on `M`. -/
lemma DD_prod_rank (x : ℚ) (a : ℕ → ℚ) (ρ : ℕ → ℕ) (M : Finset ℕ) (hρ : Set.InjOn ρ (M : Set ℕ)) :
    DD x (∏ m ∈ M, (X - C (a m))) = ∑ l ∈ M, C (∏ r ∈ M.filter (fun r => ρ r < ρ l), (x - a r)) *
      ∏ r ∈ M.filter (fun r => ρ l < ρ r), (X - C (a r)) := by
  revert hρ
  refine Finset.induction_on_min_value (motive := fun M => Set.InjOn ρ (M : Set ℕ) →
    DD x (∏ m ∈ M, (X - C (a m))) = ∑ l ∈ M, C (∏ r ∈ M.filter (fun r => ρ r < ρ l), (x - a r)) *
      ∏ r ∈ M.filter (fun r => ρ l < ρ r), (X - C (a r))) ρ M ?_ ?_
  · intro _
    simp [DD_one]
  · intro b s hb hmin ih hinj
    have hlt : ∀ y ∈ s, ρ b < ρ y := fun y hy => lt_of_le_of_ne (hmin y hy) (fun e => hb (by
      have := hinj (mem_coe.mpr (mem_insert_self b s)) (mem_coe.mpr (mem_insert_of_mem hy)) e
      rw [this]; exact hy))
    have ih' := ih (hinj.mono (coe_subset.mpr (subset_insert b s)))
    rw [prod_insert hb, DD_mul, DD_X_sub_C, one_mul, ih', sum_insert hb]
    have e1 : (insert b s).filter (fun r => ρ r < ρ b) = ∅ := by
      rw [filter_insert, ite_eq_right (lt_irrefl _), filter_eq_empty_iff]
      intro y hy
      exact not_lt.mpr (hmin y hy)
    have e2 : (insert b s).filter (fun r => ρ b < ρ r) = s := by
      rw [filter_insert, ite_eq_right (lt_irrefl _), filter_true_of_mem hlt]
    rw [e1, e2, prod_empty, map_one, one_mul, mul_sum]
    congr 1
    refine sum_congr rfl (fun l hl => ?_)
    rw [filter_insert, ite_eq_left (hlt l hl), filter_insert, ite_eq_right (not_lt.mpr (hmin l hl)),
      prod_insert (fun hm => hb (mem_filter.mp hm).1)]
    simp only [eval_sub, eval_X, eval_C, map_mul]
    ring

/-- `(∏ (X − a_s))′(t) = Σ_s ∏_{T∖s} (t − a)`. -/
lemma eval_derivative_prod {ι : Type*} [DecidableEq ι] (T : Finset ι) (a : ι → ℚ) (t : ℚ) :
    (derivative (∏ s ∈ T, (X - C (a s)))).eval t = ∑ s ∈ T, ∏ s' ∈ T.erase s, (t - a s') := by
  rw [derivative_prod_finset, eval_finsetSum]
  refine sum_congr rfl (fun s _ => ?_)
  simp [eval_prod]

/-! ### Derivative bounds -/

section Deriv

variable (hp2 : p ≠ 2)
include hp2

/-- A product over `T ⊇ [0,h] ∖ {i, j, s}` at `t = 2k + 1`. -/
lemma prod_T_le {h i : ℕ} (hi : i ≤ h) (j s k : ℕ) (T : Finset ℕ)
    (hT : ∀ r < h + 1, r ≠ i → r ≠ j → r ≠ s → r ∈ T) :
    padicNorm p (∏ r ∈ T, ((2 * (k : ℚ) + 1) - ((poleZ h r : ℤ) : ℚ))) ≤
      padicNorm p (dPrime h i) * (p : ℚ) ^ (2 * levU h p) := by
  refine (padicNorm_prod_le_nuL h T _ (fun r => (cT h k : ℤ) - 2 * r)
    (fun r _ => padicNorm_odd_sub_pole_le h k r)).trans ?_
  refine inv_pow_le_dPrime hp2 hi ?_
  unfold Vexp
  calc ∑ e ∈ levSet h p, (Aset (p ^ e) (h + 1) i).card
      ≤ ∑ e ∈ levSet h p, ((T.filter (fun r : ℕ => ((p ^ e : ℕ) : ℤ) ∣ (cT h k : ℤ) - 2 * r)).card + 2) :=
        sum_le_sum (fun e _ => level_L1 (pow_mod_two hp2 e) (Nat.lt_succ_of_le hi) j s (cT h k) T hT)
    _ = _ := by rw [sum_add_distrib, sum_const, card_levSet, smul_eq_mul]; ring

/-- A ranked divided-difference term. -/
lemma prod_DD_le {h i : ℕ} (hi : i ≤ h) (k l s : ℕ) (hl : l ∈ (range (h + 1)).erase i) :
    padicNorm p ((∏ r ∈ ((range (h + 1)).erase i).filter (fun r => rk p (h + 1) i r < rk p (h + 1) i l),
        (((poleZ h i : ℤ) : ℚ) - ((poleZ h r : ℤ) : ℚ))) *
      ∏ r ∈ (((range (h + 1)).erase i).filter (fun r => rk p (h + 1) i l < rk p (h + 1) i r)).erase s,
        ((2 * (k : ℚ) + 1) - ((poleZ h r : ℤ) : ℚ))) ≤
      padicNorm p (dPrime h i) * (p : ℚ) ^ (2 * levU h p) := by
  rw [padicNorm.mul]
  have h1 := padicNorm_prod_le_nuL h
    (((range (h + 1)).erase i).filter (fun r => rk p (h + 1) i r < rk p (h + 1) i l)) _
    (fun r => (r : ℤ) - i) (fun r _ => padicNorm_pole_sub_pole_le (p := p) hp2 h i r)
  have h2 := padicNorm_prod_le_nuL h
    ((((range (h + 1)).erase i).filter (fun r => rk p (h + 1) i l < rk p (h + 1) i r)).erase s) _
    (fun r => (cT h k : ℤ) - 2 * r) (fun r _ => padicNorm_odd_sub_pole_le (p := p) h k r)
  refine (mul_le_mul h1 h2 (padicNorm.nonneg _) (by positivity)).trans ?_
  rw [← pow_add, ← sum_add_distrib]
  refine inv_pow_le_dPrime hp2 hi ?_
  unfold Vexp
  calc ∑ e ∈ levSet h p, (Aset (p ^ e) (h + 1) i).card ≤ ∑ e ∈ levSet h p,
      (((((range (h + 1)).erase i).filter (fun r => rk p (h + 1) i r < rk p (h + 1) i l)).filter
          (fun r : ℕ => ((p ^ e : ℕ) : ℤ) ∣ (r : ℤ) - i)).card +
        (((((range (h + 1)).erase i).filter (fun r => rk p (h + 1) i l < rk p (h + 1) i r)).erase s).filter
          (fun r : ℕ => ((p ^ e : ℕ) : ℤ) ∣ (cT h k : ℤ) - 2 * r)).card + 2) :=
        sum_le_sum (fun e _ => level_L2 (pow_mod_two hp2 e) (Nat.lt_succ_of_le hi) (cT h k) l s
          (rk p (h + 1) i) hl (rk_injOn (h + 1) i)
          (fun r hr r' hr' h1 h2 => rk_lt (Nat.lt_succ_of_le hi) hr hr' h1 h2))
    _ = _ := by rw [sum_add_distrib, sum_const, card_levSet, smul_eq_mul]; ring

end Deriv

end L9
end Chi2U
