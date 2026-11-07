/-
# `G^f(0)` mod `ℓ` in block form (PROOF_U §6, steps 3–4)

* `dPrime_split`: `D′(x_i) = ℓ² κ_r W` for `i = γ + rℓ`, `κ = (8, −4, 8)`, `W = Π_{m ≢ γ}(x_i − x_m)`, and
  `W ≡ U_γ = −1` (`Cong_Wz`). In particular `v_ℓ(D′(x_i)) = 2` (`padicValRat_dPrime`).
* **`Cong_Afun`**: `G^f(0)_{γ+rℓ, γ′+sℓ} ≡ [γ = γ′]·e_γ·(c + [r = s] d_r)` with `e_γ = −z^{x_γ}`,
  `c = z^{3ℓ}/(4z)^ℓ`, `d = (8z^ℓ, 0, −8z^{3ℓ})` (PROOF_U's `e_γ M`, `M = c𝟙𝟙ᵀ + diag(8ζ, 0, −8ζ³)` with `U_γ = −1`).
-/
import Chi2U.NonVan.Entries

namespace Chi2U
namespace LP

open Polynomial Finset

/-- `κ_r`. -/
def kap (r : ℕ) : ℤ := if r = 1 then -4 else 8

/-- `W = Π_{m ≢ γ}(x_i − x_m)`. -/
def Wz (ℓ γ i : ℕ) : ℤ :=
  ∏ m ∈ (range (3 * ℓ)).filter (fun m => m % ℓ ≠ γ), (poleZ (3 * ℓ - 1) i - poleZ (3 * ℓ - 1) m)

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

omit hℓ in
lemma lt_three_mul {γ r : ℕ} (hγ : γ < ℓ) (hr : r < 3) : γ + r * ℓ < 3 * ℓ := by
  interval_cases r <;> omega

omit hℓ in
lemma class_set {γ : ℕ} (hγ : γ < ℓ) :
    (range (3 * ℓ)).filter (fun m => m % ℓ = γ) = {γ, γ + ℓ, γ + 2 * ℓ} := by
  ext m
  simp only [mem_filter, mem_range, mem_insert, mem_singleton]
  obtain ⟨h0, h1, h2⟩ := mod_of_class hγ
  constructor
  · rintro ⟨hm, hmγ⟩; exact class_cases hm hmγ
  · rintro (rfl | rfl | rfl)
    · exact ⟨by omega, h0⟩
    · exact ⟨by omega, h1⟩
    · exact ⟨by omega, h2⟩

lemma dPrime_split {γ r : ℕ} (hγ : γ < ℓ) (hr : r < 3) :
    dPrime (3 * ℓ - 1) (γ + r * ℓ) = (ℓ : ℚ) ^ 2 * (kap r : ℚ) * (Wz ℓ γ (γ + r * ℓ) : ℚ) := by
  have h3 : 3 * ℓ - 1 + 1 = 3 * ℓ := by have := hℓ.out.pos; omega
  have hiγ : (γ + r * ℓ) % ℓ = γ := add_mul_mod_eq hγ
  unfold dPrime
  rw [h3, ← prod_filter_mul_prod_filter_not (range (3 * ℓ)) (fun l => l % ℓ = γ), class_set hγ]
  have hW : ∏ l ∈ (range (3 * ℓ)).filter (fun l => ¬ l % ℓ = γ),
      (if l = γ + r * ℓ then (1 : ℚ) else ((poleZ (3 * ℓ - 1) (γ + r * ℓ) : ℤ) : ℚ) - poleZ (3 * ℓ - 1) l) =
      (Wz ℓ γ (γ + r * ℓ) : ℚ) := by
    unfold Wz; push_cast
    refine prod_congr rfl (fun l hl => ?_)
    rw [if_neg]
    intro e; rw [mem_filter] at hl; exact hl.2 (by rw [e]; exact hiγ)
  rw [hW]
  have hl0 := hℓ.out.pos
  rw [prod_insert (by simp only [mem_insert, mem_singleton]; omega),
    prod_insert (by simp only [mem_singleton]; omega), prod_singleton]
  simp only [LB.poleZ_sub]
  interval_cases r
  · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)]; simp only [kap]; push_cast; ring
  · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega)]; simp only [kap]; push_cast; ring
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; simp only [kap]; push_cast; ring

lemma Cong_Wz (hℓ2 : ℓ ≠ 2) {γ r : ℕ} (hγ : γ < ℓ) :
    Cong ℓ ((Wz ℓ γ (γ + r * ℓ) : ℚ) : Q5) (-1) := by
  rw [Rat.cast_intCast]
  refine Cong_congr (Cong_intCast _) rfl ?_
  rw [← castHom_intCast, Wz, Int.cast_prod]
  simp only [Int.cast_sub]
  rw [abar_of_mod hℓ2 hγ (add_mul_mod_eq hγ), Ubar_eq hℓ2 hγ, map_neg, map_one]

lemma padicValRat_dPrime (hℓ2 : ℓ ≠ 2) {γ r : ℕ} (hγ : γ < ℓ) (hr : r < 3) :
    padicValRat ℓ (dPrime (3 * ℓ - 1) (γ + r * ℓ)) = 2 := by
  have hk : ((kap r : ℚ) : Q5) = ((kap r : ℤ) : Q5) := by push_cast; rfl
  have hC : Cong ℓ ((((kap r : ℚ) * (Wz ℓ γ (γ + r * ℓ) : ℚ)) : ℚ) : Q5) (-(kap r : Fl ℓ)) := by
    rw [Rat.cast_mul, hk]
    refine Cong_congr (Cong_mul (Cong_intCast _) (Cong_Wz hℓ2 hγ)) rfl (by ring)
  have hne : -(kap r : Fl ℓ) ≠ 0 := by
    rw [neg_ne_zero]
    unfold kap
    split_ifs
    · have : ((-4 : ℤ) : Fl ℓ) = -(4 : Fl ℓ) := by push_cast; ring
      rw [this, neg_ne_zero]; exact four_ne_zero_Fl hℓ2
    · have : ((8 : ℤ) : Fl ℓ) = 4 * 2 := by push_cast; ring
      rw [this]; exact mul_ne_zero (four_ne_zero_Fl hℓ2) (two_ne_zero_Fl hℓ2)
  have h1 := padicNorm_eq_one_of_Cong hC hne
  have hq0 : (kap r : ℚ) * (Wz ℓ γ (γ + r * ℓ) : ℚ) ≠ 0 := by
    intro h0; rw [h0, padicNorm.zero] at h1; exact zero_ne_one h1
  have hv : padicValRat ℓ ((kap r : ℚ) * (Wz ℓ γ (γ + r * ℓ) : ℚ)) = 0 := by
    rw [padicNorm.eq_zpow_of_nonzero hq0] at h1
    have hl : (1 : ℚ) < ℓ := by exact_mod_cast hℓ.out.one_lt
    have := (zpow_right_injective₀ (by linarith : (0 : ℚ) < ℓ) hl.ne') (h1.trans (zpow_zero _).symm)
    omega
  have hl0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.out.ne_zero
  rw [dPrime_split hγ hr, mul_assoc, padicValRat.mul (pow_ne_zero _ hl0) hq0, hv, add_zero,
    padicValRat.pow (ℓ : ℚ) (k := 2), padicValRat.self hℓ.out.one_lt]
  norm_num

/-! ### The block entries -/

variable (ℓ) in
/-- `e_γ = −z^{x_γ}`. -/
noncomputable def eB (γ : ℕ) : Fl ℓ := -(zb ℓ ^ poleZ (3 * ℓ - 1) γ)

variable (ℓ) in
/-- `c = z^{3ℓ}/(4z)^ℓ`. -/
noncomputable def cB : Fl ℓ := ((4 * zb ℓ) ^ ℓ)⁻¹ * zb ℓ ^ (3 * ℓ)

variable (ℓ) in
/-- `d = (8z^ℓ, 0, −8z^{3ℓ})`. -/
noncomputable def dB (r : ℕ) : Fl ℓ := if r = 0 then 8 * zb ℓ ^ ℓ else if r = 1 then 0 else -8 * zb ℓ ^ (3 * ℓ)

lemma zb_poleZ_add (hℓ2 : ℓ ≠ 2) (γ r : ℕ) :
    zb ℓ ^ poleZ (3 * ℓ - 1) (γ + r * ℓ) = zb ℓ ^ poleZ (3 * ℓ - 1) γ * zb ℓ ^ (2 * r * ℓ) := by
  rw [poleZ_eq (hℓ.out.odd_of_ne_two hℓ2), poleZ_eq (hℓ.out.odd_of_ne_two hℓ2), ← zpow_natCast,
    ← zpow_add₀ zb_ne_zero]
  congr 1; push_cast; ring

lemma zb_poleZ_mul (hℓ2 : ℓ ≠ 2) (γ : ℕ) :
    zb ℓ ^ poleZ (3 * ℓ - 1) γ * zb ℓ ^ (3 * ℓ) = zb ℓ ^ (2 * γ + 1) := by
  rw [poleZ_eq (hℓ.out.odd_of_ne_two hℓ2), ← zpow_natCast (zb ℓ) (3 * ℓ), ← zpow_add₀ zb_ne_zero,
    ← zpow_natCast]
  congr 1; push_cast; ring

lemma natAbs_poleZ (hℓ2 : ℓ ≠ 2) {γ r : ℕ} (hγ : γ < ℓ) (hr : r < 3) :
    poleZ (3 * ℓ - 1) (γ + r * ℓ) = 2 * (γ : ℤ) + 1 + (2 * r - 3) * ℓ := by
  rw [poleZ_eq (hℓ.out.odd_of_ne_two hℓ2)]; push_cast; ring

/-- The pole part of a diagonal entry mod `ℓ`. -/
lemma Cong_pole (hℓ2 : ℓ ≠ 2) {γ r : ℕ} (hγ : γ < ℓ) (hr : r < 3) :
    Cong ℓ ((dPrime (3 * ℓ - 1) (γ + r * ℓ) : Q5) * zK ^ (poleZ (3 * ℓ - 1) (γ + r * ℓ)) *
      Psum (poleZ (3 * ℓ - 1) (γ + r * ℓ))) (eB ℓ γ * dB ℓ r) := by
  set x := poleZ (3 * ℓ - 1) (γ + r * ℓ) with hx
  have hxe : x = 2 * (γ : ℤ) + 1 + (2 * r - 3) * ℓ := natAbs_poleZ hℓ2 hγ hr
  have hev : Even x := by
    rw [hx, poleZ]; exact even_two_mul _
  have hx3 : x.natAbs < 3 * ℓ := by
    have hl := hℓ.out.pos
    interval_cases r <;> omega
  have hP := Cong_Psum hℓ2 hev hx3
  have hk : ((kap r : ℚ) : Q5) = ((kap r : ℤ) : Q5) := by push_cast; rfl
  have e : (dPrime (3 * ℓ - 1) (γ + r * ℓ) : Q5) * zK ^ x * Psum x =
      ((kap r : ℤ) : Q5) * ((Wz ℓ γ (γ + r * ℓ) : ℚ) : Q5) * zK ^ x * ((ℓ : Q5) ^ 2 * Psum x) := by
    rw [dPrime_split hγ hr, Rat.cast_mul, Rat.cast_mul, hk]; push_cast; ring
  rw [e]
  have hC := Cong_mul (Cong_mul (Cong_mul (Cong_intCast (ℓ := ℓ) (kap r)) (Cong_Wz (r := r) hℓ2 hγ))
    (Cong_zK_zpow (ℓ := ℓ) x)) hP
  refine Cong_congr hC rfl ?_
  have hz := zb_poleZ_add hℓ2 γ r
  rw [← hx] at hz
  have hl := hℓ.out.pos
  interval_cases r
  · rw [if_pos (by omega), if_pos (by omega)]
    simp only [eB, dB, kap, hz]; push_cast; ring
  · rw [if_neg (by omega)]
    simp [eB, dB]
  · rw [if_pos (by omega), if_neg (by omega)]
    simp only [eB, dB, kap, hz]
    have hz0 : zb ℓ ^ ℓ ≠ 0 := pow_ne_zero _ zb_ne_zero
    push_cast
    field_simp
    ring

/-- **Steps 3–4**: `G^f(0)` mod `ℓ` in block form. -/
theorem Cong_Afun (hℓ2 : ℓ ≠ 2) {γ γ' r s : ℕ} (hγ : γ < ℓ) (hγ' : γ' < ℓ) (hr : r < 3) (hs : s < 3) :
    Cong ℓ (Afun (3 * ℓ - 1) (fLag (3 * ℓ - 1) (γ + r * ℓ) * fLag (3 * ℓ - 1) (γ' + s * ℓ)))
      (if γ = γ' then eB ℓ γ * (cB ℓ + if r = s then dB ℓ r else 0) else 0) := by
  have hi := lt_three_mul hγ hr
  have hj := lt_three_mul hγ' hs
  have hiγ : (γ + r * ℓ) % ℓ = γ := add_mul_mod_eq hγ
  have hjγ : (γ' + s * ℓ) % ℓ = γ' := add_mul_mod_eq hγ'
  rw [Afun_ff _ (by omega)]
  have hmu := Cong_mu hℓ2 hi hj
  rw [hiγ, hjγ] at hmu
  have hpoly : -(((4 * zb ℓ) ^ ℓ)⁻¹ * zb ℓ ^ (2 * γ + 1)) = eB ℓ γ * cB ℓ := by
    rw [eB, cB, ← zb_poleZ_mul hℓ2 γ]; ring
  by_cases hij : γ + r * ℓ = γ' + s * ℓ
  · have hgg : γ = γ' := by rw [← hiγ, ← hjγ, hij]
    subst hgg
    have hrs : r = s := by
      have : r * ℓ = s * ℓ := by omega
      exact Nat.eq_of_mul_eq_mul_right hℓ.out.pos this
    subst hrs
    rw [if_pos rfl]
    have := Cong_add hmu (Cong_pole hℓ2 hγ hr)
    rw [if_pos rfl, hpoly] at this
    refine Cong_congr this ?_ ?_
    · rfl
    · rw [if_pos rfl, if_pos rfl]; ring
  · rw [if_neg hij, add_zero]
    refine Cong_congr hmu rfl ?_
    by_cases hgg : γ = γ'
    · subst hgg
      have hrs : r ≠ s := fun e => hij (by rw [e])
      rw [if_pos rfl, if_pos rfl, if_neg hrs, hpoly, add_zero]
    · rw [if_neg hgg, if_neg hgg]

end LP
end Chi2U
