/-
# Theorem V_i: `G^f(0)` mod `ℓ` in block form (PROOF_TI2 §4, PROOF_U §6 steps 3–4)

**Copy of `Chi2U/NonVan/Gram0.lean`** with the sign fixed. Reused from the χ₂ file (they do not see `z`): `kap`, `Wz`,
`lt_three_mul`, `dPrime_split` (`D′(x_i) = ℓ² κ_r W`, `κ = (8, −4, 8)`), `padicValRat_dPrime` (`v_ℓ(D′(x_i)) = 2`).

New here: the `χ₄` pole signs along a class, `sgn(x_{γ+rℓ}) = (−1)^γ (−1)^r τ` with `τ = (−1)^{(3ℓ−1)/2}`
(`sgnPole_class`), and
* **`Cong_Afun`**: `G^f(0)_{γ+rℓ, γ′+sℓ} ≡ [γ = γ′]·e_γ·(c + [r = s] d_r)` with
  `e_γ = −(−1)^γ τ z^{x_γ}` (`= −sgn(x_γ) z^{x_γ}`), `c = τ z^{3ℓ}/(n·z)^ℓ`, `d = (8ε z^ℓ, 0, 8ε z^{3ℓ})`,
  `ε = (−1)^{(ℓ−1)/2}` (χ₂: `e_γ = −z^{x_γ}`, `c = z^{3ℓ}/(az·z)^ℓ`, `d = (8z^ℓ, 0, −8z^{3ℓ})`).
This is PROOF_TI2 §4's block `e_γ M`, `M = c𝟙𝟙ᵀ + diag(d₀, 0, d₂)`, read in `K = ℚ(√d)` with `y = −z²` and `ζ = z^ℓ`
itself (no Frobenius case split). Checked exactly in all three splitting types (`scripts/ti/check_lemmaP_ti.py`, G).
-/
import Chi2U.Ti.NonVan.Entries
import Chi2U.NonVan.Gram0

namespace Chi2U
namespace Ti
namespace LP

open Polynomial Finset
open Chi2U.LP (kap Wz lt_three_mul dPrime_split padicValRat_dPrime poleZ_eq abar_of_mod Ubar_eq add_mul_mod_eq)

variable {n : ℕ} [Fact (3 ≤ n)] {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma Cong_Wz (hℓ2 : ℓ ≠ 2) {γ r : ℕ} (hγ : γ < ℓ) :
    Cong ℓ ((Wz ℓ γ (γ + r * ℓ) : ℚ) : Qt n) (-1) := by
  rw [Rat.cast_intCast]
  refine Cong_congr (Cong_intCast _) rfl ?_
  rw [← castHom_intCast, Wz, Int.cast_prod]
  simp only [Int.cast_sub]
  rw [abar_of_mod hℓ2 hγ (add_mul_mod_eq hγ), Ubar_eq hℓ2 hγ, map_neg, map_one]

omit [Fact (3 ≤ n)] in
/-- The `χ₄` pole sign along a class: `sgn(x_{γ+rℓ}) = (−1)^γ (−1)^r (−1)^{(3ℓ−1)/2}`. -/
lemma sgnPole_class (hℓ2 : ℓ ≠ 2) (γ r : ℕ) :
    sgnPole (poleZ (3 * ℓ - 1) (γ + r * ℓ)) = (-1) ^ γ * (-1) ^ r * (-1) ^ ((3 * ℓ - 1) / 2) := by
  have hodd := hℓ.out.odd_of_ne_two hℓ2
  rw [sgnPole, poleZ_eq hodd]
  obtain ⟨t, rfl⟩ := hodd
  have e1 : (2 * ((γ + r * (2 * t + 1) : ℕ) : ℤ) + 1 - 3 * ((2 * t + 1 : ℕ) : ℤ)) / 2 =
      (γ : ℤ) + 2 * ((r : ℤ) * t) + r - 3 * t - 1 := by
    rw [show (2 * ((γ + r * (2 * t + 1) : ℕ) : ℤ) + 1 - 3 * ((2 * t + 1 : ℕ) : ℤ)) =
      2 * ((γ : ℤ) + 2 * ((r : ℤ) * t) + r - 3 * t - 1) by push_cast; ring]
    omega
  have e2 : (3 * (2 * t + 1) - 1) / 2 = 3 * t + 1 := by omega
  rw [e1, e2, ← pow_add, ← pow_add, neg_one_pow_eq_pow_mod_two (R := ℚ),
    neg_one_pow_eq_pow_mod_two (R := ℚ) (n := γ + r + (3 * t + 1))]
  congr 1
  omega

/-! ### The block entries -/

variable (n ℓ) in
/-- `τ = (−1)^{(3ℓ−1)/2}`. -/
noncomputable def tauB : Fl n ℓ := (-1) ^ ((3 * ℓ - 1) / 2)

variable (n ℓ) in
/-- `e_γ = −(−1)^γ τ z^{x_γ}`. -/
noncomputable def eB (γ : ℕ) : Fl n ℓ := -((-1) ^ γ * tauB n ℓ) * zb n ℓ ^ poleZ (3 * ℓ - 1) γ

variable (n ℓ) in
/-- `c = τ z^{3ℓ}/(n·z)^ℓ`. -/
noncomputable def cB : Fl n ℓ := tauB n ℓ * ((((n : ℕ) : Fl n ℓ) * zb n ℓ) ^ ℓ)⁻¹ * zb n ℓ ^ (3 * ℓ)

variable (n ℓ) in
/-- `d = (8ε z^ℓ, 0, 8ε z^{3ℓ})`, `ε = (−1)^{(ℓ−1)/2}`. -/
noncomputable def dB (r : ℕ) : Fl n ℓ :=
  if r = 0 then 8 * (-1) ^ (ℓ / 2) * zb n ℓ ^ ℓ else if r = 1 then 0 else 8 * (-1) ^ (ℓ / 2) * zb n ℓ ^ (3 * ℓ)

lemma tauB_mul_self : tauB n ℓ * tauB n ℓ = 1 := by
  rw [tauB, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

lemma tauB_ne_zero : tauB n ℓ ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)

lemma zb_poleZ_add (hℓ2 : ℓ ≠ 2) (γ r : ℕ) :
    zb n ℓ ^ poleZ (3 * ℓ - 1) (γ + r * ℓ) = zb n ℓ ^ poleZ (3 * ℓ - 1) γ * zb n ℓ ^ (2 * r * ℓ) := by
  rw [poleZ_eq (hℓ.out.odd_of_ne_two hℓ2), poleZ_eq (hℓ.out.odd_of_ne_two hℓ2), ← zpow_natCast,
    ← zpow_add₀ zb_ne_zero]
  congr 1; push_cast; ring

lemma zb_poleZ_mul (hℓ2 : ℓ ≠ 2) (γ : ℕ) :
    zb n ℓ ^ poleZ (3 * ℓ - 1) γ * zb n ℓ ^ (3 * ℓ) = zb n ℓ ^ (2 * γ + 1) := by
  rw [poleZ_eq (hℓ.out.odd_of_ne_two hℓ2), ← zpow_natCast (zb n ℓ) (3 * ℓ), ← zpow_add₀ zb_ne_zero,
    ← zpow_natCast]
  congr 1; push_cast; ring

omit [Fact (3 ≤ n)] in
lemma natAbs_poleZ (hℓ2 : ℓ ≠ 2) {γ r : ℕ} (hγ : γ < ℓ) (hr : r < 3) :
    poleZ (3 * ℓ - 1) (γ + r * ℓ) = 2 * (γ : ℤ) + 1 + (2 * r - 3) * ℓ := by
  rw [poleZ_eq (hℓ.out.odd_of_ne_two hℓ2)]; push_cast; ring

/-- The pole part of a diagonal entry mod `ℓ`. -/
lemma Cong_pole (hℓ2 : ℓ ≠ 2) {γ r : ℕ} (hγ : γ < ℓ) (hr : r < 3) :
    Cong ℓ ((dPrime (3 * ℓ - 1) (γ + r * ℓ) : Qt n) * (sgnPole (poleZ (3 * ℓ - 1) (γ + r * ℓ)) : Qt n) *
      (zK n) ^ (poleZ (3 * ℓ - 1) (γ + r * ℓ)) * Psum n (poleZ (3 * ℓ - 1) (γ + r * ℓ)))
      (eB n ℓ γ * dB n ℓ r) := by
  set x := poleZ (3 * ℓ - 1) (γ + r * ℓ) with hx
  have hxe : x = 2 * (γ : ℤ) + 1 + (2 * r - 3) * ℓ := natAbs_poleZ hℓ2 hγ hr
  have hev : Even x := by
    rw [hx, poleZ]; exact even_two_mul _
  have hx3 : x.natAbs < 3 * ℓ := by
    have hl := hℓ.out.pos
    interval_cases r <;> omega
  have hP := Cong_Psum (n := n) hℓ2 hev hx3
  have hk : ((kap r : ℚ) : Qt n) = ((kap r : ℤ) : Qt n) := by push_cast; rfl
  have hs : ((sgnPole x : ℚ) : Qt n) = (-1) ^ γ * (-1) ^ r * (-1) ^ ((3 * ℓ - 1) / 2) := by
    rw [hx, sgnPole_class hℓ2 γ r]; push_cast; ring
  have e : (dPrime (3 * ℓ - 1) (γ + r * ℓ) : Qt n) * (sgnPole x : Qt n) * (zK n) ^ x * Psum n x =
      ((kap r : ℤ) : Qt n) * ((Wz ℓ γ (γ + r * ℓ) : ℚ) : Qt n) *
        ((-1) ^ γ * (-1) ^ r * (-1) ^ ((3 * ℓ - 1) / 2)) * (zK n) ^ x * ((ℓ : Qt n) ^ 2 * Psum n x) := by
    rw [hs, dPrime_split hγ hr, Rat.cast_mul, Rat.cast_mul, hk]; push_cast; ring
  rw [e]
  have hsgn : Cong ℓ ((-1 : Qt n) ^ γ * (-1) ^ r * (-1) ^ ((3 * ℓ - 1) / 2))
      ((-1) ^ γ * (-1) ^ r * tauB n ℓ) :=
    Cong_mul (Cong_mul (Cong_pow (Cong_neg Cong_one) _) (Cong_pow (Cong_neg Cong_one) _))
      (Cong_pow (Cong_neg Cong_one) _)
  have hC := Cong_mul (Cong_mul (Cong_mul (Cong_mul (Cong_intCast (ℓ := ℓ) (kap r)) (Cong_Wz (r := r) hℓ2 hγ))
    hsgn) (Cong_zK_zpow (ℓ := ℓ) x)) hP
  refine Cong_congr hC rfl ?_
  have hz := zb_poleZ_add (n := n) hℓ2 γ r
  rw [← hx] at hz
  have hl := hℓ.out.pos
  interval_cases r
  · rw [if_pos (by omega), if_pos (by omega)]
    simp only [eB, dB, kap, hz]; push_cast; ring
  · rw [if_neg (by omega)]
    simp [eB, dB]
  · rw [if_pos (by omega), if_neg (by omega)]
    simp only [eB, dB, kap, hz]
    have hz0 : zb n ℓ ^ ℓ ≠ 0 := pow_ne_zero _ zb_ne_zero
    push_cast
    field_simp
    ring

/-- **Steps 3–4**: `G^f(0)` mod `ℓ` in block form. -/
theorem Cong_Afun (hℓm : ¬ ℓ ∣ 2 * n) {γ γ' r s : ℕ} (hγ : γ < ℓ) (hγ' : γ' < ℓ) (hr : r < 3) (hs : s < 3) :
    Cong ℓ (Afun n (3 * ℓ - 1) (fLag (3 * ℓ - 1) (γ + r * ℓ) * fLag (3 * ℓ - 1) (γ' + s * ℓ)))
      (if γ = γ' then eB n ℓ γ * (cB n ℓ + if r = s then dB n ℓ r else 0) else 0) := by
  have hℓ2 : ℓ ≠ 2 := Chi2U.LP.ne_two_of_not_dvd hℓm
  have hi := lt_three_mul hγ hr
  have hj := lt_three_mul hγ' hs
  have hiγ : (γ + r * ℓ) % ℓ = γ := add_mul_mod_eq hγ
  have hjγ : (γ' + s * ℓ) % ℓ = γ' := add_mul_mod_eq hγ'
  rw [Afun_ff _ (by omega)]
  have hmu := Cong_mu hℓm hi hj
  rw [hiγ, hjγ] at hmu
  have hpoly : -(((((n : ℕ) : Fl n ℓ) * zb n ℓ) ^ ℓ)⁻¹ * ((-1) ^ γ * zb n ℓ ^ (2 * γ + 1))) =
      eB n ℓ γ * cB n ℓ := by
    rw [eB, cB, ← zb_poleZ_mul hℓ2 γ]
    linear_combination (((((n : ℕ) : Fl n ℓ) * zb n ℓ) ^ ℓ)⁻¹ * (-1) ^ γ * zb n ℓ ^ poleZ (3 * ℓ - 1) γ *
      zb n ℓ ^ (3 * ℓ)) * tauB_mul_self (n := n) (ℓ := ℓ)
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
end Ti
end Chi2U
