/-
# Theorem V_i: the progression formula for the moments mod `ℓ` (PROOF_TI2 §4, PROOF_U §6 steps 3–4)

**Copy of `Chi2U/NonVan/Prog.lean`** with the sign fixed: the weights are `χ₄(t) z^t`, so with `y = −z²` every χ₂
formula holds with `y` in place of `z²` and `χ₄(2j+1) = (−1)^j` in the progression sums.

* `Lmom_shift` (exact): `Lmom(p(t − 2k)) = y^k Lmom(p) + Σ_{j<k} (−1)^j z^{2j+1} p(2j+1−2k)` (iterate rec₁,
  `Lmom(p(t−2)) = y·Lmom(p) + z·p(−1)`).
* `Cong_Lmom`: for `P ∈ ℤ[t]` and a prime `ℓ ∤ 2n`,
    `Lmom(P) ≡ (n·z)^{−ℓ} Σ_{j<ℓ} (−1)^j z^{2j+1} P(2j+1)`  in the residue field `Fl n ℓ`.
  Proof: `Lmom(P(t − 2ℓ)) ≡ Lmom(P)` (the values at odd `t` agree mod `ℓ`; `vGe_Lmom_odd`, needs `ℓ ∤ n`), so the
  shift identity with `k = ℓ` gives `(1 − y^ℓ) Lmom(P) ≡ Σ_{j<ℓ} (−1)^j z^{2j+1} P(2j+1)`, and
  `1 − ȳ^ℓ = (1 − ȳ)^ℓ = (n·z̄)^ℓ` (Frobenius in characteristic `ℓ`, `1 − y = 1 + z² = n z`). As in the χ₂ file no
  Frobenius identification of `ζ = z^ℓ` (PROOF_TI2's `w^ℓ ≡ ζ` case split) is needed.
-/
import Chi2U.Ti.NonVan.ModL

namespace Chi2U
namespace Ti
namespace LP

open Polynomial Finset

variable {n : ℕ} [Fact (3 ≤ n)]

/-- The shift identity. -/
lemma Lmom_shift (p : ℚ[X]) (k : ℕ) :
    Lmom n (p.comp (X - C (2 * (k : ℚ)))) =
      (-(zK n) ^ 2) ^ k * Lmom n p +
        ∑ j ∈ range k, (-1) ^ j * (zK n) ^ (2 * j + 1) * ((p.eval (2 * (j : ℚ) + 1 - 2 * k) : ℚ) : Qt n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hc : p.comp (X - C (2 * ((k + 1 : ℕ) : ℚ))) = (p.comp (X - C (2 * (k : ℚ)))).comp (X - C 2) := by
      rw [comp_assoc, sub_comp, X_comp, C_comp]
      congr 1
      rw [sub_sub, ← C_add]
      congr 2
      push_cast; ring
    rw [hc]
    have h1 := Lmom_rec1 (n := n) (p.comp (X - C (2 * (k : ℚ))))
    rw [ih, eval_comp] at h1
    simp only [eval_sub, eval_X, eval_C] at h1
    rw [sum_range_succ']
    have hsum : ∑ j ∈ range k, (-1) ^ (j + 1) * (zK n) ^ (2 * (j + 1) + 1) *
        ((p.eval (2 * ((j + 1 : ℕ) : ℚ) + 1 - 2 * ((k + 1 : ℕ) : ℚ)) : ℚ) : Qt n) =
        (-(zK n) ^ 2) * ∑ j ∈ range k, (-1) ^ j * (zK n) ^ (2 * j + 1) *
          ((p.eval (2 * (j : ℚ) + 1 - 2 * k) : ℚ) : Qt n) := by
      rw [mul_sum]
      refine sum_congr rfl (fun j _ => ?_)
      have : (2 * ((j + 1 : ℕ) : ℚ) + 1 - 2 * ((k + 1 : ℕ) : ℚ)) = 2 * (j : ℚ) + 1 - 2 * k := by
        push_cast; ring
      rw [this]; ring
    rw [hsum]
    have h0 : (2 * ((0 : ℕ) : ℚ) + 1 - 2 * ((k + 1 : ℕ) : ℚ)) = -1 - 2 * k := by push_cast; ring
    rw [h0]
    linear_combination h1

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma eval_map_int (P : ℤ[X]) (a : ℤ) : (P.map (Int.castRingHom ℚ)).eval (a : ℚ) = ((P.eval a : ℤ) : ℚ) := by
  rw [eval_intCast_map]; rfl

/-- **Progression formula** mod `ℓ`. -/
theorem Cong_Lmom (hℓm : ¬ ℓ ∣ 2 * n) (P : ℤ[X]) :
    Cong ℓ (Lmom n (P.map (Int.castRingHom ℚ)))
      (((((n : ℕ) : Fl n ℓ) * zb n ℓ) ^ ℓ)⁻¹ *
        ∑ j ∈ range ℓ, (-1) ^ j * zb n ℓ ^ (2 * j + 1) * ((P.eval (2 * (j : ℤ) + 1) : ℤ) : Fl n ℓ)) := by
  set p := P.map (Int.castRingHom ℚ) with hp
  have hcast : ∀ k : ℕ, (2 * (k : ℚ) + 1) = ((2 * (k : ℤ) + 1 : ℤ) : ℚ) := fun k => by push_cast; ring
  have hint : vGe ℓ 0 (Lmom n p) := vGe_Lmom_odd (fun h => hℓm (Dvd.dvd.mul_left h 2)) p 0 (fun k => by
    rw [hcast, hp, eval_map_int]; simpa using padicNorm.of_int (p := ℓ) _)
  obtain ⟨L, hL⟩ : ∃ L, Cong ℓ (Lmom n p) L := ⟨_, Cong_red ⟨_, pInt_of_vGe hint⟩⟩
  have hsh : vGe ℓ 1 (Lmom n (p.comp (X - C (2 * (ℓ : ℚ)))) - Lmom n p) := by
    rw [← map_sub]
    refine vGe_Lmom_odd (fun h => hℓm (Dvd.dvd.mul_left h 2)) _ 1 (fun k => ?_)
    rw [eval_sub, eval_comp, eval_sub, eval_X, eval_C, hcast,
      show ((2 * (k : ℤ) + 1 : ℤ) : ℚ) - 2 * (ℓ : ℚ) = ((2 * (k : ℤ) + 1 - 2 * ℓ : ℤ) : ℚ) by push_cast; ring,
      hp, eval_map_int, eval_map_int, ← Int.cast_sub]
    have hd : ((ℓ ^ 1 : ℕ) : ℤ) ∣ P.eval (2 * (k : ℤ) + 1 - 2 * ℓ) - P.eval (2 * (k : ℤ) + 1) := by
      have := Polynomial.sub_dvd_eval_sub (2 * (k : ℤ) + 1 - 2 * ℓ) (2 * (k : ℤ) + 1) P
      refine dvd_trans ⟨-2, ?_⟩ this
      push_cast; ring
    exact padicNorm.dvd_iff_norm_le.mp hd
  have hL' : Cong ℓ (Lmom n (p.comp (X - C (2 * (ℓ : ℚ))))) L := Cong_of_vGe_sub hL hsh
  rw [Lmom_shift] at hL'
  have hS : Cong ℓ (∑ j ∈ range ℓ, (-1) ^ j * (zK n) ^ (2 * j + 1) *
        ((p.eval (2 * (j : ℚ) + 1 - 2 * ℓ) : ℚ) : Qt n))
      (∑ j ∈ range ℓ, (-1) ^ j * zb n ℓ ^ (2 * j + 1) * ((P.eval (2 * (j : ℤ) + 1) : ℤ) : Fl n ℓ)) := by
    refine Cong_sum _ _ _ (fun j _ => Cong_mul (Cong_mul (Cong_pow (Cong_neg Cong_one) _) (Cong_pow Cong_zK _)) ?_)
    rw [show (2 * (j : ℚ) + 1 - 2 * ℓ) = ((2 * (j : ℤ) + 1 - 2 * ℓ : ℤ) : ℚ) by push_cast; ring, hp,
      eval_map_int, Rat.cast_intCast]
    refine Cong_congr (Cong_intCast _) rfl ?_
    rw [CharP.intCast_eq_intCast (Fl n ℓ) ℓ]
    apply Int.ModEq.symm
    rw [Int.modEq_iff_dvd]
    have := Polynomial.sub_dvd_eval_sub (2 * (j : ℤ) + 1 - 2 * ℓ) (2 * (j : ℤ) + 1) P
    refine dvd_trans ⟨-2, ?_⟩ this
    ring
  have hrhs := Cong_add (Cong_mul (Cong_pow (Cong_neg (Cong_pow (Cong_zK (ℓ := ℓ)) 2)) ℓ) hL) hS
  have heq := hL'.unique hrhs
  have hfrob : (((n : ℕ) : Fl n ℓ) * zb n ℓ) ^ ℓ = 1 - (-zb n ℓ ^ 2) ^ ℓ := by
    rw [← one_add_zb_sq, show (1 : Fl n ℓ) + zb n ℓ ^ 2 = 1 - (-zb n ℓ ^ 2) by ring, sub_pow_char, one_pow]
  have hne : (((n : ℕ) : Fl n ℓ) * zb n ℓ) ^ ℓ ≠ 0 := pow_ne_zero _ (mul_ne_zero (n_ne_zero_Fl hℓm) zb_ne_zero)
  have : L = ((((n : ℕ) : Fl n ℓ) * zb n ℓ) ^ ℓ)⁻¹ *
      ∑ j ∈ range ℓ, (-1) ^ j * zb n ℓ ^ (2 * j + 1) * ((P.eval (2 * (j : ℤ) + 1) : ℤ) : Fl n ℓ) := by
    rw [eq_inv_mul_iff_mul_eq₀ hne, hfrob]
    linear_combination heq
  rw [← this]; exact hL

end LP
end Ti
end Chi2U
