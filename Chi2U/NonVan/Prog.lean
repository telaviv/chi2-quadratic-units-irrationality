/-
# The progression formula for the moments mod `ℓ` (PROOF_U §6, steps 3–4)

* `Lmom_shift` (exact): `Lmom(p(t − 2n)) = z^{2n} Lmom(p) + Σ_{j<n} z^{2j+1} p(2j+1−2n)` (iterate rec₁).
* `Cong_Lmom`: for `P ∈ ℤ[t]` and an odd prime `ℓ`,
    `Lmom(P) ≡ (4z)^{−ℓ} Σ_{j<ℓ} z^{2j+1} P(2j+1)`  in the residue field `Fl ℓ`.
  Proof: `Lmom(P(t − 2ℓ)) ≡ Lmom(P)` (the values at odd `t` agree mod `ℓ`; `vGe_Lmom_odd`), so the shift identity
  with `n = ℓ` gives `(1 − z^{2ℓ}) Lmom(P) ≡ Σ_{j<ℓ} z^{2j+1} P(2j+1)`, and `1 − z̄^{2ℓ} = (1 − z̄²)^ℓ = (4z̄)^ℓ`
  (Frobenius in characteristic `ℓ`). This is PROOF_U's progression sum `Σ_γ z^{t_γ} F′(t_γ)/(1 − ζ²)` with
  `t_γ = 2γ + 1`, `ζ = z^ℓ`; no Frobenius identification of `ζ` is needed.
-/
import Chi2U.NonVan.ModL

namespace Chi2U
namespace LP

open Polynomial Finset

/-- The shift identity. -/
lemma Lmom_shift (p : ℚ[X]) (n : ℕ) :
    Lmom 2 (p.comp (X - C (2 * (n : ℚ)))) =
      (zK 2) ^ (2 * n) * Lmom 2 p +
        ∑ j ∈ range n, (zK 2) ^ (2 * j + 1) * ((p.eval (2 * (j : ℚ) + 1 - 2 * n) : ℚ) : Q5) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : p.comp (X - C (2 * ((n + 1 : ℕ) : ℚ))) = (p.comp (X - C (2 * (n : ℚ)))).comp (X - C 2) := by
      rw [comp_assoc, sub_comp, X_comp, C_comp]
      congr 1
      rw [sub_sub, ← C_add]
      congr 2
      push_cast; ring
    rw [hc]
    have h1 := Lmom_rec1 (mz := 2) (p.comp (X - C (2 * (n : ℚ))))
    rw [ih, eval_comp] at h1
    simp only [eval_sub, eval_X, eval_C] at h1
    rw [sum_range_succ']
    have hsum : ∑ j ∈ range n, (zK 2) ^ (2 * (j + 1) + 1) *
        ((p.eval (2 * ((j + 1 : ℕ) : ℚ) + 1 - 2 * ((n + 1 : ℕ) : ℚ)) : ℚ) : Q5) =
        (zK 2) ^ 2 * ∑ j ∈ range n, (zK 2) ^ (2 * j + 1) * ((p.eval (2 * (j : ℚ) + 1 - 2 * n) : ℚ) : Q5) := by
      rw [mul_sum]
      refine sum_congr rfl (fun j _ => ?_)
      have : (2 * ((j + 1 : ℕ) : ℚ) + 1 - 2 * ((n + 1 : ℕ) : ℚ)) = 2 * (j : ℚ) + 1 - 2 * n := by
        push_cast; ring
      rw [this]; ring
    rw [hsum]
    have h0 : (2 * ((0 : ℕ) : ℚ) + 1 - 2 * ((n + 1 : ℕ) : ℚ)) = -1 - 2 * n := by push_cast; ring
    rw [h0]
    linear_combination h1

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma eval_map_int (P : ℤ[X]) (a : ℤ) : (P.map (Int.castRingHom ℚ)).eval (a : ℚ) = ((P.eval a : ℤ) : ℚ) := by
  rw [eval_intCast_map]; rfl

/-- **Progression formula** mod `ℓ`. -/
theorem Cong_Lmom (hℓ2 : ℓ ≠ 2) (P : ℤ[X]) :
    Cong ℓ (Lmom 2 (P.map (Int.castRingHom ℚ)))
      (((4 * zb ℓ) ^ ℓ)⁻¹ * ∑ j ∈ range ℓ, zb ℓ ^ (2 * j + 1) * ((P.eval (2 * (j : ℤ) + 1) : ℤ) : Fl ℓ)) := by
  set p := P.map (Int.castRingHom ℚ) with hp
  have hcast : ∀ k : ℕ, (2 * (k : ℚ) + 1) = ((2 * (k : ℤ) + 1 : ℤ) : ℚ) := fun k => by push_cast; ring
  have hint : vGe ℓ 0 (Lmom 2 p) := vGe_Lmom_odd_two hℓ2 p 0 (fun k => by
    rw [hcast, hp, eval_map_int]; simpa using padicNorm.of_int (p := ℓ) _)
  obtain ⟨L, hL⟩ : ∃ L, Cong ℓ (Lmom 2 p) L := ⟨_, Cong_red ⟨_, pInt_of_vGe hint⟩⟩
  have hsh : vGe ℓ 1 (Lmom 2 (p.comp (X - C (2 * (ℓ : ℚ)))) - Lmom 2 p) := by
    rw [← map_sub]
    refine vGe_Lmom_odd_two hℓ2 _ 1 (fun k => ?_)
    rw [eval_sub, eval_comp, eval_sub, eval_X, eval_C, hcast,
      show ((2 * (k : ℤ) + 1 : ℤ) : ℚ) - 2 * (ℓ : ℚ) = ((2 * (k : ℤ) + 1 - 2 * ℓ : ℤ) : ℚ) by push_cast; ring,
      hp, eval_map_int, eval_map_int, ← Int.cast_sub]
    have hd : ((ℓ ^ 1 : ℕ) : ℤ) ∣ P.eval (2 * (k : ℤ) + 1 - 2 * ℓ) - P.eval (2 * (k : ℤ) + 1) := by
      have := Polynomial.sub_dvd_eval_sub (2 * (k : ℤ) + 1 - 2 * ℓ) (2 * (k : ℤ) + 1) P
      refine dvd_trans ⟨-2, ?_⟩ this
      push_cast; ring
    exact padicNorm.dvd_iff_norm_le.mp hd
  have hL' : Cong ℓ (Lmom 2 (p.comp (X - C (2 * (ℓ : ℚ))))) L := Cong_of_vGe_sub hL hsh
  rw [Lmom_shift] at hL'
  have hS : Cong ℓ (∑ j ∈ range ℓ, (zK 2) ^ (2 * j + 1) * ((p.eval (2 * (j : ℚ) + 1 - 2 * ℓ) : ℚ) : Q5))
      (∑ j ∈ range ℓ, zb ℓ ^ (2 * j + 1) * ((P.eval (2 * (j : ℤ) + 1) : ℤ) : Fl ℓ)) := by
    refine Cong_sum _ _ _ (fun j _ => Cong_mul (Cong_pow Cong_zK _) ?_)
    rw [show (2 * (j : ℚ) + 1 - 2 * ℓ) = ((2 * (j : ℤ) + 1 - 2 * ℓ : ℤ) : ℚ) by push_cast; ring, hp,
      eval_map_int, Rat.cast_intCast]
    refine Cong_congr (Cong_intCast _) rfl ?_
    rw [CharP.intCast_eq_intCast (Fl ℓ) ℓ]
    apply Int.ModEq.symm
    rw [Int.modEq_iff_dvd]
    have := Polynomial.sub_dvd_eval_sub (2 * (j : ℤ) + 1 - 2 * ℓ) (2 * (j : ℤ) + 1) P
    refine dvd_trans ⟨-2, ?_⟩ this
    ring
  have hrhs := Cong_add (Cong_mul (Cong_pow (Cong_zK (ℓ := ℓ)) (2 * ℓ)) hL) hS
  have heq := hL'.unique hrhs
  have hfrob : (4 * zb ℓ) ^ ℓ = 1 - zb ℓ ^ (2 * ℓ) := by
    rw [← one_sub_zb_sq, sub_pow_char, one_pow, pow_mul]
  have hne : (4 * zb ℓ) ^ ℓ ≠ 0 := pow_ne_zero _ (mul_ne_zero (four_ne_zero_Fl hℓ2) zb_ne_zero)
  have : L = ((4 * zb ℓ) ^ ℓ)⁻¹ *
      ∑ j ∈ range ℓ, zb ℓ ^ (2 * j + 1) * ((P.eval (2 * (j : ℤ) + 1) : ℤ) : Fl ℓ) := by
    rw [eq_inv_mul_iff_mul_eq₀ hne, hfrob]
    linear_combination heq
  rw [← this]; exact hL

end LP
end Chi2U
