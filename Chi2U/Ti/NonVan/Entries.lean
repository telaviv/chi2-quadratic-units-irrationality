/-
# Theorem V_i: the Lagrange Gram matrix `G^f(0)` mod `ℓ` along `h = 3ℓ − 1` (PROOF_TI2 §4, PROOF_U §6 steps 2–4)

**Copy of `Chi2U/NonVan/Entries.lean`** with the sign fixed. Reused from the χ₂ files (they do not see `z`):
`Chi2U.LP.cPole_ff`, `fLag_eq_map`, `Dpoly_eq_map`, `divByMonic_eq_map`, `not_dvd_odd_lt`, and the Lagrange products
mod `ℓ` (`Chi2U/NonVan/PolyMod.lean`: `PZ`, `deriv_PZ_mod`).

For `i = γ + rℓ`, `j = γ′ + sℓ` (`γ, γ′ < ℓ`, `r, s < 3`), with `sgn(x) = (−1)^{x/2}` the `χ₄` pole sign:
* `Bfun_ff`: `B(f_i f_j) = −[i = j] D′(x_i) sgn(x_i) z^{x_i}` (step 2);
* `Afun_ff`: `A(f_i f_j) = μ(f_i f_j div D) + [i = j] D′(x_i) sgn(x_i) z^{x_i} P(x_i)`;
* `Cong_mu`: `μ(f_i f_j div D) ≡ −[γ = γ′] (−1)^γ z^{2γ+1}/(n·z)^ℓ` (progression formula `Cong_Lmom` +
  `deriv_PZ_mod`; χ₂: no `(−1)^γ`, `az` for `n`);
* `Cong_Psum`: `ℓ² P(x) ≡ ε z^ℓ` (`x < −ℓ`), `0` (`|x| < ℓ`), `ε z^{−ℓ}` (`x > ℓ`), `ε = (−1)^{(ℓ−1)/2} = χ₄(ℓ)`
  (χ₂: `z^ℓ`, `0`, `−z^{−ℓ}`): only the term `u = ℓ` of the partial sum is not divisible by `ℓ²`.
Checked exactly (`scripts/ti/check_lemmaP_ti.py`, statements B, L, P).
-/
import Chi2U.Ti.NonVan.Prog
import Chi2U.Ti.NonVan.LemmaB
import Chi2U.NonVan.PolyMod
import Chi2U.NonVan.Entries

namespace Chi2U
namespace Ti
namespace LP

open Polynomial Finset
open Chi2U.LP (cPole_ff divByMonic_eq_map not_dvd_odd_lt PZ deriv_PZ_mod)

variable {n : ℕ} [Fact (3 ≤ n)]

/-! ### Pole coefficients of `f_i f_j` -/

lemma sum_cPole_ff {h i : ℕ} (j : ℕ) (hi : i ≤ h) (F : ℕ → Qt n) :
    ∑ m ∈ range (h + 1), (cPole h (fLag h i * fLag h j) m : Qt n) * F m =
      if i = j then (dPrime h i : Qt n) * F i else 0 := by
  rw [sum_eq_single i]
  · rw [cPole_ff i j hi]
    by_cases hij : i = j
    · rw [if_pos ⟨rfl, hij⟩, if_pos hij]
    · rw [if_neg (fun hh => hij hh.2), if_neg hij]; simp
  · intro m hm hmi
    rw [cPole_ff i j (Nat.lt_succ_iff.mp (mem_range.mp hm)), if_neg (fun hh => hmi hh.1)]
    simp
  · intro hh; exact absurd (mem_range.mpr (Nat.lt_succ_of_le hi)) hh

lemma Bfun_ff {h i : ℕ} (j : ℕ) (hi : i ≤ h) :
    Bfun n h (fLag h i * fLag h j) =
      if i = j then -((dPrime h i : Qt n) * (sgnPole (poleZ h i) : Qt n) * (zK n) ^ (poleZ h i)) else 0 := by
  have := sum_cPole_ff j hi (fun m => (sgnPole (poleZ h m) : Qt n) * (zK n) ^ (poleZ h m))
  simp only [← mul_assoc] at this
  unfold Bfun
  rw [this]
  split_ifs <;> simp

lemma Afun_ff {h i : ℕ} (j : ℕ) (hi : i ≤ h) :
    Afun n h (fLag h i * fLag h j) = muPoly n ((fLag h i * fLag h j) /ₘ Dpoly h) +
      if i = j then (dPrime h i : Qt n) * (sgnPole (poleZ h i) : Qt n) * (zK n) ^ (poleZ h i) *
        Psum n (poleZ h i) else 0 := by
  have := sum_cPole_ff j hi
    (fun m => (sgnPole (poleZ h m) : Qt n) * (zK n) ^ (poleZ h m) * Psum n (poleZ h m))
  simp only [← mul_assoc] at this
  unfold Afun
  rw [this]

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma castHom_intCast (k : ℤ) : ZMod.castHom (dvd_refl ℓ) (Fl n ℓ) (k : ZMod ℓ) = (k : Fl n ℓ) :=
  map_intCast _ k

/-- The polynomial part of `G^f(0)_{ij}` mod `ℓ`. -/
theorem Cong_mu (hℓm : ¬ ℓ ∣ 2 * n) {i j : ℕ} (hi : i < 3 * ℓ) (hj : j < 3 * ℓ) :
    Cong ℓ (muPoly n ((fLag (3 * ℓ - 1) i * fLag (3 * ℓ - 1) j) /ₘ Dpoly (3 * ℓ - 1)))
      (if i % ℓ = j % ℓ then
        -(((((n : ℕ) : Fl n ℓ) * zb n ℓ) ^ ℓ)⁻¹ * ((-1) ^ (i % ℓ) * zb n ℓ ^ (2 * (i % ℓ) + 1))) else 0) := by
  rw [divByMonic_eq_map, muPoly, derivative_map]
  refine Cong_congr (Cong_Lmom hℓm _) rfl ?_
  have hterm : ∀ γ ∈ range ℓ, (-1) ^ γ * zb n ℓ ^ (2 * γ + 1) *
      (((derivative (PZ (3 * ℓ - 1) i j)).eval (2 * (γ : ℤ) + 1) : ℤ) : Fl n ℓ) =
      if γ = i % ℓ then
        (if i % ℓ = j % ℓ then -((-1) ^ (i % ℓ) * zb n ℓ ^ (2 * (i % ℓ) + 1)) else 0) else 0 := by
    intro γ hγ
    rw [← castHom_intCast, deriv_PZ_mod (Chi2U.LP.ne_two_of_not_dvd hℓm) hi hj (mem_range.mp hγ)]
    by_cases h1 : γ = i % ℓ
    · subst h1
      by_cases h2 : i % ℓ = j % ℓ
      · rw [if_pos ⟨rfl, h2.symm⟩, if_pos rfl, if_pos h2]; simp
      · rw [if_neg (fun hh => h2 (hh.1.trans hh.2.symm)), if_pos rfl, if_neg h2]; simp
    · rw [if_neg (fun hh => h1 hh.1.symm), if_neg h1]; simp
  rw [sum_congr rfl hterm, sum_ite_eq' (range ℓ) (i % ℓ), if_pos (mem_range.mpr (Nat.mod_lt _ hℓ.out.pos))]
  split_ifs <;> ring

/-! ### The pole part -/

/-- `ℓ² Σ_{k<N} (−1)^k u^{2k+1}/(2k+1)² ≡ [ℓ < 2N] (−1)^{(ℓ−1)/2} ū^ℓ`. -/
lemma Cong_sum_inv_sq (hℓ2 : ℓ ≠ 2) {u : Qt n} {ub : Fl n ℓ} (hu : Cong ℓ u ub) {N : ℕ}
    (hN : 2 * N < 3 * ℓ + 1) :
    Cong ℓ ((ℓ : Qt n) ^ 2 * ∑ k ∈ range N, (-1) ^ k * u ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : Qt n) ^ 2)
      (if ℓ < 2 * N then (-1) ^ (ℓ / 2) * ub ^ ℓ else 0) := by
  obtain ⟨k₀, hk₀⟩ := hℓ.out.odd_of_ne_two hℓ2
  have hl0 : (ℓ : Qt n) ≠ 0 := by exact_mod_cast hℓ.out.ne_zero
  have hk₀2 : ℓ / 2 = k₀ := by omega
  rw [mul_sum]
  have hterm : ∀ k ∈ range N, Cong ℓ ((ℓ : Qt n) ^ 2 * ((-1) ^ k * u ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : Qt n) ^ 2))
      (if k = k₀ then (-1) ^ (ℓ / 2) * ub ^ ℓ else 0) := by
    intro k hk
    have hk' := mem_range.mp hk
    by_cases hkk : k = k₀
    · subst hkk
      rw [if_pos rfl, hk₀2, ← hk₀]
      refine Cong_congr (Cong_mul (Cong_pow (Cong_neg Cong_one) k) (Cong_pow hu ℓ)) ?_ rfl
      field_simp
    · rw [if_neg hkk]
      refine Cong_zero_of_vGe ?_
      have hnd : ¬ ℓ ∣ 2 * k + 1 := not_dvd_odd_lt hℓ2 ⟨k, rfl⟩ (by omega) (by omega)
      have hr : padicNorm ℓ ((ℓ : ℚ) ^ 2 / ((2 * k + 1 : ℕ) : ℚ) ^ 2) ≤ (ℓ : ℚ) ^ (-(2 : ℤ)) := by
        rw [padicNorm.div, sq, sq, padicNorm.mul, padicNorm.mul, (padicNorm.nat_eq_one_iff _).mpr hnd,
          padicNorm.padicNorm_p_of_prime]
        norm_num [zpow_neg, sq]
      have h1 := vGe_mul (vGe_ratCast_of_padicNorm (n := n) (p := ℓ) hr)
        (vGe_of_pInt (pInt_mul (pInt_pow (pInt_neg pInt_one) k) (pInt_pow hu.mem (2 * k + 1))))
      have e : (((ℓ : ℚ) ^ 2 / ((2 * k + 1 : ℕ) : ℚ) ^ 2 : ℚ) : Qt n) * ((-1) ^ k * u ^ (2 * k + 1)) =
          (ℓ : Qt n) ^ 2 * ((-1) ^ k * u ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : Qt n) ^ 2) := by
        push_cast; ring
      rw [e] at h1
      exact vGe_mono (by norm_num) h1
  refine Cong_congr (Cong_sum _ _ _ hterm) rfl ?_
  rw [sum_ite_eq' (range N) k₀]
  congr 1
  simp only [mem_range, eq_iff_iff]
  omega

/-- `ℓ² P(x)` mod `ℓ`, `x` even with `|x| < 3ℓ` (χ₂: `z^ℓ`, `0`, `−z^{−ℓ}`). -/
lemma Cong_Psum (hℓ2 : ℓ ≠ 2) {x : ℤ} (hx : Even x) (hx3 : x.natAbs < 3 * ℓ) :
    Cong ℓ ((ℓ : Qt n) ^ 2 * Psum n x)
      (if ℓ < x.natAbs then (-1) ^ (ℓ / 2) * (if x ≤ 0 then zb n ℓ ^ ℓ else (zb n ℓ ^ ℓ)⁻¹) else 0) := by
  have h2N : 2 * (x.natAbs / 2) = x.natAbs := by
    have := Int.natAbs_even.mpr hx
    obtain ⟨t, ht⟩ := this; omega
  have hN : 2 * (x.natAbs / 2) < 3 * ℓ + 1 := by omega
  unfold Psum
  by_cases hx0 : x ≤ 0
  · rw [if_pos hx0]
    have := Cong_sum_inv_sq hℓ2 (Cong_zK (n := n) (ℓ := ℓ)) hN
    rw [h2N] at this
    refine Cong_congr this rfl ?_
    split_ifs <;> rfl
  · rw [if_neg hx0]
    have := Cong_sum_inv_sq hℓ2 (Cong_zK_inv (n := n) (ℓ := ℓ)) hN
    rw [h2N] at this
    refine Cong_congr this (by simp only [inv_pow]) ?_
    split_ifs <;> simp [inv_pow]

end LP
end Ti
end Chi2U
