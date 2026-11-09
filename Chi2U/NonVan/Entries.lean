/-
# The Lagrange Gram matrix `G^f(0)` mod `ℓ` along `h = 3ℓ − 1` (PROOF_U §6, steps 2–4)

For `i = γ + rℓ`, `j = γ′ + sℓ` (`γ, γ′ < ℓ`, `r, s < 3`):
* `Bfun_ff`: `B(f_i f_j) = −[i = j] D′(x_i) z^{x_i}` (step 2);
* `Afun_ff`: `A(f_i f_j) = μ(f_i f_j div D) + [i = j] D′(x_i) z^{x_i} P(x_i)`;
* `Cong_mu`: `μ(f_i f_j div D) ≡ −[γ = γ′] z^{2γ+1}/(az·z)^ℓ` (progression formula `Cong_Lmom` + `deriv_PZ_mod`);
* `dPrime_split`: `D′(x_i) = ℓ²·κ_r·W` with `κ = (8, −4, 8)` and `W = Π_{m ≢ γ}(x_i − x_m) ≡ U_γ = −1`;
* `Cong_Psum`: `ℓ² P(x) ≡ z^ℓ` (`x < −ℓ`), `0` (`|x| < ℓ`), `−z^{−ℓ}` (`x > ℓ`): only `n = ±ℓ` is divisible by `ℓ`;
* **`Cong_Afun`** (steps 3–4): `G^f(0)_{ij} ≡ [γ = γ′]·e_γ·(c + [r = s] d_r)` with `e_γ = −z^{x_γ}`,
  `c = z^{3ℓ}/(az·z)^ℓ`, `d = (8z^ℓ, 0, −8z^{3ℓ})`. (PROOF_U's `c = ζ³/(1 − ζ²)`, `ζ = z^ℓ`: `1 − ζ̄² = (az·z̄)^ℓ`.)

Parametric in `az` (Theorem V, Lemma P′_m); the hypothesis `ℓ ∤ az` makes `az·z̄` a unit.
-/
import Chi2U.NonVan.PolyMod
import Chi2U.Arith.LemmaB

namespace Chi2U
namespace LP

open Polynomial Finset

variable {az : ℕ} [Fact (1 ≤ az)]

/-! ### Pole coefficients of `f_i f_j` (as in `Arith/OddPrimes.lean`) -/

lemma cPole_ff {h : ℕ} (i j : ℕ) {m : ℕ} (hm : m ≤ h) :
    cPole h (fLag h i * fLag h j) m = if m = i ∧ m = j then dPrime h i else 0 := by
  unfold cPole
  rw [eval_mul, LB.eval_fLag i hm, LB.eval_fLag j hm]
  by_cases h1 : m = i
  · subst h1
    by_cases h2 : m = j
    · subst h2
      rw [if_pos rfl, if_pos ⟨rfl, rfl⟩, mul_div_assoc, div_self (LB.dPrime_ne_zero h m), mul_one]
    · rw [if_pos rfl, if_neg h2, if_neg (fun hh => h2 hh.2), mul_zero, zero_div]
  · rw [if_neg h1, zero_mul, zero_div, if_neg (fun hh => h1 hh.1)]

lemma sum_cPole_ff {h i : ℕ} (j : ℕ) (hi : i ≤ h) (F : ℕ → Qd az) :
    ∑ m ∈ range (h + 1), (cPole h (fLag h i * fLag h j) m : Qd az) * F m =
      if i = j then (dPrime h i : Qd az) * F i else 0 := by
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
    Bfun az h (fLag h i * fLag h j) = if i = j then -((dPrime h i : Qd az) * (zK az) ^ (poleZ h i)) else 0 := by
  have := sum_cPole_ff j hi (fun m => (zK az) ^ (poleZ h m))
  unfold Bfun
  rw [this]
  split_ifs <;> simp

lemma Afun_ff {h i : ℕ} (j : ℕ) (hi : i ≤ h) :
    Afun az h (fLag h i * fLag h j) = muPoly az ((fLag h i * fLag h j) /ₘ Dpoly h) +
      if i = j then (dPrime h i : Qd az) * (zK az) ^ (poleZ h i) * Psum az (poleZ h i) else 0 := by
  have := sum_cPole_ff j hi (fun m => (zK az) ^ (poleZ h m) * Psum az (poleZ h m))
  simp only [← mul_assoc] at this
  unfold Afun
  rw [this]

/-! ### Integer forms -/

lemma fLag_eq_map (h i : ℕ) : fLag h i = (fZ h i).map (Int.castRingHom ℚ) := by
  simp [fLag, fZ, Polynomial.map_prod]

lemma Dpoly_eq_map (h : ℕ) : Dpoly h = (DZ h).map (Int.castRingHom ℚ) := by
  simp [Dpoly, DZ, Polynomial.map_prod]

lemma divByMonic_eq_map (h i j : ℕ) :
    (fLag h i * fLag h j) /ₘ Dpoly h = (PZ h i j).map (Int.castRingHom ℚ) := by
  rw [PZ, map_divByMonic _ (DZ_monic h), Polynomial.map_mul, ← fLag_eq_map, ← fLag_eq_map, ← Dpoly_eq_map]

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma castHom_intCast (n : ℤ) : ZMod.castHom (dvd_refl ℓ) (Fl az ℓ) (n : ZMod ℓ) = (n : Fl az ℓ) := map_intCast _ n

/-- The polynomial part of `G^f(0)_{ij}` mod `ℓ`. -/
theorem Cong_mu (hℓm : ¬ ℓ ∣ 2 * az) {i j : ℕ} (hi : i < 3 * ℓ) (hj : j < 3 * ℓ) :
    Cong ℓ (muPoly az ((fLag (3 * ℓ - 1) i * fLag (3 * ℓ - 1) j) /ₘ Dpoly (3 * ℓ - 1)))
      (if i % ℓ = j % ℓ then -(((((az : ℕ) : Fl az ℓ) * zb az ℓ) ^ ℓ)⁻¹ * zb az ℓ ^ (2 * (i % ℓ) + 1)) else 0) := by
  rw [divByMonic_eq_map, muPoly, derivative_map]
  refine Cong_congr (Cong_Lmom hℓm _) rfl ?_
  have hterm : ∀ γ ∈ range ℓ, zb az ℓ ^ (2 * γ + 1) *
      (((derivative (PZ (3 * ℓ - 1) i j)).eval (2 * (γ : ℤ) + 1) : ℤ) : Fl az ℓ) =
      if γ = i % ℓ then (if i % ℓ = j % ℓ then -zb az ℓ ^ (2 * (i % ℓ) + 1) else 0) else 0 := by
    intro γ hγ
    rw [← castHom_intCast, deriv_PZ_mod (ne_two_of_not_dvd hℓm) hi hj (mem_range.mp hγ)]
    by_cases h1 : γ = i % ℓ
    · subst h1
      by_cases h2 : i % ℓ = j % ℓ
      · rw [if_pos ⟨rfl, h2.symm⟩, if_pos rfl, if_pos h2]; simp
      · rw [if_neg (fun hh => h2 (hh.1.trans hh.2.symm)), if_pos rfl, if_neg h2]; simp
    · rw [if_neg (fun hh => h1 hh.1.symm), if_neg h1]; simp
  rw [sum_congr rfl hterm, sum_ite_eq' (range ℓ) (i % ℓ), if_pos (mem_range.mpr (Nat.mod_lt _ hℓ.out.pos))]
  split_ifs <;> ring

/-! ### The pole part -/

lemma not_dvd_odd_lt (hℓ2 : ℓ ≠ 2) {n : ℕ} (hodd : Odd n) (hn : n < 3 * ℓ) (hne : n ≠ ℓ) : ¬ ℓ ∣ n := by
  rintro ⟨c, rfl⟩
  have hl := hℓ.out.pos
  have hc : c < 3 := by
    by_contra hc; push Not at hc
    have : ℓ * 3 ≤ ℓ * c := Nat.mul_le_mul_left ℓ hc
    omega
  have hℓo := hℓ.out.odd_of_ne_two hℓ2
  interval_cases c
  · simp at hodd
  · simp at hne
  · exact (Nat.not_even_iff_odd.mpr hodd) (by rw [mul_comm]; exact even_two_mul ℓ)

/-- `ℓ² Σ_{k<N} u^{2k+1}/(2k+1)² ≡ [ℓ < 2N] ū^ℓ`. -/
lemma Cong_sum_inv_sq (hℓ2 : ℓ ≠ 2) {u : Qd az} {ub : Fl az ℓ} (hu : Cong ℓ u ub) {N : ℕ} (hN : 2 * N < 3 * ℓ + 1) :
    Cong ℓ ((ℓ : Qd az) ^ 2 * ∑ k ∈ range N, u ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : Qd az) ^ 2)
      (if ℓ < 2 * N then ub ^ ℓ else 0) := by
  obtain ⟨k₀, hk₀⟩ := hℓ.out.odd_of_ne_two hℓ2
  have hl0 : (ℓ : Qd az) ≠ 0 := by exact_mod_cast hℓ.out.ne_zero
  rw [mul_sum]
  have hterm : ∀ k ∈ range N, Cong ℓ ((ℓ : Qd az) ^ 2 * (u ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : Qd az) ^ 2))
      (if k = k₀ then ub ^ ℓ else 0) := by
    intro k hk
    have hk' := mem_range.mp hk
    by_cases hkk : k = k₀
    · subst hkk
      rw [if_pos rfl, ← hk₀]
      refine Cong_congr (Cong_pow hu ℓ) ?_ rfl
      field_simp
    · rw [if_neg hkk]
      refine Cong_zero_of_vGe ?_
      have hnd : ¬ ℓ ∣ 2 * k + 1 := not_dvd_odd_lt hℓ2 ⟨k, rfl⟩ (by omega) (by omega)
      have hr : padicNorm ℓ ((ℓ : ℚ) ^ 2 / ((2 * k + 1 : ℕ) : ℚ) ^ 2) ≤ (ℓ : ℚ) ^ (-(2 : ℤ)) := by
        rw [padicNorm.div, sq, sq, padicNorm.mul, padicNorm.mul, (padicNorm.nat_eq_one_iff _).mpr hnd,
          padicNorm.padicNorm_p_of_prime]
        norm_num [zpow_neg, sq]
      have h1 := vGe_mul (vGe_ratCast_of_padicNorm (p := ℓ) hr) (vGe_of_pInt (pInt_pow hu.mem (2 * k + 1)))
      have e : (((ℓ : ℚ) ^ 2 / ((2 * k + 1 : ℕ) : ℚ) ^ 2 : ℚ) : Qd az) * u ^ (2 * k + 1) =
          (ℓ : Qd az) ^ 2 * (u ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : Qd az) ^ 2) := by
        push_cast; ring
      rw [e] at h1
      exact vGe_mono (by norm_num) h1
  refine Cong_congr (Cong_sum _ _ _ hterm) rfl ?_
  rw [sum_ite_eq' (range N) k₀]
  congr 1
  simp only [mem_range, eq_iff_iff]
  omega

/-- `ℓ² P(x)` mod `ℓ`, `x` even with `|x| < 3ℓ`. -/
lemma Cong_Psum (hℓ2 : ℓ ≠ 2) {x : ℤ} (hx : Even x) (hx3 : x.natAbs < 3 * ℓ) :
    Cong ℓ ((ℓ : Qd az) ^ 2 * Psum az x)
      (if ℓ < x.natAbs then (if x ≤ 0 then zb az ℓ ^ ℓ else -(zb az ℓ ^ ℓ)⁻¹) else 0) := by
  have h2N : 2 * (x.natAbs / 2) = x.natAbs := by
    have := Int.natAbs_even.mpr hx
    obtain ⟨t, ht⟩ := this; omega
  have hN : 2 * (x.natAbs / 2) < 3 * ℓ + 1 := by omega
  unfold Psum
  by_cases hx0 : x ≤ 0
  · rw [if_pos hx0]
    have := Cong_sum_inv_sq hℓ2 (Cong_zK (az := az) (ℓ := ℓ)) hN
    rw [h2N] at this
    refine Cong_congr this rfl ?_
    split_ifs <;> rfl
  · rw [if_neg hx0]
    have := Cong_neg (Cong_sum_inv_sq hℓ2 (Cong_zK_inv (az := az) (ℓ := ℓ)) hN)
    rw [h2N] at this
    refine Cong_congr this (by simp only [inv_pow]; ring) ?_
    split_ifs <;> simp [inv_pow]

end LP
end Chi2U
