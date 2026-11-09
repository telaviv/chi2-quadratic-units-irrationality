/-
# Lemma 1′: the pole expansion `Λ = A + T·B` (PROOF_U §1)

`T = χ₂(z)`, `z = zU az = √((az/2)² + 1) − az/2` (Theorem U: `az = 4`). For `h` even and `g ∈ ℚ[t]`,

    Σ_{s ≥ 0} z^{2s+1} (g/D)′(2s+1) = A(g) + T·B(g)        (in ℝ, via `emb`),

because `g/D = (g div D) + Σ_m c_m/(t − x_m)`, `μ(1/(t − x)) = −z^x (T − P(x))` for even `x` (`hasSum_pole`),
and `μ(R) = Lmom(R′)` for polynomials (`hasSum_Lmom`, from the moment series `hasSum_Smom`).
Consequence (with Corollary R): `Δ_h(T) = det(Λ(t^{i+j}))` (`aeval_chi2_Delta`), the input of Theorem B′.

All proved: the moment series in `MomentSeries.lean`; partial fractions by Lagrange interpolation of `g mod D`
(`modD_eq_lagrange`), the derivative at odd integers via the eventual equality with the partial-fraction form
(`deriv_gD_odd`), and the pole series by shifting `χ₂`'s series (`hasSum_pole_nonpos`, `hasSum_pole_pos`).
-/
import Chi2U.LemmaR
import Chi2U.Defs
import Chi2U.MomentSeries

namespace Chi2U

variable {az : ℕ} [Fact (1 ≤ az)]

open Polynomial

/-- `T = χ₂(z)`, `z = √5 − 2`. -/
noncomputable def TU (az : ℕ) : ℝ := chi2 (zU az)

/-- The moment series: `Σ_{s≥0} z^{2s+1} (2s+1)^n = emb S_n`. -/
theorem hasSum_Smom (n : ℕ) :
    HasSum (fun s : ℕ => (zU az) ^ (2 * s + 1) * ((2 * s + 1 : ℕ) : ℝ) ^ n) (emb (Smom az n)) :=
  hasSum_Smom' n

/-- The moment functional as a series: `Σ_{s≥0} z^{2s+1} p(2s+1) = emb (Lmom p)`. -/
theorem hasSum_Lmom (p : ℚ[X]) :
    HasSum (fun s : ℕ => (zU az) ^ (2 * s + 1) * aeval ((2 * s + 1 : ℕ) : ℝ) p) (emb (Lmom az p)) :=
  hasSum_Lmom' p

lemma hasSum_chi2Term_zU : HasSum (chi2Term (zU az)) (TU az) :=
  (summable_chi2Term (by rw [abs_of_pos zU_pos]; exact zU_lt_one.le)).hasSum

/-- The pole `x = −2i ≤ 0`. -/
lemma hasSum_pole_nonpos (i : ℕ) :
    HasSum (fun s : ℕ => -((zU az) ^ (2 * s + 1) / (((2 * s + 1 : ℕ) : ℝ) - (((-(i : ℤ)) + (-(i : ℤ)) : ℤ) : ℝ)) ^ 2))
      (-((zU az) ^ ((-(i : ℤ)) + (-(i : ℤ)))) * ((TU az) - emb (Psum az ((-(i : ℤ)) + (-(i : ℤ)))))) := by
  have hz0 : (zU az) ≠ 0 := zU_pos.ne'
  have hshift := (hasSum_nat_add_iff' (f := chi2Term (zU az)) i).mpr hasSum_chi2Term_zU
  have hPs : Psum az ((-(i : ℤ)) + (-(i : ℤ))) =
      ∑ k ∈ Finset.range i, (zK az) ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : (Qd az)) ^ 2 := by
    unfold Psum
    rw [if_pos (by omega), show ((-(i : ℤ)) + (-(i : ℤ))).natAbs / 2 = i by omega]
  have hfin : emb (Psum az ((-(i : ℤ)) + (-(i : ℤ)))) = ∑ k ∈ Finset.range i, chi2Term (zU az) k := by
    rw [hPs, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [map_div₀, map_pow, emb_zK, map_natCast, chi2Term]
    push_cast; ring
  rw [hfin]
  convert (hshift.mul_left ((zU az) ^ ((-(i : ℤ)) + (-(i : ℤ))))).neg using 1
  · funext s
    simp only [chi2Term]
    rw [show ((2 * s + 1 : ℕ) : ℝ) - ((((-(i : ℤ)) + (-(i : ℤ))) : ℤ) : ℝ) = 2 * ((s + i : ℕ) : ℝ) + 1 by
      push_cast; ring]
    have e2 : (zU az) ^ (2 * s + 1) = (zU az) ^ ((-(i : ℤ)) + (-(i : ℤ))) * (zU az) ^ (2 * (s + i) + 1) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hz0]; congr 1; push_cast; ring
    rw [e2]; ring
  · ring

/-- The pole `x = 2i > 0`. -/
lemma hasSum_pole_pos {i : ℕ} (hi : 0 < i) :
    HasSum (fun s : ℕ => -((zU az) ^ (2 * s + 1) / (((2 * s + 1 : ℕ) : ℝ) - ((((i : ℤ)) + ((i : ℤ)) : ℤ) : ℝ)) ^ 2))
      (-((zU az) ^ (((i : ℤ)) + ((i : ℤ)))) * ((TU az) - emb (Psum az (((i : ℤ)) + ((i : ℤ)))))) := by
  have hz0 : (zU az) ≠ 0 := zU_pos.ne'
  set t : ℕ → ℝ := fun s => -((zU az) ^ (2 * s + 1) / (((2 * s + 1 : ℕ) : ℝ) - ((((i : ℤ)) + ((i : ℤ)) : ℤ) : ℝ)) ^ 2)
    with ht
  have hshift : HasSum (fun s => t (s + i)) (-((zU az) ^ ((i : ℤ) + (i : ℤ))) * (TU az)) := by
    convert ((hasSum_chi2Term_zU (az := az)).mul_left ((zU az) ^ ((i : ℤ) + (i : ℤ)))).neg using 1
    · funext s
      simp only [ht, chi2Term]
      rw [show ((2 * (s + i) + 1 : ℕ) : ℝ) - ((((i : ℤ) + (i : ℤ)) : ℤ) : ℝ) = 2 * (s : ℝ) + 1 by
        push_cast; ring]
      have e2 : (zU az) ^ (2 * (s + i) + 1) = (zU az) ^ ((i : ℤ) + (i : ℤ)) * (zU az) ^ (2 * s + 1) := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hz0]; congr 1; push_cast; ring
      rw [e2]; ring
    · ring
  have hfull := (hasSum_nat_add_iff (f := t) i).mp hshift
  have hfin : ∑ s ∈ Finset.range i, t s =
      -((zU az) ^ ((i : ℤ) + (i : ℤ)) *
        emb (∑ k ∈ Finset.range i, ((zK az) ^ (2 * k + 1))⁻¹ / ((2 * k + 1 : ℕ) : (Qd az)) ^ 2)) := by
    rw [map_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk := Finset.mem_range.mp hk
    simp only [ht, map_div₀, map_inv₀, map_pow, emb_zK, map_natCast]
    have e1 : ((2 * (i - 1 - k) + 1 : ℕ) : ℝ) - ((((i : ℤ) + (i : ℤ)) : ℤ) : ℝ) = -((2 * k + 1 : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub (by omega : k ≤ i - 1), Nat.cast_sub (by omega : 1 ≤ i)]; ring
    rw [e1, neg_sq]
    have e2 : (zU az) ^ (2 * (i - 1 - k) + 1) = (zU az) ^ ((i : ℤ) + (i : ℤ)) * ((zU az) ^ (2 * k + 1))⁻¹ := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hz0]
      congr 1; push_cast [Nat.cast_sub (by omega : k ≤ i - 1), Nat.cast_sub (by omega : 1 ≤ i)]; ring
    rw [e2]; ring
  convert hfull using 1
  rw [hfin]
  have hPs : Psum az ((i : ℤ) + (i : ℤ)) =
      -∑ k ∈ Finset.range i, ((zK az) ^ (2 * k + 1))⁻¹ / ((2 * k + 1 : ℕ) : (Qd az)) ^ 2 := by
    unfold Psum
    rw [if_neg (by omega), show ((i : ℤ) + i).natAbs / 2 = i by omega]
  rw [hPs, map_neg]; ring

/-- `μ(1/(t − x)) = −Σ_{t odd ≥ 1} z^t/(t − x)² = −z^x (T − P(x))` for even `x`. -/
theorem hasSum_pole {x : ℤ} (hx : Even x) :
    HasSum (fun s : ℕ => -((zU az) ^ (2 * s + 1) / (((2 * s + 1 : ℕ) : ℝ) - x) ^ 2))
      (-(emb ((zK az) ^ x)) * ((TU az) - emb (Psum az x))) := by
  rw [map_zpow₀, emb_zK]
  obtain ⟨j, rfl⟩ := hx
  rcases Int.eq_nat_or_neg j with ⟨i, rfl | rfl⟩
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · have := hasSum_pole_nonpos (az := az) 0
      simpa using this
    · exact hasSum_pole_pos hi
  · exact hasSum_pole_nonpos i

/-- The real functional `Λ(g) = Σ_{s≥0} z^{2s+1} (g/D)′(2s+1)`. -/
noncomputable def LamR (az : ℕ) [Fact (1 ≤ az)] (h : ℕ) (g : ℚ[X]) : ℝ :=
  ∑' s : ℕ, (zU az) ^ (2 * s + 1) * deriv (fun t : ℝ => aeval t g / aeval t (Dpoly h)) ((2 * s + 1 : ℕ) : ℝ)

/-! ### Partial fractions -/

/-- The Lagrange polynomial `ℓ_m = Π_{l ≠ m}(t − x_l)`. -/
noncomputable def lagP (h m : ℕ) : ℚ[X] := ∏ l ∈ (Finset.range (h + 1)).erase m, (X - C ((poleZ h l : ℤ) : ℚ))

lemma poleZ_inj {h m m' : ℕ} (hmm : ((poleZ h m : ℤ) : ℚ) = poleZ h m') : m = m' := by
  have : poleZ h m = poleZ h m' := by exact_mod_cast hmm
  unfold poleZ at this; omega

lemma dPrime_eq_erase {h m : ℕ} (hm : m ≤ h) :
    dPrime h m = ∏ l ∈ (Finset.range (h + 1)).erase m, (((poleZ h m : ℤ) : ℚ) - poleZ h l) := by
  unfold dPrime
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hm)), if_pos rfl, one_mul]
  exact Finset.prod_congr rfl (fun l hl => if_neg (Finset.ne_of_mem_erase hl))

lemma dPrime_ne_zero {h m : ℕ} (hm : m ≤ h) : dPrime h m ≠ 0 := by
  rw [dPrime_eq_erase hm, Finset.prod_ne_zero_iff]
  intro l hl
  rw [sub_ne_zero]
  intro he
  exact Finset.ne_of_mem_erase hl (poleZ_inj he).symm

lemma Dpoly_eq_mul {h m : ℕ} (hm : m ≤ h) : Dpoly h = (X - C ((poleZ h m : ℤ) : ℚ)) * lagP h m := by
  unfold Dpoly lagP
  exact (Finset.mul_prod_erase (Finset.range (h + 1)) (fun l => X - C ((poleZ h l : ℤ) : ℚ))
    (Finset.mem_range.mpr (by omega))).symm

lemma eval_lagP_self {h m : ℕ} (hm : m ≤ h) : (lagP h m).eval ((poleZ h m : ℤ) : ℚ) = dPrime h m := by
  rw [dPrime_eq_erase hm, lagP, eval_prod]
  simp

lemma eval_lagP_other {h m k : ℕ} (hk : k ≤ h) (hkm : k ≠ m) : (lagP h m).eval ((poleZ h k : ℤ) : ℚ) = 0 := by
  rw [lagP, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hkm, Finset.mem_range.mpr (Nat.lt_succ_of_le hk)⟩) (by simp)

lemma natDegree_lagP_le {h m : ℕ} (hm : m ≤ h) : (lagP h m).natDegree ≤ h := by
  unfold lagP
  refine (natDegree_prod_le _ _).trans ?_
  refine (Finset.sum_le_sum (fun l _ => (natDegree_X_sub_C_le _))).trans ?_
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range]; omega

lemma natDegree_Dpoly (h : ℕ) : (Dpoly h).natDegree = h + 1 := by
  unfold Dpoly
  rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _),
    Finset.sum_congr rfl (fun _ _ => natDegree_X_sub_C _)]
  simp

lemma eval_Dpoly_pole {h k : ℕ} (hk : k ≤ h) : (Dpoly h).eval ((poleZ h k : ℤ) : ℚ) = 0 := by
  rw [Dpoly_eq_mul hk]; simp

/-- Lagrange interpolation of the remainder: `g mod D = Σ_m c_m ℓ_m`. -/
lemma modD_eq_lagrange (h : ℕ) (g : ℚ[X]) :
    g %ₘ Dpoly h = ∑ m ∈ Finset.range (h + 1), C (cPole h g m) * lagP h m := by
  set S := (Finset.range (h + 1)).image (fun m => ((poleZ h m : ℤ) : ℚ)) with hS
  have hcard : S.card = h + 1 := by
    rw [hS, Finset.card_image_of_injOn (fun m _ m' _ he => poleZ_inj he), Finset.card_range]
  apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq S
  · rw [hcard]
    have := degree_modByMonic_lt g (Dpoly_monic h)
    rwa [degree_eq_natDegree (Dpoly_monic h).ne_zero, natDegree_Dpoly] at this
  · rw [hcard]
    refine (degree_le_of_natDegree_le (natDegree_sum_le_of_forall_le _ _ (fun m _ =>
      (natDegree_C_mul_le _ _).trans (natDegree_lagP_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp ‹_›)))))).trans_lt ?_
    exact_mod_cast Nat.lt_succ_self h
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    have hk' : k ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hdiv : g %ₘ Dpoly h + Dpoly h * (g /ₘ Dpoly h) = g := modByMonic_add_div g (Dpoly h)
    have h1 : (g %ₘ Dpoly h).eval ((poleZ h k : ℤ) : ℚ) = g.eval ((poleZ h k : ℤ) : ℚ) := by
      conv_rhs => rw [← hdiv]
      rw [eval_add, eval_mul, eval_Dpoly_pole hk', zero_mul, add_zero]
    rw [h1, eval_finsetSum, Finset.sum_eq_single k]
    · rw [eval_mul, eval_C, eval_lagP_self hk', cPole, div_mul_cancel₀ _ (dPrime_ne_zero hk')]
    · intro m _ hmk
      rw [eval_mul, eval_lagP_other hk' (Ne.symm hmk), mul_zero]
    · intro hk2; exact absurd hk hk2

/-- The real pole `x_m`. -/
noncomputable def poleR (h m : ℕ) : ℝ := ((poleZ h m : ℤ) : ℝ)

lemma aeval_X_sub_pole (h m : ℕ) (t : ℝ) : aeval t (X - C ((poleZ h m : ℤ) : ℚ)) = t - poleR h m := by
  simp [poleR]

/-- Partial fractions over `ℝ`: `g/D = (g div D) + Σ_m c_m/(t − x_m)` where `D(t) ≠ 0`. -/
lemma partial_fractions (h : ℕ) (g : ℚ[X]) {t : ℝ} (ht : aeval t (Dpoly h) ≠ 0) :
    aeval t g / aeval t (Dpoly h) =
      aeval t (g /ₘ Dpoly h) + ∑ m ∈ Finset.range (h + 1), (cPole h g m : ℝ) / (t - poleR h m) := by
  have hdiv : g %ₘ Dpoly h + Dpoly h * (g /ₘ Dpoly h) = g := modByMonic_add_div g (Dpoly h)
  conv_lhs => rw [← hdiv]
  rw [map_add, map_mul, add_div, mul_div_cancel_left₀ _ ht, add_comm, modD_eq_lagrange, map_sum,
    Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hm' : m ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hD : aeval t (Dpoly h) = (t - poleR h m) * aeval t (lagP h m) := by
    rw [Dpoly_eq_mul hm', map_mul, aeval_X_sub_pole]
  rw [hD] at ht ⊢
  have h1 : t - poleR h m ≠ 0 := left_ne_zero_of_mul ht
  have h2 : aeval t (lagP h m) ≠ 0 := right_ne_zero_of_mul ht
  rw [map_mul, aeval_C, eq_ratCast]
  field_simp

/-- `D` does not vanish at odd integers. -/
lemma aeval_Dpoly_odd_ne_zero (h s : ℕ) : aeval ((2 * s + 1 : ℕ) : ℝ) (Dpoly h) ≠ 0 := by
  unfold Dpoly
  rw [map_prod, Finset.prod_ne_zero_iff]
  intro m _
  rw [aeval_X_sub_pole, poleR, sub_ne_zero]
  intro he
  have : ((2 * s + 1 : ℕ) : ℤ) = poleZ h m := by exact_mod_cast he
  unfold poleZ at this; omega

/-- The derivative of `g/D` at an odd integer. -/
lemma deriv_gD_odd (h : ℕ) (g : ℚ[X]) (s : ℕ) :
    deriv (fun t : ℝ => aeval t g / aeval t (Dpoly h)) ((2 * s + 1 : ℕ) : ℝ) =
      aeval ((2 * s + 1 : ℕ) : ℝ) (derivative (g /ₘ Dpoly h)) +
        ∑ m ∈ Finset.range (h + 1), (cPole h g m : ℝ) * (-1 / (((2 * s + 1 : ℕ) : ℝ) - poleR h m) ^ 2) := by
  set t₀ : ℝ := ((2 * s + 1 : ℕ) : ℝ)
  have hD0 := aeval_Dpoly_odd_ne_zero h s
  set F : ℝ → ℝ := fun u => aeval u (g /ₘ Dpoly h) +
    ∑ m ∈ Finset.range (h + 1), (cPole h g m : ℝ) * (u - poleR h m)⁻¹ with hF
  have hev : (fun t : ℝ => aeval t g / aeval t (Dpoly h)) =ᶠ[nhds t₀] F := by
    have hne : ∀ᶠ u in nhds t₀, aeval u (Dpoly h) ≠ 0 :=
      ((Polynomial.continuous_aeval (Dpoly h)).continuousAt).eventually_ne hD0
    filter_upwards [hne] with u hu
    rw [partial_fractions h g hu, hF]
    simp only [div_eq_mul_inv]
  have hpole : ∀ m ∈ Finset.range (h + 1), t₀ - poleR h m ≠ 0 := by
    intro m hm
    have hm' : m ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hD : aeval t₀ (Dpoly h) = (t₀ - poleR h m) * aeval t₀ (lagP h m) := by
      rw [Dpoly_eq_mul hm', map_mul, aeval_X_sub_pole]
    rw [hD] at hD0; exact left_ne_zero_of_mul hD0
  have hderiv : HasDerivAt F (aeval t₀ (derivative (g /ₘ Dpoly h)) +
      ∑ m ∈ Finset.range (h + 1), (cPole h g m : ℝ) * (-1 / (t₀ - poleR h m) ^ 2)) t₀ := by
    refine (Polynomial.hasDerivAt_aeval _ t₀).add (HasDerivAt.fun_sum (fun m hm => ?_))
    have := (((hasDerivAt_id t₀).sub_const (poleR h m)).fun_inv (by simpa using hpole m hm)).const_mul
      (cPole h g m : ℝ)
    simpa using this
  rw [hev.deriv_eq, hderiv.deriv]

/-- **Lemma 1′.** `Λ(g) = A(g) + T·B(g)` (as a convergent series). -/
theorem lemma1 {h : ℕ} (hh : Even h) (g : ℚ[X]) :
    HasSum (fun s : ℕ => (zU az) ^ (2 * s + 1) *
        deriv (fun t : ℝ => aeval t g / aeval t (Dpoly h)) ((2 * s + 1 : ℕ) : ℝ))
      (emb (Afun az h g) + (TU az) * emb (Bfun az h g)) := by
  have hQ := hasSum_Lmom' (az := az) (derivative (g /ₘ Dpoly h))
  have hP := hasSum_sum (s := Finset.range (h + 1)) (fun m _ =>
    (hasSum_pole (az := az) (even_poleZ h m)).mul_left (cPole h g m : ℝ))
  convert hQ.add hP using 1
  · funext s
    rw [deriv_gD_odd, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp only [poleR]
    ring
  · simp only [Afun, Bfun, muPoly, map_add, map_sum, map_mul, map_neg, map_ratCast]
    rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring

theorem LamR_eq {h : ℕ} (hh : Even h) (g : ℚ[X]) : LamR az h g = emb (Afun az h g) + (TU az) * emb (Bfun az h g) :=
  (lemma1 hh g).tsum_eq

/-- `Δ_h(T) = det(Λ(t^{i+j}))` (Corollary R + Lemma 1′). -/
theorem aeval_chi2_Delta {h : ℕ} (hh : Even h) :
    aeval (TU az) (Delta az h) = (Matrix.of fun i j : Fin h => LamR az h (X ^ ((i : ℕ) + j))).det := by
  rw [aeval_Delta hh]
  congr 1
  ext i j
  simp only [Matrix.of_apply, LamR_eq hh]

end Chi2U
