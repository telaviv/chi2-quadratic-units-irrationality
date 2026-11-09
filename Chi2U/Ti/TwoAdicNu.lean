/-
# Theorem V_i, Lemma 10_ν / 10_0, part 1: the entries `G_{ij}` at `zK n` (PROOF_TI2 §2 row "§4 Lemma 10_ν", §3)

**Copy of `Chi2U/V/TwoAdicNu.lean`** (same structure and lemma names) for the Ti₂ machine at the trace `n ≥ 3`
(`Qt n`, `z = n/2 − √d`, `y = −z²`). The `z`-free lemmas (`PZ`, `aAnch_comp`, `cPole_U`, `coef_U`, `V2`, `vf`, `gSZ`,
`fd_seq_formula`, the Mahler-coefficient divisibility, …) are reused from `Chi2U.TwoAdicAux`; what depends on `z` is
re-proved here with the same proofs. What changes (PROOF_TI2 §1–§3):
* the recurrence ratio is `Q = y = −z²` (χ₂: `z²`), and `Q − 1 = −(1 + z²) = −n·z`, so
  `ν := v₂(Q − 1) = v₂(n) = V.nuA n` (`vGe_zK_sq_sub_oneM`); `ν ≥ 1` for even `n` (`one_le_nuA`), `ν = 0` for odd `n`;
* the pole factor carries the sign `sgnPole x = (−1)^{x/2}` and the partial sums `Psum` carry `χ₄`; both are units
  (`vGe_sgnPole`, `vGe_PsumM`), so the sequence `T(l) = sgnPole(x)·z^x·P(x)` satisfies the χ₂ recurrence with `Q = −z²`
  (`Psum_add_twoM`, `TU_recM`; checked exactly in `scripts/ti/check_twoadic_ti.py`);
* the Mahler form is `Lmom p = Σ_b Δ^bG(0)·(−1)^b z^b/n^{b+1}` (`Ti.Lmom_eq_mahler`); the sign is a unit.

Valuations: `vGe 2 v x` of `Ti/VGe.lean` (`O₂ = ℤ_(2)[√d]` for even `n`, `ℤ_(2)[½ + √d]` for odd `n`); every bound is an
integer lower bound obtained from rational powers of `2` times elements of `O₂`, so the non-maximal order at
`n ≡ 2 mod 4` is harmless.

Main statements (`π = i + j − K`, `N₀ = K − 1 − i − j`, `K = h + 1`), exactly as in the χ₂ file:
* (L), `π ≥ 1`: `G_B = 0`, `v₂(G_A) ≥ 1 − π + b + v₂(b!) − ν(b + 1)` for every Mahler index `b < π` (`vGe_GA_L`), hence
  `≥ −(ν − 1)π − 2 − ⌊log₂ π⌋` for `ν ≥ 2` (`lemma10_LM`), `≥ −π` for `ν = 1` (`lemma10_LM1`); `π = 0`: both vanish.
* (U), `N₀ ≥ 1`: `v₂ ≥ N₀ − ⌊log₂ N₀⌋` for `ν ≥ 2` (`vGe_UM`), `v₂ ≥ 1` for even `n` (`vGe_UM1`); `N₀ = 0`: `v₂ ≥ 2`.
-/
import Chi2U.Ti.Machine
import Chi2U.Ti.Mahler
import Chi2U.V.TwoAdicNu

set_option linter.unusedSectionVars false

namespace Chi2U.Ti.TwoAdicNu

open Polynomial Finset fwdDiff Chi2U.TwoAdicAux
open scoped Nat

variable {n : ℕ} [Fact (3 ≤ n)]

/-! ### Definitions -/

/-- `G_A = 2^{K+1} A((a_i b_j)(t/2))` at `zK n`. -/
noncomputable def GAm (n : ℕ) [Fact (3 ≤ n)] (h i j : ℕ) : Qt n :=
  2 ^ (h + 2) * Afun n h ((aAnch h i * bAnch h j).comp (C (1 / 2) * X))

/-- `G_B = 2^{K+1} B((a_i b_j)(t/2))` at `zK n`. -/
noncomputable def GBm (n : ℕ) [Fact (3 ≤ n)] (h i j : ℕ) : Qt n :=
  2 ^ (h + 2) * Bfun n h ((aAnch h i * bAnch h j).comp (C (1 / 2) * X))

/-! ### `ℚ → ℚ(√d)` -/

/-- From `V2` on `ℚ` to `vGe 2` on `ℚ(√d)`. -/
lemma vGe_of_V2M {e : ℤ} {x : ℚ} (hx : V2 e x) : vGe 2 e (x : Qt n) := by
  apply vGe_ratCast_of_padicNorm; unfold V2 at hx; exact_mod_cast hx

lemma fd_ratCastM (f : ℕ → ℚ) (k y : ℕ) :
    (Δ_[1])^[k] (fun l => ((f l : ℚ) : Qt n)) y = (((Δ_[1])^[k] f y : ℚ) : Qt n) := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih => rw [fd_succ, fd_succ, ih, ih]; push_cast; rfl

/-- `|n^b|₂ = 2^{−νb}`. -/
lemma padicNorm_az_pow (b : ℕ) :
    padicNorm 2 (((n : ℕ) : ℚ) ^ b) = (2 : ℚ) ^ (-((V.nuA n : ℤ) * b)) := by
  have hm : n ≠ 0 := by have := (Fact.out : 3 ≤ n); omega
  have h0 : ((n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [padicNorm.eq_zpow_of_nonzero (pow_ne_zero _ h0), padicValRat.pow _, padicValRat.of_nat]
  unfold V.nuA
  push_cast
  ring_nf

lemma V2_az : V2 (V.nuA n) (((n : ℕ) : ℚ)) := by
  unfold V2
  have := padicNorm_az_pow (n := n) 1
  rw [pow_one] at this
  rw [this]; simp

/-- `v₂(Q − 1) ≥ ν` for `Q = y = −z²`: `−z² − 1 = −n·z`. -/
lemma vGe_zK_sq_sub_oneM : vGe 2 (V.nuA n) (-(zK n) ^ 2 - 1) := by
  have e : -(zK n) ^ 2 - 1 = -((((n : ℕ) : ℚ) : Qt n) * (zK n)) := by
    push_cast
    linear_combination (-1 : Qt n) * one_add_zK_sq (n := n)
  rw [e]
  have := vGe_neg (vGe_mul (vGe_of_V2M (n := n) (V2_az (n := n))) (vGe_zK_zpow (p := 2) (n := n) 1))
  simpa using this

/-- `ν = v₂(n) ≥ 1` for even trace. -/
lemma one_le_nuA (ha : Even n) : 1 ≤ V.nuA n := by
  unfold V.nuA
  exact one_le_padicValNat_of_dvd (by have := (Fact.out : 3 ≤ n); omega) (even_iff_two_dvd.mp ha)

/-! ### The sequence bounds in `ℚ(√d)` -/

/-- Theorem U's sequence bound, in `ℚ(√d)`: `v₂(Q − 1) ≥ 2` gives `v₂(Δ^m T(0)) ≥ v₂(m!) + m − 2 − ⌊log₂ m⌋`. -/
theorem vGe_fd_seqM {Q e : Qt n} (hη : vGe 2 2 (Q - 1)) (he : vGe 2 0 e) {s : ℤ} (hs : Odd s) {T : ℕ → Qt n}
    (hT0 : vGe 2 0 (T 0)) (hrec : ∀ l, T (l + 1) = Q * T l + e * ((gSZ s l : ℚ) : Qt n)) (m : ℕ) :
    vGe 2 ((vf m : ℤ) + m - 2 - Nat.log 2 m) ((Δ_[1])^[m] T 0) := by
  rw [fd_seq_formula hrec]
  refine vGe_add (vGe_mono ?_ (vGe_mul (vGe_pow hη m) hT0)) ?_
  · have := vf_le m; omega
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [range_zero, sum_empty, mul_zero]; exact vGe_zero _
    refine vGe_mono ?_ (vGe_mul he (vGe_sum (v := (vf m : ℤ) + m - 2 - Nat.log 2 m) _ _ (fun k hk => ?_)))
    · simp
    have hk := mem_range.mp hk
    rw [fd_ratCastM]
    refine vGe_mono ?_ (vGe_mul (vGe_pow hη _) (vGe_of_V2M (V2_fd_gSZ hs k)))
    have h1 := vf_ge k
    have h2 := vf_lt (Nat.pos_iff_ne_zero.mp hm)
    have h3 := log_two_mono hk.le
    omega

/-- The coarse sequence bound for `v₂(Q − 1) ≥ 1`: `v₂(Δ^m T(0)) ≥ m − 1`. -/
theorem vGe_fd_seqM1 {Q e : Qt n} (hη : vGe 2 1 (Q - 1)) (he : vGe 2 0 e) {s : ℤ} (hs : Odd s) {T : ℕ → Qt n}
    (hT0 : vGe 2 0 (T 0)) (hrec : ∀ l, T (l + 1) = Q * T l + e * ((gSZ s l : ℚ) : Qt n)) (m : ℕ) :
    vGe 2 ((m : ℤ) - 1) ((Δ_[1])^[m] T 0) := by
  rw [fd_seq_formula hrec]
  refine vGe_add (vGe_mono ?_ (vGe_mul (vGe_pow hη m) hT0)) ?_
  · omega
  · refine vGe_mono ?_ (vGe_mul he (vGe_sum (v := (m : ℤ) - 1) _ _ (fun k hk => ?_)))
    · simp
    have hk := mem_range.mp hk
    rw [fd_ratCastM]
    refine vGe_mono ?_ (vGe_mul (vGe_pow hη _) (vGe_of_V2M (V2_fd_gSZ hs k)))
    have := Nat.zero_le (vf k)
    omega

/-! ### Linearity of `A`, `B` -/

lemma Afun_addM (h : ℕ) (f g : ℚ[X]) : Afun n h (f + g) = Afun n h f + Afun n h g := by
  unfold Afun cPole
  rw [add_divByMonic, muPoly_add]
  simp only [eval_add, add_div]
  push_cast
  simp only [add_mul, sum_add_distrib]
  ring

lemma Bfun_addM (h : ℕ) (f g : ℚ[X]) : Bfun n h (f + g) = Bfun n h f + Bfun n h g := by
  unfold Bfun cPole
  simp only [eval_add, add_div]
  push_cast
  simp only [add_mul, sum_add_distrib]
  ring

lemma Afun_C_mulM (h : ℕ) (c : ℚ) (g : ℚ[X]) : Afun n h (C c * g) = (c : Qt n) * Afun n h g := by
  unfold Afun cPole
  rw [← smul_eq_C_mul, smul_divByMonic, muPoly_smul, Algebra.smul_def, eq_ratCast]
  simp only [eval_smul, smul_eq_mul, mul_div_assoc]
  push_cast
  rw [mul_add, mul_sum]
  congr 1
  refine sum_congr rfl (fun m _ => ?_)
  ring

lemma Bfun_C_mulM (h : ℕ) (c : ℚ) (g : ℚ[X]) : Bfun n h (C c * g) = (c : Qt n) * Bfun n h g := by
  unfold Bfun cPole
  simp only [eval_mul, eval_C, mul_div_assoc]
  push_cast
  rw [mul_neg, mul_sum]
  congr 1
  refine sum_congr rfl (fun m _ => ?_)
  ring

lemma scale_eqM (h i j : ℕ) :
    (2 : Qt n) ^ (h + 2) * (((1 / 2 : ℚ) ^ (i + j) : ℚ) : Qt n) =
      (((2 : ℚ) ^ ((h : ℤ) + 2 - i - j) : ℚ) : Qt n) := by
  have e : ((h : ℤ) + 2 - i - j) = ((h + 2 : ℕ) : ℤ) - ((i + j : ℕ) : ℤ) := by push_cast; ring
  rw [e, zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast]
  push_cast
  rw [div_pow, one_pow, div_eq_mul_one_div (2 ^ (h + 2) : Qt n)]

lemma GA_eqM {h i j : ℕ} (hj : j ≤ h + 1) :
    GAm n h i j = (((2 : ℚ) ^ ((h : ℤ) + 2 - i - j) : ℚ) : Qt n) *
      Afun n h (PZ h (range i) * PZ h (Ico (h + 1 - j) (h + 1))) := by
  unfold GAm
  rw [gAB_comp h i j hj, Afun_C_mulM, ← mul_assoc, scale_eqM]

lemma GB_eqM {h i j : ℕ} (hj : j ≤ h + 1) :
    GBm n h i j = (((2 : ℚ) ^ ((h : ℤ) + 2 - i - j) : ℚ) : Qt n) *
      Bfun n h (PZ h (range i) * PZ h (Ico (h + 1 - j) (h + 1))) := by
  unfold GBm
  rw [gAB_comp h i j hj, Bfun_C_mulM, ← mul_assoc, scale_eqM]

/-! ### Case (L): `i + j ≥ K` -/

lemma Afun_D_mulM (h : ℕ) (F : ℚ[X]) : Afun n h (Dpoly h * F) = muPoly n F := by
  unfold Afun
  rw [mul_divByMonic_cancel_left _ (Dpoly_monic h)]
  rw [sum_eq_zero, add_zero]
  intro m hm
  unfold cPole
  rw [eval_mul, Dpoly_eq_PZ, eval_PZ_eq_zero hm]
  simp

lemma Bfun_D_mulM (h : ℕ) (F : ℚ[X]) : Bfun n h (Dpoly h * F) = 0 := by
  unfold Bfun
  rw [sum_eq_zero, neg_zero]
  intro m hm
  unfold cPole
  rw [eval_mul, Dpoly_eq_PZ, eval_PZ_eq_zero hm]
  simp

/-- `(−1)^k` is a unit of `O₂`. -/
lemma vGe_neg_one_pow (k : ℕ) : vGe 2 0 ((-1 : Qt n) ^ k) :=
  vGe_of_pInt (pInt_pow (pInt_neg pInt_one) k)

/-- The Mahler form with `ν`: if `B ≤ b + v₂(b!) − ν(b + 1)` for every `b < N`, then `v₂(Lmom q) ≥ B` for
`q ∈ ℤ[X]` of degree `< N` (the sign `(−1)^b` of the Ti₂ Mahler form is a unit). -/
lemma vGe_Lmom_intM (q : ℤ[X]) {N : ℕ} (hq : (q.map (Int.castRingHom ℚ)).natDegree < N) (B : ℤ)
    (hB : ∀ b < N, B ≤ (b : ℤ) + vf b - (V.nuA n : ℤ) * (b + 1)) :
    vGe 2 B (Lmom n (q.map (Int.castRingHom ℚ))) := by
  rw [Ti.Lmom_eq_mahler]
  refine vGe_sum _ _ (fun b hb => ?_)
  have hb' : b < N := by have := mem_range.mp hb; omega
  have e : (mahlerCoeff (q.map (Int.castRingHom ℚ)) b : Qt n) * (-1) ^ b * (zK n) ^ b / ((n : ℕ) : Qt n) ^ (b + 1) =
      (mahlerCoeff (q.map (Int.castRingHom ℚ)) b : Qt n) * ((-1) ^ b * (zK n) ^ (b : ℤ)) *
        (((1 / ((n : ℕ) : ℚ) ^ (b + 1)) : ℚ) : Qt n) := by
    rw [zpow_natCast, div_eq_mul_inv]
    push_cast
    ring
  rw [e]
  have h1 := vGe_of_V2M (n := n) (V2_mahlerCoeff_map q b)
  have h2 : vGe 2 0 ((-1 : Qt n) ^ b * (zK n) ^ (b : ℤ)) := by
    simpa using vGe_mul (vGe_neg_one_pow (n := n) b) (vGe_zK_zpow (p := 2) (n := n) (b : ℤ))
  have h3 : vGe 2 (0 - (V.nuA n : ℤ) * ((b + 1 : ℕ) : ℤ)) ((((1 / ((n : ℕ) : ℚ) ^ (b + 1)) : ℚ) : Qt n)) :=
    vGe_of_V2M (V2_div_of_norm V2_one (padicNorm_az_pow (b + 1)))
  refine vGe_mono ?_ (vGe_mul (vGe_mul h1 h2) h3)
  have := hB b hb'
  push_cast at this ⊢
  linarith

/-- The (L) entries: `G_A = 2^{1−π} Lmom(F′)`. -/
lemma GA_LM {h i j : ℕ} (hi : i ≤ h + 1) (hj : j ≤ h + 1) (hij : h + 1 ≤ i + j) :
    GAm n h i j = (((2 : ℚ) ^ ((h : ℤ) + 2 - i - j) : ℚ) : Qt n) *
      Lmom n ((derivative (PZint h (Ico (h + 1 - j) i))).map (Int.castRingHom ℚ)) := by
  rw [GA_eqM hj, PZ_L hi hj hij, Afun_D_mulM, muPoly, PZ_eq_map, derivative_map]

/-- The (L) entries: `G_B = 0`. -/
lemma GB_LM {h i j : ℕ} (hi : i ≤ h + 1) (hj : j ≤ h + 1) (hij : h + 1 ≤ i + j) : GBm n h i j = 0 := by
  rw [GB_eqM hj, PZ_L hi hj hij, Bfun_D_mulM, mul_zero]

/-- `G_A = 2^{1−π}·Lmom(F′)` with `v₂ ≥ 1 − π + b + v₂(b!) − ν(b + 1)` for all `b < π` (PROOF_V (L)). -/
lemma vGe_GA_L {h i j : ℕ} (hi : i < h) (hj : j < h) (hπ : h + 2 ≤ i + j) (B : ℤ)
    (hB : ∀ b < i + j - (h + 1), B ≤ ((h : ℤ) + 2 - i - j) + (b : ℤ) + vf b - (V.nuA n : ℤ) * (b + 1)) :
    vGe 2 B (GAm n h i j) := by
  rw [GA_LM (by omega) (by omega) (by omega)]
  have h1 := vGe_of_V2M (n := n) (V2_two_zpow ((h : ℤ) + 2 - i - j))
  have h2 := vGe_Lmom_intM (n := n) _ (V.TwoAdicNu.natDegree_L hπ (by omega)) (B - ((h : ℤ) + 2 - i - j))
    (fun b hb => by have := hB b hb; linarith)
  refine vGe_mono (le_of_eq ?_) (vGe_mul h1 h2)
  ring

/-- **(L), `ν ≥ 2`**: `v₂(G_A) ≥ −(ν − 1)π − 2 − ⌊log₂ π⌋`, `G_B = 0` (`π = i + j − K ≥ 1`). -/
theorem lemma10_LM {h i j : ℕ} (hν : 2 ≤ V.nuA n) (hi : i < h) (hj : j < h) (hπ : h + 2 ≤ i + j) :
    vGe 2 (-((V.nuA n : ℤ) - 1) * ((i + j - (h + 1) : ℕ) : ℤ) - 2 - Nat.log 2 (i + j - (h + 1))) (GAm n h i j) ∧
      GBm n h i j = 0 := by
  refine ⟨vGe_GA_L hi hj hπ _ (fun b hb => ?_), GB_LM (by omega) (by omega) (by omega)⟩
  set π := i + j - (h + 1) with hπdef
  have hπ' : ((h : ℤ) + 2 - i - j) = 1 - (π : ℤ) := by rw [hπdef]; push_cast [show h + 1 ≤ i + j by omega]; ring
  rw [hπ']
  have h1 := vf_ge b
  have h3 := log_two_mono hb.le
  have hν' : (2 : ℤ) ≤ V.nuA n := by exact_mod_cast hν
  have hbπ : (b : ℤ) + 1 ≤ π := by exact_mod_cast hb
  have key : ((V.nuA n : ℤ) - 2) * ((π : ℤ) - 1 - b) ≥ 0 := mul_nonneg (by linarith) (by linarith)
  have h1' : (b : ℤ) ≤ vf b + Nat.log 2 b + 1 := by exact_mod_cast h1
  have h3' : (Nat.log 2 b : ℤ) ≤ Nat.log 2 π := by exact_mod_cast h3
  nlinarith

/-- **(L), `ν = 1`**: `v₂(G_A) ≥ −π`. -/
theorem lemma10_LM1 {h i j : ℕ} (hν : V.nuA n = 1) (hi : i < h) (hj : j < h) (hπ : h + 2 ≤ i + j) :
    vGe 2 (-((i + j - (h + 1) : ℕ) : ℤ)) (GAm n h i j) ∧ GBm n h i j = 0 := by
  refine ⟨vGe_GA_L hi hj hπ _ (fun b hb => ?_), GB_LM (by omega) (by omega) (by omega)⟩
  rw [hν]
  push_cast [show h + 1 ≤ i + j by omega]
  have := Nat.zero_le (vf b)
  omega

/-- `π = 0`: both entries vanish. -/
theorem lemma10_L0M {h i j : ℕ} (hij : i + j = h + 1) : GAm n h i j = 0 ∧ GBm n h i j = 0 := by
  refine ⟨?_, GB_LM (by omega) (by omega) (by omega)⟩
  rw [GA_LM (by omega) (by omega) (by omega), show Ico (h + 1 - j) i = ∅ by
    rw [Finset.Ico_eq_empty_iff]; omega]
  simp [PZint]

/-! ### Case (U): `i + j ≤ h` -/

lemma muPoly_zeroM : muPoly n 0 = 0 := by simp [muPoly]

/-- The pole sum in case (U) is a finite difference. -/
lemma sum_UM {h i j : ℕ} (hij : i + j ≤ h) (Y : ℕ → Qt n) :
    ∑ m ∈ range (h + 1), (cPole h (PZ h (range i ∪ Ico (h + 1 - j) (h + 1))) m : Qt n) * Y m =
      (((1 : ℚ) / (2 ^ (h - i - j) * (((h - i - j) ! : ℕ) : ℚ)) : ℚ) : Qt n) *
        (Δ_[1])^[h - i - j] (fun l => Y (i + l)) 0 := by
  set N := h - i - j with hN
  have hsub : Ico i (h + 1 - j) ⊆ range (h + 1) := fun k hk => by
    simp only [mem_Ico] at hk; simp only [mem_range]; omega
  rw [← sum_subset hsub (fun m hm hmW => by rw [cPole_U_zero hij hm hmW]; simp)]
  rw [sum_Ico_eq_sum_range, show h + 1 - j - i = N + 1 by omega, fwdDiff_iter_eq_sum_shift, mul_sum]
  refine sum_congr rfl (fun l hl => ?_)
  have hl' : l ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hl)
  rw [cPole_U hij hl', coef_U hl']
  simp only [zero_add, smul_eq_mul, mul_one, zsmul_eq_mul]
  push_cast
  ring

/-- `T(l) = (−1)^{x/2} z^x P(x)` at `x = x_{i+l}`. -/
noncomputable def TseqAM (n : ℕ) [Fact (3 ≤ n)] (h i l : ℕ) : Qt n :=
  (sgnPole (poleZ h (i + l)) : Qt n) * ((zK n) ^ poleZ h (i + l) * Psum n (poleZ h (i + l)))

/-- `T_B(l) = (−1)^{x/2} z^x` at `x = x_{i+l}`. -/
noncomputable def TseqBM (n : ℕ) [Fact (3 ≤ n)] (h i l : ℕ) : Qt n :=
  (sgnPole (poleZ h (i + l)) : Qt n) * (zK n) ^ poleZ h (i + l)

lemma GA_UM {h i j : ℕ} (hij : i + j ≤ h) :
    GAm n h i j = ((4 / (((h - i - j) ! : ℕ) : ℚ) : ℚ) : Qt n) * (Δ_[1])^[h - i - j] (TseqAM n h i) 0 := by
  rw [GA_eqM (by omega), PZ_U hij]
  unfold Afun
  rw [divD_U hij, muPoly_zeroM, zero_add]
  simp_rw [mul_assoc]
  rw [sum_UM hij (fun m => (sgnPole (poleZ h m) : Qt n) * ((zK n) ^ poleZ h m * Psum n (poleZ h m))),
    ← mul_assoc, ← Rat.cast_mul, scale_U hij]
  rfl

lemma GB_UM {h i j : ℕ} (hij : i + j ≤ h) :
    GBm n h i j = -(((4 / (((h - i - j) ! : ℕ) : ℚ) : ℚ) : Qt n) * (Δ_[1])^[h - i - j] (TseqBM n h i) 0) := by
  rw [GB_eqM (by omega), PZ_U hij]
  unfold Bfun
  simp_rw [mul_assoc]
  rw [sum_UM hij (fun m => (sgnPole (poleZ h m) : Qt n) * (zK n) ^ poleZ h m), mul_neg, ← mul_assoc,
    ← Rat.cast_mul, scale_U hij]
  rfl

/-! ### The recurrences -/

lemma sgnPole_add_self (r : ℤ) : sgnPole (r + r) = (-1) ^ r.natAbs := by
  unfold sgnPole; rw [show (r + r) / 2 = r by omega]

/-- `(−1)^{(x+2)/2} = −(−1)^{x/2}` for even `x`. -/
lemma sgnPole_add_two {x : ℤ} (hx : Even x) : sgnPole (x + 2) = -sgnPole x := by
  obtain ⟨r, rfl⟩ := hx
  rw [show r + r + 2 = (r + 1) + (r + 1) by ring, sgnPole_add_self, sgnPole_add_self]
  rcases Int.even_or_odd r with hr | hr
  · have h1 : Odd (r + 1).natAbs := Int.natAbs_odd.mpr hr.add_one
    have h2 : Even r.natAbs := Int.natAbs_even.mpr hr
    rw [h1.neg_one_pow, h2.neg_one_pow]
  · have h1 : Even (r + 1).natAbs := Int.natAbs_even.mpr hr.add_one
    have h2 : Odd r.natAbs := Int.natAbs_odd.mpr hr
    rw [h1.neg_one_pow, h2.neg_one_pow, neg_neg]

lemma sgnPole_mul_self (x : ℤ) : ((sgnPole x : ℚ) : Qt n) * (sgnPole x : Qt n) = 1 := by
  unfold sgnPole
  push_cast
  rw [← mul_pow]; simp

/-- `P(x + 2) = P(x) + (−1)^{x/2} z^{−x−1}/(x + 1)²` for even `x` (χ₂: `P(x + 2) = P(x) − z^{−x−1}/(x+1)²`). -/
lemma Psum_add_twoM {x : ℤ} (hx : Even x) :
    Psum n (x + 2) = Psum n x + (sgnPole x : Qt n) * (zK n) ^ (-x - 1) / ((x + 1 : ℤ) : Qt n) ^ 2 := by
  obtain ⟨r, rfl⟩ := hx
  rw [sgnPole_add_self]
  rcases lt_or_ge r 0 with hr | hr
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, r = -((m : ℤ) + 1) := ⟨(-r - 1).toNat, by omega⟩
    have e1 : (-((m : ℤ) + 1) + -((m : ℤ) + 1) + 2) = -((2 * m : ℕ) : ℤ) := by push_cast; ring
    have e2 : (-((m : ℤ) + 1) + -((m : ℤ) + 1)) = -((2 * (m + 1) : ℕ) : ℤ) := by push_cast; ring
    have e3 : -(-((m : ℤ) + 1) + -((m : ℤ) + 1)) - 1 = ((2 * m + 1 : ℕ) : ℤ) := by push_cast; ring
    have e4 : (((-((m : ℤ) + 1) + -((m : ℤ) + 1) + 1 : ℤ)) : Qt n) ^ 2 = ((2 * m + 1 : ℕ) : Qt n) ^ 2 := by
      push_cast; ring
    have e5 : (-((m : ℤ) + 1)).natAbs = m + 1 := by omega
    unfold Psum
    rw [e3, e4, e1, e2, e5, if_pos (by omega), if_pos (by omega), Int.natAbs_neg, Int.natAbs_neg,
      Int.natAbs_natCast, Int.natAbs_natCast, show 2 * m / 2 = m by omega, show 2 * (m + 1) / 2 = m + 1 by omega,
      sum_range_succ, zpow_natCast]
    push_cast
    ring
  · lift r to ℕ using hr with m
    have hPx : Psum n ((m : ℤ) + m) =
        ∑ k ∈ range m, (-1) ^ k * ((zK n) ^ (2 * k + 1))⁻¹ / ((2 * k + 1 : ℕ) : Qt n) ^ 2 := by
      unfold Psum
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      · rw [if_neg (by omega), show ((m : ℤ) + m) = ((2 * m : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast,
          show 2 * m / 2 = m by omega]
    have e1 : ((m : ℤ) + m + 2) = ((2 * (m + 1) : ℕ) : ℤ) := by push_cast; ring
    have e3 : -((m : ℤ) + m) - 1 = -((2 * m + 1 : ℕ) : ℤ) := by push_cast; ring
    have e4 : ((((m : ℤ) + m + 1 : ℤ)) : Qt n) ^ 2 = ((2 * m + 1 : ℕ) : Qt n) ^ 2 := by push_cast; ring
    rw [hPx, e3, e4, Int.natAbs_natCast]
    unfold Psum
    rw [e1, if_neg (by omega), Int.natAbs_natCast, show 2 * (m + 1) / 2 = m + 1 by omega, sum_range_succ,
      zpow_neg, zpow_natCast]
    push_cast
    ring

lemma TU_recM (h i l : ℕ) :
    TseqAM n h i (l + 1) = (-(zK n) ^ 2) * TseqAM n h i l + (-(zK n)) * ((gSZ (poleZ h i + 1) l : ℚ) : Qt n) := by
  unfold TseqAM
  set x := poleZ h (i + l) with hx
  have hxe : Even x := even_poleZ h (i + l)
  have hx2 : poleZ h (i + (l + 1)) = x + 2 := by rw [hx, poleZ_add, poleZ_add]; push_cast; ring
  have hg : ((gSZ (poleZ h i + 1) l : ℚ) : Qt n) = 1 / ((x + 1 : ℤ) : Qt n) ^ 2 := by
    unfold gSZ; rw [hx, poleZ_add]; push_cast; ring
  rw [hx2, Psum_add_twoM hxe, hg, sgnPole_add_two hxe]
  have hz1 : (zK n) ^ (x + 2) = (zK n) ^ 2 * (zK n) ^ x := by
    rw [zpow_add₀ zK_ne_zero, mul_comm]; norm_cast
  have hz2 : (zK n) ^ 2 * (zK n) ^ x * (zK n) ^ (-x - 1) = (zK n) := by
    rw [← hz1, ← zpow_add₀ zK_ne_zero, show x + 2 + (-x - 1) = 1 by ring, zpow_one]
  have hs := sgnPole_mul_self (n := n) x
  rw [hz1]
  set s : Qt n := ((sgnPole x : ℚ) : Qt n)
  set w : Qt n := ((x + 1 : ℤ) : Qt n) ^ 2
  push_cast
  linear_combination (-(s * s) / w) * hz2 + (-(zK n) / w) * hs

lemma TB_recM (h i l : ℕ) :
    TseqBM n h i (l + 1) = (-(zK n) ^ 2) * TseqBM n h i l + 0 * ((gSZ (poleZ h i + 1) l : ℚ) : Qt n) := by
  unfold TseqBM
  have hxe : Even (poleZ h (i + l)) := even_poleZ h (i + l)
  rw [show poleZ h (i + (l + 1)) = poleZ h (i + l) + 2 by rw [poleZ_add, poleZ_add]; push_cast; ring,
    sgnPole_add_two hxe, zpow_add₀ zK_ne_zero, zero_mul, add_zero]
  push_cast
  rw [zpow_two]
  ring

/-! ### Valuations of the ingredients -/

lemma vGe_zKM : vGe 2 0 (zK n) := by simpa using vGe_zK_zpow (p := 2) (n := n) 1

lemma vGe_fourM : vGe 2 2 (4 : Qt n) := by
  have := vGe_of_V2M (n := n) (V2_two_zpow 2)
  norm_num at this
  exact this

lemma vGe_inv_odd_sqM (k : ℕ) : vGe 2 0 ((((2 * k + 1 : ℕ) : Qt n) ^ 2)⁻¹) := by
  have e : ((((2 * k + 1 : ℕ) : Qt n) ^ 2)⁻¹) = (((1 / ((2 * k + 1 : ℤ) : ℚ)) ^ 2 : ℚ) : Qt n) := by
    push_cast; rw [one_div, inv_pow]
  rw [e]
  have := V2_pow (V2_inv_oddInt (n := 2 * k + 1) ⟨k, rfl⟩) 2
  simpa using vGe_of_V2M (n := n) this

/-- The sign `(−1)^{x/2}` is a unit of `O₂`. -/
lemma vGe_sgnPole (x : ℤ) : vGe 2 0 ((sgnPole x : ℚ) : Qt n) := by
  unfold sgnPole; push_cast; exact vGe_neg_one_pow _

lemma vGe_PsumM (x : ℤ) : vGe 2 0 (Psum n x) := by
  unfold Psum
  split_ifs
  · refine vGe_sum _ _ (fun k _ => ?_)
    rw [div_eq_mul_inv]
    have := vGe_mul (vGe_mul (vGe_neg_one_pow (n := n) k) (vGe_zK_zpow (p := 2) (n := n) ((2 * k + 1 : ℕ) : ℤ)))
      (vGe_inv_odd_sqM k)
    rw [zpow_natCast, add_zero, add_zero] at this
    exact this
  · refine vGe_sum _ _ (fun k _ => ?_)
    rw [div_eq_mul_inv]
    have := vGe_mul (vGe_mul (vGe_neg_one_pow (n := n) k)
      (vGe_zK_zpow (p := 2) (n := n) (-((2 * k + 1 : ℕ) : ℤ)))) (vGe_inv_odd_sqM k)
    rw [add_zero, add_zero, zpow_neg, zpow_natCast] at this
    exact this

lemma vGe_TA0 (h i : ℕ) : vGe 2 0 (TseqAM n h i 0) := by
  unfold TseqAM
  have := vGe_mul (vGe_sgnPole (n := n) (poleZ h (i + 0)))
    (vGe_mul (vGe_zK_zpow (p := 2) (n := n) (poleZ h (i + 0))) (vGe_PsumM (poleZ h (i + 0))))
  simpa using this

lemma vGe_TB0 (h i : ℕ) : vGe 2 0 (TseqBM n h i 0) := by
  unfold TseqBM
  have := vGe_mul (vGe_sgnPole (n := n) (poleZ h (i + 0))) (vGe_zK_zpow (p := 2) (n := n) (poleZ h (i + 0)))
  simpa using this

/-- **(U), `ν ≥ 2`** (Theorem U's bound, using only `v₂(1 − y) ≥ 2`): `v₂ ≥ N₀ − ⌊log₂ N₀⌋`. -/
theorem vGe_UM {h i j : ℕ} (hν : 2 ≤ V.nuA n) (hij : i + j ≤ h) :
    vGe 2 (((h - i - j : ℕ) : ℤ) - Nat.log 2 (h - i - j)) (GAm n h i j) ∧
      vGe 2 (((h - i - j : ℕ) : ℤ) - Nat.log 2 (h - i - j)) (GBm n h i j) := by
  set N := h - i - j
  have hη : vGe 2 2 (-(zK n) ^ 2 - 1) := vGe_mono (by exact_mod_cast hν) vGe_zK_sq_sub_oneM
  have hc := vGe_of_V2M (n := n) (V2_four_div_factorial N)
  have hA := vGe_fd_seqM hη (vGe_neg vGe_zKM) (oddS h i) (vGe_TA0 h i) (TU_recM h i) N
  have hB := vGe_fd_seqM hη (vGe_zero 0) (oddS h i) (vGe_TB0 h i) (TB_recM h i) N
  refine ⟨?_, ?_⟩
  · rw [GA_UM hij]
    refine vGe_mono ?_ (vGe_mul hc hA)
    omega
  · rw [GB_UM hij]
    refine vGe_neg (vGe_mono ?_ (vGe_mul hc hB))
    omega

/-- **(U), any `ν ≥ 1`** (coarse): `v₂ ≥ 1`. -/
theorem vGe_UM1 (ha : Even n) {h i j : ℕ} (hij : i + j ≤ h) : vGe 2 1 (GAm n h i j) ∧ vGe 2 1 (GBm n h i j) := by
  set N := h - i - j
  have hη : vGe 2 1 (-(zK n) ^ 2 - 1) := vGe_mono (by exact_mod_cast one_le_nuA ha) vGe_zK_sq_sub_oneM
  have hc := vGe_of_V2M (n := n) (V2_four_div_factorial N)
  have hA := vGe_fd_seqM1 hη (vGe_neg vGe_zKM) (oddS h i) (vGe_TA0 h i) (TU_recM h i) N
  have hB := vGe_fd_seqM1 hη (vGe_zero 0) (oddS h i) (vGe_TB0 h i) (TB_recM h i) N
  have hv := vf_le N
  refine ⟨?_, ?_⟩
  · rw [GA_UM hij]
    refine vGe_mono ?_ (vGe_mul hc hA)
    omega
  · rw [GB_UM hij]
    refine vGe_neg (vGe_mono ?_ (vGe_mul hc hB))
    omega

/-- **(U)**, `N₀ = 0`: `v₂ ≥ 2`. -/
theorem vGe_U0M {h i j : ℕ} (hij : i + j = h) : vGe 2 2 (GAm n h i j) ∧ vGe 2 2 (GBm n h i j) := by
  have hN : h - i - j = 0 := by omega
  have h4 : (((4 / (((0 : ℕ) ! : ℕ) : ℚ) : ℚ) : Qt n)) = 4 := by norm_num
  refine ⟨?_, ?_⟩
  · rw [GA_UM hij.le, hN, h4, Function.iterate_zero, id]
    have := vGe_mul vGe_fourM (vGe_TA0 (n := n) h i)
    rwa [add_zero] at this
  · rw [GB_UM hij.le, hN, h4, Function.iterate_zero, id]
    have := vGe_neg (vGe_mul vGe_fourM (vGe_TB0 (n := n) h i))
    rwa [add_zero] at this

end Chi2U.Ti.TwoAdicNu
