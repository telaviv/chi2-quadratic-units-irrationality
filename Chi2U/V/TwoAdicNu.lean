/-
# Lemma 10_ν, part 1: the entries `G_{ij}` at `zU az` (PROOF_V §4, "Proof of (L), (U)")

The `az`-generic version of `Arith/TwoAdicEntries.lean` + the `ℚ(√5)`-specific parts of `Arith/TwoAdicBasis.lean`
(Theorem U's Lemma 10′, `az = 4`). The `az`-free lemmas (`PZ`, `aAnch_comp`, `cPole_U`, `V2`, `vf`, `gSZ`, the
Mahler-coefficient divisibility, …) are reused from `Chi2U.TwoAdicAux`; what depends on `az` is re-proved here with the
same proofs (`Qd az` in place of `Q5`, `az` in place of `4`).

Valuations: `vGe 2 n x` (`Arith/Defs.lean`) is `x/2^n ∈ O₂`, `O₂ = ℤ_(2)[(1+√d)/2]` (`az ≡ 0 mod 4`, i.e. `m` even) or
`ℤ_(2)[√d]` (`az ≡ 2 mod 4`, `m` odd); all bounds below are integer lower bounds obtained from rational powers of `2`
times elements of `O₂` (`z^k`, `P(x)`), so the ramified case (`m` odd, where the true valuations live in `½ℤ`) needs no
special treatment.
`ν = nuA az = v₂(az)` (`= 1 + v₂(m)` for Theorem V's `az = 2m`) enters only through `v₂(1 − y) = v₂(az·z) = ν`;
only even traces are used here (`ν ≥ 1`: `one_le_nuA`, needed by `vGe_UM1`).

Main statements (`π = i + j − K`, `N₀ = K − 1 − i − j`, `K = h + 1`):
* (L), `π ≥ 1`: `G_B = 0`, `G_A = 2^{1−π} Lmom(F′)` and `v₂ ≥ 1 − π + b + v₂(b!) − ν(b + 1)` for every Mahler index
  `b < π` (`vGe_Lmom_intM`); hence `v₂(G_A) ≥ −(ν − 1)π − 2 − ⌊log₂ π⌋` for `ν ≥ 2` (`lemma10_LM`) and `≥ −π` for
  `ν = 1` (`lemma10_LM1`) (PROOF_V's (L) with its two corollaries).
* (U), `N₀ ≥ 1`: `v₂ ≥ N₀ − ⌊log₂ N₀⌋` when `ν ≥ 2` (exactly Theorem U's bound, which uses only `v₂(1 − y) ≥ 2`,
  `vGe_UM`) and `v₂ ≥ 1` for every `ν ≥ 1` (`vGe_UM1`; PROOF_V proves `≥ 2`, `≥ 0` is all that is used); `N₀ = 0`:
  `v₂ ≥ 2` (`vGe_U0M`).
-/
import Chi2U.V.Defs
import Chi2U.Arith.TwoAdic

namespace Chi2U.V.TwoAdicNu

open Polynomial Finset fwdDiff Chi2U.TwoAdicAux
open scoped Nat

variable {az : ℕ} [Fact (1 ≤ az)]

/-! ### Definitions -/

/-- `G_A = 2^{K+1} A((a_i b_j)(t/2))` at `zU az`. -/
noncomputable def GAm (az : ℕ) [Fact (1 ≤ az)] (h i j : ℕ) : Qd az :=
  2 ^ (h + 2) * Afun az h ((aAnch h i * bAnch h j).comp (C (1 / 2) * X))

/-- `G_B = 2^{K+1} B((a_i b_j)(t/2))` at `zU az`. -/
noncomputable def GBm (az : ℕ) [Fact (1 ≤ az)] (h i j : ℕ) : Qd az :=
  2 ^ (h + 2) * Bfun az h ((aAnch h i * bAnch h j).comp (C (1 / 2) * X))

/-! ### `ℚ → ℚ(√d)` -/

/-- From `V2` on `ℚ` to `vGe 2` on `ℚ(√d)`. -/
lemma vGe_of_V2M {e : ℤ} {x : ℚ} (hx : V2 e x) : vGe 2 e (x : Qd az) := by
  apply vGe_ratCast_of_padicNorm; unfold V2 at hx; exact_mod_cast hx

lemma fd_ratCastM (f : ℕ → ℚ) (k y : ℕ) :
    (Δ_[1])^[k] (fun l => ((f l : ℚ) : Qd az)) y = (((Δ_[1])^[k] f y : ℚ) : Qd az) := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih => rw [fd_succ, fd_succ, ih, ih]; push_cast; rfl

/-- `|(az)^b|₂ = 2^{−νb}`. -/
lemma padicNorm_az_pow (b : ℕ) :
    padicNorm 2 (((az : ℕ) : ℚ) ^ b) = (2 : ℚ) ^ (-((nuA az : ℤ) * b)) := by
  have hm : az ≠ 0 := by have := (Fact.out : 1 ≤ az); omega
  have h0 : ((az : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [padicNorm.eq_zpow_of_nonzero (pow_ne_zero _ h0), padicValRat.pow _, padicValRat.of_nat]
  unfold nuA
  push_cast
  ring_nf

lemma V2_az : V2 (nuA az) (((az : ℕ) : ℚ)) := by
  unfold V2
  have := padicNorm_az_pow (az := az) 1
  rw [pow_one] at this
  rw [this]; simp

/-- `v₂(z² − 1) = v₂(−az·z) ≥ ν`. -/
lemma vGe_zK_sq_sub_oneM : vGe 2 (nuA az) ((zK az) ^ 2 - 1) := by
  have e : (zK az) ^ 2 - 1 = -((((az : ℕ) : ℚ) : Qd az) * (zK az)) := by
    push_cast
    linear_combination (-1 : Qd az) * one_sub_zK_sq (az := az)
  rw [e]
  have := vGe_neg (vGe_mul (vGe_of_V2M (az := az) (V2_az (az := az))) (vGe_zK_zpow (p := 2) (az := az) 1))
  simpa using this

/-- `ν = v₂(az) ≥ 1` for even trace. -/
lemma one_le_nuA (ha : Even az) : 1 ≤ nuA az := by
  unfold nuA
  exact one_le_padicValNat_of_dvd (by have := (Fact.out : 1 ≤ az); omega) (even_iff_two_dvd.mp ha)

/-! ### The sequence bounds in `ℚ(√d)` -/

/-- Theorem U's sequence bound, in `ℚ(√d)`: `v₂(Q − 1) ≥ 2` gives `v₂(Δ^m T(0)) ≥ v₂(m!) + m − 2 − ⌊log₂ m⌋`. -/
theorem vGe_fd_seqM {Q e : Qd az} (hη : vGe 2 2 (Q - 1)) (he : vGe 2 0 e) {s : ℤ} (hs : Odd s) {T : ℕ → Qd az}
    (hT0 : vGe 2 0 (T 0)) (hrec : ∀ l, T (l + 1) = Q * T l + e * ((gSZ s l : ℚ) : Qd az)) (m : ℕ) :
    vGe 2 ((vf m : ℤ) + m - 2 - Nat.log 2 m) ((Δ_[1])^[m] T 0) := by
  rw [fd_seq_formula hrec]
  refine vGe_add (vGe_mono ?_ (vGe_mul (vGe_pow hη m) hT0)) ?_
  · have := vf_le m; omega
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [range_zero, sum_empty, mul_zero]; exact vGe_zero _
    refine vGe_mono ?_ (vGe_mul he (vGe_sum (n := (vf m : ℤ) + m - 2 - Nat.log 2 m) _ _ (fun k hk => ?_)))
    · simp
    have hk := mem_range.mp hk
    rw [fd_ratCastM]
    refine vGe_mono ?_ (vGe_mul (vGe_pow hη _) (vGe_of_V2M (V2_fd_gSZ hs k)))
    have h1 := vf_ge k
    have h2 := vf_lt (Nat.pos_iff_ne_zero.mp hm)
    have h3 := log_two_mono hk.le
    omega

/-- The coarse sequence bound for `v₂(Q − 1) ≥ 1`: `v₂(Δ^m T(0)) ≥ m − 1`. -/
theorem vGe_fd_seqM1 {Q e : Qd az} (hη : vGe 2 1 (Q - 1)) (he : vGe 2 0 e) {s : ℤ} (hs : Odd s) {T : ℕ → Qd az}
    (hT0 : vGe 2 0 (T 0)) (hrec : ∀ l, T (l + 1) = Q * T l + e * ((gSZ s l : ℚ) : Qd az)) (m : ℕ) :
    vGe 2 ((m : ℤ) - 1) ((Δ_[1])^[m] T 0) := by
  rw [fd_seq_formula hrec]
  refine vGe_add (vGe_mono ?_ (vGe_mul (vGe_pow hη m) hT0)) ?_
  · omega
  · refine vGe_mono ?_ (vGe_mul he (vGe_sum (n := (m : ℤ) - 1) _ _ (fun k hk => ?_)))
    · simp
    have hk := mem_range.mp hk
    rw [fd_ratCastM]
    refine vGe_mono ?_ (vGe_mul (vGe_pow hη _) (vGe_of_V2M (V2_fd_gSZ hs k)))
    have := Nat.zero_le (vf k)
    omega

/-! ### Linearity of `A`, `B` -/

lemma Afun_addM (h : ℕ) (f g : ℚ[X]) : Afun az h (f + g) = Afun az h f + Afun az h g := by
  unfold Afun cPole
  rw [add_divByMonic, muPoly_add]
  simp only [eval_add, add_div]
  push_cast
  simp only [add_mul, sum_add_distrib]
  ring

lemma Bfun_addM (h : ℕ) (f g : ℚ[X]) : Bfun az h (f + g) = Bfun az h f + Bfun az h g := by
  unfold Bfun cPole
  simp only [eval_add, add_div]
  push_cast
  simp only [add_mul, sum_add_distrib]
  ring

lemma Afun_C_mulM (h : ℕ) (c : ℚ) (g : ℚ[X]) : Afun az h (C c * g) = (c : Qd az) * Afun az h g := by
  unfold Afun cPole
  rw [← smul_eq_C_mul, smul_divByMonic, muPoly_smul, Algebra.smul_def, eq_ratCast]
  simp only [eval_smul, smul_eq_mul, mul_div_assoc]
  push_cast
  rw [mul_add, mul_sum]
  congr 1
  refine sum_congr rfl (fun m _ => ?_)
  ring

lemma Bfun_C_mulM (h : ℕ) (c : ℚ) (g : ℚ[X]) : Bfun az h (C c * g) = (c : Qd az) * Bfun az h g := by
  unfold Bfun cPole
  simp only [eval_mul, eval_C, mul_div_assoc]
  push_cast
  rw [mul_neg, mul_sum]
  congr 1
  refine sum_congr rfl (fun m _ => ?_)
  ring

lemma scale_eqM (h i j : ℕ) :
    (2 : Qd az) ^ (h + 2) * (((1 / 2 : ℚ) ^ (i + j) : ℚ) : Qd az) =
      (((2 : ℚ) ^ ((h : ℤ) + 2 - i - j) : ℚ) : Qd az) := by
  have e : ((h : ℤ) + 2 - i - j) = ((h + 2 : ℕ) : ℤ) - ((i + j : ℕ) : ℤ) := by push_cast; ring
  rw [e, zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast]
  push_cast
  rw [div_pow, one_pow, div_eq_mul_one_div (2 ^ (h + 2) : Qd az)]

lemma GA_eqM {h i j : ℕ} (hj : j ≤ h + 1) :
    GAm az h i j = (((2 : ℚ) ^ ((h : ℤ) + 2 - i - j) : ℚ) : Qd az) *
      Afun az h (PZ h (range i) * PZ h (Ico (h + 1 - j) (h + 1))) := by
  unfold GAm
  rw [gAB_comp h i j hj, Afun_C_mulM, ← mul_assoc, scale_eqM]

lemma GB_eqM {h i j : ℕ} (hj : j ≤ h + 1) :
    GBm az h i j = (((2 : ℚ) ^ ((h : ℤ) + 2 - i - j) : ℚ) : Qd az) *
      Bfun az h (PZ h (range i) * PZ h (Ico (h + 1 - j) (h + 1))) := by
  unfold GBm
  rw [gAB_comp h i j hj, Bfun_C_mulM, ← mul_assoc, scale_eqM]

/-! ### Case (L): `i + j ≥ K` -/

lemma Afun_D_mulM (h : ℕ) (F : ℚ[X]) : Afun az h (Dpoly h * F) = muPoly az F := by
  unfold Afun
  rw [mul_divByMonic_cancel_left _ (Dpoly_monic h)]
  rw [sum_eq_zero, add_zero]
  intro m hm
  unfold cPole
  rw [eval_mul, Dpoly_eq_PZ, eval_PZ_eq_zero hm]
  simp

lemma Bfun_D_mulM (h : ℕ) (F : ℚ[X]) : Bfun az h (Dpoly h * F) = 0 := by
  unfold Bfun
  rw [sum_eq_zero, neg_zero]
  intro m hm
  unfold cPole
  rw [eval_mul, Dpoly_eq_PZ, eval_PZ_eq_zero hm]
  simp

/-- The Mahler form with `ν`: if `B ≤ b + v₂(b!) − ν(b + 1)` for every `b < n`, then `v₂(Lmom q) ≥ B` for
`q ∈ ℤ[X]` of degree `< n`. -/
lemma vGe_Lmom_intM (q : ℤ[X]) {n : ℕ} (hq : (q.map (Int.castRingHom ℚ)).natDegree < n) (B : ℤ)
    (hB : ∀ b < n, B ≤ (b : ℤ) + vf b - (nuA az : ℤ) * (b + 1)) :
    vGe 2 B (Lmom az (q.map (Int.castRingHom ℚ))) := by
  rw [Lmom_eq_mahler]
  refine vGe_sum _ _ (fun b hb => ?_)
  have hb' : b < n := by have := mem_range.mp hb; omega
  have e : (mahlerCoeff (q.map (Int.castRingHom ℚ)) b : Qd az) * (zK az) ^ b / ((az : ℕ) : Qd az) ^ (b + 1) =
      (mahlerCoeff (q.map (Int.castRingHom ℚ)) b : Qd az) * (zK az) ^ (b : ℤ) *
        (((1 / ((az : ℕ) : ℚ) ^ (b + 1)) : ℚ) : Qd az) := by
    rw [zpow_natCast, div_eq_mul_inv]
    congr 1
    push_cast
    ring
  rw [e]
  have h1 := vGe_of_V2M (az := az) (V2_mahlerCoeff_map q b)
  have h2 : vGe 2 0 ((zK az) ^ (b : ℤ)) := vGe_zK_zpow _
  have h3 : vGe 2 (0 - (nuA az : ℤ) * ((b + 1 : ℕ) : ℤ)) ((((1 / ((az : ℕ) : ℚ) ^ (b + 1)) : ℚ) : Qd az)) :=
    vGe_of_V2M (V2_div_of_norm V2_one (padicNorm_az_pow (b + 1)))
  refine vGe_mono ?_ (vGe_mul (vGe_mul h1 h2) h3)
  have := hB b hb'
  push_cast at this ⊢
  linarith

/-- The (L) entries: `G_A = 2^{1−π} Lmom(F′)`. -/
lemma GA_LM {h i j : ℕ} (hi : i ≤ h + 1) (hj : j ≤ h + 1) (hij : h + 1 ≤ i + j) :
    GAm az h i j = (((2 : ℚ) ^ ((h : ℤ) + 2 - i - j) : ℚ) : Qd az) *
      Lmom az ((derivative (PZint h (Ico (h + 1 - j) i))).map (Int.castRingHom ℚ)) := by
  rw [GA_eqM hj, PZ_L hi hj hij, Afun_D_mulM, muPoly, PZ_eq_map, derivative_map]

/-- The (L) entries: `G_B = 0`. -/
lemma GB_LM {h i j : ℕ} (hi : i ≤ h + 1) (hj : j ≤ h + 1) (hij : h + 1 ≤ i + j) : GBm az h i j = 0 := by
  rw [GB_eqM hj, PZ_L hi hj hij, Bfun_D_mulM, mul_zero]

lemma natDegree_L {h i j : ℕ} (hπ : h + 2 ≤ i + j) (hj : j ≤ h + 1) :
    ((derivative (PZint h (Ico (h + 1 - j) i))).map (Int.castRingHom ℚ)).natDegree < i + j - (h + 1) := by
  rw [← derivative_map, ← PZ_eq_map]
  have hc : (PZ h (Ico (h + 1 - j) i)).natDegree = i + j - (h + 1) := by
    rw [natDegree_PZ, Nat.card_Ico]; omega
  rw [← hc]
  exact natDegree_derivative_lt (by rw [hc]; omega)

/-- `G_A = 2^{1−π}·Lmom(F′)` with `v₂ ≥ 1 − π + b + v₂(b!) − ν(b + 1)` for all `b < π` (PROOF_V (L)). -/
lemma vGe_GA_L {h i j : ℕ} (hi : i < h) (hj : j < h) (hπ : h + 2 ≤ i + j) (B : ℤ)
    (hB : ∀ b < i + j - (h + 1), B ≤ ((h : ℤ) + 2 - i - j) + (b : ℤ) + vf b - (nuA az : ℤ) * (b + 1)) :
    vGe 2 B (GAm az h i j) := by
  rw [GA_LM (by omega) (by omega) (by omega)]
  have h1 := vGe_of_V2M (az := az) (V2_two_zpow ((h : ℤ) + 2 - i - j))
  have h2 := vGe_Lmom_intM (az := az) _ (natDegree_L hπ (by omega)) (B - ((h : ℤ) + 2 - i - j))
    (fun b hb => by have := hB b hb; linarith)
  refine vGe_mono (le_of_eq ?_) (vGe_mul h1 h2)
  ring

/-- **(L), `ν ≥ 2`**: `v₂(G_A) ≥ −(ν − 1)π − 2 − ⌊log₂ π⌋`, `G_B = 0` (`π = i + j − K ≥ 1`). -/
theorem lemma10_LM {h i j : ℕ} (hν : 2 ≤ nuA az) (hi : i < h) (hj : j < h) (hπ : h + 2 ≤ i + j) :
    vGe 2 (-((nuA az : ℤ) - 1) * ((i + j - (h + 1) : ℕ) : ℤ) - 2 - Nat.log 2 (i + j - (h + 1))) (GAm az h i j) ∧
      GBm az h i j = 0 := by
  refine ⟨vGe_GA_L hi hj hπ _ (fun b hb => ?_), GB_LM (by omega) (by omega) (by omega)⟩
  set π := i + j - (h + 1) with hπdef
  have hπ' : ((h : ℤ) + 2 - i - j) = 1 - (π : ℤ) := by rw [hπdef]; push_cast [show h + 1 ≤ i + j by omega]; ring
  rw [hπ']
  have h1 := vf_ge b
  have h3 := log_two_mono hb.le
  have hν' : (2 : ℤ) ≤ nuA az := by exact_mod_cast hν
  have hbπ : (b : ℤ) + 1 ≤ π := by exact_mod_cast hb
  have key : ((nuA az : ℤ) - 2) * ((π : ℤ) - 1 - b) ≥ 0 := mul_nonneg (by linarith) (by linarith)
  have h1' : (b : ℤ) ≤ vf b + Nat.log 2 b + 1 := by exact_mod_cast h1
  have h3' : (Nat.log 2 b : ℤ) ≤ Nat.log 2 π := by exact_mod_cast h3
  nlinarith

/-- **(L), `ν = 1`**: `v₂(G_A) ≥ −π`. -/
theorem lemma10_LM1 {h i j : ℕ} (hν : nuA az = 1) (hi : i < h) (hj : j < h) (hπ : h + 2 ≤ i + j) :
    vGe 2 (-((i + j - (h + 1) : ℕ) : ℤ)) (GAm az h i j) ∧ GBm az h i j = 0 := by
  refine ⟨vGe_GA_L hi hj hπ _ (fun b hb => ?_), GB_LM (by omega) (by omega) (by omega)⟩
  rw [hν]
  push_cast [show h + 1 ≤ i + j by omega]
  have := Nat.zero_le (vf b)
  omega

/-- `π = 0`: both entries vanish. -/
theorem lemma10_L0M {h i j : ℕ} (hij : i + j = h + 1) : GAm az h i j = 0 ∧ GBm az h i j = 0 := by
  refine ⟨?_, GB_LM (by omega) (by omega) (by omega)⟩
  rw [GA_LM (by omega) (by omega) (by omega), show Ico (h + 1 - j) i = ∅ by
    rw [Finset.Ico_eq_empty_iff]; omega]
  simp [PZint]

/-! ### Case (U): `i + j ≤ h` -/

lemma muPoly_zeroM : muPoly az 0 = 0 := by simp [muPoly]

/-- The pole sum in case (U) is a finite difference. -/
lemma sum_UM {h i j : ℕ} (hij : i + j ≤ h) (Y : ℕ → Qd az) :
    ∑ m ∈ range (h + 1), (cPole h (PZ h (range i ∪ Ico (h + 1 - j) (h + 1))) m : Qd az) * Y m =
      (((1 : ℚ) / (2 ^ (h - i - j) * (((h - i - j) ! : ℕ) : ℚ)) : ℚ) : Qd az) *
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

/-- `T(l) = z^{x_{i+l}} P(x_{i+l})`. -/
noncomputable def TseqAM (az : ℕ) [Fact (1 ≤ az)] (h i l : ℕ) : Qd az :=
  (zK az) ^ poleZ h (i + l) * Psum az (poleZ h (i + l))

/-- `T_B(l) = z^{x_{i+l}}`. -/
noncomputable def TseqBM (az : ℕ) [Fact (1 ≤ az)] (h i l : ℕ) : Qd az := (zK az) ^ poleZ h (i + l)

lemma GA_UM {h i j : ℕ} (hij : i + j ≤ h) :
    GAm az h i j = ((4 / (((h - i - j) ! : ℕ) : ℚ) : ℚ) : Qd az) * (Δ_[1])^[h - i - j] (TseqAM az h i) 0 := by
  rw [GA_eqM (by omega), PZ_U hij]
  unfold Afun
  rw [divD_U hij, muPoly_zeroM, zero_add]
  simp_rw [mul_assoc]
  rw [sum_UM hij (fun m => (zK az) ^ poleZ h m * Psum az (poleZ h m)), ← mul_assoc, ← Rat.cast_mul,
    scale_U hij]
  rfl

lemma GB_UM {h i j : ℕ} (hij : i + j ≤ h) :
    GBm az h i j = -(((4 / (((h - i - j) ! : ℕ) : ℚ) : ℚ) : Qd az) * (Δ_[1])^[h - i - j] (TseqBM az h i) 0) := by
  rw [GB_eqM (by omega), PZ_U hij]
  unfold Bfun
  rw [sum_UM hij (fun m => (zK az) ^ poleZ h m), mul_neg, ← mul_assoc, ← Rat.cast_mul, scale_U hij]
  rfl

/-! ### The recurrences -/

lemma Psum_add_twoM {x : ℤ} (hx : Even x) :
    Psum az (x + 2) = Psum az x - (zK az) ^ (-x - 1) / ((x + 1 : ℤ) : Qd az) ^ 2 := by
  obtain ⟨r, rfl⟩ := hx
  rcases lt_or_ge r 0 with hr | hr
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = -((n : ℤ) + 1) := ⟨(-r - 1).toNat, by omega⟩
    have e1 : (-((n : ℤ) + 1) + -((n : ℤ) + 1) + 2) = -((2 * n : ℕ) : ℤ) := by push_cast; ring
    have e2 : (-((n : ℤ) + 1) + -((n : ℤ) + 1)) = -((2 * (n + 1) : ℕ) : ℤ) := by push_cast; ring
    have e3 : -(-((n : ℤ) + 1) + -((n : ℤ) + 1)) - 1 = ((2 * n + 1 : ℕ) : ℤ) := by push_cast; ring
    have e4 : (((-((n : ℤ) + 1) + -((n : ℤ) + 1) + 1 : ℤ)) : Qd az) ^ 2 = ((2 * n + 1 : ℕ) : Qd az) ^ 2 := by
      push_cast; ring
    unfold Psum
    rw [e3, e4, e1, e2, if_pos (by omega), if_pos (by omega), Int.natAbs_neg, Int.natAbs_neg,
      Int.natAbs_natCast, Int.natAbs_natCast, show 2 * n / 2 = n by omega, show 2 * (n + 1) / 2 = n + 1 by omega,
      sum_range_succ, zpow_natCast]
    ring
  · lift r to ℕ using hr with n
    have hPx : Psum az ((n : ℤ) + n) =
        -∑ k ∈ range n, ((zK az) ^ (2 * k + 1))⁻¹ / ((2 * k + 1 : ℕ) : Qd az) ^ 2 := by
      unfold Psum
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [if_neg (by omega), show ((n : ℤ) + n) = ((2 * n : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast,
          show 2 * n / 2 = n by omega]
    have e1 : ((n : ℤ) + n + 2) = ((2 * (n + 1) : ℕ) : ℤ) := by push_cast; ring
    have e3 : -((n : ℤ) + n) - 1 = -((2 * n + 1 : ℕ) : ℤ) := by push_cast; ring
    have e4 : ((((n : ℤ) + n + 1 : ℤ)) : Qd az) ^ 2 = ((2 * n + 1 : ℕ) : Qd az) ^ 2 := by push_cast; ring
    rw [hPx, e3, e4]
    unfold Psum
    rw [e1, if_neg (by omega), Int.natAbs_natCast, show 2 * (n + 1) / 2 = n + 1 by omega, sum_range_succ,
      zpow_neg, zpow_natCast]
    ring

lemma TU_recM (h i l : ℕ) :
    TseqAM az h i (l + 1) = (zK az) ^ 2 * TseqAM az h i l + (-(zK az)) * ((gSZ (poleZ h i + 1) l : ℚ) : Qd az) := by
  unfold TseqAM
  set x := poleZ h (i + l) with hx
  have hx2 : poleZ h (i + (l + 1)) = x + 2 := by rw [hx, poleZ_add, poleZ_add]; push_cast; ring
  have hg : ((gSZ (poleZ h i + 1) l : ℚ) : Qd az) = 1 / ((x + 1 : ℤ) : Qd az) ^ 2 := by
    unfold gSZ; rw [hx, poleZ_add]; push_cast; ring
  rw [hx2, Psum_add_twoM (even_poleZ h (i + l)), hg]
  have hz1 : (zK az) ^ (x + 2) = (zK az) ^ 2 * (zK az) ^ x := by
    rw [zpow_add₀ zK_ne_zero, mul_comm]; norm_cast
  have hz2 : (zK az) ^ (x + 2) * (zK az) ^ (-x - 1) = (zK az) := by
    rw [← zpow_add₀ zK_ne_zero, show x + 2 + (-x - 1) = 1 by ring, zpow_one]
  rw [mul_sub, mul_div_assoc', hz2, hz1]
  ring

lemma TB_recM (h i l : ℕ) :
    TseqBM az h i (l + 1) = (zK az) ^ 2 * TseqBM az h i l + 0 * ((gSZ (poleZ h i + 1) l : ℚ) : Qd az) := by
  unfold TseqBM
  rw [show poleZ h (i + (l + 1)) = poleZ h (i + l) + 2 by rw [poleZ_add, poleZ_add]; push_cast; ring,
    zpow_add₀ zK_ne_zero, zero_mul, add_zero, zpow_two, sq]
  ring

/-! ### Valuations of the ingredients -/

lemma vGe_zKM : vGe 2 0 (zK az) := by simpa using vGe_zK_zpow (p := 2) (az := az) 1

lemma vGe_fourM : vGe 2 2 (4 : Qd az) := by
  have := vGe_of_V2M (az := az) (V2_two_zpow 2)
  norm_num at this
  exact this

lemma vGe_inv_odd_sqM (k : ℕ) : vGe 2 0 ((((2 * k + 1 : ℕ) : Qd az) ^ 2)⁻¹) := by
  have e : ((((2 * k + 1 : ℕ) : Qd az) ^ 2)⁻¹) = (((1 / ((2 * k + 1 : ℤ) : ℚ)) ^ 2 : ℚ) : Qd az) := by
    push_cast; rw [one_div, inv_pow]
  rw [e]
  have := V2_pow (V2_inv_oddInt (n := 2 * k + 1) ⟨k, rfl⟩) 2
  simpa using vGe_of_V2M (az := az) this

lemma vGe_PsumM (x : ℤ) : vGe 2 0 (Psum az x) := by
  unfold Psum
  split_ifs
  · refine vGe_sum _ _ (fun k _ => ?_)
    rw [div_eq_mul_inv]
    have := vGe_mul (vGe_zK_zpow (p := 2) (az := az) ((2 * k + 1 : ℕ) : ℤ)) (vGe_inv_odd_sqM k)
    rw [zpow_natCast, add_zero] at this
    exact this
  · refine vGe_neg (vGe_sum _ _ (fun k _ => ?_))
    rw [div_eq_mul_inv, ← zpow_natCast, ← zpow_neg]
    have := vGe_mul (vGe_zK_zpow (p := 2) (az := az) (-((2 * k + 1 : ℕ) : ℤ))) (vGe_inv_odd_sqM k)
    rw [add_zero] at this
    exact this

lemma vGe_TA0 (h i : ℕ) : vGe 2 0 (TseqAM az h i 0) := by
  have := vGe_mul (vGe_zK_zpow (p := 2) (az := az) (poleZ h (i + 0))) (vGe_PsumM (poleZ h (i + 0)))
  rw [zero_add] at this
  exact this

/-- **(U), `ν ≥ 2`** (Theorem U's bound, using only `v₂(1 − y) ≥ 2`): `v₂ ≥ N₀ − ⌊log₂ N₀⌋`. -/
theorem vGe_UM {h i j : ℕ} (hν : 2 ≤ nuA az) (hij : i + j ≤ h) :
    vGe 2 (((h - i - j : ℕ) : ℤ) - Nat.log 2 (h - i - j)) (GAm az h i j) ∧
      vGe 2 (((h - i - j : ℕ) : ℤ) - Nat.log 2 (h - i - j)) (GBm az h i j) := by
  set N := h - i - j
  have hη : vGe 2 2 ((zK az) ^ 2 - 1) := vGe_mono (by exact_mod_cast hν) vGe_zK_sq_sub_oneM
  have hc := vGe_of_V2M (az := az) (V2_four_div_factorial N)
  have hB0 : vGe 2 0 (TseqBM az h i 0) := vGe_zK_zpow _
  have hA := vGe_fd_seqM hη (vGe_neg vGe_zKM) (oddS h i) (vGe_TA0 h i) (TU_recM h i) N
  have hB := vGe_fd_seqM hη (vGe_zero 0) (oddS h i) hB0 (TB_recM h i) N
  refine ⟨?_, ?_⟩
  · rw [GA_UM hij]
    refine vGe_mono ?_ (vGe_mul hc hA)
    omega
  · rw [GB_UM hij]
    refine vGe_neg (vGe_mono ?_ (vGe_mul hc hB))
    omega

/-- **(U), any `ν ≥ 1`** (coarse): `v₂ ≥ 1`. -/
theorem vGe_UM1 (ha : Even az) {h i j : ℕ} (hij : i + j ≤ h) : vGe 2 1 (GAm az h i j) ∧ vGe 2 1 (GBm az h i j) := by
  set N := h - i - j
  have hη : vGe 2 1 ((zK az) ^ 2 - 1) := vGe_mono (by exact_mod_cast one_le_nuA ha) vGe_zK_sq_sub_oneM
  have hc := vGe_of_V2M (az := az) (V2_four_div_factorial N)
  have hB0 : vGe 2 0 (TseqBM az h i 0) := vGe_zK_zpow _
  have hA := vGe_fd_seqM1 hη (vGe_neg vGe_zKM) (oddS h i) (vGe_TA0 h i) (TU_recM h i) N
  have hB := vGe_fd_seqM1 hη (vGe_zero 0) (oddS h i) hB0 (TB_recM h i) N
  have hv := vf_le N
  refine ⟨?_, ?_⟩
  · rw [GA_UM hij]
    refine vGe_mono ?_ (vGe_mul hc hA)
    omega
  · rw [GB_UM hij]
    refine vGe_neg (vGe_mono ?_ (vGe_mul hc hB))
    omega

/-- **(U)**, `N₀ = 0`: `v₂ ≥ 2`. -/
theorem vGe_U0M {h i j : ℕ} (hij : i + j = h) : vGe 2 2 (GAm az h i j) ∧ vGe 2 2 (GBm az h i j) := by
  have hN : h - i - j = 0 := by omega
  have h4 : (((4 / (((0 : ℕ) ! : ℕ) : ℚ) : ℚ) : Qd az)) = 4 := by norm_num
  have hB0 : vGe 2 0 (TseqBM az h i 0) := vGe_zK_zpow _
  refine ⟨?_, ?_⟩
  · rw [GA_UM hij.le, hN, h4, Function.iterate_zero, id]
    have := vGe_mul vGe_fourM (vGe_TA0 (az := az) h i)
    rwa [add_zero] at this
  · rw [GB_UM hij.le, hN, h4, Function.iterate_zero, id]
    have := vGe_neg (vGe_mul vGe_fourM hB0)
    rwa [add_zero] at this

end Chi2U.V.TwoAdicNu
