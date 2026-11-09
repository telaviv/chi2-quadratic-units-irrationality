/-
# Theorem V_i, Lemma 10_0 (PROOF_TI2 §3 = PROOF_VODD §2): `n₂(Δ_h) ≤ h²/2 + h` at an odd trace `n`

**Copy of `Chi2U/VOdd/TenZero.lean`** for the Ti₂ machine. At odd `n` the prime `2` is inert in `ℚ(√(n² − 4))`
(`n² − 4 ≡ 5 mod 8`), the order is `O₂ = ℤ_(2)[½ + √d]` (`Ti/VGe.lean`), and `ν = v₂(1 − y) = v₂(n·z) = 0`
(`VOdd.nuA_odd`). The entries `G_{ij}`, their trace-generic (L), (U) formulas and the Gram identity
`det G = 2^{3h} Δ_h` are those of `Chi2U/Ti/TwoAdicNu.lean`, `Chi2U/Ti/Lemma10nu.lean` (stated for every trace; only
their `ν ≥ 1` corollaries need `Even n`). The `z`-free parts (`VOdd.gO`, `VOdd.gO_concave`, `VOdd.sum_gO`) are reused.

PROOF_TI2 §3 lists the six facts used: `y = −z²` and `1 − y = n z` are units of `O₂`, `z^{±1} ∈ O₂`, the Mahler form
with `v₂(n^{b+1}) = 0`, the factor `2^{1−π}`, and `(U′)` with `v₂(Q − 1) ≥ 0`; none sees the sign of `y` (the signs
`χ₄(t)`, `(−1)^{x/2}`, `(−1)^b` are units).

Entry bounds (`s = i + j`, `K = h + 1`, `π = s − K`, `N₀ = K − 1 − s`):
* (L), `π ≥ 1`: `G_B = 0`, `v₂(G_A) ≥ 1 − π` (`vGe_GA_L` with `ν = 0`); `π = 0`: `G_A = G_B = 0`;
* (U), `N₀ ≥ 0`: `v₂ ≥ 2 − v₂(N₀!)` (`vGe_UM0`; PROOF_VODD's (U′)).
Hence `v₂(G_{ij}) ≥ g(i + j)`, `g(s) = min(s − K + 3, K + 1 − s)` (`vGe_entryO`).

**Departure from PROOF_VODD** (as in the χ₂ file): concavity of `g` and integer row/column weights replace the
majorisation/Karamata step; `v₂(det G) ≥ Σ_i g(2i) = 2h − h²/2`, so `n₂ ≤ h²/2 + h = n2O h`. Checked numerically:
`scripts/ti/check_twoadic_ti.py` (odd n = 3, …, 11, 71, h ≤ 16; observed n₂ = 104 at h = 16, bound 144).
-/
import Chi2U.Ti.Lemma10nu
import Chi2U.VOdd.TenZero

set_option linter.unusedSectionVars false

namespace Chi2U.Ti.TenZero

open Polynomial Finset fwdDiff Chi2U.TwoAdicAux Chi2U.Ti.TwoAdicNu
open scoped Nat

variable {n : ℕ} [Fact (3 ≤ n)]

/-! ### (U) at `ν = 0` -/

/-- The sequence bound with `v₂(Q − 1) ≥ 0`: `Δ^m T(0)` is integral. -/
theorem vGe_fd_seqM0 {Q e : Qt n} (hη : vGe 2 0 (Q - 1)) (he : vGe 2 0 e) {s : ℤ} (hs : Odd s)
    {T : ℕ → Qt n} (hT0 : vGe 2 0 (T 0))
    (hrec : ∀ l, T (l + 1) = Q * T l + e * ((gSZ s l : ℚ) : Qt n)) (m : ℕ) :
    vGe 2 0 ((Δ_[1])^[m] T 0) := by
  rw [fd_seq_formula hrec]
  refine vGe_add (vGe_mono ?_ (vGe_mul (vGe_pow hη m) hT0)) ?_
  · simp
  · refine vGe_mono ?_ (vGe_mul he (vGe_sum (v := 0) _ _ (fun k hk => ?_)))
    · simp
    rw [fd_ratCastM]
    refine vGe_mono ?_ (vGe_mul (vGe_pow hη _) (vGe_of_V2M (V2_fd_gSZ hs k)))
    have := Nat.zero_le (vf k)
    omega

/-- **(U′)**, any trace: `v₂(G_A), v₂(G_B) ≥ 2 − v₂(N₀!)` for `i + j ≤ h`, `N₀ = h − i − j`. -/
theorem vGe_UM0 {h i j : ℕ} (hij : i + j ≤ h) :
    vGe 2 (2 - (vf (h - i - j) : ℤ)) (GAm n h i j) ∧ vGe 2 (2 - (vf (h - i - j) : ℤ)) (GBm n h i j) := by
  set N := h - i - j
  have hη : vGe 2 0 (-(zK n) ^ 2 - 1) :=
    vGe_mono (by positivity) (vGe_zK_sq_sub_oneM (n := n))
  have hc := vGe_of_V2M (n := n) (V2_four_div_factorial N)
  have hA := vGe_fd_seqM0 hη (vGe_neg vGe_zKM) (oddS h i) (vGe_TA0 h i) (TU_recM h i) N
  have hB := vGe_fd_seqM0 hη (vGe_zero 0) (oddS h i) (vGe_TB0 h i) (TB_recM h i) N
  refine ⟨?_, ?_⟩
  · rw [GA_UM hij]
    refine vGe_mono ?_ (vGe_mul hc hA)
    omega
  · rw [GB_UM hij]
    refine vGe_neg (vGe_mono ?_ (vGe_mul hc hB))
    omega

/-! ### The concave entry bound -/

/-- **Entry bound** at odd `n` (PROOF_VODD §2, (L) and (U′) at `ν = 0`): `v₂(G_{ij}) ≥ g(i + j)`, `g = VOdd.gO h`. -/
theorem vGe_entryO (ha : Odd n) {h i j : ℕ} (hi : i < h) (hj : j < h) :
    vGe 2 (VOdd.gO h ((i : ℤ) + j)) (GAm n h i j) ∧ vGe 2 (VOdd.gO h ((i : ℤ) + j)) (GBm n h i j) := by
  unfold VOdd.gO
  rcases Nat.lt_or_ge (i + j) (h + 1) with hij | hij
  · have hU := vGe_UM0 (n := n) (h := h) (i := i) (j := j) (by omega)
    have hv := vf_le (h - i - j)
    have hle : min ((i : ℤ) + j - h + 2) ((h : ℤ) + 2 - (i + j)) ≤ 2 - (vf (h - i - j) : ℤ) := by
      refine (min_le_left _ _).trans ?_
      omega
    exact ⟨vGe_mono hle hU.1, vGe_mono hle hU.2⟩
  · rcases Nat.eq_or_lt_of_le hij with hij' | hij'
    · have := lemma10_L0M (n := n) hij'.symm
      rw [this.1, this.2]; exact ⟨vGe_zero _, vGe_zero _⟩
    · have hle : min ((i : ℤ) + j - h + 2) ((h : ℤ) + 2 - (i + j)) ≤ (h : ℤ) + 2 - i - j :=
        (min_le_right _ _).trans (le_of_eq (by ring))
      refine ⟨vGe_GA_L hi hj (by omega) _ (fun b _ => ?_), ?_⟩
      · rw [VOdd.nuA_odd ha]
        have := Nat.zero_le (vf b)
        push_cast
        omega
      · rw [GB_LM (by omega) (by omega) (by omega)]; exact vGe_zero _

/-! ### Leibniz with row and column weights -/

/-- `v₂(det G) ≥ Σ_i g(2i) = 2h − h²/2` at odd `n` (`h = 2J`). -/
theorem vGeX_detO (ha : Odd n) {J : ℕ} (hJ : 1 ≤ J) :
    vGeX 2 (4 * (J : ℤ) - 2 * (J : ℤ) ^ 2)
      (Matrix.of fun i j : Fin (J + J) => C (GAm n (J + J) i j) + X * C (GBm n (J + J) i j)).det := by
  set h := J + J with hhdef
  set ρ : Fin h → ℤ := fun i => VOdd.gO h (2 * ((i : ℕ) : ℤ)) / 2 with hρ
  set κ : Fin h → ℤ := fun j => VOdd.gO h (2 * ((j : ℕ) : ℤ)) - VOdd.gO h (2 * ((j : ℕ) : ℤ)) / 2 with hκ
  have hdet := vGeX_det2M (Matrix.of fun i j : Fin h => C (GAm n h i j) + X * C (GBm n h i j)) ρ κ
    (fun i j => by
      have hE := vGe_entryO (n := n) ha (h := h) i.isLt j.isLt
      have hc := VOdd.gO_concave h ((i : ℕ) : ℤ) ((j : ℕ) : ℤ)
      have hle : ρ i + κ j ≤ VOdd.gO h (((i : ℕ) : ℤ) + ((j : ℕ) : ℤ)) := by
        simp only [hρ, hκ]; omega
      rw [Matrix.of_apply]
      exact vGeX_add (vGeX_C (vGe_mono hle hE.1)) (vGeX_X_mul (vGeX_C (vGe_mono hle hE.2))))
  have hsum : ∑ i, ρ i + ∑ i, κ i = 4 * (J : ℤ) - 2 * (J : ℤ) ^ 2 := by
    rw [← sum_add_distrib, ← VOdd.sum_gO hJ, ← Fin.sum_univ_eq_sum_range (fun i => VOdd.gO h (2 * (i : ℤ))) h]
    refine sum_congr rfl (fun i _ => ?_)
    simp only [hρ, hκ]; ring
  rwa [hsum] at hdet

end Chi2U.Ti.TenZero

namespace Chi2U.Ti

open Polynomial Finset Chi2U.TwoAdicAux Chi2U.Ti.TwoAdicNu Chi2U.Ti.TenZero

/-- **Lemma 10_0** (PROOF_TI2 §3 = PROOF_VODD §2): at an odd trace `n` (`2` inert, `ν = 0`),
`n₂(Δ_h) ≤ h²/2 + h` for even `h ≥ 2`. Route (as `Chi2U.VOdd.lemma10_0_proof`): `Δ_h = 2^{−3h} det G`
(`det_anchoredM`), `v₂(det G) ≥ 2h − h²/2` (`vGeX_detO`). -/
theorem lemma10_0_proof (n : ℕ) [Fact (3 ≤ n)] (hn : Odd n) {h : ℕ} (hh : Even h) (h2 : 2 ≤ h) (k : ℕ) :
    padicNorm 2 ((Delta n h).coeff k) ≤ (2 : ℚ) ^ VOdd.n2O h := by
  obtain ⟨J, rfl⟩ := hh
  have hJ : 1 ≤ J := by omega
  have hdet := vGeX_detO (n := n) hn hJ
  rw [det_anchoredM ⟨J, rfl⟩] at hdet
  have hinv : (Delta n (J + J)).map (algebraMap ℚ (Qt n)) =
      C ((((2 : ℚ) ^ (-((3 * (J + J) : ℕ) : ℤ))) : ℚ) : Qt n) *
        (C ((2 : Qt n) ^ (3 * (J + J))) * (Delta n (J + J)).map (algebraMap ℚ (Qt n))) := by
    rw [← mul_assoc, ← C_mul]
    have : ((((2 : ℚ) ^ (-((3 * (J + J) : ℕ) : ℤ))) : ℚ) : Qt n) * (2 : Qt n) ^ (3 * (J + J)) = 1 := by
      rw [zpow_neg, zpow_natCast, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat,
        inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)]
    rw [this, C_1, one_mul]
  have hfin := vGeX_mul (vGeX_C (vGe_of_V2M (n := n) (V2_two_zpow (-((3 * (J + J) : ℕ) : ℤ))))) hdet
  rw [← hinv] at hfin
  refine (padicNorm_coeff_of_vGeX_map hfin k).trans ?_
  rw [← zpow_natCast]
  refine zpow_le_zpow_right₀ (by norm_num) ?_
  have hn2 : (VOdd.n2O (J + J) : ℤ) = 2 * (J : ℤ) ^ 2 + 2 * J := by
    unfold VOdd.n2O
    rw [show (J + J) ^ 2 / 2 = 2 * J ^ 2 by ring_nf; omega]
    push_cast; ring
  rw [hn2]
  push_cast
  nlinarith

end Chi2U.Ti
