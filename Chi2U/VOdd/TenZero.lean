/-
# Lemma 10_0 (PROOF_VODD §2): `n₂(Δ_h) ≤ h²/2 + h` at an odd trace `az`

At odd `az` the prime `2` is inert in `ℚ(√(az² + 4))` and `ν = nuA az = v₂(az) = 0`. The entries `G_{ij}` of the
rescaled anchored Gram matrix, their `az`-generic (L), (U) formulas and the Gram identity `det G = 2^{3h} Δ_h` are
those of Lemma 10_ν (`Chi2U/V/TwoAdicNu.lean`, `Chi2U/V/Lemma10nu.lean`, which are stated for every trace; only their
`ν ≥ 1` corollaries need `Even az`). This file supplies the `ν = 0` entry bounds and the weighted Leibniz count.

Entry bounds (`s = i + j`, `K = h + 1`, `π = s − K`, `N₀ = K − 1 − s`):
* (L), `π ≥ 1`: `G_B = 0`, `v₂(G_A) ≥ 1 − π + b + v₂(b!) − 0·(b + 1) ≥ 1 − π` (`vGe_GA_L` with `ν = 0`);
* `π = 0`: `G_A = G_B = 0` (`lemma10_L0M`);
* (U), `N₀ ≥ 0`: `G = (4/N₀!)·Δ^{N₀}T(0)` with `T` integral (`v₂(z² − 1) ≥ 0` suffices), so
  `v₂ ≥ 2 − v₂(N₀!) ≥ 2 − N₀` (`vGe_UM0`; PROOF_VODD's (U′)).
Hence `v₂(G_{ij}) ≥ g(i + j)`, `g(s) = min(s − K + 3, K + 1 − s)` (`gO`, `vGe_entryO`).

**Departure from PROOF_VODD** (as in Lemma 10_ν): instead of the majorisation/Karamata step, concavity of `g` gives
`g(2i) + g(2j) ≤ 2g(i + j)`; with integer row/column weights `⌊g(2i)/2⌋`, `⌈g(2j)/2⌉` the weighted Leibniz bound gives
`v₂(det G) ≥ Σ_i g(2i) = 2h − h²/2` (`sum_gO`), so `n₂ ≤ 3h − (2h − h²/2) = h²/2 + h = n2O h`.
-/
import Chi2U.VOdd.Defs
import Chi2U.V.Lemma10nu

namespace Chi2U.VOdd

open Polynomial Finset fwdDiff Chi2U.TwoAdicAux Chi2U.V.TwoAdicNu
open scoped Nat

variable {az : ℕ} [Fact (1 ≤ az)]

omit [Fact (1 ≤ az)] in
/-- `ν = v₂(az) = 0` at an odd trace. -/
lemma nuA_odd (ha : Odd az) : V.nuA az = 0 := by
  unfold V.nuA
  exact padicValNat.eq_zero_of_not_dvd (fun hd => (Nat.not_even_iff_odd.mpr ha) (even_iff_two_dvd.mpr hd))

/-! ### (U) at `ν = 0` -/

/-- The sequence bound with `v₂(Q − 1) ≥ 0`: `Δ^m T(0)` is integral. -/
theorem vGe_fd_seqM0 {Q e : Qd az} (hη : vGe 2 0 (Q - 1)) (he : vGe 2 0 e) {s : ℤ} (hs : Odd s)
    {T : ℕ → Qd az} (hT0 : vGe 2 0 (T 0))
    (hrec : ∀ l, T (l + 1) = Q * T l + e * ((gSZ s l : ℚ) : Qd az)) (m : ℕ) :
    vGe 2 0 ((Δ_[1])^[m] T 0) := by
  rw [fd_seq_formula hrec]
  refine vGe_add (vGe_mono ?_ (vGe_mul (vGe_pow hη m) hT0)) ?_
  · simp
  · refine vGe_mono ?_ (vGe_mul he (vGe_sum (n := 0) _ _ (fun k hk => ?_)))
    · simp
    rw [fd_ratCastM]
    refine vGe_mono ?_ (vGe_mul (vGe_pow hη _) (vGe_of_V2M (V2_fd_gSZ hs k)))
    have := Nat.zero_le (vf k)
    omega

/-- **(U′)**, any trace: `v₂(G_A), v₂(G_B) ≥ 2 − v₂(N₀!)` for `i + j ≤ h`, `N₀ = h − i − j`. -/
theorem vGe_UM0 {h i j : ℕ} (hij : i + j ≤ h) :
    vGe 2 (2 - (vf (h - i - j) : ℤ)) (GAm az h i j) ∧ vGe 2 (2 - (vf (h - i - j) : ℤ)) (GBm az h i j) := by
  set N := h - i - j
  have hη : vGe 2 0 ((zK az) ^ 2 - 1) :=
    vGe_mono (by positivity) (vGe_zK_sq_sub_oneM (az := az))
  have hc := vGe_of_V2M (az := az) (V2_four_div_factorial N)
  have hB0 : vGe 2 0 (TseqBM az h i 0) := vGe_zK_zpow _
  have hA := vGe_fd_seqM0 hη (vGe_neg vGe_zKM) (oddS h i) (vGe_TA0 h i) (TU_recM h i) N
  have hB := vGe_fd_seqM0 hη (vGe_zero 0) (oddS h i) hB0 (TB_recM h i) N
  refine ⟨?_, ?_⟩
  · rw [GA_UM hij]
    refine vGe_mono ?_ (vGe_mul hc hA)
    omega
  · rw [GB_UM hij]
    refine vGe_neg (vGe_mono ?_ (vGe_mul hc hB))
    omega

/-! ### The concave entry bound -/

/-- The concave entry minorant `g(s) = min(s − K + 3, K + 1 − s)`, `K = h + 1`. -/
def gO (h : ℕ) (s : ℤ) : ℤ := min (s - h + 2) ((h : ℤ) + 2 - s)

/-- **Entry bound** at odd `az` (PROOF_VODD §2, (L) and (U′) at `ν = 0`): `v₂(G_{ij}) ≥ g(i + j)`. -/
theorem vGe_entryO (ha : Odd az) {h i j : ℕ} (hi : i < h) (hj : j < h) :
    vGe 2 (gO h ((i : ℤ) + j)) (GAm az h i j) ∧ vGe 2 (gO h ((i : ℤ) + j)) (GBm az h i j) := by
  unfold gO
  rcases Nat.lt_or_ge (i + j) (h + 1) with hij | hij
  · have hU := vGe_UM0 (az := az) (h := h) (i := i) (j := j) (by omega)
    have hv := vf_le (h - i - j)
    have hle : min ((i : ℤ) + j - h + 2) ((h : ℤ) + 2 - (i + j)) ≤ 2 - (vf (h - i - j) : ℤ) := by
      refine (min_le_left _ _).trans ?_
      omega
    exact ⟨vGe_mono hle hU.1, vGe_mono hle hU.2⟩
  · rcases Nat.eq_or_lt_of_le hij with hij' | hij'
    · have := lemma10_L0M (az := az) hij'.symm
      rw [this.1, this.2]; exact ⟨vGe_zero _, vGe_zero _⟩
    · have hle : min ((i : ℤ) + j - h + 2) ((h : ℤ) + 2 - (i + j)) ≤ (h : ℤ) + 2 - i - j :=
        (min_le_right _ _).trans (le_of_eq (by ring))
      refine ⟨vGe_GA_L hi hj (by omega) _ (fun b _ => ?_), ?_⟩
      · rw [nuA_odd ha]
        have := Nat.zero_le (vf b)
        push_cast
        omega
      · rw [GB_LM (by omega) (by omega) (by omega)]; exact vGe_zero _

/-- `g` is concave: `g(2i) + g(2j) ≤ 2g(i + j)`. -/
lemma gO_concave (h : ℕ) (i j : ℤ) : gO h (2 * i) + gO h (2 * j) ≤ 2 * gO h (i + j) := by
  unfold gO
  rcases min_cases ((i + j) - (h : ℤ) + 2) ((h : ℤ) + 2 - (i + j)) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]
  · have := min_le_left (2 * i - (h : ℤ) + 2) ((h : ℤ) + 2 - 2 * i)
    have := min_le_left (2 * j - (h : ℤ) + 2) ((h : ℤ) + 2 - 2 * j)
    linarith
  · have := min_le_right (2 * i - (h : ℤ) + 2) ((h : ℤ) + 2 - 2 * i)
    have := min_le_right (2 * j - (h : ℤ) + 2) ((h : ℤ) + 2 - 2 * j)
    linarith

/-- `Σ_{i < h} g(2i) = 2h − h²/2` (`h = 2J`: `4J − 2J²`). -/
lemma sum_gO {J : ℕ} (hJ : 1 ≤ J) :
    ∑ i ∈ range (J + J), gO (J + J) (2 * (i : ℤ)) = 4 * (J : ℤ) - 2 * (J : ℤ) ^ 2 := by
  have hsplit : J + J = (J + 1) + (J - 1) := by omega
  rw [hsplit, sum_range_add, ← hsplit]
  unfold gO
  have hJc : ((J - 1 : ℕ) : ℤ) = (J : ℤ) - 1 := by push_cast [hJ]; ring
  have s1 : ∑ x ∈ range (J + 1), min (2 * (x : ℤ) - ((J + J : ℕ) : ℤ) + 2) (((J + J : ℕ) : ℤ) + 2 - 2 * (x : ℤ)) =
      ∑ x ∈ range (J + 1), ((2 - 2 * (J : ℤ)) + 2 * (x : ℤ)) := by
    refine sum_congr rfl (fun x hx => ?_)
    have hx' : (x : ℤ) ≤ J := by have := mem_range.mp hx; omega
    rw [min_eq_left (by push_cast; omega)]; push_cast; ring
  have s2 : ∑ x ∈ range (J - 1), min (2 * (((J + 1 + x : ℕ)) : ℤ) - ((J + J : ℕ) : ℤ) + 2)
      (((J + J : ℕ) : ℤ) + 2 - 2 * (((J + 1 + x : ℕ)) : ℤ)) =
      ∑ x ∈ range (J - 1), ((0 : ℤ) + (-2) * (x : ℤ)) := by
    refine sum_congr rfl (fun x _ => ?_)
    rw [min_eq_right (by push_cast; omega)]; push_cast; ring
  rw [s1, s2]
  have a1 := V.TwoAdicNu.sum_affine (2 - 2 * (J : ℤ)) 2 (J + 1)
  have a2 := V.TwoAdicNu.sum_affine 0 (-2) (J - 1)
  rw [hJc] at a2
  push_cast at a1 a2 ⊢
  nlinarith

/-! ### Leibniz with row and column weights -/

/-- `v₂(det G) ≥ Σ_i g(2i) = 2h − h²/2` at odd `az` (`h = 2J`). -/
theorem vGeX_detO (ha : Odd az) {J : ℕ} (hJ : 1 ≤ J) :
    vGeX 2 (4 * (J : ℤ) - 2 * (J : ℤ) ^ 2)
      (Matrix.of fun i j : Fin (J + J) => C (GAm az (J + J) i j) + X * C (GBm az (J + J) i j)).det := by
  set h := J + J with hhdef
  set ρ : Fin h → ℤ := fun i => gO h (2 * ((i : ℕ) : ℤ)) / 2 with hρ
  set κ : Fin h → ℤ := fun j => gO h (2 * ((j : ℕ) : ℤ)) - gO h (2 * ((j : ℕ) : ℤ)) / 2 with hκ
  have hdet := vGeX_det2M (Matrix.of fun i j : Fin h => C (GAm az h i j) + X * C (GBm az h i j)) ρ κ
    (fun i j => by
      have hE := vGe_entryO (az := az) ha (h := h) i.isLt j.isLt
      have hc := gO_concave h ((i : ℕ) : ℤ) ((j : ℕ) : ℤ)
      have hle : ρ i + κ j ≤ gO h (((i : ℕ) : ℤ) + ((j : ℕ) : ℤ)) := by
        simp only [hρ, hκ]; omega
      rw [Matrix.of_apply]
      exact vGeX_add (vGeX_C (vGe_mono hle hE.1)) (vGeX_X_mul (vGeX_C (vGe_mono hle hE.2))))
  have hsum : ∑ i, ρ i + ∑ i, κ i = 4 * (J : ℤ) - 2 * (J : ℤ) ^ 2 := by
    rw [← sum_add_distrib, ← sum_gO hJ, ← Fin.sum_univ_eq_sum_range (fun i => gO h (2 * (i : ℤ))) h]
    refine sum_congr rfl (fun i _ => ?_)
    simp only [hρ, hκ]; ring
  rwa [hsum] at hdet

/-- **Lemma 10_0** (PROOF_VODD §2): at odd `az` (`2` inert, `ν = 0`), `n₂(Δ_h) ≤ h²/2 + h` for even `h ≥ 2`.
Route: `Δ_h = 2^{−3h} det G` (`det_anchoredM`), `v₂(det G) ≥ 2h − h²/2` (`vGeX_detO`). -/
theorem lemma10_0_proof (az : ℕ) [Fact (1 ≤ az)] (ha : Odd az) {h : ℕ} (hh : Even h) (h2 : 2 ≤ h) (k : ℕ) :
    padicNorm 2 ((Delta az h).coeff k) ≤ (2 : ℚ) ^ n2O h := by
  obtain ⟨J, rfl⟩ := hh
  have hJ : 1 ≤ J := by omega
  have hdet := vGeX_detO (az := az) ha hJ
  rw [det_anchoredM ⟨J, rfl⟩] at hdet
  have hinv : (Delta az (J + J)).map (algebraMap ℚ (Qd az)) =
      C ((((2 : ℚ) ^ (-((3 * (J + J) : ℕ) : ℤ))) : ℚ) : Qd az) *
        (C ((2 : Qd az) ^ (3 * (J + J))) * (Delta az (J + J)).map (algebraMap ℚ (Qd az))) := by
    rw [← mul_assoc, ← C_mul]
    have : ((((2 : ℚ) ^ (-((3 * (J + J) : ℕ) : ℤ))) : ℚ) : Qd az) * (2 : Qd az) ^ (3 * (J + J)) = 1 := by
      rw [zpow_neg, zpow_natCast, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat,
        inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)]
    rw [this, C_1, one_mul]
  have hfin := vGeX_mul (vGeX_C (vGe_of_V2M (az := az) (V2_two_zpow (-((3 * (J + J) : ℕ) : ℤ))))) hdet
  rw [← hinv] at hfin
  refine (padicNorm_coeff_of_vGeX_map hfin k).trans ?_
  rw [← zpow_natCast]
  refine zpow_le_zpow_right₀ (by norm_num) ?_
  have hn : (n2O (J + J) : ℤ) = 2 * (J : ℤ) ^ 2 + 2 * J := by
    unfold n2O
    rw [show (J + J) ^ 2 / 2 = 2 * J ^ 2 by ring_nf; omega]
    push_cast; ring
  rw [hn]
  push_cast
  nlinarith

end Chi2U.VOdd
