/-
# Theorem V_i: Lemma R and Corollary R — the reflection puts `Δ_h` in `ℚ[X]` (PROOF_TI2 §1 "Lemma R", PROOF_U §1)

**Copy of `Chi2U/LemmaR.lean`** with the sign fixed. The pole lemmas that do not see `z` are reused from
`Chi2U.LemmaR`: `poleZ_reflect`, `even_poleZ`, `Dpoly_monic`, `Dpoly_comp_neg`, `divD_comp_neg`, `dPrime_reflect`,
`cPole_reflect`. The exponent is called `e` here (`n` is the trace).

For `h` even (`K = h + 1` odd, poles `x_m` symmetric under `m ↦ h − m`):
* `σ(z^x) = z^{−x}` for every `x` (`σz = z⁻¹`; χ₂ needed `x` even, from `σz = −z⁻¹`), `(−1)^{−x/2} = (−1)^{x/2}`,
  `σ P(x) = P(−x)` (no sign: `σ(z^u) = z^{−u}` and the `χ₄` signs are rational);
* with the moment parity `σ μ(R) = −μ(R(−t))` (`Ti.sig_muPoly`) this gives **Lemma R** in the same form as for χ₂:
  `σ A(t^e) = (−1)^e A(t^e)` and `σ B(t^e) = (−1)^e B(t^e)` (`sig_Afun`, `sig_Bfun`): even-`e` entries are rational,
  odd-`e` entries are rational multiples of `√d`. (PROOF_TI2 §1 reads it through `w = iz`; the direct check in `K`
  with `y = −z²` is the route taken here.)
* **Corollary R** (`eval₂_Delta`): for every ring hom `ι : ℚ(√d) → L` and `x ∈ L`,
  `Δ_h(x) = det(ι A(t^{i+j}) + x ι B(t^{i+j}))`, by the same diagonal conjugation `W = diag(√d^{[j odd]})`.
  Special cases: `aeval_Delta` (`ι = emb`, real `x`) and `Delta_map` (`ι = C`, `x = X`).
-/
import Chi2U.Ti.Machine

set_option linter.unusedSectionVars false

namespace Chi2U
namespace Ti

variable {n : ℕ} [Fact (3 ≤ n)]

open Polynomial Matrix

variable {h : ℕ}

/-! ### The conjugation on the pole data -/

/-- `σ(z^x) = z^{−x}` (norm `+1`: no parity condition on `x`). -/
lemma sig_zK_zpow (x : ℤ) : sig ((zK n) ^ x) = (zK n) ^ (-x) := by
  rw [map_zpow₀, sig_zK, _root_.inv_zpow']

lemma sig_zK_pow_odd (k : ℕ) : sig ((zK n) ^ (2 * k + 1)) = ((zK n) ^ (2 * k + 1))⁻¹ := by
  rw [map_pow, sig_zK, inv_pow]

lemma sig_inv_zK_pow_odd (k : ℕ) : sig (((zK n) ^ (2 * k + 1))⁻¹) = (zK n) ^ (2 * k + 1) := by
  rw [map_inv₀, sig_zK_pow_odd, inv_inv]

lemma sig_natCast_Qt (k : ℕ) : sig (k : (Qt n)) = k := map_natCast sig k

lemma sig_neg_one_pow (k : ℕ) : sig ((-1 : Qt n) ^ k) = (-1) ^ k := by
  rw [map_pow, map_neg, map_one]

/-- `(−1)^{−x/2} = (−1)^{x/2}` for even `x`. -/
lemma sgnPole_neg {x : ℤ} (hx : Even x) : sgnPole (-x) = sgnPole x := by
  unfold sgnPole
  obtain ⟨j, rfl⟩ := hx
  rw [show -(j + j) = (-j) + (-j) by ring, show (-j + -j) / 2 = -j by omega, show (j + j) / 2 = j by omega,
    Int.natAbs_neg]

/-- `σ P(x) = P(−x)`. -/
lemma sig_Psum (x : ℤ) : sig (Psum n x) = Psum n (-x) := by
  unfold Psum
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [if_pos hx.le, if_neg (by omega), Int.natAbs_neg, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_div₀, map_mul, sig_neg_one_pow, sig_zK_pow_odd, map_pow, sig_natCast_Qt]
  · simp
  · rw [if_neg (by omega), if_pos (by omega), Int.natAbs_neg, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_div₀, map_mul, sig_neg_one_pow, sig_inv_zK_pow_odd, map_pow, sig_natCast_Qt]

/-- Reflection of a sum over the poles. -/
lemma sig_sum_reflect (f : ℕ → (Qt n)) (s : (Qt n))
    (hf : ∀ m ≤ h, sig (f m) = s * f (h - m)) :
    sig (∑ m ∈ Finset.range (h + 1), f m) = s * ∑ m ∈ Finset.range (h + 1), f m := by
  rw [map_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun m hm => hf m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)))]
  simpa using Finset.sum_range_reflect (fun m => s * f m) (h + 1)

lemma neg_one_pow_mul_self_Qt (e : ℕ) : ((-1 : (Qt n)) ^ e) * (-1) ^ e = 1 := by
  rw [← mul_pow]; simp

/-! ### Lemma R -/

/-- **Lemma R** for `B`: `σ B(t^e) = (−1)^e B(t^e)`. -/
theorem sig_Bfun (hh : Even h) (e : ℕ) : sig (Bfun n h (X ^ e)) = (-1) ^ e * Bfun n h (X ^ e) := by
  unfold Bfun
  rw [map_neg, sig_sum_reflect (s := (-1) ^ e), mul_neg]
  intro m hm
  rw [map_mul, map_mul, sig_ratCast, sig_ratCast, sig_zK_zpow, cPole_reflect hh e hm,
    poleZ_reflect hh hm, sgnPole_neg (even_poleZ h m)]
  push_cast
  simp only [← mul_assoc, neg_one_pow_mul_self_Qt, one_mul]

/-- **Lemma R** for `A`: `σ A(t^e) = (−1)^e A(t^e)`. -/
theorem sig_Afun (hh : Even h) (e : ℕ) : sig (Afun n h (X ^ e)) = (-1) ^ e * Afun n h (X ^ e) := by
  unfold Afun
  rw [map_add, mul_add]
  congr 1
  · rw [sig_muPoly, divD_comp_neg hh, ← smul_eq_C_mul, muPoly_smul, pow_succ]
    rw [Algebra.smul_def]
    simp
  · rw [sig_sum_reflect (s := (-1) ^ e)]
    intro m hm
    rw [map_mul, map_mul, map_mul, sig_ratCast, sig_ratCast, sig_zK_zpow, sig_Psum,
      cPole_reflect hh e hm, poleZ_reflect hh hm, sgnPole_neg (even_poleZ h m)]
    push_cast
    simp only [← mul_assoc, neg_one_pow_mul_self_Qt, one_mul]

lemma im_eq_zero_of_sig {e : (Qt n)} {k : ℕ} (he : sig e = (-1) ^ k * e) (hk : Even k) : e.im = 0 := by
  rw [hk.neg_one_pow, one_mul] at he
  have := congrArg QuadraticAlgebra.im he
  simp at this
  linarith

lemma re_eq_zero_of_sig {e : (Qt n)} {k : ℕ} (he : sig e = (-1) ^ k * e) (hk : Odd k) : e.re = 0 := by
  rw [hk.neg_one_pow, neg_one_mul] at he
  have := congrArg QuadraticAlgebra.re he
  simp at this
  linarith

/-! ### Corollary R -/

/-- The diagonal scaling `w_i = √d^{[i odd]}`. -/
noncomputable def wSc (n : ℕ) [Fact (3 ≤ n)] (i : ℕ) : (Qt n) := if Even i then 1 else (sqrtd n)

/-- Its inverse `w_i⁻¹`. -/
noncomputable def wScInv (n : ℕ) [Fact (3 ≤ n)] (i : ℕ) : (Qt n) :=
  if Even i then 1 else (1 / dT n : ℚ) • (sqrtd n)

lemma wSc_mul_inv (i : ℕ) : wSc n i * wScInv n i = 1 := by
  unfold wSc wScInv
  split_ifs
  · simp
  · rw [mul_smul_comm, sqrtd_mul_self, Algebra.smul_def, eq_ratCast, ← Rat.cast_mul, one_div,
      inv_mul_cancel₀ dT_ne_zero, Rat.cast_one]

lemma ratCast_Qt (r : ℚ) : ((r : ℚ) : (Qt n)) = ⟨r, 0⟩ := rfl

/-- The entry identity behind Corollary R: `Ẽ_{ij} w_j = w_i E_{i+j}`. -/
lemma tildeCoord_mul (i j : ℕ) {e : (Qt n)} (he : sig e = (-1) ^ (i + j) * e) :
    ((tildeCoord i j e : ℚ) : (Qt n)) * wSc n j = wSc n i * e := by
  unfold tildeCoord wSc
  rw [ratCast_Qt]
  rcases Nat.even_or_odd i with hi | hi <;> rcases Nat.even_or_odd j with hj | hj
  · have hij : Even (i + j) := hi.add hj
    have him := im_eq_zero_of_sig he hij
    rw [if_pos hij, if_pos hi, if_pos hj]
    ext <;> simp [him]
  · have hij : Odd (i + j) := hi.add_odd hj
    have hre := re_eq_zero_of_sig he hij
    rw [if_neg (Nat.not_even_iff_odd.mpr hij), if_neg (Nat.not_even_iff_odd.mpr hj), if_pos hi,
      if_neg (Nat.not_even_iff_odd.mpr hj)]
    ext <;> simp [sqrtd, hre, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  · have hij : Odd (i + j) := hi.add_even hj
    have hre := re_eq_zero_of_sig he hij
    rw [if_neg (Nat.not_even_iff_odd.mpr hij), if_pos hj, if_neg (Nat.not_even_iff_odd.mpr hi), if_pos hj]
    ext <;> simp [sqrtd, hre, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  · have hij : Even (i + j) := hi.add_odd hj
    have him := im_eq_zero_of_sig he hij
    rw [if_pos hij, if_neg (Nat.not_even_iff_odd.mpr hi), if_neg (Nat.not_even_iff_odd.mpr hj)]
    ext <;> simp [sqrtd, him]

/-- **Corollary R.** For any ring hom `ι : ℚ(√d) → L` and `x ∈ L`:
`Δ_h(x) = det(ι A(t^{i+j}) + x · ι B(t^{i+j}))`. -/
theorem eval₂_Delta (hh : Even h) {L : Type*} [CommRing L] (ι : (Qt n) →+* L) (x : L) :
    (Delta n h).eval₂ (ι.comp (algebraMap ℚ (Qt n))) x =
      (Matrix.of fun i j : Fin h => ι (Afun n h (X ^ ((i : ℕ) + j))) + x * ι (Bfun n h (X ^ ((i : ℕ) + j)))).det := by
  set f := ι.comp (algebraMap ℚ (Qt n)) with hf
  have hf' : ∀ r : ℚ, f r = ι (r : (Qt n)) := fun r => by rw [hf, RingHom.comp_apply, eq_ratCast]
  unfold Delta
  rw [← coe_eval₂RingHom, RingHom.map_det]
  set Mt : Matrix (Fin h) (Fin h) L := (eval₂RingHom f x).mapMatrix ((X : ℚ[X]) • (Btil n h).map C + (Atil n h).map C)
  set M : Matrix (Fin h) (Fin h) L :=
    Matrix.of fun i j : Fin h => ι (Afun n h (X ^ ((i : ℕ) + j))) + x * ι (Bfun n h (X ^ ((i : ℕ) + j))) with hM
  set W : Matrix (Fin h) (Fin h) L := Matrix.diagonal (fun i => ι (wSc n i))
  set W' : Matrix (Fin h) (Fin h) L := Matrix.diagonal (fun i => ι (wScInv n i))
  have hWW' : W.det * W'.det = 1 := by
    rw [← det_mul, diagonal_mul_diagonal]
    simp only [← map_mul, wSc_mul_inv, map_one]
    rw [diagonal_one, det_one]
  have hcomm : Mt * W = W * M := by
    ext i j
    rw [mul_diagonal, diagonal_mul]
    simp only [Mt, M, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.of_apply, smul_eq_mul, coe_eval₂RingHom, eval₂_add, eval₂_mul, eval₂_X, eval₂_C, hf', Atil, Btil]
    have hA := congrArg ι (tildeCoord_mul i j (sig_Afun hh ((i : ℕ) + j)))
    have hB := congrArg ι (tildeCoord_mul i j (sig_Bfun hh ((i : ℕ) + j)))
    simp only [map_mul] at hA hB
    linear_combination hA + x * hB
  have h1 := congrArg Matrix.det hcomm
  rw [det_mul, det_mul] at h1
  calc Mt.det = Mt.det * (W.det * W'.det) := by rw [hWW', mul_one]
    _ = (W.det * M.det) * W'.det := by rw [← h1]; ring
    _ = M.det := by rw [mul_comm W.det, mul_assoc, hWW', mul_one]

/-- Corollary R over `ℝ`: `Δ_h(x) = det(emb A + x · emb B)`. -/
theorem aeval_Delta (hh : Even h) (x : ℝ) :
    aeval x (Delta n h) =
      (Matrix.of fun i j : Fin h => emb (Afun n h (X ^ ((i : ℕ) + j))) + x * emb (Bfun n h (X ^ ((i : ℕ) + j)))).det := by
  rw [aeval_def, ← emb_comp_algebraMap (n := n)]
  exact eval₂_Delta hh emb x

/-- Corollary R over `ℚ(√d)[X]`: `Δ_h = det(A(t^{i+j}) + X B(t^{i+j}))` (so the `K`-valued Hankel determinant is
rational). -/
theorem Delta_map (hh : Even h) :
    (Delta n h).map (algebraMap ℚ (Qt n)) =
      (Matrix.of fun i j : Fin h => C (Afun n h (X ^ ((i : ℕ) + j))) + X * C (Bfun n h (X ^ ((i : ℕ) + j)))).det :=
  eval₂_Delta hh C X

end Ti
end Chi2U
