/-
# Lemma R and Corollary R: the reflection puts `Δ_h` in `ℚ[X]` (PROOF_U §1)

For `h` even (`K = h + 1` odd, poles `x_m` symmetric under `m ↦ h − m`):
* `D(−t) = −D(t)` (`Dpoly_comp_neg`), so `(t^n div D)(−t) = (−1)^{n+1}(t^n div D)` (`divD_comp_neg`);
* `x_{h−m} = −x_m`, `D′(x_{h−m}) = D′(x_m)`, `σ(z^x) = z^{−x}` (`x` even), `σ P(x) = P(−x)`;
* with the moment parity `σ μ(R) = −μ(R(−t))` (`Moments.sig_muPoly`) this gives **Lemma R**:
  `σ A(t^n) = (−1)^n A(t^n)` and `σ B(t^n) = (−1)^n B(t^n)` (`sig_Afun`, `sig_Bfun`):
  even-`n` entries are rational, odd-`n` entries are rational multiples of `√d` (only `σz = −1/z` is used).
* **Corollary R** (`eval₂_Delta`): for every ring hom `ι : ℚ(√d) → L` and `x ∈ L`,
  `Δ_h(x) = det(ι A(t^{i+j}) + x ι B(t^{i+j}))`. Proof: `Ã + xB̃` (mapped) times `W = diag(w_j)`,
  `w_j = √d^{[j odd]}`, equals `W` times the Hankel matrix, and `det W` is a unit.
  Special cases: `aeval_Delta` (`ι = emb`, real `x`) and `Delta_map` (`ι = C`, `x = X`).
-/
import Chi2U.Machine

namespace Chi2U

variable {mz : ℕ} [Fact (1 ≤ mz)]

open Polynomial Matrix

variable {h : ℕ}

/-! ### Symmetry of the poles -/

lemma poleZ_reflect (hh : Even h) {m : ℕ} (hm : m ≤ h) : poleZ h (h - m) = -poleZ h m := by
  obtain ⟨j, rfl⟩ := hh
  unfold poleZ
  have : (j + j) / 2 = j := by omega
  rw [this]
  push_cast [Nat.cast_sub hm]
  ring

lemma even_poleZ (h m : ℕ) : Even (poleZ h m) := ⟨(m : ℤ) - ((h / 2 : ℕ) : ℤ), by unfold poleZ; ring⟩

lemma Dpoly_monic (h : ℕ) : (Dpoly h).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

lemma Dpoly_comp_neg (hh : Even h) : (Dpoly h).comp (-X) = -Dpoly h := by
  unfold Dpoly
  rw [prod_comp]
  have h1 : ∀ m ∈ Finset.range (h + 1), (X - C ((poleZ h m : ℤ) : ℚ)).comp (-X) =
      (-1) * (X - C ((poleZ h (h - m) : ℤ) : ℚ)) := by
    intro m hm
    rw [poleZ_reflect hh (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))]
    simp only [sub_comp, X_comp, C_comp]
    push_cast
    simp only [C_neg]
    ring
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    ← Finset.prod_range_reflect (fun m => X - C ((poleZ h m : ℤ) : ℚ)) (h + 1)]
  simp only [Nat.add_sub_cancel]
  rw [pow_succ, (hh.neg_one_pow), one_mul, neg_one_mul]

/-- Division by an odd monic polynomial commutes with `t ↦ −t` up to sign. -/
lemma divByMonic_comp_neg {D : ℚ[X]} (hmon : D.Monic) (hD : D.comp (-X) = -D) (n : ℕ) :
    (X ^ n /ₘ D).comp (-X) = C ((-1) ^ (n + 1)) * (X ^ n /ₘ D) := by
  have hdiv : X ^ n %ₘ D + D * (X ^ n /ₘ D) = X ^ n := modByMonic_add_div (X ^ n) D
  have hcomp : (X ^ n %ₘ D).comp (-X) + -D * (X ^ n /ₘ D).comp (-X) = C ((-1) ^ n) * X ^ n := by
    have := congrArg (fun p => p.comp (-X)) hdiv
    simp only [add_comp, mul_comp, X_pow_comp, hD] at this
    rw [this, neg_pow, C_pow, C_neg, C_1]
  have h1 : C ((-1 : ℚ) ^ n) * C ((-1) ^ n) = 1 := by rw [← C_mul, ← mul_pow]; simp
  have key : C ((-1) ^ n) * (X ^ n %ₘ D).comp (-X) + D * (C ((-1) ^ (n + 1)) * (X ^ n /ₘ D).comp (-X)) =
      X ^ n := by
    calc C ((-1) ^ n) * (X ^ n %ₘ D).comp (-X) + D * (C ((-1) ^ (n + 1)) * (X ^ n /ₘ D).comp (-X))
        = C ((-1) ^ n) * ((X ^ n %ₘ D).comp (-X) + -D * (X ^ n /ₘ D).comp (-X)) := by
          rw [pow_succ, C_mul, C_neg, C_1]; ring
      _ = C ((-1) ^ n) * (C ((-1) ^ n) * X ^ n) := by rw [hcomp]
      _ = X ^ n := by rw [← mul_assoc, h1, one_mul]
  have hdeg : degree (C ((-1 : ℚ) ^ n) * (X ^ n %ₘ D).comp (-X)) < degree D := by
    rw [degree_C_mul (pow_ne_zero _ (by norm_num)), degree_comp_neg_X]
    exact degree_modByMonic_lt _ hmon
  have huniq : X ^ n /ₘ D = C ((-1) ^ (n + 1)) * (X ^ n /ₘ D).comp (-X) :=
    (div_modByMonic_unique (C ((-1) ^ (n + 1)) * (X ^ n /ₘ D).comp (-X))
      (C ((-1) ^ n) * (X ^ n %ₘ D).comp (-X)) hmon ⟨key, hdeg⟩).1
  have h2 : C ((-1 : ℚ) ^ (n + 1)) * C ((-1) ^ (n + 1)) = 1 := by rw [← C_mul, ← mul_pow]; simp
  calc (X ^ n /ₘ D).comp (-X) = C ((-1) ^ (n + 1)) * (C ((-1) ^ (n + 1)) * (X ^ n /ₘ D).comp (-X)) := by
        rw [← mul_assoc, h2, one_mul]
    _ = C ((-1) ^ (n + 1)) * (X ^ n /ₘ D) := by rw [← huniq]

/-- `(t^n div D)(−t) = (−1)^{n+1} (t^n div D)`. -/
lemma divD_comp_neg (hh : Even h) (n : ℕ) :
    (X ^ n /ₘ Dpoly h).comp (-X) = C ((-1) ^ (n + 1)) * (X ^ n /ₘ Dpoly h) :=
  divByMonic_comp_neg (Dpoly_monic h) (Dpoly_comp_neg hh) n

/-- `D′(x_{h−m}) = D′(x_m)`. -/
lemma dPrime_reflect (hh : Even h) {m : ℕ} (hm : m ≤ h) : dPrime h (h - m) = dPrime h m := by
  unfold dPrime
  rw [← Finset.prod_range_reflect _ (h + 1)]
  simp only [Nat.add_sub_cancel]
  have h1 : ∀ l ∈ Finset.range (h + 1),
      (if h - l = h - m then (1 : ℚ) else ((poleZ h (h - m) : ℚ) - poleZ h (h - l))) =
        (if l = m then 1 else -1) * (if l = m then 1 else ((poleZ h m : ℚ) - poleZ h l)) := by
    intro l hl
    have hl' : l ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    by_cases hlm : l = m
    · subst hlm; simp
    · have : h - l ≠ h - m := by omega
      rw [if_neg this, if_neg hlm, if_neg hlm, poleZ_reflect hh hm, poleZ_reflect hh hl']
      push_cast; ring
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib]
  have h2 : ∏ l ∈ Finset.range (h + 1), (if l = m then (1 : ℚ) else -1) = 1 := by
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, Finset.filter_ne',
      Finset.card_erase_of_mem (Finset.mem_range.mpr (Nat.lt_succ_of_le hm)), Finset.card_range,
      Nat.succ_sub_one, hh.neg_one_pow]
  rw [h2, one_mul]

lemma cPole_reflect (hh : Even h) (n : ℕ) {m : ℕ} (hm : m ≤ h) :
    cPole h (X ^ n) (h - m) = (-1) ^ n * cPole h (X ^ n) m := by
  unfold cPole
  rw [dPrime_reflect hh hm, poleZ_reflect hh hm]
  simp only [eval_pow, eval_X]
  push_cast
  rw [neg_pow]; ring

/-! ### The conjugation on the pole data -/

lemma sig_zK_zpow_even {x : ℤ} (hx : Even x) : sig ((zK mz) ^ x) = (zK mz) ^ (-x) := by
  rw [map_zpow₀, sig_zK, hx.neg_zpow, _root_.inv_zpow']

lemma sig_zK_pow_odd (k : ℕ) : sig ((zK mz) ^ (2 * k + 1)) = -((zK mz) ^ (2 * k + 1))⁻¹ := by
  rw [map_pow, sig_zK, Odd.neg_pow ⟨k, rfl⟩, inv_pow]

lemma sig_inv_zK_pow_odd (k : ℕ) : sig (((zK mz) ^ (2 * k + 1))⁻¹) = -(zK mz) ^ (2 * k + 1) := by
  rw [map_inv₀, sig_zK_pow_odd, inv_neg, inv_inv]

lemma sig_natCast_Q5 (n : ℕ) : sig (n : (Qd mz)) = n := map_natCast sig n

/-- `σ P(x) = P(−x)`. -/
lemma sig_Psum (x : ℤ) : sig (Psum mz x) = Psum mz (-x) := by
  unfold Psum
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [if_pos hx.le, if_neg (by omega), Int.natAbs_neg, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_div₀, sig_zK_pow_odd, map_pow, sig_natCast_Q5, neg_div]
  · simp
  · rw [if_neg (by omega), if_pos (by omega), Int.natAbs_neg, map_neg, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_div₀, sig_inv_zK_pow_odd, map_pow, sig_natCast_Q5, neg_div, neg_neg]

/-- Reflection of a sum over the poles. -/
lemma sig_sum_reflect (f : ℕ → (Qd mz)) (s : (Qd mz))
    (hf : ∀ m ≤ h, sig (f m) = s * f (h - m)) :
    sig (∑ m ∈ Finset.range (h + 1), f m) = s * ∑ m ∈ Finset.range (h + 1), f m := by
  rw [map_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun m hm => hf m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)))]
  simpa using Finset.sum_range_reflect (fun m => s * f m) (h + 1)

lemma neg_one_pow_mul_self_Q5 (n : ℕ) : ((-1 : (Qd mz)) ^ n) * (-1) ^ n = 1 := by
  rw [← mul_pow]; simp

/-! ### Lemma R -/

/-- **Lemma R** for `B`: `σ B(t^n) = (−1)^n B(t^n)`. -/
theorem sig_Bfun (hh : Even h) (n : ℕ) : sig (Bfun mz h (X ^ n)) = (-1) ^ n * Bfun mz h (X ^ n) := by
  unfold Bfun
  rw [map_neg, sig_sum_reflect (s := (-1) ^ n), mul_neg]
  intro m hm
  rw [map_mul, sig_ratCast, sig_zK_zpow_even (even_poleZ h m), cPole_reflect hh n hm,
    poleZ_reflect hh hm]
  push_cast
  simp only [← mul_assoc, neg_one_pow_mul_self_Q5, one_mul]

/-- **Lemma R** for `A`: `σ A(t^n) = (−1)^n A(t^n)`. -/
theorem sig_Afun (hh : Even h) (n : ℕ) : sig (Afun mz h (X ^ n)) = (-1) ^ n * Afun mz h (X ^ n) := by
  unfold Afun
  rw [map_add, mul_add]
  congr 1
  · rw [sig_muPoly, divD_comp_neg hh, ← smul_eq_C_mul, muPoly_smul, pow_succ]
    rw [Algebra.smul_def]
    simp
  · rw [sig_sum_reflect (s := (-1) ^ n)]
    intro m hm
    rw [map_mul, map_mul, sig_ratCast, sig_zK_zpow_even (even_poleZ h m), sig_Psum,
      cPole_reflect hh n hm, poleZ_reflect hh hm]
    push_cast
    simp only [← mul_assoc, neg_one_pow_mul_self_Q5, one_mul]

lemma im_eq_zero_of_sig {e : (Qd mz)} {n : ℕ} (he : sig e = (-1) ^ n * e) (hn : Even n) : e.im = 0 := by
  rw [hn.neg_one_pow, one_mul] at he
  have := congrArg QuadraticAlgebra.im he
  simp at this
  linarith

lemma re_eq_zero_of_sig {e : (Qd mz)} {n : ℕ} (he : sig e = (-1) ^ n * e) (hn : Odd n) : e.re = 0 := by
  rw [hn.neg_one_pow, neg_one_mul] at he
  have := congrArg QuadraticAlgebra.re he
  simp at this
  linarith

/-! ### Corollary R -/

/-- The diagonal scaling `w_i = √5^{[i odd]}`. -/
noncomputable def wSc (mz : ℕ) [Fact (1 ≤ mz)] (i : ℕ) : (Qd mz) := if Even i then 1 else (sqrtd mz)

/-- Its inverse `w_i⁻¹`. -/
noncomputable def wScInv (mz : ℕ) [Fact (1 ≤ mz)] (i : ℕ) : (Qd mz) := if Even i then 1 else (1 / dQ mz : ℚ) • (sqrtd mz)

lemma wSc_mul_inv (i : ℕ) : wSc mz i * wScInv mz i = 1 := by
  unfold wSc wScInv
  split_ifs
  · simp
  · rw [mul_smul_comm, sqrtd_mul_self, Algebra.smul_def, eq_ratCast, ← Rat.cast_mul, one_div,
      inv_mul_cancel₀ dQ_ne_zero, Rat.cast_one]

lemma ratCast_Q5 (r : ℚ) : ((r : ℚ) : (Qd mz)) = ⟨r, 0⟩ := rfl

/-- The entry identity behind Corollary R: `Ẽ_{ij} w_j = w_i E_{i+j}`. -/
lemma tildeCoord_mul (i j : ℕ) {e : (Qd mz)} (he : sig e = (-1) ^ (i + j) * e) :
    ((tildeCoord i j e : ℚ) : (Qd mz)) * wSc mz j = wSc mz i * e := by
  unfold tildeCoord wSc
  rw [ratCast_Q5]
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
theorem eval₂_Delta (hh : Even h) {L : Type*} [CommRing L] (ι : (Qd mz) →+* L) (x : L) :
    (Delta mz h).eval₂ (ι.comp (algebraMap ℚ (Qd mz))) x =
      (Matrix.of fun i j : Fin h => ι (Afun mz h (X ^ ((i : ℕ) + j))) + x * ι (Bfun mz h (X ^ ((i : ℕ) + j)))).det := by
  set f := ι.comp (algebraMap ℚ (Qd mz)) with hf
  have hf' : ∀ r : ℚ, f r = ι (r : (Qd mz)) := fun r => by rw [hf, RingHom.comp_apply, eq_ratCast]
  unfold Delta
  rw [← coe_eval₂RingHom, RingHom.map_det]
  set Mt : Matrix (Fin h) (Fin h) L := (eval₂RingHom f x).mapMatrix ((X : ℚ[X]) • (Btil mz h).map C + (Atil mz h).map C)
  set M : Matrix (Fin h) (Fin h) L :=
    Matrix.of fun i j : Fin h => ι (Afun mz h (X ^ ((i : ℕ) + j))) + x * ι (Bfun mz h (X ^ ((i : ℕ) + j))) with hM
  set W : Matrix (Fin h) (Fin h) L := Matrix.diagonal (fun i => ι (wSc mz i))
  set W' : Matrix (Fin h) (Fin h) L := Matrix.diagonal (fun i => ι (wScInv mz i))
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
    aeval x (Delta mz h) =
      (Matrix.of fun i j : Fin h => emb (Afun mz h (X ^ ((i : ℕ) + j))) + x * emb (Bfun mz h (X ^ ((i : ℕ) + j)))).det := by
  rw [aeval_def, ← emb_comp_algebraMap (mz := mz)]
  exact eval₂_Delta hh emb x

/-- Corollary R over `ℚ(√5)[X]`: `Δ_h = det(A(t^{i+j}) + X B(t^{i+j}))` (so the `K`-valued Hankel determinant is
rational). -/
theorem Delta_map (hh : Even h) :
    (Delta mz h).map (algebraMap ℚ (Qd mz)) =
      (Matrix.of fun i j : Fin h => C (Afun mz h (X ^ ((i : ℕ) + j))) + X * C (Bfun mz h (X ^ ((i : ℕ) + j)))).det :=
  eval₂_Delta hh C X

end Chi2U
