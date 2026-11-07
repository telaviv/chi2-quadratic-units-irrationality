/-
# Theorem B′, step 1: the node expansion (PROOF_U §5.2 steps 1–3)

Port of `lean_chi2/Chi2Irrational/Analytic/Nodes.lean` to the machine of PROOF_U. With `φ(u) = 1/D(u)` and odd nodes
`τ = 2t + 1`:
* `HT h T`: the truncation `Σ_{t<T} z^τ [(i+j) τ^{i+j−1} φ(τ) + τ^{i+j} φ′(τ)]` of `Λ(u^{i+j})` (Lemma 1′);
* `HT_rankOne`: `HT T` is `Σ_k c_k x_k y_kᵀ` over slot triples `k = (t, ν)`, `ν ∈ {(val,val), (der,val), (val,der)}`;
* `abs_cN_le`: `|c_k| ≤ b(τ) = z^τ |φ(τ)| (2 + log(2h+1))` (`abs_deriv_invD_le'`; here `D(τ)` may be negative, so
  absolute values replace lean_chi2's positivity of `φ`);
* `abs_det_HT_le`: `|det HT T| ≤ (h!)⁻¹ K² Σ_f [x-slots of f distinct] ∏_i b(τ_i) ∏_{i<j} pf(τ_i, τ_j)²`,
  `K = h^h (1 + 2/h)^{h²}` (Andreief + `abs_det_slot_le`, both generic).
-/
import Chi2U.Machine
import Chi2U.Analytic.Andreief
import Chi2U.Analytic.SlotDet
import Chi2U.Analytic.PoleBoundU

namespace Chi2U

open Polynomial Finset Filter Topology Matrix

/-- `φ(u) = 1/D(u)`. -/
noncomputable def phiU (h : ℕ) (u : ℝ) : ℝ := (aeval u (Dpoly h))⁻¹

lemma hasDerivAt_phiU {h : ℕ} (hh : Even h) (s : ℕ) :
    HasDerivAt (phiU h) (deriv (phiU h) ((2 * s + 1 : ℕ) : ℝ)) ((2 * s + 1 : ℕ) : ℝ) := by
  obtain ⟨J, rfl⟩ := hh
  exact (hasDerivAt_invD J s).differentiableAt.hasDerivAt

/-- The derivative of `u ↦ u^n/D(u)` at a node. -/
lemma deriv_pow_phi {h : ℕ} (hh : Even h) (n s : ℕ) :
    deriv (fun u : ℝ => aeval u ((X : ℚ[X]) ^ n) / aeval u (Dpoly h)) ((2 * s + 1 : ℕ) : ℝ) =
      (n : ℝ) * ((2 * s + 1 : ℕ) : ℝ) ^ (n - 1) * phiU h ((2 * s + 1 : ℕ) : ℝ) +
        ((2 * s + 1 : ℕ) : ℝ) ^ n * deriv (phiU h) ((2 * s + 1 : ℕ) : ℝ) := by
  have heq : (fun u : ℝ => aeval u ((X : ℚ[X]) ^ n) / aeval u (Dpoly h)) = fun u => u ^ n * phiU h u := by
    ext u; simp only [map_pow, aeval_X, phiU]; rw [div_eq_mul_inv]
  rw [heq]
  exact ((hasDerivAt_pow n _).mul (hasDerivAt_phiU hh s)).deriv

/-! ### The truncations -/

/-- The node term of `Λ(u^n)` at `τ = 2t + 1`. -/
noncomputable def nodeTerm (h n t : ℕ) : ℝ :=
  zU ^ (2 * t + 1) * ((n : ℝ) * ((2 * t + 1 : ℕ) : ℝ) ^ (n - 1) * phiU h ((2 * t + 1 : ℕ) : ℝ) +
    ((2 * t + 1 : ℕ) : ℝ) ^ n * deriv (phiU h) ((2 * t + 1 : ℕ) : ℝ))

/-- The truncated matrix. -/
noncomputable def HT (h T : ℕ) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j => ∑ t ∈ range T, nodeTerm h ((i : ℕ) + j) t

/-! ### Rank-one form -/

/-- The node `τ = 2t + 1` of a triple `(t, ν)`. -/
def tnode {T : ℕ} (k : Fin T × Fin 3) : ℕ := 2 * (k.1 : ℕ) + 1

/-- The x-slot of a triple: derivative iff `ν = 1`. -/
def xslot {T : ℕ} (k : Fin T × Fin 3) : ℕ × Bool := (tnode k, decide ((k.2 : ℕ) = 1))

/-- The y-slot of a triple: derivative iff `ν = 2`. -/
def yslot {T : ℕ} (k : Fin T × Fin 3) : ℕ × Bool := (tnode k, decide ((k.2 : ℕ) = 2))

/-- The coefficient of a triple. -/
noncomputable def cN (h : ℕ) {T : ℕ} (k : Fin T × Fin 3) : ℝ :=
  zU ^ tnode k * (if (k.2 : ℕ) = 0 then deriv (phiU h) (tnode k) else phiU h (tnode k))

lemma pow_deriv_split (s : ℝ) (i j : ℕ) :
    ((i : ℝ) + j) * s ^ (i + j - 1) =
      ((i : ℝ) * s ^ (i - 1)) * s ^ j + s ^ i * ((j : ℝ) * s ^ (j - 1)) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  have e1 : s ^ (i + j - 1) = s ^ (i - 1) * s ^ j := by rw [← pow_add]; congr 1; omega
  have e2 : s ^ (i + j - 1) = s ^ i * s ^ (j - 1) := by rw [← pow_add]; congr 1; omega
  rw [add_mul, show (i : ℝ) * s ^ (i + j - 1) = i * (s ^ (i - 1) * s ^ j) by rw [e1],
    show (j : ℝ) * s ^ (i + j - 1) = j * (s ^ i * s ^ (j - 1)) by rw [e2]]
  ring

lemma HT_rankOne (h T : ℕ) :
    HT h T = Matrix.of fun i j => ∑ k : Fin T × Fin 3,
      cN h k * slotRow h (xslot k) i * slotRow h (yslot k) j := by
  ext i j
  simp only [HT, Matrix.of_apply]
  rw [Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range (fun t => nodeTerm h ((i : ℕ) + j) t) T]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Fin.sum_univ_three]
  simp only [cN, xslot, yslot, tnode, slotRow, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  simp only [show (0 : ℕ) ≠ 1 by norm_num, show (0 : ℕ) ≠ 2 by norm_num, show (1 : ℕ) ≠ 2 by norm_num,
    show (1 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num,
    decide_false, decide_true, ite_true, ite_false, Bool.false_eq_true]
  unfold nodeTerm
  push_cast
  rw [pow_deriv_split]
  ring

/-! ### The bound on the truncated determinant -/

/-- The slot-minor constant `h^h (1 + 2/h)^{h²}`. -/
noncomputable def Kslot (h : ℕ) : ℝ := (h : ℝ) ^ h * (1 + 2 / (h : ℝ)) ^ (h ^ 2)

/-- The node weight `b(τ) = z^τ |φ(τ)| (2 + log(2h+1))`. -/
noncomputable def bN (h τ : ℕ) : ℝ := zU ^ τ * |phiU h τ| * (2 + Real.log (2 * (h : ℝ) + 1))

lemma two_add_log_ge_one (h : ℕ) : 1 ≤ 2 + Real.log (2 * (h : ℝ) + 1) := by
  have : 0 ≤ Real.log (2 * (h : ℝ) + 1) := Real.log_nonneg (by have := (Nat.cast_nonneg h : (0 : ℝ) ≤ h); linarith)
  linarith

lemma abs_cN_le {h T : ℕ} (hh : Even h) (k : Fin T × Fin 3) : |cN h k| ≤ bN h (tnode k) := by
  have hz := zU_pos
  have hA := two_add_log_ge_one h
  unfold cN bN
  rw [abs_mul, abs_of_pos (pow_pos hz _), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (pow_pos hz _).le
  split_ifs
  · obtain ⟨J, rfl⟩ := hh
    exact abs_deriv_invD_le' J (k.1 : ℕ)
  · have := abs_nonneg (phiU h (tnode k))
    nlinarith

lemma bN_pos {h : ℕ} (hh : Even h) (s : ℕ) : 0 < bN h (2 * s + 1) := by
  have hz := zU_pos
  have hA := two_add_log_ge_one h
  have hphi : 0 < |phiU h ((2 * s + 1 : ℕ) : ℝ)| := by
    obtain ⟨J, rfl⟩ := hh
    exact abs_pos.mpr (inv_ne_zero (aeval_Dpoly_ne J s))
  unfold bN
  have : (0 : ℝ) < 2 + Real.log (2 * (h : ℝ) + 1) := by linarith
  positivity

lemma bN_tnode_pos {h T : ℕ} (hh : Even h) (k : Fin T × Fin 3) : 0 < bN h (tnode k) := bN_pos hh _

/-- **The truncated determinant, slot form.** -/
theorem abs_det_HT_le {h T : ℕ} (hh : Even h) (h2 : 2 ≤ h) :
    |(HT h T).det| ≤ ((h.factorial : ℝ))⁻¹ * Kslot h ^ 2 *
      ∑ f : Fin h → Fin T × Fin 3, (if Function.Injective (fun i => xslot (f i)) then
        (∏ i, bN h (tnode (f i))) *
          ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j)) ^ 2 else 0) := by
  have hfac : (0 : ℝ) < h.factorial := by exact_mod_cast Nat.factorial_pos h
  have hA := factorial_smul_det_sum_rankOne (R := ℝ) (cN h (T := T)) (fun k => slotRow h (xslot k))
    (fun k => slotRow h (yslot k))
  rw [← HT_rankOne, Fintype.card_fin, nsmul_eq_mul] at hA
  have hdet : (HT h T).det = ((h.factorial : ℝ))⁻¹ * ∑ f : Fin h → Fin T × Fin 3,
      (∏ i, cN h (f i)) * (Matrix.of fun i j => slotRow h (xslot (f i)) j).det *
        (Matrix.of fun i j => slotRow h (yslot (f i)) j).det := by
    rw [← hA]; field_simp
  rw [hdet, abs_mul, abs_of_pos (inv_pos.mpr hfac), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (inv_pos.mpr hfac).le
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun f _ => ?_))
  split_ifs with hinj
  · rw [abs_mul, abs_mul, Finset.abs_prod]
    have hX := abs_det_slot_le h2 (fun i => xslot (f i))
    have hY := abs_det_slot_le h2 (fun i => yslot (f i))
    simp only [xslot, yslot] at hX hY
    have hc : ∏ i, |cN h (f i)| ≤ ∏ i, bN h (tnode (f i)) :=
      Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => abs_cN_le hh (f i))
    have hP : 0 ≤ ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j)) :=
      Finset.prod_nonneg (fun i _ => Finset.prod_nonneg (fun j _ => pairFactor_nonneg _ _))
    have hK : 0 ≤ Kslot h := by unfold Kslot; positivity
    have hb : 0 ≤ ∏ i, bN h (tnode (f i)) :=
      Finset.prod_nonneg (fun i _ => (bN_tnode_pos hh (f i)).le)
    calc (∏ i, |cN h (f i)|) * |(Matrix.of fun i j => slotRow h (xslot (f i)) j).det| *
          |(Matrix.of fun i j => slotRow h (yslot (f i)) j).det|
        ≤ (∏ i, bN h (tnode (f i))) * (Kslot h * ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j))) *
            (Kslot h * ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j))) := by
          gcongr
          · unfold Kslot; exact hX
          · unfold Kslot; exact hY
      _ = Kslot h ^ 2 * ((∏ i, bN h (tnode (f i))) *
            ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j)) ^ 2) := by
          simp_rw [Finset.prod_pow]; ring
  · -- two equal x-slots: the x-minor vanishes
    rw [Function.Injective] at hinj
    push Not at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    have h0 : (Matrix.of fun i j => slotRow h (xslot (f i)) j).det = 0 :=
      Matrix.det_zero_of_row_eq hne (by ext k; simp [hij])
    rw [h0]; simp

end Chi2U
