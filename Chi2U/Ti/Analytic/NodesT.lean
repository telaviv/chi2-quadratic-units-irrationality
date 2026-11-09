/-
# Theorem V_i, Theorem B′ at `z = zT n`: node expansion, truncations, weak duality (PROOF_TI2 §2, §5.1 row)

**Copy of the `az`-dependent parts of `Chi2U/Analytic/NodesU.lean`, `Chi2U/Analytic/TruncU.lean` and
`Chi2U/Analytic/DualU.lean`**, with the signed node weights `χ₄(τ) z^τ = (−1)^t z^{2t+1}` at `τ = 2t + 1`, `z = zT n`.
Lemma names are those of the χ₂ files. Every bound only sees `|(−1)^t z^τ| = z^τ`, so the node weight
`b(τ) = z^τ |φ(τ)| (2 + log(2h+1))` (`bN`) and everything downstream are the χ₂ ones with `zU az` replaced by `zT n`.

The `z`-free lemmas (`phiU`, `deriv_pow_phi`, `tnode`, `xslot`, `yslot`, `slotRow`, `Kslot`, `abs_det_slot_le`,
`pairFactor`, `sum_fiber`, `polya_Lk`, …) are reused from the χ₂ files (namespace `Chi2U`).

* `HT n h T`: the truncation `Σ_{t<T} (−1)^t z^τ [(i+j) τ^{i+j−1} φ(τ) + τ^{i+j} φ′(τ)]` of `Λ(u^{i+j})`;
* `abs_cN_le`: `|c_k| ≤ b(τ)` (the sign disappears under `|·|`);
* `abs_Delta_le_of`: a uniform bound on `|det HT T|` bounds `|Δ_h(T)|` (via `aeval_Ti2_Delta`, Ti's Lemma 1′);
* `abs_det_HT_le_dual`: the discrete weak-duality bound (DualU's proof verbatim).
-/
import Chi2U.Analytic.TheoremBU
import Chi2U.Ti.PoleExpansion

namespace Chi2U
namespace Ti

variable {n : ℕ} [Fact (3 ≤ n)]

open Polynomial Finset Filter Topology Matrix Real

/-! ### The truncations (NodesU) -/

/-- The node term of `Λ(u^e)` at `τ = 2t + 1`, with the sign `(−1)^t = χ₄(τ)`. -/
noncomputable def nodeTerm (n : ℕ) (h e t : ℕ) : ℝ :=
  (-1) ^ t * (zT n) ^ (2 * t + 1) * ((e : ℝ) * ((2 * t + 1 : ℕ) : ℝ) ^ (e - 1) * phiU h ((2 * t + 1 : ℕ) : ℝ) +
    ((2 * t + 1 : ℕ) : ℝ) ^ e * deriv (phiU h) ((2 * t + 1 : ℕ) : ℝ))

/-- The truncated matrix. -/
noncomputable def HT (n : ℕ) (h T : ℕ) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j => ∑ t ∈ range T, nodeTerm n h ((i : ℕ) + j) t

/-- The coefficient of a triple (signed weight `(−1)^t z^τ`). -/
noncomputable def cN (n : ℕ) (h : ℕ) {T : ℕ} (k : Fin T × Fin 3) : ℝ :=
  (-1) ^ (k.1 : ℕ) * (zT n) ^ tnode k * (if (k.2 : ℕ) = 0 then deriv (phiU h) (tnode k) else phiU h (tnode k))

omit [Fact (3 ≤ n)] in
lemma HT_rankOne (h T : ℕ) :
    HT n h T = Matrix.of fun i j => ∑ k : Fin T × Fin 3,
      cN n h k * slotRow h (xslot k) i * slotRow h (yslot k) j := by
  ext i j
  simp only [HT, Matrix.of_apply]
  rw [Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range (fun t => nodeTerm n h ((i : ℕ) + j) t) T]
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

/-- The node weight `b(τ) = z^τ |φ(τ)| (2 + log(2h+1))`, `z = zT n`. -/
noncomputable def bN (n : ℕ) (h τ : ℕ) : ℝ := (zT n) ^ τ * |phiU h τ| * (2 + Real.log (2 * (h : ℝ) + 1))

lemma abs_cN_le {h T : ℕ} (hh : Even h) (k : Fin T × Fin 3) : |cN n h k| ≤ bN n h (tnode k) := by
  have hz := zT_pos (n := n)
  have hA := two_add_log_ge_one h
  unfold cN bN
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos (pow_pos hz _), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (pow_pos hz _).le
  split_ifs
  · obtain ⟨J, rfl⟩ := hh
    exact abs_deriv_invD_le' J (k.1 : ℕ)
  · have := abs_nonneg (phiU h (tnode k))
    nlinarith

lemma bN_pos {h : ℕ} (hh : Even h) (s : ℕ) : 0 < bN n h (2 * s + 1) := by
  have hz := zT_pos (n := n)
  have hA := two_add_log_ge_one h
  have hphi : 0 < |phiU h ((2 * s + 1 : ℕ) : ℝ)| := by
    obtain ⟨J, rfl⟩ := hh
    exact abs_pos.mpr (inv_ne_zero (aeval_Dpoly_ne J s))
  unfold bN
  have : (0 : ℝ) < 2 + Real.log (2 * (h : ℝ) + 1) := by linarith
  positivity

lemma bN_tnode_pos {h T : ℕ} (hh : Even h) (k : Fin T × Fin 3) : 0 < bN n h (tnode k) := bN_pos hh _

/-- **The truncated determinant, slot form.** -/
theorem abs_det_HT_le {h T : ℕ} (hh : Even h) (h2 : 2 ≤ h) :
    |(HT n h T).det| ≤ ((h.factorial : ℝ))⁻¹ * Kslot h ^ 2 *
      ∑ f : Fin h → Fin T × Fin 3, (if Function.Injective (fun i => xslot (f i)) then
        (∏ i, bN n h (tnode (f i))) *
          ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j)) ^ 2 else 0) := by
  have hfac : (0 : ℝ) < h.factorial := by exact_mod_cast Nat.factorial_pos h
  have hA := factorial_smul_det_sum_rankOne (R := ℝ) (cN n h (T := T)) (fun k => slotRow h (xslot k))
    (fun k => slotRow h (yslot k))
  rw [← HT_rankOne, Fintype.card_fin, nsmul_eq_mul] at hA
  have hdet : (HT n h T).det = ((h.factorial : ℝ))⁻¹ * ∑ f : Fin h → Fin T × Fin 3,
      (∏ i, cN n h (f i)) * (Matrix.of fun i j => slotRow h (xslot (f i)) j).det *
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
    have hc : ∏ i, |cN n h (f i)| ≤ ∏ i, bN n h (tnode (f i)) :=
      Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => abs_cN_le hh (f i))
    have hP : 0 ≤ ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j)) :=
      Finset.prod_nonneg (fun i _ => Finset.prod_nonneg (fun j _ => pairFactor_nonneg _ _))
    have hK : 0 ≤ Kslot h := by unfold Kslot; positivity
    have hb : 0 ≤ ∏ i, bN n h (tnode (f i)) :=
      Finset.prod_nonneg (fun i _ => (bN_tnode_pos hh (f i)).le)
    calc (∏ i, |cN n h (f i)|) * |(Matrix.of fun i j => slotRow h (xslot (f i)) j).det| *
          |(Matrix.of fun i j => slotRow h (yslot (f i)) j).det|
        ≤ (∏ i, bN n h (tnode (f i))) * (Kslot h * ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j))) *
            (Kslot h * ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j))) := by
          gcongr
          · unfold Kslot; exact hX
          · unfold Kslot; exact hY
      _ = Kslot h ^ 2 * ((∏ i, bN n h (tnode (f i))) *
            ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j)) ^ 2) := by
          simp_rw [Finset.prod_pow]; ring
  · -- two equal x-slots: the x-minor vanishes
    rw [Function.Injective] at hinj
    push Not at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    have h0 : (Matrix.of fun i j => slotRow h (xslot (f i)) j).det = 0 :=
      Matrix.det_zero_of_row_eq hne (by ext k; simp [hij])
    rw [h0]; simp

/-! ### The truncations converge (TruncU) -/

/-- The Hankel matrix `Λ(u^{i+j})` (Ti's `LamR`). -/
noncomputable def LamMat (n : ℕ) [Fact (3 ≤ n)] (h : ℕ) : Matrix (Fin h) (Fin h) ℝ :=
  Matrix.of fun i j => LamR n h ((X : ℚ[X]) ^ ((i : ℕ) + j))

lemma LamMat_hasSum {h : ℕ} (hh : Even h) (i j : Fin h) :
    HasSum (fun t => nodeTerm n h ((i : ℕ) + j) t) (LamMat n h i j) := by
  simp only [LamMat, Matrix.of_apply]
  rw [LamR_eq hh]
  convert lemma1 hh ((X : ℚ[X]) ^ ((i : ℕ) + j)) using 1
  ext t
  rw [deriv_pow_phi hh]
  unfold nodeTerm
  ring

lemma tendsto_det_HT {h : ℕ} (hh : Even h) :
    Tendsto (fun T => (HT n h T).det) atTop (𝓝 (LamMat n h).det) := by
  have hmat : Tendsto (fun T => HT n h T) atTop (𝓝 (LamMat n h)) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => (LamMat_hasSum hh i j).tendsto_sum_nat
  exact ((continuous_id.matrix_det).tendsto _).comp hmat

/-- A uniform bound on the truncations bounds `|Δ_h(T)|`, `T = Ti₂(zT n)`. -/
theorem abs_Delta_le_of {h : ℕ} (hh : Even h) {B : ℝ} (hB : ∀ T, |(HT n h T).det| ≤ B) :
    |aeval (TT n) (Delta n h)| ≤ B := by
  rw [aeval_Ti2_Delta hh]
  exact le_of_tendsto' ((continuous_abs.tendsto _).comp (tendsto_det_HT hh)) hB

/-! ### Weak duality (DualU) -/

/-- The node weight function `g`. -/
noncomputable def gD (n : ℕ) (h M : ℕ) (m : ℕ → ℝ) (lam : ℝ) (s : ℕ) : ℝ :=
  Real.log (bN n h s) + 2 * Pm M m s - lam

/-- The dual constant (`z`-free; DualU's `Cd` without the trace argument). -/
noncomputable def Cd (h M : ℕ) (m : ℕ → ℝ) (lam : ℝ) : ℝ :=
  -Em M m + lam * h + Real.log 2 * (4 * h + 2 * ∑ s ∈ range M, m s ^ 2)

/-- **Weak duality for one slot assignment.** -/
theorem pattern_le {h T M : ℕ} (hh' : Even h) (hh : 2 ≤ h) (hTM : 2 * T < M) (m : ℕ → ℝ)
    (hmsum : ∑ s ∈ range M, m s = h) (lam : ℝ) (f : Fin h → Fin T × Fin 3)
    (hinj : Function.Injective (fun i => xslot (f i))) :
    (∏ i, bN n h (tnode (f i))) * ∏ i, ∏ j ∈ Ioi i, pairFactor (tnode (f i)) (tnode (f j)) ^ 2 ≤
      Real.exp (Cd h M m lam + ∑ i, gD n h M m lam (tnode (f i))) := by
  set t : Fin h → ℕ := fun i => tnode (f i)
  have ht : ∀ i, t i < M := fun i => by simp only [t, tnode]; have := (f i).1.isLt; omega
  set nn : ℕ → ℝ := fun s => ((univ.filter (fun i => t i = s)).card : ℝ)
  have hn2 : ∀ s, nn s ≤ 2 := fun s => by
    have := card_fiber_le_two f hinj s
    simp only [nn, t]; exact_mod_cast this
  have hn0 : ∀ s, 0 ≤ nn s := fun s => by positivity
  have hnsum : ∑ s ∈ range M, nn s = h := by
    have := sum_fiber t ht (fun _ => (1 : ℝ))
    simp only [mul_one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    rw [← this]
  have hM : 1 ≤ M := by omega
  -- the product as an exponential
  have hb : ∀ i, 0 < bN n h (t i) := fun i => bN_tnode_pos hh' (f i)
  have hprod : (∏ i, bN n h (t i)) * ∏ i, ∏ j ∈ Ioi i, pairFactor (t i) (t j) ^ 2 =
      Real.exp (∑ i, Real.log (bN n h (t i)) + ∑ i, ∑ j, Lk (t i) (t j)) := by
    rw [Real.exp_add, Real.exp_sum, sum_pairs_symm (fun i j => Lk (t i) (t j))
      (fun i j => Lk_symm _ _) (fun i => by simp [Lk])]
    congr 1
    · exact Finset.prod_congr rfl (fun i _ => (Real.exp_log (hb i)).symm)
    · rw [Finset.mul_sum, Real.exp_sum]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum, Real.exp_sum]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [pairFactor_eq_exp, ← Real.exp_nat_mul]
      push_cast; ring_nf
  -- the pair sum through multiplicities
  have hpairs : ∑ i, ∑ j, Lk (t i) (t j) = ∑ s ∈ range M, ∑ s' ∈ range M, nn s * nn s' * Lk s s' :=
    sum_fiber2 t ht Lk
  -- the weight sum
  have hwt : ∑ i, Real.log (bN n h (t i)) + 2 * ∑ s ∈ range M, nn s * Pm M m s =
      ∑ i, gD n h M m lam (t i) + lam * h := by
    have hP := sum_fiber t ht (fun s => Pm M m s)
    unfold gD
    rw [← hP, Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [show ∑ i, (Real.log (bN n h (t i)) + 2 * Pm M m (t i) - lam) + lam * h =
      ∑ i, (Real.log (bN n h (t i)) + 2 * Pm M m (t i)) - lam * h + lam * h by
        rw [Finset.sum_sub_distrib, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring]
    ring
  -- the lattice inequality
  have hν : ∑ s ∈ range M, (nn s - m s) = 0 := by rw [Finset.sum_sub_distrib, hnsum, hmsum, sub_self]
  have hpol := polya_Lk hM (fun s => nn s - m s) hν
  have hsq : ∑ s ∈ range M, (nn s - m s) ^ 2 ≤ 4 * h + 2 * ∑ s ∈ range M, m s ^ 2 := by
    have : ∀ s ∈ range M, (nn s - m s) ^ 2 ≤ 4 * nn s + 2 * m s ^ 2 := by
      intro s _
      have := hn2 s; have := hn0 s
      nlinarith [sq_nonneg (nn s + m s)]
    calc ∑ s ∈ range M, (nn s - m s) ^ 2 ≤ ∑ s ∈ range M, (4 * nn s + 2 * m s ^ 2) := Finset.sum_le_sum this
      _ = 4 * h + 2 * ∑ s ∈ range M, m s ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hnsum]
  have hid := quad_identity M nn m
  rw [hprod]
  refine Real.exp_le_exp.mpr ?_
  unfold Cd
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hsq hlog2]

/-- The far-node weight: `1` for node indices `< N₀`, `e^{g(τ)}` beyond. -/
noncomputable def zf (n : ℕ) (h M : ℕ) (m : ℕ → ℝ) (lam : ℝ) (N0 : ℕ) {T : ℕ} (k : Fin T × Fin 3) : ℝ :=
  if (k.1 : ℕ) < N0 then 1 else Real.exp (gD n h M m lam (tnode k))

omit [Fact (3 ≤ n)] in
lemma split_near_far {h T M : ℕ} (m : ℕ → ℝ) (lam : ℝ) (N0 : ℕ)
    (f : Fin h → Fin T × Fin 3) (hinj : Function.Injective (fun i => xslot (f i))) :
    ∑ i, gD n h M m lam (tnode (f i)) ≤
      2 * ∑ r ∈ range N0, max (gD n h M m lam (2 * r + 1)) 0 +
        ∑ i, (if ((f i).1 : ℕ) < N0 then 0 else gD n h M m lam (tnode (f i))) := by
  set g := gD n h M m lam
  set u : Fin h → ℕ := fun i => ((f i).1 : ℕ)
  have hu : ∀ i, u i < T := fun i => (f i).1.isLt
  have htn : ∀ i, tnode (f i) = 2 * u i + 1 := fun i => rfl
  have hnear : ∑ i, (if u i < N0 then max (g (2 * u i + 1)) 0 else 0) ≤
      2 * ∑ r ∈ range N0, max (g (2 * r + 1)) 0 := by
    rw [sum_fiber u hu (fun r => if r < N0 then max (g (2 * r + 1)) 0 else 0)]
    calc ∑ r ∈ range T, ((univ.filter (fun i => u i = r)).card : ℝ) *
          (if r < N0 then max (g (2 * r + 1)) 0 else 0)
        ≤ ∑ r ∈ range T, 2 * (if r < N0 then max (g (2 * r + 1)) 0 else 0) := by
          refine Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_right ?_ (by split_ifs <;> simp))
          exact_mod_cast card_fiber_idx_le_two f hinj r
      _ = 2 * ∑ r ∈ (range T).filter (fun r => r < N0), max (g (2 * r + 1)) 0 := by
          rw [← Finset.mul_sum, Finset.sum_filter]
      _ ≤ 2 * ∑ r ∈ range N0, max (g (2 * r + 1)) 0 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (by norm_num)
          · intro r hr; rw [mem_filter] at hr; rw [mem_range]; exact hr.2
          · intro r _ _; exact le_max_right _ _
  calc ∑ i, g (tnode (f i)) ≤ ∑ i, ((if u i < N0 then max (g (2 * u i + 1)) 0 else 0) +
        (if u i < N0 then 0 else g (tnode (f i)))) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [htn i]
        split_ifs <;> simp
    _ ≤ _ := by rw [Finset.sum_add_distrib]; linarith

/-- **The dual bound on the truncated determinant.** -/
theorem abs_det_HT_le_dual {h T M : ℕ} (hh' : Even h) (hh : 2 ≤ h) (hTM : 2 * T < M) (m : ℕ → ℝ)
    (hmsum : ∑ s ∈ range M, m s = h) (lam : ℝ) (N0 : ℕ) :
    |(HT n h T).det| ≤ ((h.factorial : ℝ))⁻¹ * Kslot h ^ 2 *
      (Real.exp (Cd h M m lam + 2 * ∑ r ∈ range N0, max (gD n h M m lam (2 * r + 1)) 0) *
        (∑ k : Fin T × Fin 3, zf n h M m lam N0 k) ^ h) := by
  refine (abs_det_HT_le hh' hh).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (inv_nonneg.mpr (by positivity)) (sq_nonneg _))
  rw [Finset.sum_pow', Fintype.piFinset_univ, Finset.mul_sum]
  refine Finset.sum_le_sum (fun f _ => ?_)
  split_ifs with hinj
  · refine (pattern_le hh' hh hTM m hmsum lam f hinj).trans ?_
    have hsplit := split_near_far (n := n) (M := M) m lam N0 f hinj
    have hz : ∏ i, zf n h M m lam N0 (f i) =
        Real.exp (∑ i, (if ((f i).1 : ℕ) < N0 then 0 else gD n h M m lam (tnode (f i)))) := by
      rw [Real.exp_sum]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      unfold zf; split_ifs <;> simp
    rw [hz, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  · exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg (fun i _ => by
      unfold zf; split_ifs
      · norm_num
      · exact (Real.exp_pos _).le))

end Ti
end Chi2U
