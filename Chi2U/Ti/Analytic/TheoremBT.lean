/-
# Theorem V_i: Theorem B′ at `z = zT n` from a dual certificate (PROOF_TI2 §2 row "§5.1 Theorem B′_z")

**Copy of `Chi2U/Analytic/TheoremBU.lean`** (from `DualCertU` on), with the machine of `Ti₂(zT n)`: the node weights
are `χ₄(τ) z^τ` (`Ti/Analytic/NodesT.lean`), so only `|χ₄(τ) z^τ| = z^τ` enters, and the proof is TheoremBU's with
`zU az` replaced by `zT n` (PROOF_TI2: "only `|ω_t| = z^t` enters, via the triangle inequality"). Lemma names are
TheoremBU's; `DualCertU` becomes `DualCertT`, `vU` becomes `vT`.

`DualCertT n`: a certificate at `z = zT n` (fields as `DualCertU`, external field `v(x) = x log z − Ψ(x)`);
**Theorem B′_z** (`DualCertT.analytic`): `|Δ_h(T)| ≤ exp((Φ + ε) h²)` for even `h`, eventually, `T = Ti₂(zT n)`.
The `z`-free lemmas (`PsiU`, `c1U`, `log_abs_Dpoly_ge`, `near_count_odd`, `eventually_small`, `StepData` API, …) are
reused from the χ₂ files. Like TheoremBU, the monotonicity of `v` is not used (so no condition on `n` beyond `n ≥ 3`).
-/
import Chi2U.Ti.Analytic.NodesT

namespace Chi2U
namespace Ti

variable {n : ℕ} [Fact (3 ≤ n)]

open Finset Real Filter Polynomial

/-- The external field `v(x) = x log z − Ψ(x)`, `z = zT n`. -/
noncomputable def vT (n : ℕ) (x : ℝ) : ℝ := x * Real.log (zT n) - PsiU x

/-- A dual certificate for Theorem B′. -/
structure DualCertT (n : ℕ) [Fact (3 ≤ n)] where
  μ : StepData
  hc1 : ∀ j, μ.c j ≤ 1
  hsupp : μ.a μ.K ≤ 2
  lam : ℝ
  L : ℕ
  X : ℕ
  Sk : ℕ → ℝ
  hL : 1 ≤ L
  hX : 4 ≤ X
  hF : ∀ k < X * L, ∀ x : ℝ, (k : ℝ) / L ≤ x → x ≤ ((k : ℝ) + 1) / L → 2 * μ.U x + vT n x ≤ Sk k
  htail1 : 1 / (X : ℝ) + Real.log (zT n) < 0
  htail2 : 2 * Real.log X - Real.log ((X : ℝ) - 1) + X * Real.log (zT n) - lam < 0

/-- **The node weight bound**: `log b(τ) ≤ h v(τ/h) − (h+1) log h + c₁(h)` at odd `τ`. -/
lemma log_bN_le {h : ℕ} (hh : Even h) (h2 : 2 ≤ h) (s : ℕ) :
    Real.log (bN n h (2 * s + 1)) ≤
      h * vT n (((2 * s + 1 : ℕ) : ℝ) / h) - ((h : ℝ) + 1) * Real.log h + c1U h := by
  have hD := log_abs_Dpoly_ge hh h2 s
  have hne : aeval ((2 * s + 1 : ℕ) : ℝ) (Dpoly h) ≠ 0 := by
    obtain ⟨J, rfl⟩ := hh; exact aeval_Dpoly_ne J s
  have hA := two_add_log_ge_one h
  have hz := zT_pos (n := n)
  have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  unfold bN phiU
  rw [Real.log_mul (by positivity) (by linarith), Real.log_mul (by positivity)
    (abs_pos.mpr (inv_ne_zero hne)).ne', Real.log_pow, abs_inv, Real.log_inv]
  have e : (h : ℝ) * vT n (((2 * s + 1 : ℕ) : ℝ) / h) =
      ((2 * s + 1 : ℕ) : ℝ) * Real.log (zT n) - h * PsiU (((2 * s + 1 : ℕ) : ℝ) / h) := by
    unfold vT; rw [mul_sub, ← mul_assoc, mul_div_cancel₀ _ hh0]
  rw [e]
  unfold c1U
  linarith

namespace DualCertT

variable (C : DualCertT n)

/-- The excess `Σ_k (S_k − λ)₊`. -/
noncomputable def σ : ℝ := ∑ k ∈ range (C.X * C.L), max (C.Sk k - C.lam) 0

/-- **The certified exponent** `Φ = −E(μ) + λ + (1/L) Σ_k (S_k − λ)₊`. -/
noncomputable def Phi : ℝ := -C.μ.E + C.lam + 1 / C.L * C.σ

/-! ### The tail -/

omit [Fact (3 ≤ n)] in
lemma vT_le_tail {x : ℝ} (hx : 2 ≤ x) : vT n x ≤ x * Real.log (zT n) - Real.log (x - 1) := by
  have := DualCertU.PsiU_ge_log hx; unfold vT; linarith

/-- The decay rate beyond `X`. -/
noncomputable def δ : ℝ :=
  -max (1 / (C.X : ℝ) + Real.log (zT n))
    ((2 * Real.log C.X - Real.log ((C.X : ℝ) - 1) + C.X * Real.log (zT n) - C.lam) / C.X)

lemma X_pos : (0 : ℝ) < C.X := by exact_mod_cast (by have := C.hX; omega : 0 < C.X)

lemma X_ge : (4 : ℝ) ≤ C.X := by exact_mod_cast C.hX

lemma δ_pos : 0 < C.δ := by
  unfold δ
  have h2 : (2 * Real.log C.X - Real.log ((C.X : ℝ) - 1) + C.X * Real.log (zT n) - C.lam) / C.X < 0 :=
    div_neg_of_neg_of_pos C.htail2 C.X_pos
  have := max_lt C.htail1 h2
  linarith

lemma σ_nonneg : 0 ≤ C.σ := Finset.sum_nonneg (fun _ _ => le_max_right _ _)

/-- **The tail:** `F(x) − λ ≤ −δx` for `x ≥ X`. -/
lemma tail {x : ℝ} (hx : (C.X : ℝ) ≤ x) : 2 * C.μ.U x + vT n x - C.lam ≤ -C.δ * x := by
  have hX0 := C.X_pos
  have hX4 := C.X_ge
  have hx0 : 0 < x := by linarith
  have hNX : C.μ.a C.μ.K ≤ x := by linarith [C.hsupp]
  have hU := C.μ.U_le_log hNX hx0
  have hV := vT_le_tail (n := n) (show (2 : ℝ) ≤ x by linarith)
  have hlog : Real.log x ≤ Real.log C.X + x / C.X - 1 := by
    have := Real.log_le_sub_one_of_pos (div_pos hx0 hX0)
    rw [Real.log_div hx0.ne' hX0.ne'] at this
    linarith
  have hq : Real.log x - Real.log (x - 1) ≤ Real.log C.X - Real.log ((C.X : ℝ) - 1) := by
    have h1 : Real.log (x * ((C.X : ℝ) - 1)) ≤ Real.log (C.X * (x - 1)) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    rw [Real.log_mul hx0.ne' (by linarith), Real.log_mul hX0.ne' (by linarith)] at h1
    linarith
  set c1 := 1 / (C.X : ℝ) + Real.log (zT n)
  set c2 := (2 * Real.log C.X - Real.log ((C.X : ℝ) - 1) + C.X * Real.log (zT n) - C.lam) / C.X
  have hδ : -C.δ = max c1 c2 := by unfold δ; ring
  have e1 : c1 * x = x / C.X + x * Real.log (zT n) := by simp only [c1]; ring
  have e2 : (C.X : ℝ) * (c2 - c1) = 2 * Real.log C.X - Real.log ((C.X : ℝ) - 1) - C.lam - 1 := by
    simp only [c1, c2]; field_simp; ring
  have hG : 2 * C.μ.U x + vT n x - C.lam ≤ C.X * (c2 - c1) + c1 * x := by
    rw [e1, e2]; linarith
  rw [hδ]
  rcases le_total c1 c2 with h | h
  · rw [max_eq_right h]
    have : (C.X : ℝ) * (c2 - c1) ≤ x * (c2 - c1) := mul_le_mul_of_nonneg_right hx (by linarith)
    nlinarith
  · rw [max_eq_left h]
    have : (C.X : ℝ) * (c2 - c1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hX0.le (by linarith)
    linarith

/-! ### The node weight function -/

/-- The cell-average error `8K(1 + log h) + 2 log(2h + 1)` (support index `S = 2h`). -/
noncomputable def errB (h : ℕ) : ℝ := 8 * C.μ.K * (1 + Real.log h) + 2 * Real.log (((2 * h : ℕ) : ℝ) + 1)

/-- The per-node remainder `c₁(h) + 2·err`. -/
noncomputable def gerr (h : ℕ) : ℝ := c1U h + 2 * C.errB h

lemma errB_nonneg {h : ℕ} (hh : 1 ≤ h) : 0 ≤ C.errB h := by
  unfold errB
  have : 0 ≤ Real.log h := Real.log_nonneg (by exact_mod_cast hh)
  have : 0 ≤ Real.log (((2 * h : ℕ) : ℝ) + 1) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ ((2 * h : ℕ) : ℝ) := by positivity
    linarith)
  positivity

lemma gerr_nonneg {h : ℕ} (hh : 1 ≤ h) : 0 ≤ C.gerr h := by
  unfold gerr; have := c1U_nonneg hh; have := C.errB_nonneg hh; linarith

lemma hS {h : ℕ} (hh : 1 ≤ h) : C.μ.a C.μ.K ≤ ((2 * h : ℕ) : ℝ) / h := by
  have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  push_cast; rw [mul_div_assoc, div_self hh0, mul_one]; exact C.hsupp

/-- The node weight function of the certificate (threshold `hλ + h log h`). -/
noncomputable def g (h M τ : ℕ) : ℝ := gD n h M (C.μ.mref h) (h * C.lam + h * Real.log h) τ

lemma g_le {h M : ℕ} (hh : Even h) (h2 : 2 ≤ h) (hM : 2 * h + 1 ≤ M) (s : ℕ) :
    C.g h M (2 * s + 1) ≤ h * (2 * C.μ.U (((2 * s + 1 : ℕ) : ℝ) / h) + vT n (((2 * s + 1 : ℕ) : ℝ) / h) - C.lam) +
      C.gerr h := by
  have hh1 : 1 ≤ h := by omega
  have hlogh : 0 ≤ Real.log h := Real.log_nonneg (by exact_mod_cast hh1)
  unfold g gD gerr errB
  have h1 := log_bN_le (n := n) hh h2 s
  have h2 := C.μ.Pm_le hh1 (C.hS hh1) hM (2 * s + 1)
  linarith

/-! ### Near nodes -/

lemma near_le {h M J : ℕ} (hh : Even h) (h2 : 2 ≤ h) (hM : 2 * h + 1 ≤ M) (hJ : h = J + J) :
    ∑ r ∈ range (C.X * J), max (C.g h M (2 * r + 1)) 0 ≤
      h * (((h : ℝ) / (2 * C.L) + 1) * C.σ) + (C.X * J : ℕ) * C.gerr h := by
  have hh1 : 1 ≤ h := by omega
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hge := C.gerr_nonneg hh1
  set Fx : ℕ → ℝ := fun r => max (2 * C.μ.U (((2 * r + 1 : ℕ) : ℝ) / h) +
    vT n (((2 * r + 1 : ℕ) : ℝ) / h) - C.lam) 0 with hFx
  have hnode : ∀ r ∈ range (C.X * J), max (C.g h M (2 * r + 1)) 0 ≤ h * Fx r + C.gerr h := by
    intro r _
    have hg := C.g_le hh h2 hM r
    have hmax : (h : ℝ) * (2 * C.μ.U (((2 * r + 1 : ℕ) : ℝ) / h) + vT n (((2 * r + 1 : ℕ) : ℝ) / h) - C.lam) ≤
        h * Fx r := mul_le_mul_of_nonneg_left (le_max_left _ _) hh0.le
    have hFx0 : 0 ≤ (h : ℝ) * Fx r := mul_nonneg hh0.le (le_max_right _ _)
    exact max_le (by linarith) (by linarith)
  have hcount := near_count_odd (h := h) (L := C.L) (X := C.X) (J := J) hJ hh1 C.hL
    (fun k => max (C.Sk k - C.lam) 0) (fun k => le_max_right _ _) Fx (fun r _ k hk hlo hhi => by
      simp only [hFx]
      refine max_le_max ?_ le_rfl
      have := C.hF k hk (((2 * r + 1 : ℕ) : ℝ) / h) hlo hhi
      linarith)
  have hsum := Finset.sum_le_sum hnode
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, card_range, nsmul_eq_mul] at hsum
  have := mul_le_mul_of_nonneg_left hcount hh0.le
  unfold σ
  linarith

/-! ### Far nodes -/

/-- The far-node constant `1/(1 − e^{−δ})`. -/
noncomputable def Cf : ℝ := 1 / (1 - Real.exp (-C.δ))

lemma Cf_pos : 0 < C.Cf := by
  unfold Cf
  have := C.δ_pos
  have : Real.exp (-C.δ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have : 0 < 1 - Real.exp (-C.δ) := by linarith
  positivity

lemma far_node {h M J : ℕ} (hh : Even h) (h2 : 2 ≤ h) (hM : 2 * h + 1 ≤ M) (hJ : h = J + J) {s : ℕ}
    (hs : C.X * J ≤ s) :
    Real.exp (C.g h M (2 * s + 1)) ≤ Real.exp (C.gerr h) * Real.exp (-C.δ) ^ (s + 1) := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hδ := C.δ_pos
  have hg := C.g_le hh h2 hM s
  have hx : (C.X : ℝ) ≤ ((2 * s + 1 : ℕ) : ℝ) / h := by
    rw [le_div_iff₀ hh0]
    have : C.X * h ≤ 2 * s + 1 := by
      have e : C.X * h = 2 * (C.X * J) := by rw [hJ]; ring
      omega
    exact_mod_cast this
  have ht := C.tail hx
  have ht' : (h : ℝ) * (2 * C.μ.U (((2 * s + 1 : ℕ) : ℝ) / h) + vT n (((2 * s + 1 : ℕ) : ℝ) / h) - C.lam) ≤
      -C.δ * ((s : ℝ) + 1) := by
    have := mul_le_mul_of_nonneg_left ht hh0.le
    have e : (h : ℝ) * (-C.δ * (((2 * s + 1 : ℕ) : ℝ) / h)) = -C.δ * ((2 * s + 1 : ℕ) : ℝ) := by
      field_simp
    have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    have : -C.δ * ((2 * s + 1 : ℕ) : ℝ) ≤ -C.δ * ((s : ℝ) + 1) := by push_cast; nlinarith
    linarith
  calc Real.exp (C.g h M (2 * s + 1)) ≤ Real.exp (C.gerr h + -C.δ * ((s + 1 : ℕ) : ℝ)) :=
        Real.exp_le_exp.mpr (by push_cast; linarith)
    _ = Real.exp (C.gerr h) * Real.exp (-C.δ) ^ (s + 1) := by
        rw [Real.exp_add, ← Real.exp_nat_mul]; ring_nf

lemma far_le {h T J : ℕ} (hh : Even h) (h2 : 2 ≤ h) (hJ : h = J + J) :
    ∑ k : Fin T × Fin 3, zf n h (2 * T + 2 * h + 1) (C.μ.mref h) (h * C.lam + h * Real.log h) (C.X * J) k ≤
      3 * ((C.X * J : ℕ) + C.Cf * Real.exp (C.gerr h)) := by
  have hδ := C.δ_pos
  set M := 2 * T + 2 * h + 1
  have hM : 2 * h + 1 ≤ M := by omega
  set r := Real.exp (-C.δ) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  set Cg := Real.exp (C.gerr h) with hCg
  have hCg0 : 0 ≤ Cg := (Real.exp_pos _).le
  set f : ℕ → ℝ := fun t => if t < C.X * J then 1 else Real.exp (C.g h M (2 * t + 1)) with hf
  have hzf : ∀ k : Fin T × Fin 3,
      zf n h M (C.μ.mref h) (h * C.lam + h * Real.log h) (C.X * J) k = f k.1 := by
    intro k; simp only [zf, tnode, hf]; rfl
  rw [Fintype.sum_prod_type]
  simp_rw [hzf]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun t => f t) T]
  push_cast
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hbound : ∀ t ∈ range T, f t ≤ (if t < C.X * J then 1 else 0) + Cg * r ^ (t + 1) := by
    intro t _
    simp only [hf]
    split_ifs with ht
    · have : 0 ≤ Cg * r ^ (t + 1) := by positivity
      linarith
    · rw [zero_add, hCg, hr]
      exact C.far_node hh h2 hM hJ (by omega)
  refine (Finset.sum_le_sum hbound).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (((range T).filter (fun t => t < C.X * J)).card : ℝ) ≤ ((C.X * J : ℕ) : ℝ) := by
    have : ((range T).filter (fun t => t < C.X * J)).card ≤ C.X * J := by
      refine (Finset.card_le_card (t := range (C.X * J)) (fun t ht => ?_)).trans (card_range _).le
      simp only [mem_filter, mem_range] at ht ⊢; omega
    exact_mod_cast this
  have hgeo := sum_geom_succ_le hr0 hr1 T
  have : Cg * ∑ t ∈ range T, r ^ (t + 1) ≤ Cg * (1 / (1 - r)) := mul_le_mul_of_nonneg_left hgeo hCg0
  have e : Cg * (1 / (1 - r)) = C.Cf * Real.exp (C.gerr h) := by
    simp only [hCg, Cf, hr]; ring
  push_cast at hcard
  linarith

/-! ### The dual constant -/

lemma msum {h M : ℕ} (hh : 1 ≤ h) (hM : 2 * h + 1 ≤ M) : ∑ s ∈ range M, C.μ.mref h s = h := by
  rw [sum_range_support hM (C.μ.mref h) (C.μ.mref_zero h) (fun n hn => C.μ.mref_supp hh (C.hS hh) n hn)]
  exact C.μ.sum_mref_cells hh (C.hS hh)

lemma Cd_le {h M : ℕ} (hh : 1 ≤ h) (hM : 2 * h + 1 ≤ M) :
    Cd h M (C.μ.mref h) (h * C.lam + h * Real.log h) ≤
      (h : ℝ) ^ 2 * (C.lam - C.μ.E) + 4 * h * Real.log (((2 * h : ℕ) : ℝ) + 1) + 8 * h * Real.log 2 := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hE := C.μ.Em_ge hh (C.hS hh) hM
  have hmsum := C.msum hh hM
  have hsq : ∑ s ∈ range M, C.μ.mref h s ^ 2 ≤ 2 * h := by
    calc ∑ s ∈ range M, C.μ.mref h s ^ 2 ≤ ∑ s ∈ range M, 2 * C.μ.mref h s :=
          Finset.sum_le_sum (fun s _ => by
            have := C.μ.mref_nonneg (h := h) (by omega) s
            have := C.μ.mref_le_two (h := h) (by omega) s
            nlinarith)
      _ = 2 * h := by rw [← Finset.mul_sum, hmsum]
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold Cd
  nlinarith

/-! ### Assembly -/

/-- The far-node bound `Z(h) = 3(Xh + C_f e^{gerr})`. -/
noncomputable def Zb (h : ℕ) : ℝ := 3 * ((C.X : ℝ) * h + C.Cf * Real.exp (C.gerr h))

lemma Zb_pos {h : ℕ} (hh : 1 ≤ h) : 0 < C.Zb h := by
  unfold Zb
  have := C.Cf_pos
  have : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  positivity

/-- The remainder (all `O(h log h)`). -/
noncomputable def Rem (h : ℕ) : ℝ :=
  2 * h * Real.log h + 4 * h + 4 * h * Real.log (((2 * h : ℕ) : ℝ) + 1) + 8 * h * Real.log 2 + 2 * h * C.σ +
    2 * (C.X * h) * C.gerr h + h * Real.log (C.Zb h)

/-- **The truncated determinants, uniformly in `T`.** -/
theorem det_bound {h : ℕ} (hh : Even h) (h2 : 2 ≤ h) (T : ℕ) :
    |(HT n h T).det| ≤ Real.exp (C.Phi * (h : ℝ) ^ 2 + C.Rem h) := by
  obtain ⟨J, hJ⟩ := hh
  have hh1 : 1 ≤ h := by omega
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  set M := 2 * T + 2 * h + 1 with hMdef
  have hM : 2 * h + 1 ≤ M := by omega
  have hTM : 2 * T < M := by omega
  have hmsum := C.msum hh1 hM
  have hdual := abs_det_HT_le_dual (n := n) ⟨J, hJ⟩ h2 hTM (C.μ.mref h) hmsum (h * C.lam + h * Real.log h) (C.X * J)
  -- the pieces
  have hfar := C.far_le (T := T) ⟨J, hJ⟩ h2 hJ
  have hnear := C.near_le ⟨J, hJ⟩ h2 hM hJ
  have hCd := C.Cd_le hh1 hM
  have hK := log_Kslot_sq_le hh1
  have hZ := C.Zb_pos hh1
  have hge := C.gerr_nonneg hh1
  have hKpos : 0 < Kslot h ^ 2 := by unfold Kslot; positivity
  have hfac1 : (1 : ℝ) ≤ h.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero h)
  have hfac : ((h.factorial : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hfac1
  have hXJ : ((C.X * J : ℕ) : ℝ) ≤ (C.X : ℝ) * h := by
    have : C.X * J ≤ C.X * h := Nat.mul_le_mul_left _ (by omega)
    exact_mod_cast this
  have hfar' : ∑ k : Fin T × Fin 3, zf n h M (C.μ.mref h) (h * C.lam + h * Real.log h) (C.X * J) k ≤ C.Zb h := by
    refine hfar.trans ?_
    unfold Zb; linarith
  have hzf0 : 0 ≤ ∑ k : Fin T × Fin 3, zf n h M (C.μ.mref h) (h * C.lam + h * Real.log h) (C.X * J) k :=
    Finset.sum_nonneg (fun k _ => by unfold zf; split_ifs <;> positivity)
  have hpow : (∑ k : Fin T × Fin 3, zf n h M (C.μ.mref h) (h * C.lam + h * Real.log h) (C.X * J) k) ^ h ≤
      C.Zb h ^ h := pow_le_pow_left₀ hzf0 hfar' h
  refine hdual.trans ?_
  generalize hE1 : Cd h M (C.μ.mref h) (h * C.lam + h * Real.log h) +
    2 * ∑ r ∈ range (C.X * J), max (gD n h M (C.μ.mref h) (h * C.lam + h * Real.log h) (2 * r + 1)) 0 = E1
  have hstep : ((h.factorial : ℝ))⁻¹ * Kslot h ^ 2 * (Real.exp E1 *
      (∑ k : Fin T × Fin 3, zf n h M (C.μ.mref h) (h * C.lam + h * Real.log h) (C.X * J) k) ^ h) ≤
      Real.exp (Real.log (Kslot h ^ 2) + E1 + h * Real.log (C.Zb h)) := by
    calc ((h.factorial : ℝ))⁻¹ * Kslot h ^ 2 * (Real.exp E1 *
          (∑ k : Fin T × Fin 3, zf n h M (C.μ.mref h) (h * C.lam + h * Real.log h) (C.X * J) k) ^ h)
        ≤ 1 * Kslot h ^ 2 * (Real.exp E1 * C.Zb h ^ h) := by gcongr
      _ = _ := by
          rw [Real.exp_add, Real.exp_add, Real.exp_log hKpos, Real.exp_nat_mul, Real.exp_log hZ]; ring
  refine hstep.trans (Real.exp_le_exp.mpr ?_)
  -- the exponent
  have hnear' : ∑ r ∈ range (C.X * J), max (gD n h M (C.μ.mref h) (h * C.lam + h * Real.log h) (2 * r + 1)) 0 ≤
      h * (((h : ℝ) / (2 * C.L) + 1) * C.σ) + (C.X * J : ℕ) * C.gerr h := hnear
  have hL0 : (0 : ℝ) < C.L := by exact_mod_cast (by have := C.hL; omega : 0 < C.L)
  have eΦ : C.Phi * (h : ℝ) ^ 2 = (h : ℝ) ^ 2 * (C.lam - C.μ.E) + 2 * (h * ((h : ℝ) / (2 * C.L) * C.σ)) := by
    unfold Phi; field_simp; ring
  have hXJg : ((C.X * J : ℕ) : ℝ) * C.gerr h ≤ (C.X : ℝ) * h * C.gerr h := mul_le_mul_of_nonneg_right hXJ hge
  unfold Rem
  rw [← hE1, eΦ]
  nlinarith

/-- `gerr h = O(log h)`. -/
lemma gerr_le : ∃ G0 G1 : ℝ, 0 ≤ G1 ∧ ∀ h : ℕ, 1 ≤ h → C.gerr h ≤ G0 + G1 * Real.log h := by
  refine ⟨Real.log 2 + 1 + Real.log 4 + 16 * C.μ.K + 4 * Real.log 3, 6 + 16 * C.μ.K, by positivity,
    fun h hh => ?_⟩
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hh0 : (0 : ℝ) < h := by linarith
  have a1 : Real.log (2 * (h : ℝ)) = Real.log 2 + Real.log h := Real.log_mul (by norm_num) hh0.ne'
  have a2 : Real.log (2 * (h : ℝ) + 1) ≤ Real.log 3 + Real.log h := by
    rw [← Real.log_mul (by norm_num) hh0.ne']; exact Real.log_le_log (by positivity) (by linarith)
  have a3 : Real.log (2 + Real.log (2 * (h : ℝ) + 1)) ≤ Real.log 4 + Real.log h := by
    rw [← Real.log_mul (by norm_num) hh0.ne']
    have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * h + 1 by positivity)
    have hl0 : 0 ≤ Real.log (2 * (h : ℝ) + 1) := Real.log_nonneg (by linarith)
    exact Real.log_le_log (by linarith) (by linarith)
  have a4 : Real.log (((2 * h : ℕ) : ℝ) + 1) ≤ Real.log 3 + Real.log h := by push_cast; exact a2
  have hK0 : (0 : ℝ) ≤ C.μ.K := Nat.cast_nonneg _
  have hL : 0 ≤ Real.log (h : ℝ) := Real.log_nonneg hh1
  unfold gerr errB c1U
  nlinarith

/-- The remainder is `O(h log h)`. -/
lemma Rem_le : ∃ a b c : ℝ, ∀ h : ℕ, 1 ≤ h → C.Rem h ≤ a * h * Real.log h + b * h + c := by
  obtain ⟨G0, G1, hG1, hG⟩ := C.gerr_le
  set cZ := Real.log (3 * ((C.X : ℝ) + C.Cf))
  refine ⟨2 + 4 + 2 * C.X * G1 + 1 + G1,
    4 + 4 * Real.log 3 + 8 * Real.log 2 + 2 * C.σ + 2 * C.X * G0 + cZ + G0, 0, fun h hh => ?_⟩
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hh0 : (0 : ℝ) < h := by linarith
  have hX0 := C.X_pos
  have hCf := C.Cf_pos
  have hge := C.gerr_nonneg hh
  set Lg := Real.log (h : ℝ) with hLg
  have hLg0 : 0 ≤ Lg := Real.log_nonneg hh1
  have F1 : Real.log (((2 * h : ℕ) : ℝ) + 1) ≤ Real.log 3 + Lg := by
    push_cast; rw [hLg, ← Real.log_mul (by norm_num) hh0.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have F4 : Real.log (C.Zb h) ≤ cZ + Lg + C.gerr h := by
    have hE : 1 ≤ Real.exp (C.gerr h) := Real.one_le_exp hge
    have hle : C.Zb h ≤ 3 * ((C.X : ℝ) + C.Cf) * h * Real.exp (C.gerr h) := by
      unfold Zb
      have : (C.X : ℝ) * h ≤ C.X * h * Real.exp (C.gerr h) := by
        have := mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℝ) ≤ C.X * h)
        linarith
      have : C.Cf * Real.exp (C.gerr h) ≤ C.Cf * h * Real.exp (C.gerr h) := by
        have := mul_le_mul_of_nonneg_left hh1 (by positivity : (0 : ℝ) ≤ C.Cf * Real.exp (C.gerr h))
        linarith
      nlinarith
    calc Real.log (C.Zb h) ≤ Real.log (3 * ((C.X : ℝ) + C.Cf) * h * Real.exp (C.gerr h)) :=
          Real.log_le_log (C.Zb_pos hh) hle
      _ = cZ + Lg + C.gerr h := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) hh0.ne',
            Real.log_exp]
  have G := hG h hh
  have P1 := mul_le_mul_of_nonneg_left F1 hh0.le
  have P2 := mul_le_mul_of_nonneg_left G (by positivity : (0 : ℝ) ≤ 2 * (C.X * h))
  have P3 := mul_le_mul_of_nonneg_left F4 hh0.le
  have P4 := mul_le_mul_of_nonneg_left G hh0.le
  unfold Rem
  nlinarith

/-- **Theorem B′.** -/
theorem analytic : ∀ ε > 0, ∀ᶠ h : ℕ in atTop, Even h →
    |aeval (TT n) (Delta n h)| ≤ Real.exp ((C.Phi + ε) * (h : ℝ) ^ 2) := by
  intro ε hε
  obtain ⟨a, b, c, hR⟩ := C.Rem_le
  filter_upwards [eventually_small a b c ε hε, eventually_ge_atTop 2] with h hsmall hh heven
  refine abs_Delta_le_of heven (fun T => (C.det_bound heven hh T).trans (Real.exp_le_exp.mpr ?_))
  have := hR h (by omega)
  nlinarith

end DualCertT

end Ti
end Chi2U
