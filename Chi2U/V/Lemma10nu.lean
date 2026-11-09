/-
# Lemma 10_ν (PROOF_V §4): `n₂(Δ_h) ≤ n2A az h` at an even trace `az`

`ν = nuA az = v₂(az)` (`= 1 + v₂(m)` for `az = 2m`; `n2A (2m) h = n2V m h`). Entries `G_{ij}` of the rescaled anchored Gram matrix and their (L), (U) bounds:
`Chi2U/V/TwoAdicNu.lean`. This file: the Gram identity `det G = 2^{3h} Δ_h` at `zU az` (`det_anchoredM`, Theorem U's
`det_anchored` with `Qd az` for `Q5`), a uniform entry bound `v₂(G_{ij}) ≥ ĝ(i + j)` with a concave piecewise-linear
`ĝ` (`gW`, `vGe_entryM`), and the Leibniz bound.

**Departure from PROOF_V.** PROOF_V bounds `Σ_i ĝ(i + σ(i)) ≥ Σ_i ĝ(2i)` for every permutation `σ` by majorisation
and Karamata. Here the same bound comes from row/column weights: concavity gives `ĝ(2i) + ĝ(2j) ≤ 2ĝ(i + j)`, so with
`ρ_i = ⌊ĝ(2i)/2⌋`, `κ_j = ĝ(2j) − ⌊ĝ(2j)/2⌋` (integers) we get `ρ_i + κ_j ≤ ĝ(i + j)` (both sides integers) and
`Σρ + Σκ = Σ_i ĝ(2i)`; the weighted Leibniz bound (`vGeX_det2M`, as in Lemma 10′) then gives
`v₂(det G) ≥ Σ_i ĝ(2i)`. The functions (`J = h/2`, `L = ⌊log₂ h⌋`, `K = h + 1`):
* `ν ≥ 2`: `ĝ(s) = min(h − s − L − 2, −3 − (ν − 1)(s − K) − L)` (PROOF_V's `ĝ − L − 2`, with the (L) branch lowered
  by the slack 1), `Σ_i ĝ(2i) = J² + 1 − (ν − 1)(J − 1)² − h(L + 2)`;
* `ν = 1`: `ĝ₁(s) = min(0, K − s)`, `Σ_i ĝ₁(2i) = −(J − 1)²`.
With `Δ_h = 2^{−3h} det G` this is `n₂ ≤ (ν − 1)(J − 1)² − J² + hL + 5h − 1`, resp. `(J − 1)² + 3h`, i.e. `n2A az h`.
-/
import Chi2U.V.TwoAdicNu

namespace Chi2U.V.TwoAdicNu

open Polynomial Finset Chi2U.TwoAdicAux

variable {az : ℕ} [Fact (1 ≤ az)]

/-! ### The Gram identity at `zU az` -/

/-- `Λ_X(g) = A(g) + X·B(g) ∈ ℚ(√d)[X]`. -/
noncomputable def LamQM (az : ℕ) [Fact (1 ≤ az)] (h : ℕ) (g : ℚ[X]) : (Qd az)[X] :=
  C (Afun az h g) + X * C (Bfun az h g)

lemma LamQM_add (h : ℕ) (f g : ℚ[X]) : LamQM az h (f + g) = LamQM az h f + LamQM az h g := by
  unfold LamQM; rw [Afun_addM, Bfun_addM, C_add, C_add]; ring

lemma LamQM_C_mul (h : ℕ) (c : ℚ) (g : ℚ[X]) : LamQM az h (C c * g) = C (c : Qd az) * LamQM az h g := by
  unfold LamQM; rw [Afun_C_mulM, Bfun_C_mulM, C_mul, C_mul]; ring

lemma LamQM_sum (h : ℕ) {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    LamQM az h (∑ i ∈ s, f i) = ∑ i ∈ s, LamQM az h (f i) :=
  map_sum (AddMonoidHom.mk' (LamQM az h) (LamQM_add h)) f s

/-- `ℚ → ℚ(√d)[X]`. -/
noncomputable def psiQd (az : ℕ) [Fact (1 ≤ az)] : ℚ →+* (Qd az)[X] := C.comp (algebraMap ℚ (Qd az))

lemma psiQd_apply (r : ℚ) : psiQd az r = C (r : Qd az) := by simp [psiQd]

/-- The monomial matrix `H_{de} = Λ_X(t^{d+e})`. -/
noncomputable def HQM (az : ℕ) [Fact (1 ≤ az)] (h : ℕ) : Matrix (Fin h) (Fin h) (Qd az)[X] :=
  fun d e => LamQM az h (X ^ ((d : ℕ) + e))

theorem gram_eqM {h : ℕ} (a b : Fin h → ℚ[X]) (ha : ∀ i, (a i).natDegree < h) (hb : ∀ i, (b i).natDegree < h) :
    Matrix.of (fun i j => LamQM az h (a i * b j)) =
      (CoefM a).map (psiQd az) * HQM az h * ((CoefM b).map (psiQd az)).transpose := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [expand_fin a ha i, expand_fin b hb j, sum_mul_sum, LamQM_sum]
  simp only [LamQM_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun e _ => ?_)
  rw [sum_mul]
  refine sum_congr rfl (fun d _ => ?_)
  have : C (CoefM a i d) * X ^ (d : ℕ) * (C (CoefM b j e) * X ^ (e : ℕ)) =
      C (CoefM a i d * CoefM b j e) * X ^ ((d : ℕ) + e) := by
    rw [C_mul, pow_add]; ring
  rw [this, LamQM_C_mul, psiQd_apply, psiQd_apply, Rat.cast_mul, C_mul]
  simp only [HQM]
  ring

lemma det_map_psiQd {h : ℕ} (M : Matrix (Fin h) (Fin h) ℚ) : (M.map (psiQd az)).det = psiQd az M.det :=
  (RingHom.map_det (psiQd az) M).symm

/-- Rescaling and the unitriangular change of basis at `zU az`: `det G = 2^{3h} Δ_h`. -/
theorem det_anchoredM {h : ℕ} (hh : Even h) :
    (Matrix.of fun i j : Fin h => C (GAm az h i j) + X * C (GBm az h i j)).det =
      C ((2 : Qd az) ^ (3 * h)) * (Delta az h).map (algebraMap ℚ (Qd az)) := by
  set a : Fin h → ℚ[X] := fun i => (aAnch h i).comp (C (1 / 2) * X) with ha
  set b : Fin h → ℚ[X] := fun j => (bAnch h j).comp (C (1 / 2) * X) with hb
  have hA : ∀ i : Fin h, (a i).natDegree = i ∧ (a i).leadingCoeff = (1 / 2) ^ (i : ℕ) := fun i => by
    have := natDegree_lead_C_mul_PZ (h := h) ((1 / 2 : ℚ) ^ (i : ℕ)) (by positivity) (range i)
    rw [card_range] at this
    simp only [ha]; rw [aAnch_comp]; exact this
  have hB : ∀ j : Fin h, (b j).natDegree = j ∧ (b j).leadingCoeff = (1 / 2) ^ (j : ℕ) := fun j => by
    have := natDegree_lead_C_mul_PZ (h := h) ((1 / 2 : ℚ) ^ (j : ℕ)) (by positivity) (Ico (h + 1 - j) (h + 1))
    rw [Nat.card_Ico, show h + 1 - (h + 1 - j) = j by have := j.isLt; omega] at this
    simp only [hb]; rw [bAnch_comp h j (by have := j.isLt; omega)]; exact this
  have hM : (Matrix.of fun i j : Fin h => C (GAm az h i j) + X * C (GBm az h i j)) =
      (C ((2 : Qd az) ^ (h + 2))) • Matrix.of (fun i j => LamQM az h (a i * b j)) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, GAm, GBm, LamQM, ha, hb, mul_comp, C_mul]
    ring
  have hH : (HQM az h).det = (Delta az h).map (algebraMap ℚ (Qd az)) := by
    rw [Delta_map hh]; rfl
  rw [hM, Matrix.det_smul, Fintype.card_fin,
    gram_eqM a b (fun i => by rw [(hA i).1]; exact i.isLt) (fun j => by rw [(hB j).1]; exact j.isLt),
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_map_psiQd, det_map_psiQd,
    det_CoefM a (fun i => (hA i).1), det_CoefM b (fun j => (hB j).1), hH]
  simp only [fun i => (hA i).2, fun j => (hB j).2, psiQd_apply]
  have key : ((2 : Qd az) ^ (h + 2)) ^ h * (((∏ i : Fin h, (1 / 2 : ℚ) ^ (i : ℕ)) : ℚ) : Qd az) *
      (((∏ i : Fin h, (1 / 2 : ℚ) ^ (i : ℕ)) : ℚ) : Qd az) = 2 ^ (3 * h) := by
    have := congrArg (fun r : ℚ => (r : Qd az)) (scalar_eq h)
    push_cast at this ⊢
    rw [← this]; ring
  rw [← key]
  simp only [map_mul, map_pow]
  ring

/-! ### The concave entry bound -/

/-- The concave piecewise-linear lower bound `ĝ` for `v₂(G_{ij})`, as a function of `s = i + j`. -/
def gW (m h : ℕ) (s : ℤ) : ℤ :=
  if 2 ≤ nuA m then
    min ((h : ℤ) - s - Nat.log 2 h - 2) (-3 - ((nuA m : ℤ) - 1) * (s - (h + 1)) - Nat.log 2 h)
  else min 0 ((h : ℤ) + 1 - s)

/-- **Entry bound** (PROOF_V (L), (U), coarsened): `v₂(G_{ij}) ≥ ĝ(i + j)`. -/
theorem vGe_entryM (ha : Even az) {h i j : ℕ} (hi : i < h) (hj : j < h) :
    vGe 2 (gW az h ((i : ℤ) + j)) (GAm az h i j) ∧ vGe 2 (gW az h ((i : ℤ) + j)) (GBm az h i j) := by
  unfold gW
  split_ifs with hν
  · rcases Nat.lt_or_ge (i + j) (h + 1) with hij | hij
    · have hU := vGe_UM (az := az) (h := h) (i := i) (j := j) hν (by omega)
      have hl := log_two_mono (show h - i - j ≤ h by omega)
      have hle : min ((h : ℤ) - (i + j) - Nat.log 2 h - 2)
          (-3 - ((nuA az : ℤ) - 1) * ((i : ℤ) + j - (h + 1)) - Nat.log 2 h) ≤
          ((h - i - j : ℕ) : ℤ) - Nat.log 2 (h - i - j) := by
        refine (min_le_left _ _).trans ?_
        omega
      exact ⟨vGe_mono hle hU.1, vGe_mono hle hU.2⟩
    · rcases Nat.eq_or_lt_of_le hij with hij' | hij'
      · have := lemma10_L0M (az := az) hij'.symm
        rw [this.1, this.2]; exact ⟨vGe_zero _, vGe_zero _⟩
      · have hL := lemma10_LM (az := az) hν hi hj (by omega)
        have hl := log_two_mono (show i + j - (h + 1) ≤ h by omega)
        have hle : min ((h : ℤ) - (i + j) - Nat.log 2 h - 2)
            (-3 - ((nuA az : ℤ) - 1) * ((i : ℤ) + j - (h + 1)) - Nat.log 2 h) ≤
            -((nuA az : ℤ) - 1) * ((i + j - (h + 1) : ℕ) : ℤ) - 2 - Nat.log 2 (i + j - (h + 1)) := by
          refine (min_le_right _ _).trans ?_
          push_cast [show h + 1 ≤ i + j by omega]
          have : ((Nat.log 2 (i + j - (h + 1)) : ℕ) : ℤ) ≤ Nat.log 2 h := by exact_mod_cast hl
          nlinarith
        refine ⟨vGe_mono hle hL.1, ?_⟩
        rw [hL.2]; exact vGe_zero _
  · have hν1 : nuA az = 1 := by have := one_le_nuA ha; omega
    rcases Nat.lt_or_ge (i + j) (h + 1) with hij | hij
    · have hU := vGe_UM1 (az := az) ha (h := h) (i := i) (j := j) (by omega)
      have hle : min (0 : ℤ) ((h : ℤ) + 1 - (i + j)) ≤ 1 := (min_le_left _ _).trans (by norm_num)
      exact ⟨vGe_mono hle hU.1, vGe_mono hle hU.2⟩
    · rcases Nat.eq_or_lt_of_le hij with hij' | hij'
      · have := lemma10_L0M (az := az) hij'.symm
        rw [this.1, this.2]; exact ⟨vGe_zero _, vGe_zero _⟩
      · have hL := lemma10_LM1 (az := az) hν1 hi hj (by omega)
        have hle : min (0 : ℤ) ((h : ℤ) + 1 - (i + j)) ≤ -((i + j - (h + 1) : ℕ) : ℤ) := by
          refine (min_le_right _ _).trans ?_
          push_cast [show h + 1 ≤ i + j by omega]
          omega
        refine ⟨vGe_mono hle hL.1, ?_⟩
        rw [hL.2]; exact vGe_zero _

/-- `ĝ` is concave: `ĝ(2i) + ĝ(2j) ≤ 2ĝ(i + j)` (a minimum of two affine functions). -/
lemma gW_concave (m h : ℕ) (i j : ℤ) : gW m h (2 * i) + gW m h (2 * j) ≤ 2 * gW m h (i + j) := by
  unfold gW
  split_ifs
  · set c : ℤ := (nuA m : ℤ) - 1
    set L : ℤ := (Nat.log 2 h : ℤ)
    have e2 : (-3 - c * (2 * i - (h + 1)) - L) + (-3 - c * (2 * j - (h + 1)) - L) =
        2 * (-3 - c * (i + j - (h + 1)) - L) := by ring
    rcases min_cases ((h : ℤ) - (i + j) - L - 2) (-3 - c * (i + j - (h + 1)) - L) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
      rw [h1]
    · have := min_le_left ((h : ℤ) - 2 * i - L - 2) (-3 - c * (2 * i - (h + 1)) - L)
      have := min_le_left ((h : ℤ) - 2 * j - L - 2) (-3 - c * (2 * j - (h + 1)) - L)
      linarith
    · have := min_le_right ((h : ℤ) - 2 * i - L - 2) (-3 - c * (2 * i - (h + 1)) - L)
      have := min_le_right ((h : ℤ) - 2 * j - L - 2) (-3 - c * (2 * j - (h + 1)) - L)
      linarith
  · rcases min_cases (0 : ℤ) ((h : ℤ) + 1 - (i + j)) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]
    · have := min_le_left (0 : ℤ) ((h : ℤ) + 1 - 2 * i)
      have := min_le_left (0 : ℤ) ((h : ℤ) + 1 - 2 * j)
      linarith
    · have := min_le_right (0 : ℤ) ((h : ℤ) + 1 - 2 * i)
      have := min_le_right (0 : ℤ) ((h : ℤ) + 1 - 2 * j)
      linarith

/-! ### `Σ_i ĝ(2i)` -/

lemma sum_range_id_int (n : ℕ) : (∑ i ∈ range n, (i : ℤ)) * 2 = (n : ℤ) * ((n : ℤ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, add_mul, ih]; push_cast; ring

lemma sum_affine (a b : ℤ) (n : ℕ) : (∑ i ∈ range n, (a + b * (i : ℤ))) * 2 = 2 * n * a + b * n * (n - 1) := by
  rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  linear_combination b * sum_range_id_int n

/-- The weighted total: `Σ_i ĝ(2i)` in closed form. -/
def Sg (m h : ℕ) : ℤ :=
  if 2 ≤ nuA m then ((h / 2 : ℕ) : ℤ) ^ 2 + 1 - ((nuA m : ℤ) - 1) * (((h / 2 : ℕ) : ℤ) - 1) ^ 2 -
      (h : ℤ) * (Nat.log 2 h + 2)
  else -(((h / 2 : ℕ) : ℤ) - 1) ^ 2

lemma sum_gW {h : ℕ} (m : ℕ) (hh : Even h) (h2 : 2 ≤ h) :
    ∑ i ∈ range h, gW m h (2 * (i : ℤ)) = Sg m h := by
  obtain ⟨J, rfl⟩ := hh
  have hJ : (J + J) / 2 = J := by omega
  have hsplit : J + J = (J + 1) + (J - 1) := by omega
  rw [hsplit, sum_range_add]
  rw [← hsplit]
  unfold Sg gW
  rw [hJ]
  set L : ℤ := (Nat.log 2 (J + J) : ℤ)
  have hJ1 : (1 : ℤ) ≤ J := by exact_mod_cast (show 1 ≤ J by omega)
  have hJc : ((J - 1 : ℕ) : ℤ) = (J : ℤ) - 1 := by push_cast [show 1 ≤ J by omega]; ring
  split_ifs with hν
  · set c : ℤ := (nuA m : ℤ) - 1
    have hc : 1 ≤ c := by have : (2 : ℤ) ≤ nuA m := by exact_mod_cast hν
                          simp only [c]; linarith
    have s1 : ∑ x ∈ range (J + 1), min (((J + J : ℕ) : ℤ) - 2 * (x : ℤ) - L - 2)
        (-3 - c * (2 * (x : ℤ) - ((J + J : ℕ) + 1)) - L) =
        ∑ x ∈ range (J + 1), ((2 * (J : ℤ) - L - 2) + (-2) * (x : ℤ)) := by
      refine sum_congr rfl (fun x hx => ?_)
      have hx' : (x : ℤ) ≤ J := by have := mem_range.mp hx; omega
      rw [min_eq_left]
      · push_cast; ring
      · push_cast
        have : (c - 1) * (2 * (J : ℤ) + 1 - 2 * x) ≥ 0 := mul_nonneg (by linarith) (by linarith)
        nlinarith
    have s2 : ∑ x ∈ range (J - 1), min (((J + J : ℕ) : ℤ) - 2 * (((J + 1 + x : ℕ)) : ℤ) - L - 2)
        (-3 - c * (2 * ((J + 1 + x : ℕ) : ℤ) - ((J + J : ℕ) + 1)) - L) =
        ∑ x ∈ range (J - 1), ((-3 - c - L) + (-2 * c) * (x : ℤ)) := by
      refine sum_congr rfl (fun x _ => ?_)
      have hx0 : (0 : ℤ) ≤ x := by positivity
      rw [min_eq_right]
      · push_cast; ring
      · push_cast
        have : (c - 1) * (2 * (x : ℤ) + 1) ≥ 0 := mul_nonneg (by linarith) (by linarith)
        nlinarith
    rw [s1, s2]
    have a1 := sum_affine (2 * (J : ℤ) - L - 2) (-2) (J + 1)
    have a2 := sum_affine (-3 - c - L) (-2 * c) (J - 1)
    rw [hJc] at a2
    push_cast at a1 a2 ⊢
    linarith
  · have s1 : ∑ x ∈ range (J + 1), min (0 : ℤ) (((J + J : ℕ) : ℤ) + 1 - 2 * (x : ℤ)) =
        ∑ x ∈ range (J + 1), ((0 : ℤ) + 0 * (x : ℤ)) := by
      refine sum_congr rfl (fun x hx => ?_)
      have hx' : (x : ℤ) ≤ J := by have := mem_range.mp hx; omega
      rw [min_eq_left (by push_cast; omega)]; ring
    have s2 : ∑ x ∈ range (J - 1), min (0 : ℤ) (((J + J : ℕ) : ℤ) + 1 - 2 * (((J + 1 + x : ℕ)) : ℤ)) =
        ∑ x ∈ range (J - 1), ((-1 : ℤ) + (-2) * (x : ℤ)) := by
      refine sum_congr rfl (fun x _ => ?_)
      rw [min_eq_right (by push_cast; omega)]; push_cast; ring
    rw [s1, s2]
    have a2 := sum_affine (-1) (-2) (J - 1)
    rw [hJc] at a2
    simp only [zero_mul, add_zero, sum_const_zero, zero_add]
    linarith

/-! ### Leibniz with row and column weights -/

/-- Leibniz for polynomial matrices with row and column weights. -/
theorem vGeX_det2M {k : ℕ} (M : Matrix (Fin k) (Fin k) (Qd az)[X]) (ρ κ : Fin k → ℤ)
    (h : ∀ i j, vGeX 2 (ρ i + κ j) (M i j)) : vGeX 2 (∑ i, ρ i + ∑ i, κ i) M.det := by
  rw [Matrix.det_apply]
  refine vGeX_sum _ _ (fun σ _ => ?_)
  have hprod : vGeX 2 (∑ i, (ρ (σ i) + κ i)) (∏ i, M (σ i) i) :=
    vGeX_prod _ _ _ (fun i _ => h (σ i) i)
  rw [sum_add_distrib, Equiv.sum_comp σ ρ] at hprod
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
  · simpa using hprod
  · simpa using vGeX_neg hprod

/-- `v₂(det G) ≥ Σ_i ĝ(2i)` (the weights `⌊ĝ(2i)/2⌋`, `⌈ĝ(2j)/2⌉`). -/
theorem vGeX_detG (ha : Even az) {h : ℕ} (hh : Even h) (h2 : 2 ≤ h) :
    vGeX 2 (Sg az h) (Matrix.of fun i j : Fin h => C (GAm az h i j) + X * C (GBm az h i j)).det := by
  set ρ : Fin h → ℤ := fun i => gW az h (2 * ((i : ℕ) : ℤ)) / 2 with hρ
  set κ : Fin h → ℤ := fun j => gW az h (2 * ((j : ℕ) : ℤ)) - gW az h (2 * ((j : ℕ) : ℤ)) / 2 with hκ
  have hdet := vGeX_det2M (Matrix.of fun i j : Fin h => C (GAm az h i j) + X * C (GBm az h i j)) ρ κ
    (fun i j => by
      have hE := vGe_entryM (az := az) ha (h := h) i.isLt j.isLt
      have hc := gW_concave az h ((i : ℕ) : ℤ) ((j : ℕ) : ℤ)
      have hle : ρ i + κ j ≤ gW az h (((i : ℕ) : ℤ) + ((j : ℕ) : ℤ)) := by
        simp only [hρ, hκ]; omega
      rw [Matrix.of_apply]
      exact vGeX_add (vGeX_C (vGe_mono hle hE.1)) (vGeX_X_mul (vGeX_C (vGe_mono hle hE.2))))
  have hsum : ∑ i, ρ i + ∑ i, κ i = Sg az h := by
    rw [← sum_add_distrib, ← sum_gW az hh h2, ← Fin.sum_univ_eq_sum_range (fun i => gW az h (2 * (i : ℤ))) h]
    refine sum_congr rfl (fun i _ => ?_)
    simp only [hρ, hκ]; ring
  rwa [hsum] at hdet

end Chi2U.V.TwoAdicNu

namespace Chi2U.V

open Polynomial Finset Chi2U.TwoAdicAux Chi2U.V.TwoAdicNu

/-- `3h − Σ_i ĝ(2i) ≤ n2A m h` (equality up to `ℕ`-truncation, which does not occur). -/
lemma three_h_sub_Sg_le (m : ℕ) {h : ℕ} (hh : Even h) (h2 : 2 ≤ h) : 3 * (h : ℤ) - Sg m h ≤ n2A m h := by
  obtain ⟨J, rfl⟩ := hh
  have hJ : (J + J) / 2 = J := by omega
  have hJc : ((J - 1 : ℕ) : ℤ) = (J : ℤ) - 1 := by push_cast [show 1 ≤ J by omega]; ring
  unfold Sg n2A
  rw [hJ]
  split_ifs with hν
  · set L := Nat.log 2 (J + J)
    set c := nuA m - 1 with hc
    have hcz : ((c : ℕ) : ℤ) = (nuA m : ℤ) - 1 := by rw [hc]; push_cast [show 1 ≤ nuA m by omega]; ring
    generalize hA : c * (J - 1) ^ 2 = A
    have hAz : (A : ℤ) = ((nuA m : ℤ) - 1) * ((J : ℤ) - 1) ^ 2 := by rw [← hA]; push_cast; rw [hcz, hJc]
    generalize hB : (J + J) * L = B
    have hBz : (B : ℤ) = ((J : ℤ) + J) * L := by rw [← hB]; push_cast; ring
    generalize hP : J ^ 2 = P
    have hPz : (P : ℤ) = (J : ℤ) ^ 2 := by rw [← hP]; push_cast; ring
    have key : ((A + B + 5 * (J + J) - 1 - P : ℕ) : ℤ) ≥ (A : ℤ) + B + 5 * ((J : ℤ) + J) - 1 - P := by omega
    push_cast
    linarith
  · push_cast
    rw [hJc]
    linarith

/-- **Lemma 10_ν** (PROOF_V §4): `n₂(Δ_h) ≤ n2A az h` for even `h ≥ 2`, every even trace `az ≥ 2`, `ν = v₂(az)`.
Route: `Δ_h = 2^{−3h} det G` (`det_anchoredM`) and `v₂(det G) ≥ Σ_i ĝ(2i)` (`vGeX_detG`, entry bounds
`vGe_entryM` from PROOF_V's (L), (U); weights from the concavity of `ĝ` in place of PROOF_V's Karamata step). -/
theorem lemma10nu_proof (az : ℕ) [Fact (1 ≤ az)] (ha : Even az) {h : ℕ} (hh : Even h) (h2 : 2 ≤ h) (k : ℕ) :
    padicNorm 2 ((Delta az h).coeff k) ≤ (2 : ℚ) ^ n2A az h := by
  have hdet := vGeX_detG (az := az) ha hh h2
  rw [det_anchoredM hh] at hdet
  have hinv : (Delta az h).map (algebraMap ℚ (Qd az)) =
      C ((((2 : ℚ) ^ (-((3 * h : ℕ) : ℤ))) : ℚ) : Qd az) *
        (C ((2 : Qd az) ^ (3 * h)) * (Delta az h).map (algebraMap ℚ (Qd az))) := by
    rw [← mul_assoc, ← C_mul]
    have : ((((2 : ℚ) ^ (-((3 * h : ℕ) : ℤ))) : ℚ) : Qd az) * (2 : Qd az) ^ (3 * h) = 1 := by
      rw [zpow_neg, zpow_natCast, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat,
        inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)]
    rw [this, C_1, one_mul]
  have hfin := vGeX_mul (vGeX_C (vGe_of_V2M (az := az) (V2_two_zpow (-((3 * h : ℕ) : ℤ))))) hdet
  rw [← hinv] at hfin
  refine (padicNorm_coeff_of_vGeX_map hfin k).trans ?_
  rw [← zpow_natCast]
  refine zpow_le_zpow_right₀ (by norm_num) ?_
  have := three_h_sub_Sg_le az hh h2
  push_cast at this ⊢
  linarith

end Chi2U.V
