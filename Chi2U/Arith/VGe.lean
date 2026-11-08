/-
# `p`-adic valuations on `ℚ(√d)`, `d = mz² + 1`: the `vGe` API (analogue of lean_chi2's `Arith/Gauss.lean`)

`pInt p x` (`Arith/Defs.lean`): `x ∈ O_p`; for even `mz`, `O_p = ℤ_(p)[ω]`, `ω = (1 + √d)/2`, basis `{1, ω}`
(`x = (re − im) + (2 im) ω`), a subring since `ω² = ω + (mz/2)²`; for odd `mz`, `O_p = ℤ_(p)[√d]`. Membership
only ever yields lower bounds on valuations.
`vGe p n x` (defined in `Arith/Defs.lean`) is `pInt p (p^{−n} • x)`.

Closure lemmas (`add`, `mul`, `sum`, `prod`, `pow`, units `z^k`), rational elements, the extraction
`vGe p n (r : Q5) → |r|_p ≤ p^{−n}`, the Leibniz bound for determinants (`vGe_det`), and the coefficientwise
version `vGeX` for `ℚ(√5)[X]` (`vGeX_mul`, `vGeX_det`, `padicNorm_coeff_of_vGeX_map`).
-/
import Chi2U.Arith.Defs

namespace Chi2U

variable {mz : ℕ} [Fact (1 ≤ mz)]

open Polynomial Finset

variable {p : ℕ} [hp : Fact p.Prime]

lemma pInt_iff_even (he : Even mz) (x : Qd mz) :
    pInt p x ↔ padicNorm p (x.re - x.im) ≤ 1 ∧ padicNorm p (2 * x.im) ≤ 1 := by
  rw [pInt, if_pos he]

lemma pInt_iff_odd (he : ¬ Even mz) (x : Qd mz) : pInt p x ↔ padicNorm p x.re ≤ 1 ∧ padicNorm p x.im ≤ 1 := by
  rw [pInt, if_neg he]

lemma vGe_iff_pInt (n : ℤ) (x : Qd mz) : vGe p n x ↔ pInt p (((p : ℚ) ^ (-n) : ℚ) • x) := by rw [vGe]

/-- Elements with `p`-integral coordinates `re`, `im` lie in `O_p`. -/
lemma pInt_of_coords {x : Qd mz} (hre : padicNorm p x.re ≤ 1) (him : padicNorm p x.im ≤ 1) : pInt p x := by
  by_cases he : Even mz
  · rw [pInt_iff_even he]
    refine ⟨(padicNorm.sub).trans (max_le hre him), ?_⟩
    rw [padicNorm.mul]
    have : padicNorm p (2 : ℚ) ≤ 1 := by simpa using padicNorm.of_nat (p := p) 2
    nlinarith [padicNorm.nonneg (p := p) x.im, padicNorm.nonneg (p := p) (2 : ℚ)]
  · exact (pInt_iff_odd he x).mpr ⟨hre, him⟩

lemma pInt_zero : pInt p (0 : Qd mz) := pInt_of_coords (by simp) (by simp)

lemma pInt_add {x y : Qd mz} (hx : pInt p x) (hy : pInt p y) : pInt p (x + y) := by
  by_cases he : Even mz
  · rw [pInt_iff_even he] at *
    refine ⟨?_, ?_⟩
    · have : (x + y).re - (x + y).im = (x.re - x.im) + (y.re - y.im) := by simp; ring
      rw [this]; exact (padicNorm.nonarchimedean).trans (max_le hx.1 hy.1)
    · have : 2 * (x + y).im = 2 * x.im + 2 * y.im := by simp; ring
      rw [this]; exact (padicNorm.nonarchimedean).trans (max_le hx.2 hy.2)
  · rw [pInt_iff_odd he] at *
    refine ⟨?_, ?_⟩
    · simp only [QuadraticAlgebra.re_add]; exact (padicNorm.nonarchimedean).trans (max_le hx.1 hy.1)
    · simp only [QuadraticAlgebra.im_add]; exact (padicNorm.nonarchimedean).trans (max_le hx.2 hy.2)

lemma pInt_neg {x : Qd mz} (hx : pInt p x) : pInt p (-x) := by
  by_cases he : Even mz
  · rw [pInt_iff_even he] at *
    refine ⟨?_, ?_⟩
    · have : (-x).re - (-x).im = -(x.re - x.im) := by simp; ring
      rw [this, padicNorm.neg]; exact hx.1
    · have : 2 * (-x).im = -(2 * x.im) := by simp
      rw [this, padicNorm.neg]; exact hx.2
  · rw [pInt_iff_odd he] at *
    simp only [QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, padicNorm.neg]; exact hx

lemma pInt_sub {x y : Qd mz} (hx : pInt p x) (hy : pInt p y) : pInt p (x - y) := by
  rw [sub_eq_add_neg]; exact pInt_add hx (pInt_neg hy)

lemma pInt_mul {x y : Qd mz} (hx : pInt p x) (hy : pInt p y) : pInt p (x * y) := by
  have hn : ∀ u v : ℚ, padicNorm p u ≤ 1 → padicNorm p v ≤ 1 → padicNorm p (u * v) ≤ 1 := fun u v hu hv => by
    rw [padicNorm.mul]; nlinarith [padicNorm.nonneg (p := p) u, padicNorm.nonneg (p := p) v]
  have hadd : ∀ u v : ℚ, padicNorm p u ≤ 1 → padicNorm p v ≤ 1 → padicNorm p (u + v) ≤ 1 := fun u v hu hv =>
    (padicNorm.nonarchimedean).trans (max_le hu hv)
  by_cases he : Even mz
  · rw [pInt_iff_even he] at *
    obtain ⟨k, hk⟩ := he
    have hd : dQ mz = 1 + 4 * ((k : ℚ) * k) := by rw [dQ_eq, hk]; push_cast; ring
    have hkk : padicNorm p ((k : ℚ) * k) ≤ 1 := by
      have := padicNorm.of_nat (p := p) (k * k); push_cast at this; exact this
    set a₁ := x.re - x.im; set b₁ := 2 * x.im; set a₂ := y.re - y.im; set b₂ := 2 * y.im
    refine ⟨?_, ?_⟩
    · have : (x * y).re - (x * y).im = a₁ * a₂ + b₁ * b₂ * ((k : ℚ) * k) := by
        simp only [a₁, b₁, a₂, b₂, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
        linear_combination (x.im * y.im) * hd
      rw [this]; exact hadd _ _ (hn _ _ hx.1 hy.1) (hn _ _ (hn _ _ hx.2 hy.2) hkk)
    · have : 2 * (x * y).im = a₁ * b₂ + b₁ * a₂ + b₁ * b₂ := by
        simp only [a₁, b₁, a₂, b₂, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]; ring
      rw [this]; exact hadd _ _ (hadd _ _ (hn _ _ hx.1 hy.2) (hn _ _ hx.2 hy.1)) (hn _ _ hx.2 hy.2)
  · rw [pInt_iff_odd he] at *
    have hd : padicNorm p (dQ mz) ≤ 1 := by
      have := padicNorm.of_nat (p := p) (mz ^ 2 + 1); push_cast at this; rwa [dQ_eq]
    refine ⟨?_, ?_⟩
    · simp only [QuadraticAlgebra.re_mul]
      exact hadd _ _ (hn _ _ hx.1 hy.1) (hn _ _ (hn _ _ hd hx.2) hy.2)
    · simp only [QuadraticAlgebra.im_mul, zero_mul, add_zero]
      exact hadd _ _ (hn _ _ hx.1 hy.2) (hn _ _ hx.2 hy.1)

lemma pInt_ratCast {r : ℚ} (hr : padicNorm p r ≤ 1) : pInt p (r : Qd mz) :=
  pInt_of_coords (by simpa using hr) (by simp)

lemma pInt_one : pInt p (1 : Qd mz) := by simpa using pInt_ratCast (mz := mz) (p := p) (r := 1) (by simp)

lemma pInt_natCast (n : ℕ) : pInt p (n : Qd mz) := by
  simpa using pInt_ratCast (mz := mz) (p := p) (r := n) (padicNorm.of_nat n)

lemma pInt_intCast (n : ℤ) : pInt p (n : Qd mz) := by
  simpa using pInt_ratCast (mz := mz) (p := p) (r := n) (padicNorm.of_int n)

lemma pInt_sum {ι : Type*} (s : Finset ι) (f : ι → Qd mz) (h : ∀ i ∈ s, pInt p (f i)) :
    pInt p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pInt_zero (mz := mz) (p := p)
  | insert a s ha ih =>
      rw [sum_insert ha]
      exact pInt_add (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

lemma pInt_prod {ι : Type*} (s : Finset ι) (f : ι → Qd mz) (h : ∀ i ∈ s, pInt p (f i)) :
    pInt p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pInt_one (mz := mz) (p := p)
  | insert a s ha ih =>
      rw [prod_insert ha]
      exact pInt_mul (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

lemma pInt_pow {x : Qd mz} (hx : pInt p x) (n : ℕ) : pInt p (x ^ n) := by
  induction n with
  | zero => simpa using pInt_one (mz := mz) (p := p)
  | succ n ih => rw [pow_succ]; exact pInt_mul ih hx

lemma pInt_zK : pInt p (zK mz) :=
  pInt_of_coords (by simpa [zK] using padicNorm.of_nat (p := p) mz) (by simp [zK])

lemma pInt_zK_inv : pInt p (zK mz)⁻¹ := by
  rw [zK_inv]; exact pInt_of_coords (by simpa using padicNorm.of_nat (p := p) mz) (by simp)

lemma pInt_zK_zpow (k : ℤ) : pInt p ((zK mz) ^ k) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · simpa using pInt_pow pInt_zK n
  · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pInt_pow pInt_zK_inv n

lemma pInt_smul {r : ℚ} (hr : padicNorm p r ≤ 1) {x : Qd mz} (hx : pInt p x) : pInt p (r • x) := by
  rw [Algebra.smul_def, eq_ratCast]; exact pInt_mul (pInt_ratCast hr) hx

lemma pInt_sqrtd : pInt p (sqrtd mz) := pInt_of_coords (by simp [sqrtd]) (by simp [sqrtd])

/-- The rational part: `r ∈ O_p` gives `|r|_p ≤ 1`. -/
lemma padicNorm_le_one_of_pInt_ratCast {r : ℚ} (h : pInt p (r : Qd mz)) : padicNorm p r ≤ 1 := by
  by_cases he : Even mz
  · have := ((pInt_iff_even he _).mp h).1; simpa using this
  · have := ((pInt_iff_odd he _).mp h).1; simpa using this

/-! ### `vGe` -/

lemma padicNorm_p_zpow (n : ℤ) : padicNorm p ((p : ℚ) ^ n) = (p : ℚ) ^ (-n) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [padicNorm.eq_zpow_of_nonzero (zpow_ne_zero n hp0), padicValRat.zpow, padicValRat.self hp.out.one_lt,
    mul_one]

lemma vGe_zero (n : ℤ) : vGe p n (0 : Qd mz) := by rw [vGe_iff_pInt, smul_zero]; exact pInt_zero

lemma vGe_add {n : ℤ} {x y : (Qd mz)} (hx : vGe p n x) (hy : vGe p n y) : vGe p n (x + y) := by
  rw [vGe_iff_pInt] at *; rw [smul_add]; exact pInt_add hx hy

lemma vGe_neg {n : ℤ} {x : (Qd mz)} (hx : vGe p n x) : vGe p n (-x) := by
  rw [vGe_iff_pInt] at *; rw [smul_neg]; exact pInt_neg hx

lemma vGe_sub {n : ℤ} {x y : (Qd mz)} (hx : vGe p n x) (hy : vGe p n y) : vGe p n (x - y) := by
  rw [sub_eq_add_neg]; exact vGe_add hx (vGe_neg hy)

lemma vGe_sum {ι : Type*} (s : Finset ι) {n : ℤ} (f : ι → (Qd mz)) (h : ∀ i ∈ s, vGe p n (f i)) :
    vGe p n (∑ i ∈ s, f i) := by
  rw [vGe_iff_pInt, smul_sum]; exact pInt_sum _ _ (fun i hi => (vGe_iff_pInt n _).mp (h i hi))

lemma vGe_mul {n m : ℤ} {x y : (Qd mz)} (hx : vGe p n x) (hy : vGe p m y) : vGe p (n + m) (x * y) := by
  rw [vGe_iff_pInt] at *
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have : ((p : ℚ) ^ (-(n + m))) • (x * y) = ((p : ℚ) ^ (-n) • x) * ((p : ℚ) ^ (-m) • y) := by
    rw [smul_mul_smul_comm, ← zpow_add₀ hp0]; congr 2; ring
  rw [this]; exact pInt_mul hx hy

lemma vGe_mono {n m : ℤ} (hmn : m ≤ n) {x : (Qd mz)} (hx : vGe p n x) : vGe p m x := by
  rw [vGe_iff_pInt] at *
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have : ((p : ℚ) ^ (-m)) • x = ((p : ℚ) ^ (n - m)) • ((p : ℚ) ^ (-n) • x) := by
    rw [smul_smul, ← zpow_add₀ hp0]; congr 2; ring
  rw [this]
  refine pInt_smul ?_ hx
  rw [padicNorm_p_zpow]
  exact zpow_le_one_of_nonpos₀ (by exact_mod_cast hp.out.one_lt.le) (by omega)

lemma vGe_of_pInt {x : (Qd mz)} (hx : pInt p x) : vGe p 0 x := by
  rw [vGe_iff_pInt]; simpa using hx

lemma pInt_of_vGe {x : (Qd mz)} (hx : vGe p 0 x) : pInt p x := by
  rw [vGe_iff_pInt] at hx; simpa using hx

lemma vGe_prod {ι : Type*} (s : Finset ι) (ρ : ι → ℤ) (f : ι → (Qd mz)) (h : ∀ i ∈ s, vGe p (ρ i) (f i)) :
    vGe p (∑ i ∈ s, ρ i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vGe_of_pInt (p := p) pInt_one
  | insert a s ha ih =>
      rw [prod_insert ha, sum_insert ha]
      exact vGe_mul (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

lemma vGe_pow {n : ℤ} {x : (Qd mz)} (hx : vGe p n x) (k : ℕ) : vGe p (k * n) (x ^ k) := by
  induction k with
  | zero => simpa using vGe_of_pInt (p := p) pInt_one
  | succ k ih => rw [pow_succ]; convert vGe_mul ih hx using 1; push_cast; ring

/-- A rational `r` has `v_p(r) ≥ v_p(r)`. -/
lemma vGe_ratCast (r : ℚ) : vGe p (padicValRat p r) (r : (Qd mz)) := by
  by_cases hr : r = 0
  · subst hr; simpa using vGe_zero (p := p) _
  rw [vGe_iff_pInt, Algebra.smul_def, eq_ratCast, ← Rat.cast_mul]
  refine pInt_ratCast ?_
  rw [padicNorm.mul, padicNorm_p_zpow, padicNorm.eq_zpow_of_nonzero hr, neg_neg, ← zpow_add₀ (by
    exact_mod_cast hp.out.ne_zero)]
  simp

/-- Rational `r` with `|r|_p ≤ p^{−n}`. -/
lemma vGe_ratCast_of_padicNorm {r : ℚ} {n : ℤ} (hr : padicNorm p r ≤ (p : ℚ) ^ (-n)) : vGe p n (r : (Qd mz)) := by
  rw [vGe_iff_pInt, Algebra.smul_def, eq_ratCast, ← Rat.cast_mul]
  refine pInt_ratCast ?_
  rw [padicNorm.mul, padicNorm_p_zpow, neg_neg]
  have hp0 : (0 : ℚ) < (p : ℚ) ^ n := zpow_pos (by exact_mod_cast hp.out.pos) n
  calc (p : ℚ) ^ n * padicNorm p r ≤ (p : ℚ) ^ n * (p : ℚ) ^ (-n) := by gcongr
    _ = 1 := by rw [← zpow_add₀ (by exact_mod_cast hp.out.ne_zero)]; simp

/-- Extraction: `vGe p n (r : Q5) → |r|_p ≤ p^{−n}`. -/
lemma padicNorm_le_of_vGe {r : ℚ} {n : ℤ} (h : vGe p n (r : (Qd mz))) : padicNorm p r ≤ (p : ℚ) ^ (-n) := by
  rw [vGe_iff_pInt, Algebra.smul_def, eq_ratCast, ← Rat.cast_mul] at h
  have h1 := padicNorm_le_one_of_pInt_ratCast h
  rw [padicNorm.mul, padicNorm_p_zpow, neg_neg] at h1
  have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpos : (0 : ℚ) ≤ (p : ℚ) ^ (-n) := (zpow_pos (by exact_mod_cast hp.out.pos) _).le
  calc padicNorm p r = (p : ℚ) ^ (-n) * ((p : ℚ) ^ n * padicNorm p r) := by
        rw [← mul_assoc, ← zpow_add₀ hpne]; simp
    _ ≤ (p : ℚ) ^ (-n) * 1 := by gcongr
    _ = (p : ℚ) ^ (-n) := mul_one _

lemma vGe_zK_zpow (k : ℤ) : vGe p 0 ((zK mz) ^ k) := vGe_of_pInt (pInt_zK_zpow k)

/-- Leibniz: row bounds give a bound on the determinant. -/
theorem vGe_det {k : ℕ} (M : Matrix (Fin k) (Fin k) (Qd mz)) (ρ : Fin k → ℤ) (h : ∀ i j, vGe p (ρ i) (M i j)) :
    vGe p (∑ i, ρ i) M.det := by
  rw [Matrix.det_apply]
  refine vGe_sum _ _ (fun σ _ => ?_)
  have hprod : vGe p (∑ i, ρ (σ i)) (∏ i, M (σ i) i) := vGe_prod _ _ _ (fun i _ => h (σ i) i)
  rw [Equiv.sum_comp σ ρ] at hprod
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
  · simpa using hprod
  · simpa using vGe_neg hprod

/-! ### Coefficientwise bounds on `ℚ(√5)[X]` -/

/-- `v_p(F) ≥ n` coefficientwise. -/
def vGeX (p : ℕ) (n : ℤ) (F : (Qd mz)[X]) : Prop := ∀ k, vGe p n (F.coeff k)

lemma vGeX_add {n : ℤ} {F G : (Qd mz)[X]} (hF : vGeX p n F) (hG : vGeX p n G) : vGeX p n (F + G) := fun k => by
  rw [coeff_add]; exact vGe_add (hF k) (hG k)

lemma vGeX_neg {n : ℤ} {F : (Qd mz)[X]} (hF : vGeX p n F) : vGeX p n (-F) := fun k => by
  rw [coeff_neg]; exact vGe_neg (hF k)

lemma vGeX_sum {ι : Type*} (s : Finset ι) {n : ℤ} (F : ι → (Qd mz)[X]) (h : ∀ i ∈ s, vGeX p n (F i)) :
    vGeX p n (∑ i ∈ s, F i) := fun k => by
  rw [finsetSum_coeff]; exact vGe_sum _ _ (fun i hi => h i hi k)

lemma vGeX_C {n : ℤ} {x : (Qd mz)} (hx : vGe p n x) : vGeX p n (C x) := fun k => by
  rw [coeff_C]; split_ifs
  · exact hx
  · exact vGe_zero n

lemma vGeX_X_mul {n : ℤ} {F : (Qd mz)[X]} (hF : vGeX p n F) : vGeX p n (X * F) := fun k => by
  rcases k with _ | k
  · simpa using vGe_zero (p := p) n
  · rw [coeff_X_mul]; exact hF k

lemma vGeX_mul {n m : ℤ} {F G : (Qd mz)[X]} (hF : vGeX p n F) (hG : vGeX p m G) : vGeX p (n + m) (F * G) :=
  fun k => by
    rw [coeff_mul]; exact vGe_sum _ _ (fun x _ => vGe_mul (hF x.1) (hG x.2))

lemma vGeX_one : vGeX p 0 (1 : (Qd mz)[X]) := by
  rw [← C_1]; exact vGeX_C (vGe_of_pInt pInt_one)

lemma vGeX_prod {ι : Type*} (s : Finset ι) (ρ : ι → ℤ) (F : ι → (Qd mz)[X]) (h : ∀ i ∈ s, vGeX p (ρ i) (F i)) :
    vGeX p (∑ i ∈ s, ρ i) (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vGeX_one (p := p)
  | insert a s ha ih =>
      rw [prod_insert ha, sum_insert ha]
      exact vGeX_mul (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

/-- Leibniz for polynomial matrices. -/
theorem vGeX_det {k : ℕ} (M : Matrix (Fin k) (Fin k) (Qd mz)[X]) (ρ : Fin k → ℤ) (h : ∀ i j, vGeX p (ρ i) (M i j)) :
    vGeX p (∑ i, ρ i) M.det := by
  rw [Matrix.det_apply]
  refine vGeX_sum _ _ (fun σ _ => ?_)
  have hprod : vGeX p (∑ i, ρ (σ i)) (∏ i, M (σ i) i) := vGeX_prod _ _ _ (fun i _ => h (σ i) i)
  rw [Equiv.sum_comp σ ρ] at hprod
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
  · simpa using hprod
  · simpa using vGeX_neg hprod

/-- From `ℚ(√5)[X]` back to `ℚ[X]`. -/
lemma padicNorm_coeff_of_vGeX_map {P : ℚ[X]} {n : ℤ} (h : vGeX p n (P.map (algebraMap ℚ (Qd mz)))) (k : ℕ) :
    padicNorm p (P.coeff k) ≤ (p : ℚ) ^ (-n) := by
  have := h k
  rw [coeff_map, eq_ratCast] at this
  exact padicNorm_le_of_vGe this

end Chi2U
