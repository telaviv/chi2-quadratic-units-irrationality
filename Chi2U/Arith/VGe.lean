/-
# `p`-adic valuations on `ℚ(√d)`, `d = (az/2)² + 1`: the `vGe` API (analogue of lean_chi2's `Arith/Gauss.lean`)

`pInt p x` (`Arith/Defs.lean`): `x ∈ O_p = ℤ_(p)[ω]`, basis `{1, ω}`, `ω = s + t√d` (`omS`, `omT`): `(1 + √d)/2`
for `az ≡ 0 mod 4`, `√d` for `az ≡ 2 mod 4`, `1/2 + √d` for odd `az`; a subring since `ω² = 2s·ω + (t²d − s²)` with
`2s ∈ {0, 1}` and `t²d − s² ∈ ℕ` (`exists_omN`). Uniform description `pInt_iff_omega`; case descriptions
`pInt_iff_four_dvd`, `pInt_iff_two_mod_four`, `pInt_iff_odd`. Membership only ever yields lower bounds on valuations.
`vGe p n x` (defined in `Arith/Defs.lean`) is `pInt p (p^{−n} • x)`.

Closure lemmas (`add`, `mul`, `sum`, `prod`, `pow`, units `z^k`), rational elements, the extraction
`vGe p n (r : Q5) → |r|_p ≤ p^{−n}`, the Leibniz bound for determinants (`vGe_det`), and the coefficientwise
version `vGeX` for `ℚ(√5)[X]` (`vGeX_mul`, `vGeX_det`, `padicNorm_coeff_of_vGeX_map`).
-/
import Chi2U.Arith.Defs

namespace Chi2U

variable {az : ℕ} [Fact (1 ≤ az)]

open Polynomial Finset

variable {p : ℕ} [hp : Fact p.Prime]

lemma pInt_iff_four_dvd (h : az % 4 = 0) (x : Qd az) :
    pInt p x ↔ padicNorm p (x.re - x.im) ≤ 1 ∧ padicNorm p (2 * x.im) ≤ 1 := by
  rw [pInt, if_pos h]

lemma pInt_iff_two_mod_four (h : az % 4 = 2) (x : Qd az) :
    pInt p x ↔ padicNorm p x.re ≤ 1 ∧ padicNorm p x.im ≤ 1 := by
  rw [pInt, if_neg (by omega), if_pos h]

lemma pInt_iff_odd (h : az % 2 = 1) (x : Qd az) :
    pInt p x ↔ padicNorm p (x.re - x.im / 2) ≤ 1 ∧ padicNorm p x.im ≤ 1 := by
  rw [pInt, if_neg (by omega), if_neg (by omega)]

lemma vGe_iff_pInt (n : ℤ) (x : Qd az) : vGe p n x ↔ pInt p (((p : ℚ) ^ (-n) : ℚ) • x) := by rw [vGe]

omit [Fact (1 ≤ az)] in
lemma omT_ne_zero : omT az ≠ 0 := by unfold omT; split_ifs <;> norm_num

omit [Fact (1 ≤ az)] in
/-- The three cases of the basis `{1, ω}`, `ω = omS + omT·√d`. -/
lemma omS_omT_cases : (az % 4 = 0 ∧ omS az = 1 / 2 ∧ omT az = 1 / 2) ∨ (az % 4 = 2 ∧ omS az = 0 ∧ omT az = 1) ∨
    (az % 2 = 1 ∧ omS az = 1 / 2 ∧ omT az = 1) := by
  unfold omS omT
  by_cases h0 : az % 4 = 0
  · left; exact ⟨h0, by rw [if_neg (by omega)], by rw [if_pos h0]⟩
  by_cases h2 : az % 4 = 2
  · right; left; exact ⟨h2, by rw [if_pos h2], by rw [if_neg h0]⟩
  · right; right; exact ⟨by omega, by rw [if_neg h2], by rw [if_neg h0]⟩

/-- Uniform form of `pInt`: the coordinates `re − (s/t)·im`, `im/t` of `x` in the basis `{1, ω}`, `ω = s + t√d`
(`s = omS az`, `t = omT az`), are `p`-integral. -/
lemma pInt_iff_omega (x : Qd az) :
    pInt p x ↔ padicNorm p (x.re - omS az / omT az * x.im) ≤ 1 ∧ padicNorm p (x.im / omT az) ≤ 1 := by
  rcases omS_omT_cases (az := az) with ⟨h, hS, hT⟩ | ⟨h, hS, hT⟩ | ⟨h, hS, hT⟩ <;> rw [hS, hT]
  · rw [pInt_iff_four_dvd h, show (1 / 2 : ℚ) / (1 / 2) * x.im = x.im by ring,
      show x.im / (1 / 2 : ℚ) = 2 * x.im by ring]
  · rw [pInt_iff_two_mod_four h]; simp
  · rw [pInt_iff_odd h, show (1 / 2 : ℚ) / 1 * x.im = x.im / 2 by ring, div_one]

omit [Fact (1 ≤ az)] hp in
/-- `2s ∈ ℤ` (`ω² = 2s·ω + (t²d − s²)`). -/
lemma padicNorm_two_omS_le : padicNorm p (2 * omS az) ≤ 1 := by
  unfold omS; split_ifs <;> norm_num

omit [Fact (1 ≤ az)] in
/-- `t²d − s² ∈ ℕ`: `(az/4)²`, `(az/2)² + 1`, `(az² + 3)/4` in the three cases. -/
lemma exists_omN : ∃ n : ℕ, omT az ^ 2 * dQ az - omS az ^ 2 = n := by
  rw [dQ_eq]
  rcases omS_omT_cases (az := az) with ⟨h, hS, hT⟩ | ⟨h, hS, hT⟩ | ⟨h, hS, hT⟩ <;> rw [hS, hT]
  · obtain ⟨k, hk⟩ : ∃ k, az = 4 * k := ⟨az / 4, by omega⟩
    exact ⟨k ^ 2, by rw [hk]; push_cast; ring⟩
  · obtain ⟨k, hk⟩ : ∃ k, az = 4 * k + 2 := ⟨az / 4, by omega⟩
    exact ⟨(2 * k + 1) ^ 2 + 1, by rw [hk]; push_cast; ring⟩
  · obtain ⟨k, hk⟩ : ∃ k, az = 2 * k + 1 := ⟨az / 2, by omega⟩
    exact ⟨k ^ 2 + k + 1, by rw [hk]; push_cast; ring⟩

omit [Fact (1 ≤ az)] in
lemma padicNorm_omN_le : padicNorm p (omT az ^ 2 * dQ az - omS az ^ 2) ≤ 1 := by
  obtain ⟨n, hn⟩ := exists_omN (az := az); rw [hn]; exact padicNorm.of_nat n

omit [Fact (1 ≤ az)] in
lemma padicNorm_le_one_of_eq_int {q : ℚ} (z : ℤ) (h : q = z) : padicNorm p q ≤ 1 := h ▸ padicNorm.of_int z

/-- Elements with integral coordinates in the basis `{1, ω}` lie in `O_p`. -/
lemma pInt_of_int_coords {x : Qd az} (u v : ℤ) (hu : x.re - omS az / omT az * x.im = u) (hv : x.im / omT az = v) :
    pInt p x := by
  rw [pInt_iff_omega, hu, hv]; exact ⟨padicNorm.of_int u, padicNorm.of_int v⟩

/-- Elements with `p`-integral coordinates `re`, `im` lie in `O_p` when `p` is odd or the trace `az` is even (for odd
`az`, `√d = ω − 1/2 ∉ O_2`). -/
lemma pInt_of_coords (hp2 : p ≠ 2 ∨ Even az) {x : Qd az} (hre : padicNorm p x.re ≤ 1) (him : padicNorm p x.im ≤ 1) :
    pInt p x := by
  rcases omS_omT_cases (az := az) with ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩
  · rw [pInt_iff_four_dvd h]
    refine ⟨(padicNorm.sub).trans (max_le hre him), ?_⟩
    rw [padicNorm.mul]
    have : padicNorm p (2 : ℚ) ≤ 1 := by simpa using padicNorm.of_nat (p := p) 2
    nlinarith [padicNorm.nonneg (p := p) x.im, padicNorm.nonneg (p := p) (2 : ℚ)]
  · exact (pInt_iff_two_mod_four h x).mpr ⟨hre, him⟩
  · rw [pInt_iff_odd h]
    have hp2' : p ≠ 2 := hp2.resolve_right (by rintro ⟨k, hk⟩; omega)
    have h2 : padicNorm p (2 : ℚ) = 1 := by
      have := (padicNorm.nat_eq_one_iff (p := p) 2).mpr
        (fun hd => hp2' ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hd))
      simpa using this
    refine ⟨(padicNorm.sub).trans (max_le hre ?_), him⟩
    rw [padicNorm.div, h2, div_one]; exact him

lemma pInt_zero : pInt p (0 : Qd az) := pInt_of_int_coords 0 0 (by simp) (by simp)

lemma pInt_add {x y : Qd az} (hx : pInt p x) (hy : pInt p y) : pInt p (x + y) := by
  rw [pInt_iff_omega] at *
  refine ⟨?_, ?_⟩
  · have : (x + y).re - omS az / omT az * (x + y).im =
        (x.re - omS az / omT az * x.im) + (y.re - omS az / omT az * y.im) := by
      simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]; ring
    rw [this]; exact (padicNorm.nonarchimedean).trans (max_le hx.1 hy.1)
  · have : (x + y).im / omT az = x.im / omT az + y.im / omT az := by
      simp only [QuadraticAlgebra.im_add]; ring
    rw [this]; exact (padicNorm.nonarchimedean).trans (max_le hx.2 hy.2)

lemma pInt_neg {x : Qd az} (hx : pInt p x) : pInt p (-x) := by
  rw [pInt_iff_omega] at *
  refine ⟨?_, ?_⟩
  · have : (-x).re - omS az / omT az * (-x).im = -(x.re - omS az / omT az * x.im) := by
      simp only [QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg]; ring
    rw [this, padicNorm.neg]; exact hx.1
  · have : (-x).im / omT az = -(x.im / omT az) := by simp only [QuadraticAlgebra.im_neg]; ring
    rw [this, padicNorm.neg]; exact hx.2

lemma pInt_sub {x y : Qd az} (hx : pInt p x) (hy : pInt p y) : pInt p (x - y) := by
  rw [sub_eq_add_neg]; exact pInt_add hx (pInt_neg hy)

/-- `O_p` is a ring: `(a₁ + b₁ω)(a₂ + b₂ω) = (a₁a₂ + b₁b₂N) + (a₁b₂ + b₁a₂ + 2s·b₁b₂)ω`, `N = t²d − s²`. -/
lemma pInt_mul {x y : Qd az} (hx : pInt p x) (hy : pInt p y) : pInt p (x * y) := by
  have hn : ∀ u v : ℚ, padicNorm p u ≤ 1 → padicNorm p v ≤ 1 → padicNorm p (u * v) ≤ 1 := fun u v hu hv => by
    rw [padicNorm.mul]; nlinarith [padicNorm.nonneg (p := p) u, padicNorm.nonneg (p := p) v]
  have hadd : ∀ u v : ℚ, padicNorm p u ≤ 1 → padicNorm p v ≤ 1 → padicNorm p (u + v) ≤ 1 := fun u v hu hv =>
    (padicNorm.nonarchimedean).trans (max_le hu hv)
  rw [pInt_iff_omega] at *
  have hT := omT_ne_zero (az := az)
  have hN := padicNorm_omN_le (p := p) (az := az)
  have h2S := padicNorm_two_omS_le (p := p) (az := az)
  set S := omS az
  set T := omT az
  set a₁ := x.re - S / T * x.im with ha₁
  set b₁ := x.im / T with hb₁
  set a₂ := y.re - S / T * y.im with ha₂
  set b₂ := y.im / T with hb₂
  refine ⟨?_, ?_⟩
  · have : (x * y).re - S / T * (x * y).im = a₁ * a₂ + b₁ * b₂ * (T ^ 2 * dQ az - S ^ 2) := by
      simp only [ha₁, hb₁, ha₂, hb₂, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
      field_simp
      ring
    rw [this]; exact hadd _ _ (hn _ _ hx.1 hy.1) (hn _ _ (hn _ _ hx.2 hy.2) hN)
  · have : (x * y).im / T = a₁ * b₂ + b₁ * a₂ + b₁ * b₂ * (2 * S) := by
      simp only [ha₁, hb₁, ha₂, hb₂, QuadraticAlgebra.im_mul]
      field_simp
      ring
    rw [this]
    exact hadd _ _ (hadd _ _ (hn _ _ hx.1 hy.2) (hn _ _ hx.2 hy.1)) (hn _ _ (hn _ _ hx.2 hy.2) h2S)

lemma pInt_ratCast {r : ℚ} (hr : padicNorm p r ≤ 1) : pInt p (r : Qd az) := by
  rw [pInt_iff_omega]; exact ⟨by simpa using hr, by simp⟩

lemma pInt_one : pInt p (1 : Qd az) := by simpa using pInt_ratCast (az := az) (p := p) (r := 1) (by simp)

lemma pInt_natCast (n : ℕ) : pInt p (n : Qd az) := by
  simpa using pInt_ratCast (az := az) (p := p) (r := n) (padicNorm.of_nat n)

lemma pInt_intCast (n : ℤ) : pInt p (n : Qd az) := by
  simpa using pInt_ratCast (az := az) (p := p) (r := n) (padicNorm.of_int n)

lemma pInt_sum {ι : Type*} (s : Finset ι) (f : ι → Qd az) (h : ∀ i ∈ s, pInt p (f i)) :
    pInt p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pInt_zero (az := az) (p := p)
  | insert a s ha ih =>
      rw [sum_insert ha]
      exact pInt_add (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

lemma pInt_prod {ι : Type*} (s : Finset ι) (f : ι → Qd az) (h : ∀ i ∈ s, pInt p (f i)) :
    pInt p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pInt_one (az := az) (p := p)
  | insert a s ha ih =>
      rw [prod_insert ha]
      exact pInt_mul (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

lemma pInt_pow {x : Qd az} (hx : pInt p x) (n : ℕ) : pInt p (x ^ n) := by
  induction n with
  | zero => simpa using pInt_one (az := az) (p := p)
  | succ n ih => rw [pow_succ]; exact pInt_mul ih hx

lemma pInt_zK : pInt p (zK az) := by
  rw [pInt_iff_omega, show (zK az).re = -(az : ℚ) / 2 from rfl, show (zK az).im = 1 from rfl]
  rcases omS_omT_cases (az := az) with ⟨h, hS, hT⟩ | ⟨h, hS, hT⟩ | ⟨h, hS, hT⟩ <;> rw [hS, hT]
  · obtain ⟨k, hk⟩ : ∃ k, az = 4 * k := ⟨az / 4, by omega⟩
    exact ⟨padicNorm_le_one_of_eq_int (-(2 * k + 1)) (by rw [hk]; push_cast; ring),
      padicNorm_le_one_of_eq_int 2 (by norm_num)⟩
  · obtain ⟨k, hk⟩ : ∃ k, az = 4 * k + 2 := ⟨az / 4, by omega⟩
    exact ⟨padicNorm_le_one_of_eq_int (-(2 * k + 1)) (by rw [hk]; push_cast; ring),
      padicNorm_le_one_of_eq_int 1 (by norm_num)⟩
  · obtain ⟨k, hk⟩ : ∃ k, az = 2 * k + 1 := ⟨az / 2, by omega⟩
    exact ⟨padicNorm_le_one_of_eq_int (-(k + 1)) (by rw [hk]; push_cast; ring),
      padicNorm_le_one_of_eq_int 1 (by norm_num)⟩

lemma pInt_zK_inv : pInt p (zK az)⁻¹ := by
  rw [pInt_iff_omega, zK_inv]
  rcases omS_omT_cases (az := az) with ⟨h, hS, hT⟩ | ⟨h, hS, hT⟩ | ⟨h, hS, hT⟩ <;> rw [hS, hT]
  · obtain ⟨k, hk⟩ : ∃ k, az = 4 * k := ⟨az / 4, by omega⟩
    exact ⟨padicNorm_le_one_of_eq_int (2 * k - 1) (by rw [hk]; push_cast; ring),
      padicNorm_le_one_of_eq_int 2 (by norm_num)⟩
  · obtain ⟨k, hk⟩ : ∃ k, az = 4 * k + 2 := ⟨az / 4, by omega⟩
    exact ⟨padicNorm_le_one_of_eq_int (2 * k + 1) (by rw [hk]; push_cast; ring),
      padicNorm_le_one_of_eq_int 1 (by norm_num)⟩
  · obtain ⟨k, hk⟩ : ∃ k, az = 2 * k + 1 := ⟨az / 2, by omega⟩
    exact ⟨padicNorm_le_one_of_eq_int k (by rw [hk]; push_cast; ring),
      padicNorm_le_one_of_eq_int 1 (by norm_num)⟩

lemma pInt_zK_zpow (k : ℤ) : pInt p ((zK az) ^ k) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · simpa using pInt_pow pInt_zK n
  · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pInt_pow pInt_zK_inv n

lemma pInt_smul {r : ℚ} (hr : padicNorm p r ≤ 1) {x : Qd az} (hx : pInt p x) : pInt p (r • x) := by
  rw [Algebra.smul_def, eq_ratCast]; exact pInt_mul (pInt_ratCast hr) hx

/-- `√d ∈ O_p` for odd `p` or even trace (for odd `az`, `√d = ω − 1/2` is not `2`-integral). -/
lemma pInt_sqrtd (hp2 : p ≠ 2 ∨ Even az) : pInt p (sqrtd az) := pInt_of_coords hp2 (by simp [sqrtd]) (by simp [sqrtd])

/-- The rational part: `r ∈ O_p` gives `|r|_p ≤ 1`. -/
lemma padicNorm_le_one_of_pInt_ratCast {r : ℚ} (h : pInt p (r : Qd az)) : padicNorm p r ≤ 1 := by
  have := ((pInt_iff_omega _).mp h).1; simpa using this

/-! ### `vGe` -/

lemma padicNorm_p_zpow (n : ℤ) : padicNorm p ((p : ℚ) ^ n) = (p : ℚ) ^ (-n) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [padicNorm.eq_zpow_of_nonzero (zpow_ne_zero n hp0), padicValRat.zpow, padicValRat.self hp.out.one_lt,
    mul_one]

lemma vGe_zero (n : ℤ) : vGe p n (0 : Qd az) := by rw [vGe_iff_pInt, smul_zero]; exact pInt_zero

lemma vGe_add {n : ℤ} {x y : (Qd az)} (hx : vGe p n x) (hy : vGe p n y) : vGe p n (x + y) := by
  rw [vGe_iff_pInt] at *; rw [smul_add]; exact pInt_add hx hy

lemma vGe_neg {n : ℤ} {x : (Qd az)} (hx : vGe p n x) : vGe p n (-x) := by
  rw [vGe_iff_pInt] at *; rw [smul_neg]; exact pInt_neg hx

lemma vGe_sub {n : ℤ} {x y : (Qd az)} (hx : vGe p n x) (hy : vGe p n y) : vGe p n (x - y) := by
  rw [sub_eq_add_neg]; exact vGe_add hx (vGe_neg hy)

lemma vGe_sum {ι : Type*} (s : Finset ι) {n : ℤ} (f : ι → (Qd az)) (h : ∀ i ∈ s, vGe p n (f i)) :
    vGe p n (∑ i ∈ s, f i) := by
  rw [vGe_iff_pInt, smul_sum]; exact pInt_sum _ _ (fun i hi => (vGe_iff_pInt n _).mp (h i hi))

lemma vGe_mul {n m : ℤ} {x y : (Qd az)} (hx : vGe p n x) (hy : vGe p m y) : vGe p (n + m) (x * y) := by
  rw [vGe_iff_pInt] at *
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have : ((p : ℚ) ^ (-(n + m))) • (x * y) = ((p : ℚ) ^ (-n) • x) * ((p : ℚ) ^ (-m) • y) := by
    rw [smul_mul_smul_comm, ← zpow_add₀ hp0]; congr 2; ring
  rw [this]; exact pInt_mul hx hy

lemma vGe_mono {n m : ℤ} (hmn : m ≤ n) {x : (Qd az)} (hx : vGe p n x) : vGe p m x := by
  rw [vGe_iff_pInt] at *
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have : ((p : ℚ) ^ (-m)) • x = ((p : ℚ) ^ (n - m)) • ((p : ℚ) ^ (-n) • x) := by
    rw [smul_smul, ← zpow_add₀ hp0]; congr 2; ring
  rw [this]
  refine pInt_smul ?_ hx
  rw [padicNorm_p_zpow]
  exact zpow_le_one_of_nonpos₀ (by exact_mod_cast hp.out.one_lt.le) (by omega)

lemma vGe_of_pInt {x : (Qd az)} (hx : pInt p x) : vGe p 0 x := by
  rw [vGe_iff_pInt]; simpa using hx

lemma pInt_of_vGe {x : (Qd az)} (hx : vGe p 0 x) : pInt p x := by
  rw [vGe_iff_pInt] at hx; simpa using hx

lemma vGe_prod {ι : Type*} (s : Finset ι) (ρ : ι → ℤ) (f : ι → (Qd az)) (h : ∀ i ∈ s, vGe p (ρ i) (f i)) :
    vGe p (∑ i ∈ s, ρ i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vGe_of_pInt (p := p) pInt_one
  | insert a s ha ih =>
      rw [prod_insert ha, sum_insert ha]
      exact vGe_mul (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

lemma vGe_pow {n : ℤ} {x : (Qd az)} (hx : vGe p n x) (k : ℕ) : vGe p (k * n) (x ^ k) := by
  induction k with
  | zero => simpa using vGe_of_pInt (p := p) pInt_one
  | succ k ih => rw [pow_succ]; convert vGe_mul ih hx using 1; push_cast; ring

/-- A rational `r` has `v_p(r) ≥ v_p(r)`. -/
lemma vGe_ratCast (r : ℚ) : vGe p (padicValRat p r) (r : (Qd az)) := by
  by_cases hr : r = 0
  · subst hr; simpa using vGe_zero (p := p) _
  rw [vGe_iff_pInt, Algebra.smul_def, eq_ratCast, ← Rat.cast_mul]
  refine pInt_ratCast ?_
  rw [padicNorm.mul, padicNorm_p_zpow, padicNorm.eq_zpow_of_nonzero hr, neg_neg, ← zpow_add₀ (by
    exact_mod_cast hp.out.ne_zero)]
  simp

/-- Rational `r` with `|r|_p ≤ p^{−n}`. -/
lemma vGe_ratCast_of_padicNorm {r : ℚ} {n : ℤ} (hr : padicNorm p r ≤ (p : ℚ) ^ (-n)) : vGe p n (r : (Qd az)) := by
  rw [vGe_iff_pInt, Algebra.smul_def, eq_ratCast, ← Rat.cast_mul]
  refine pInt_ratCast ?_
  rw [padicNorm.mul, padicNorm_p_zpow, neg_neg]
  have hp0 : (0 : ℚ) < (p : ℚ) ^ n := zpow_pos (by exact_mod_cast hp.out.pos) n
  calc (p : ℚ) ^ n * padicNorm p r ≤ (p : ℚ) ^ n * (p : ℚ) ^ (-n) := by gcongr
    _ = 1 := by rw [← zpow_add₀ (by exact_mod_cast hp.out.ne_zero)]; simp

/-- Extraction: `vGe p n (r : Q5) → |r|_p ≤ p^{−n}`. -/
lemma padicNorm_le_of_vGe {r : ℚ} {n : ℤ} (h : vGe p n (r : (Qd az))) : padicNorm p r ≤ (p : ℚ) ^ (-n) := by
  rw [vGe_iff_pInt, Algebra.smul_def, eq_ratCast, ← Rat.cast_mul] at h
  have h1 := padicNorm_le_one_of_pInt_ratCast h
  rw [padicNorm.mul, padicNorm_p_zpow, neg_neg] at h1
  have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpos : (0 : ℚ) ≤ (p : ℚ) ^ (-n) := (zpow_pos (by exact_mod_cast hp.out.pos) _).le
  calc padicNorm p r = (p : ℚ) ^ (-n) * ((p : ℚ) ^ n * padicNorm p r) := by
        rw [← mul_assoc, ← zpow_add₀ hpne]; simp
    _ ≤ (p : ℚ) ^ (-n) * 1 := by gcongr
    _ = (p : ℚ) ^ (-n) := mul_one _

lemma vGe_zK_zpow (k : ℤ) : vGe p 0 ((zK az) ^ k) := vGe_of_pInt (pInt_zK_zpow k)

/-- Leibniz: row bounds give a bound on the determinant. -/
theorem vGe_det {k : ℕ} (M : Matrix (Fin k) (Fin k) (Qd az)) (ρ : Fin k → ℤ) (h : ∀ i j, vGe p (ρ i) (M i j)) :
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
def vGeX (p : ℕ) (n : ℤ) (F : (Qd az)[X]) : Prop := ∀ k, vGe p n (F.coeff k)

lemma vGeX_add {n : ℤ} {F G : (Qd az)[X]} (hF : vGeX p n F) (hG : vGeX p n G) : vGeX p n (F + G) := fun k => by
  rw [coeff_add]; exact vGe_add (hF k) (hG k)

lemma vGeX_neg {n : ℤ} {F : (Qd az)[X]} (hF : vGeX p n F) : vGeX p n (-F) := fun k => by
  rw [coeff_neg]; exact vGe_neg (hF k)

lemma vGeX_sum {ι : Type*} (s : Finset ι) {n : ℤ} (F : ι → (Qd az)[X]) (h : ∀ i ∈ s, vGeX p n (F i)) :
    vGeX p n (∑ i ∈ s, F i) := fun k => by
  rw [finsetSum_coeff]; exact vGe_sum _ _ (fun i hi => h i hi k)

lemma vGeX_C {n : ℤ} {x : (Qd az)} (hx : vGe p n x) : vGeX p n (C x) := fun k => by
  rw [coeff_C]; split_ifs
  · exact hx
  · exact vGe_zero n

lemma vGeX_X_mul {n : ℤ} {F : (Qd az)[X]} (hF : vGeX p n F) : vGeX p n (X * F) := fun k => by
  rcases k with _ | k
  · simpa using vGe_zero (p := p) n
  · rw [coeff_X_mul]; exact hF k

lemma vGeX_mul {n m : ℤ} {F G : (Qd az)[X]} (hF : vGeX p n F) (hG : vGeX p m G) : vGeX p (n + m) (F * G) :=
  fun k => by
    rw [coeff_mul]; exact vGe_sum _ _ (fun x _ => vGe_mul (hF x.1) (hG x.2))

lemma vGeX_one : vGeX p 0 (1 : (Qd az)[X]) := by
  rw [← C_1]; exact vGeX_C (vGe_of_pInt pInt_one)

lemma vGeX_prod {ι : Type*} (s : Finset ι) (ρ : ι → ℤ) (F : ι → (Qd az)[X]) (h : ∀ i ∈ s, vGeX p (ρ i) (F i)) :
    vGeX p (∑ i ∈ s, ρ i) (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vGeX_one (p := p)
  | insert a s ha ih =>
      rw [prod_insert ha, sum_insert ha]
      exact vGeX_mul (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

/-- Leibniz for polynomial matrices. -/
theorem vGeX_det {k : ℕ} (M : Matrix (Fin k) (Fin k) (Qd az)[X]) (ρ : Fin k → ℤ) (h : ∀ i j, vGeX p (ρ i) (M i j)) :
    vGeX p (∑ i, ρ i) M.det := by
  rw [Matrix.det_apply]
  refine vGeX_sum _ _ (fun σ _ => ?_)
  have hprod : vGeX p (∑ i, ρ (σ i)) (∏ i, M (σ i) i) := vGeX_prod _ _ _ (fun i _ => h (σ i) i)
  rw [Equiv.sum_comp σ ρ] at hprod
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
  · simpa using hprod
  · simpa using vGeX_neg hprod

/-- From `ℚ(√5)[X]` back to `ℚ[X]`. -/
lemma padicNorm_coeff_of_vGeX_map {P : ℚ[X]} {n : ℤ} (h : vGeX p n (P.map (algebraMap ℚ (Qd az)))) (k : ℕ) :
    padicNorm p (P.coeff k) ≤ (p : ℚ) ^ (-n) := by
  have := h k
  rw [coeff_map, eq_ratCast] at this
  exact padicNorm_le_of_vGe this

end Chi2U
