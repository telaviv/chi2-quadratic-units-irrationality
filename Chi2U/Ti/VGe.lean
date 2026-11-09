/-
# Theorem V_i: `p`-adic valuations on `ℚ(√d)`, `d = (n/2)² − 1`: the `vGe` API

**Copy of the `pInt`/`vGe` part of `Chi2U/Arith/Defs.lean` and of `Chi2U/Arith/VGe.lean`**, for the field `Qt n` of
the norm `+1` units (trace `n ≥ 3`). Only the order `O_p` changes (two cases instead of three):
* `n` even (`n = 2k`, `d = k² − 1`): `O_p = ℤ_(p)[√d]`, `ω = √d` (`z = k − √d`);
* `n` odd (`d = (n² − 4)/4`, `n² − 4 ≡ 5 mod 8`): `O_p = ℤ_(p)[ω]`, `ω = 1/2 + √d = (1 + √(n² − 4))/2`
  (`ω² = ω + (n² − 5)/4`), as for odd `az` in the χ₂ files.
For odd `p` both are `ℤ_(p)[√d]`. `O_p` is a subring (`pInt_mul`) contained in the integral closure, so membership gives
**lower bounds** on the valuations at every prime above `p` (all that is used). For `n ≡ 2 mod 4` (`d ≡ 0 mod 8`)
`ℤ_(2)[√d]` is not the maximal order; this only weakens 2-adic lower bounds, never makes them wrong.

`vGe p v x` is `pInt p (p^{−v} • x)`. Closure lemmas (`add`, `mul`, `sum`, `prod`, `pow`, units `z^k`), rational
elements, the extraction `vGe p v (r : Qt n) → |r|_p ≤ p^{−v}`, the Leibniz bound for determinants (`vGe_det`), and the
coefficientwise version `vGeX` (`vGeX_mul`, `vGeX_det`, `padicNorm_coeff_of_vGeX_map`). The integer level is called `v`
(`w`) here (it is `n` (`m`) in the χ₂ file, where `n` is free).
-/
import Chi2U.Ti.Field

set_option linter.unusedSectionVars false

namespace Chi2U
namespace Ti

open Polynomial Finset

/-- The basis `{1, ω}` of `O_p`, `ω = omS n + omT n · √d`: `ω = √d` for even `n`, `ω = 1/2 + √d` for odd `n`. -/
def omS (n : ℕ) : ℚ := if n % 2 = 0 then 0 else 1 / 2

/-- See `omS`. -/
def omT (_n : ℕ) : ℚ := 1

/-- `x ∈ O_p` (see the module docstring): the coordinates of `x` in the basis `{1, ω}` are `p`-integral. -/
@[irreducible] def pInt {n : ℕ} (p : ℕ) (x : Qt n) : Prop :=
  if n % 2 = 0 then padicNorm p x.re ≤ 1 ∧ padicNorm p x.im ≤ 1
  else padicNorm p (x.re - x.im / 2) ≤ 1 ∧ padicNorm p x.im ≤ 1

/-- `v_p(x) ≥ v` for `x ∈ ℚ(√d)`: `x/p^v ∈ O_p` (`pInt`). -/
@[irreducible] def vGe {n : ℕ} (p : ℕ) (v : ℤ) (x : Qt n) : Prop := pInt p (((p : ℚ) ^ (-v) : ℚ) • x)

variable {n : ℕ} [Fact (3 ≤ n)]

variable {p : ℕ} [hp : Fact p.Prime]

lemma pInt_iff_even (h : n % 2 = 0) (x : Qt n) :
    pInt p x ↔ padicNorm p x.re ≤ 1 ∧ padicNorm p x.im ≤ 1 := by
  rw [pInt, if_pos h]

lemma pInt_iff_odd (h : n % 2 = 1) (x : Qt n) :
    pInt p x ↔ padicNorm p (x.re - x.im / 2) ≤ 1 ∧ padicNorm p x.im ≤ 1 := by
  rw [pInt, if_neg (by omega)]

lemma vGe_iff_pInt (v : ℤ) (x : Qt n) : vGe p v x ↔ pInt p (((p : ℚ) ^ (-v) : ℚ) • x) := by rw [vGe]

omit [Fact (3 ≤ n)] in
lemma omT_ne_zero : omT n ≠ 0 := by unfold omT; norm_num

omit [Fact (3 ≤ n)] in
/-- The two cases of the basis `{1, ω}`, `ω = omS + omT·√d`. -/
lemma omS_omT_cases : (n % 2 = 0 ∧ omS n = 0 ∧ omT n = 1) ∨ (n % 2 = 1 ∧ omS n = 1 / 2 ∧ omT n = 1) := by
  unfold omS omT
  by_cases h0 : n % 2 = 0
  · left; exact ⟨h0, by rw [if_pos h0], rfl⟩
  · right; exact ⟨by omega, by rw [if_neg h0], rfl⟩

/-- Uniform form of `pInt`: the coordinates `re − (s/t)·im`, `im/t` of `x` in the basis `{1, ω}`, `ω = s + t√d`, are
`p`-integral. -/
lemma pInt_iff_omega (x : Qt n) :
    pInt p x ↔ padicNorm p (x.re - omS n / omT n * x.im) ≤ 1 ∧ padicNorm p (x.im / omT n) ≤ 1 := by
  rcases omS_omT_cases (n := n) with ⟨h, hS, hT⟩ | ⟨h, hS, hT⟩ <;> rw [hS, hT]
  · rw [pInt_iff_even h]; simp
  · rw [pInt_iff_odd h, show (1 / 2 : ℚ) / 1 * x.im = x.im / 2 by ring, div_one]

omit [Fact (3 ≤ n)] hp in
/-- `2s ∈ ℤ` (`ω² = 2s·ω + (t²d − s²)`). -/
lemma padicNorm_two_omS_le : padicNorm p (2 * omS n) ≤ 1 := by
  unfold omS; split_ifs <;> norm_num

/-- `t²d − s² ∈ ℕ`: `k² − 1` for `n = 2k`, `k² + k − 1` for `n = 2k + 1` (`n ≥ 3`). -/
lemma exists_omN : ∃ N : ℕ, omT n ^ 2 * dT n - omS n ^ 2 = N := by
  rw [dT_eq]
  have h3 := (Fact.out : 3 ≤ n)
  rcases omS_omT_cases (n := n) with ⟨h, hS, hT⟩ | ⟨h, hS, hT⟩ <;> rw [hS, hT]
  · obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 4 := ⟨n / 2 - 2, by omega⟩
    exact ⟨(k + 2) ^ 2 - 1, by
      rw [Nat.cast_sub (by nlinarith), hk]; push_cast; ring⟩
  · obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 3 := ⟨n / 2 - 1, by omega⟩
    exact ⟨(k + 1) ^ 2 + (k + 1) - 1, by
      rw [Nat.cast_sub (by nlinarith), hk]; push_cast; ring⟩

lemma padicNorm_omN_le : padicNorm p (omT n ^ 2 * dT n - omS n ^ 2) ≤ 1 := by
  obtain ⟨N, hN⟩ := exists_omN (n := n); rw [hN]; exact padicNorm.of_nat N

omit [Fact (3 ≤ n)] in
lemma padicNorm_le_one_of_eq_int {q : ℚ} (z : ℤ) (h : q = z) : padicNorm p q ≤ 1 := h ▸ padicNorm.of_int z

/-- Elements with integral coordinates in the basis `{1, ω}` lie in `O_p`. -/
lemma pInt_of_int_coords {x : Qt n} (u v : ℤ) (hu : x.re - omS n / omT n * x.im = u) (hv : x.im / omT n = v) :
    pInt p x := by
  rw [pInt_iff_omega, hu, hv]; exact ⟨padicNorm.of_int u, padicNorm.of_int v⟩

/-- Elements with `p`-integral coordinates `re`, `im` lie in `O_p` when `p` is odd or the trace `n` is even (for odd
`n`, `√d = ω − 1/2 ∉ O_2`). -/
lemma pInt_of_coords (hp2 : p ≠ 2 ∨ Even n) {x : Qt n} (hre : padicNorm p x.re ≤ 1) (him : padicNorm p x.im ≤ 1) :
    pInt p x := by
  rcases omS_omT_cases (n := n) with ⟨h, -, -⟩ | ⟨h, -, -⟩
  · exact (pInt_iff_even h x).mpr ⟨hre, him⟩
  · rw [pInt_iff_odd h]
    have hp2' : p ≠ 2 := hp2.resolve_right (by rintro ⟨k, hk⟩; omega)
    have h2 : padicNorm p (2 : ℚ) = 1 := by
      have := (padicNorm.nat_eq_one_iff (p := p) 2).mpr
        (fun hd => hp2' ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hd))
      simpa using this
    refine ⟨(padicNorm.sub).trans (max_le hre ?_), him⟩
    rw [padicNorm.div, h2, div_one]; exact him

lemma pInt_zero : pInt p (0 : Qt n) := pInt_of_int_coords 0 0 (by simp) (by simp)

lemma pInt_add {x y : Qt n} (hx : pInt p x) (hy : pInt p y) : pInt p (x + y) := by
  rw [pInt_iff_omega] at *
  refine ⟨?_, ?_⟩
  · have : (x + y).re - omS n / omT n * (x + y).im =
        (x.re - omS n / omT n * x.im) + (y.re - omS n / omT n * y.im) := by
      simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]; ring
    rw [this]; exact (padicNorm.nonarchimedean).trans (max_le hx.1 hy.1)
  · have : (x + y).im / omT n = x.im / omT n + y.im / omT n := by
      simp only [QuadraticAlgebra.im_add]; ring
    rw [this]; exact (padicNorm.nonarchimedean).trans (max_le hx.2 hy.2)

lemma pInt_neg {x : Qt n} (hx : pInt p x) : pInt p (-x) := by
  rw [pInt_iff_omega] at *
  refine ⟨?_, ?_⟩
  · have : (-x).re - omS n / omT n * (-x).im = -(x.re - omS n / omT n * x.im) := by
      simp only [QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg]; ring
    rw [this, padicNorm.neg]; exact hx.1
  · have : (-x).im / omT n = -(x.im / omT n) := by simp only [QuadraticAlgebra.im_neg]; ring
    rw [this, padicNorm.neg]; exact hx.2

lemma pInt_sub {x y : Qt n} (hx : pInt p x) (hy : pInt p y) : pInt p (x - y) := by
  rw [sub_eq_add_neg]; exact pInt_add hx (pInt_neg hy)

/-- `O_p` is a ring: `(a₁ + b₁ω)(a₂ + b₂ω) = (a₁a₂ + b₁b₂N) + (a₁b₂ + b₁a₂ + 2s·b₁b₂)ω`, `N = t²d − s²`. -/
lemma pInt_mul {x y : Qt n} (hx : pInt p x) (hy : pInt p y) : pInt p (x * y) := by
  have hn : ∀ u v : ℚ, padicNorm p u ≤ 1 → padicNorm p v ≤ 1 → padicNorm p (u * v) ≤ 1 := fun u v hu hv => by
    rw [padicNorm.mul]; nlinarith [padicNorm.nonneg (p := p) u, padicNorm.nonneg (p := p) v]
  have hadd : ∀ u v : ℚ, padicNorm p u ≤ 1 → padicNorm p v ≤ 1 → padicNorm p (u + v) ≤ 1 := fun u v hu hv =>
    (padicNorm.nonarchimedean).trans (max_le hu hv)
  rw [pInt_iff_omega] at *
  have hT := omT_ne_zero (n := n)
  have hN := padicNorm_omN_le (p := p) (n := n)
  have h2S := padicNorm_two_omS_le (p := p) (n := n)
  set S := omS n
  set T := omT n
  set a₁ := x.re - S / T * x.im with ha₁
  set b₁ := x.im / T with hb₁
  set a₂ := y.re - S / T * y.im with ha₂
  set b₂ := y.im / T with hb₂
  refine ⟨?_, ?_⟩
  · have : (x * y).re - S / T * (x * y).im = a₁ * a₂ + b₁ * b₂ * (T ^ 2 * dT n - S ^ 2) := by
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

lemma pInt_ratCast {r : ℚ} (hr : padicNorm p r ≤ 1) : pInt p (r : Qt n) := by
  rw [pInt_iff_omega]; exact ⟨by simpa using hr, by simp⟩

lemma pInt_one : pInt p (1 : Qt n) := by simpa using pInt_ratCast (n := n) (p := p) (r := 1) (by simp)

lemma pInt_natCast (v : ℕ) : pInt p (v : Qt n) := by
  simpa using pInt_ratCast (n := n) (p := p) (r := v) (padicNorm.of_nat v)

lemma pInt_intCast (v : ℤ) : pInt p (v : Qt n) := by
  simpa using pInt_ratCast (n := n) (p := p) (r := v) (padicNorm.of_int v)

lemma pInt_sum {ι : Type*} (s : Finset ι) (f : ι → Qt n) (h : ∀ i ∈ s, pInt p (f i)) :
    pInt p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pInt_zero (n := n) (p := p)
  | insert a s ha ih =>
      rw [sum_insert ha]
      exact pInt_add (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

lemma pInt_prod {ι : Type*} (s : Finset ι) (f : ι → Qt n) (h : ∀ i ∈ s, pInt p (f i)) :
    pInt p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pInt_one (n := n) (p := p)
  | insert a s ha ih =>
      rw [prod_insert ha]
      exact pInt_mul (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

lemma pInt_pow {x : Qt n} (hx : pInt p x) (v : ℕ) : pInt p (x ^ v) := by
  induction v with
  | zero => simpa using pInt_one (n := n) (p := p)
  | succ v ih => rw [pow_succ]; exact pInt_mul ih hx


/-- `z = n/2 − √d ∈ O_p`: coordinates `(k, −1)` for `n = 2k`, `(k + 1, −1)` for `n = 2k + 1`. -/
lemma pInt_zK : pInt p (zK n) := by
  rw [pInt_iff_omega, show (zK n).re = (n : ℚ) / 2 from rfl, show (zK n).im = -1 from rfl]
  rcases omS_omT_cases (n := n) with ⟨h, hS, hT⟩ | ⟨h, hS, hT⟩ <;> rw [hS, hT]
  · obtain ⟨k, hk⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    exact ⟨padicNorm_le_one_of_eq_int k (by rw [hk]; push_cast; ring),
      padicNorm_le_one_of_eq_int (-1) (by norm_num)⟩
  · obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    exact ⟨padicNorm_le_one_of_eq_int (k + 1) (by rw [hk]; push_cast; ring),
      padicNorm_le_one_of_eq_int (-1) (by norm_num)⟩

/-- `z⁻¹ = n/2 + √d ∈ O_p`: coordinates `(k, 1)` for `n = 2k` and for `n = 2k + 1`. -/
lemma pInt_zK_inv : pInt p (zK n)⁻¹ := by
  rw [pInt_iff_omega, zK_inv]
  rcases omS_omT_cases (n := n) with ⟨h, hS, hT⟩ | ⟨h, hS, hT⟩ <;> rw [hS, hT]
  · obtain ⟨k, hk⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    exact ⟨padicNorm_le_one_of_eq_int k (by rw [hk]; push_cast; ring),
      padicNorm_le_one_of_eq_int 1 (by norm_num)⟩
  · obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    exact ⟨padicNorm_le_one_of_eq_int k (by rw [hk]; push_cast; ring),
      padicNorm_le_one_of_eq_int 1 (by norm_num)⟩

lemma pInt_zK_zpow (k : ℤ) : pInt p ((zK n) ^ k) := by
  rcases Int.eq_nat_or_neg k with ⟨v, rfl | rfl⟩
  · simpa using pInt_pow pInt_zK v
  · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pInt_pow pInt_zK_inv v

lemma pInt_smul {r : ℚ} (hr : padicNorm p r ≤ 1) {x : Qt n} (hx : pInt p x) : pInt p (r • x) := by
  rw [Algebra.smul_def, eq_ratCast]; exact pInt_mul (pInt_ratCast hr) hx

/-- `√d ∈ O_p` for odd `p` or even trace (for odd `n`, `√d = ω − 1/2` is not `2`-integral). -/
lemma pInt_sqrtd (hp2 : p ≠ 2 ∨ Even n) : pInt p (sqrtd n) := pInt_of_coords hp2 (by simp [sqrtd]) (by simp [sqrtd])

/-- The rational part: `r ∈ O_p` gives `|r|_p ≤ 1`. -/
lemma padicNorm_le_one_of_pInt_ratCast {r : ℚ} (h : pInt p (r : Qt n)) : padicNorm p r ≤ 1 := by
  have := ((pInt_iff_omega _).mp h).1; simpa using this

/-! ### `vGe` -/

lemma padicNorm_p_zpow (v : ℤ) : padicNorm p ((p : ℚ) ^ v) = (p : ℚ) ^ (-v) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [padicNorm.eq_zpow_of_nonzero (zpow_ne_zero v hp0), padicValRat.zpow, padicValRat.self hp.out.one_lt,
    mul_one]

lemma vGe_zero (v : ℤ) : vGe p v (0 : Qt n) := by rw [vGe_iff_pInt, smul_zero]; exact pInt_zero

lemma vGe_add {v : ℤ} {x y : (Qt n)} (hx : vGe p v x) (hy : vGe p v y) : vGe p v (x + y) := by
  rw [vGe_iff_pInt] at *; rw [smul_add]; exact pInt_add hx hy

lemma vGe_neg {v : ℤ} {x : (Qt n)} (hx : vGe p v x) : vGe p v (-x) := by
  rw [vGe_iff_pInt] at *; rw [smul_neg]; exact pInt_neg hx

lemma vGe_sub {v : ℤ} {x y : (Qt n)} (hx : vGe p v x) (hy : vGe p v y) : vGe p v (x - y) := by
  rw [sub_eq_add_neg]; exact vGe_add hx (vGe_neg hy)

lemma vGe_sum {ι : Type*} (s : Finset ι) {v : ℤ} (f : ι → (Qt n)) (h : ∀ i ∈ s, vGe p v (f i)) :
    vGe p v (∑ i ∈ s, f i) := by
  rw [vGe_iff_pInt, smul_sum]; exact pInt_sum _ _ (fun i hi => (vGe_iff_pInt v _).mp (h i hi))

lemma vGe_mul {v w : ℤ} {x y : (Qt n)} (hx : vGe p v x) (hy : vGe p w y) : vGe p (v + w) (x * y) := by
  rw [vGe_iff_pInt] at *
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have : ((p : ℚ) ^ (-(v + w))) • (x * y) = ((p : ℚ) ^ (-v) • x) * ((p : ℚ) ^ (-w) • y) := by
    rw [smul_mul_smul_comm, ← zpow_add₀ hp0]; congr 2; ring
  rw [this]; exact pInt_mul hx hy

lemma vGe_mono {v w : ℤ} (hmn : w ≤ v) {x : (Qt n)} (hx : vGe p v x) : vGe p w x := by
  rw [vGe_iff_pInt] at *
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have : ((p : ℚ) ^ (-w)) • x = ((p : ℚ) ^ (v - w)) • ((p : ℚ) ^ (-v) • x) := by
    rw [smul_smul, ← zpow_add₀ hp0]; congr 2; ring
  rw [this]
  refine pInt_smul ?_ hx
  rw [padicNorm_p_zpow]
  exact zpow_le_one_of_nonpos₀ (by exact_mod_cast hp.out.one_lt.le) (by omega)

lemma vGe_of_pInt {x : (Qt n)} (hx : pInt p x) : vGe p 0 x := by
  rw [vGe_iff_pInt]; simpa using hx

lemma pInt_of_vGe {x : (Qt n)} (hx : vGe p 0 x) : pInt p x := by
  rw [vGe_iff_pInt] at hx; simpa using hx

lemma vGe_prod {ι : Type*} (s : Finset ι) (ρ : ι → ℤ) (f : ι → (Qt n)) (h : ∀ i ∈ s, vGe p (ρ i) (f i)) :
    vGe p (∑ i ∈ s, ρ i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vGe_of_pInt (p := p) pInt_one
  | insert a s ha ih =>
      rw [prod_insert ha, sum_insert ha]
      exact vGe_mul (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

lemma vGe_pow {v : ℤ} {x : (Qt n)} (hx : vGe p v x) (k : ℕ) : vGe p (k * v) (x ^ k) := by
  induction k with
  | zero => simpa using vGe_of_pInt (p := p) pInt_one
  | succ k ih => rw [pow_succ]; convert vGe_mul ih hx using 1; push_cast; ring

/-- A rational `r` has `v_p(r) ≥ v_p(r)`. -/
lemma vGe_ratCast (r : ℚ) : vGe p (padicValRat p r) (r : (Qt n)) := by
  by_cases hr : r = 0
  · subst hr; simpa using vGe_zero (p := p) _
  rw [vGe_iff_pInt, Algebra.smul_def, eq_ratCast, ← Rat.cast_mul]
  refine pInt_ratCast ?_
  rw [padicNorm.mul, padicNorm_p_zpow, padicNorm.eq_zpow_of_nonzero hr, neg_neg, ← zpow_add₀ (by
    exact_mod_cast hp.out.ne_zero)]
  simp

/-- Rational `r` with `|r|_p ≤ p^{−v}`. -/
lemma vGe_ratCast_of_padicNorm {r : ℚ} {v : ℤ} (hr : padicNorm p r ≤ (p : ℚ) ^ (-v)) : vGe p v (r : (Qt n)) := by
  rw [vGe_iff_pInt, Algebra.smul_def, eq_ratCast, ← Rat.cast_mul]
  refine pInt_ratCast ?_
  rw [padicNorm.mul, padicNorm_p_zpow, neg_neg]
  have hp0 : (0 : ℚ) < (p : ℚ) ^ v := zpow_pos (by exact_mod_cast hp.out.pos) v
  calc (p : ℚ) ^ v * padicNorm p r ≤ (p : ℚ) ^ v * (p : ℚ) ^ (-v) := by gcongr
    _ = 1 := by rw [← zpow_add₀ (by exact_mod_cast hp.out.ne_zero)]; simp

/-- Extraction: `vGe p v (r : Q5) → |r|_p ≤ p^{−v}`. -/
lemma padicNorm_le_of_vGe {r : ℚ} {v : ℤ} (h : vGe p v (r : (Qt n))) : padicNorm p r ≤ (p : ℚ) ^ (-v) := by
  rw [vGe_iff_pInt, Algebra.smul_def, eq_ratCast, ← Rat.cast_mul] at h
  have h1 := padicNorm_le_one_of_pInt_ratCast h
  rw [padicNorm.mul, padicNorm_p_zpow, neg_neg] at h1
  have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpos : (0 : ℚ) ≤ (p : ℚ) ^ (-v) := (zpow_pos (by exact_mod_cast hp.out.pos) _).le
  calc padicNorm p r = (p : ℚ) ^ (-v) * ((p : ℚ) ^ v * padicNorm p r) := by
        rw [← mul_assoc, ← zpow_add₀ hpne]; simp
    _ ≤ (p : ℚ) ^ (-v) * 1 := by gcongr
    _ = (p : ℚ) ^ (-v) := mul_one _

lemma vGe_zK_zpow (k : ℤ) : vGe p 0 ((zK n) ^ k) := vGe_of_pInt (pInt_zK_zpow k)

/-- Leibniz: row bounds give a bound on the determinant. -/
theorem vGe_det {k : ℕ} (M : Matrix (Fin k) (Fin k) (Qt n)) (ρ : Fin k → ℤ) (h : ∀ i j, vGe p (ρ i) (M i j)) :
    vGe p (∑ i, ρ i) M.det := by
  rw [Matrix.det_apply]
  refine vGe_sum _ _ (fun σ _ => ?_)
  have hprod : vGe p (∑ i, ρ (σ i)) (∏ i, M (σ i) i) := vGe_prod _ _ _ (fun i _ => h (σ i) i)
  rw [Equiv.sum_comp σ ρ] at hprod
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
  · simpa using hprod
  · simpa using vGe_neg hprod

/-! ### Coefficientwise bounds on `ℚ(√5)[X]` -/

/-- `v_p(F) ≥ v` coefficientwise. -/
def vGeX (p : ℕ) (v : ℤ) (F : (Qt n)[X]) : Prop := ∀ k, vGe p v (F.coeff k)

lemma vGeX_add {v : ℤ} {F G : (Qt n)[X]} (hF : vGeX p v F) (hG : vGeX p v G) : vGeX p v (F + G) := fun k => by
  rw [coeff_add]; exact vGe_add (hF k) (hG k)

lemma vGeX_neg {v : ℤ} {F : (Qt n)[X]} (hF : vGeX p v F) : vGeX p v (-F) := fun k => by
  rw [coeff_neg]; exact vGe_neg (hF k)

lemma vGeX_sum {ι : Type*} (s : Finset ι) {v : ℤ} (F : ι → (Qt n)[X]) (h : ∀ i ∈ s, vGeX p v (F i)) :
    vGeX p v (∑ i ∈ s, F i) := fun k => by
  rw [finsetSum_coeff]; exact vGe_sum _ _ (fun i hi => h i hi k)

lemma vGeX_C {v : ℤ} {x : (Qt n)} (hx : vGe p v x) : vGeX p v (C x) := fun k => by
  rw [coeff_C]; split_ifs
  · exact hx
  · exact vGe_zero v

lemma vGeX_X_mul {v : ℤ} {F : (Qt n)[X]} (hF : vGeX p v F) : vGeX p v (X * F) := fun k => by
  rcases k with _ | k
  · simpa using vGe_zero (p := p) v
  · rw [coeff_X_mul]; exact hF k

lemma vGeX_mul {v w : ℤ} {F G : (Qt n)[X]} (hF : vGeX p v F) (hG : vGeX p w G) : vGeX p (v + w) (F * G) :=
  fun k => by
    rw [coeff_mul]; exact vGe_sum _ _ (fun x _ => vGe_mul (hF x.1) (hG x.2))

lemma vGeX_one : vGeX p 0 (1 : (Qt n)[X]) := by
  rw [← C_1]; exact vGeX_C (vGe_of_pInt pInt_one)

lemma vGeX_prod {ι : Type*} (s : Finset ι) (ρ : ι → ℤ) (F : ι → (Qt n)[X]) (h : ∀ i ∈ s, vGeX p (ρ i) (F i)) :
    vGeX p (∑ i ∈ s, ρ i) (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vGeX_one (p := p)
  | insert a s ha ih =>
      rw [prod_insert ha, sum_insert ha]
      exact vGeX_mul (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

/-- Leibniz for polynomial matrices. -/
theorem vGeX_det {k : ℕ} (M : Matrix (Fin k) (Fin k) (Qt n)[X]) (ρ : Fin k → ℤ) (h : ∀ i j, vGeX p (ρ i) (M i j)) :
    vGeX p (∑ i, ρ i) M.det := by
  rw [Matrix.det_apply]
  refine vGeX_sum _ _ (fun σ _ => ?_)
  have hprod : vGeX p (∑ i, ρ (σ i)) (∏ i, M (σ i) i) := vGeX_prod _ _ _ (fun i _ => h (σ i) i)
  rw [Equiv.sum_comp σ ρ] at hprod
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
  · simpa using hprod
  · simpa using vGeX_neg hprod

/-- From `ℚ(√5)[X]` back to `ℚ[X]`. -/
lemma padicNorm_coeff_of_vGeX_map {P : ℚ[X]} {v : ℤ} (h : vGeX p v (P.map (algebraMap ℚ (Qt n)))) (k : ℕ) :
    padicNorm p (P.coeff k) ≤ (p : ℚ) ^ (-v) := by
  have := h k
  rw [coeff_map, eq_ratCast] at this
  exact padicNorm_le_of_vGe this

end Ti
end Chi2U
