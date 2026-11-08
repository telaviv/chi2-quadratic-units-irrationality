/-
# The reflection Hankel machine for `χ₂(√5 − 2)` (PROOF_U §1)

For `h` even, `J = h/2`, `K = h + 1` poles at the even integers `x_m = 2(m − J)`, `m ≤ h`:
* `D(t) = ∏_{m ≤ h} (t − x_m)`, `D′(x_m) = ∏_{l ≠ m} (x_m − x_l)`;
* partial sums `P(x)` for even `x` (`Psum`): `Σ_{n odd, 0<n<|x|} z^n/n²` for `x < 0`,
  `−Σ_{n odd, −x<n<0} z^n/n²` for `x > 0`, `P(0) = 0`;
* `Λ(g) = μ(g/D) = A(g) + T·B(g)` (Lemma 1′, `PoleExpansion.lean`) with
  `A(g) = μ(g div D) + Σ_m c_m z^{x_m} P(x_m)`, `B(g) = −Σ_m c_m z^{x_m}`, `c_m = g(x_m)/D′(x_m)`;
  both are `ℚ(√5)`-valued;
* the rational matrices `Ã_{ij}, B̃_{ij}`: the `ℚ`-coordinates of `E_{i+j}·√5^{[i odd] − [j odd]}`
  (`tildeCoord`); by Lemma R (`LemmaR.lean`) these are the honest entries of a diagonal conjugate of the Hankel
  matrix, so
* `Δ_h(X) = det(Ã + X·B̃) ∈ ℚ[X]` has `Δ_h(T) = det(Λ(t^{i+j}))` (`LemmaR.aeval_Delta`).

The definitions make sense for every `h`; the theorems assume `h` even.
-/
import Chi2U.Moments

namespace Chi2U

variable {mz : ℕ} [Fact (1 ≤ mz)]

open Polynomial

/-- The pole `x_m = 2(m − ⌊h/2⌋)` (an even integer). -/
def poleZ (h m : ℕ) : ℤ := 2 * ((m : ℤ) - ((h / 2 : ℕ) : ℤ))

/-- `D(t) = ∏_{m ≤ h} (t − x_m)`. -/
noncomputable def Dpoly (h : ℕ) : ℚ[X] := ∏ m ∈ Finset.range (h + 1), (X - C ((poleZ h m : ℤ) : ℚ))

/-- `D′(x_m) = ∏_{l ≤ h, l ≠ m} (x_m − x_l)`. -/
def dPrime (h m : ℕ) : ℚ :=
  ∏ l ∈ Finset.range (h + 1), if l = m then 1 else ((poleZ h m : ℚ) - poleZ h l)

/-- The partial sums `P(x)` of `T = χ₂(z)` (`x` even). -/
noncomputable def Psum (mz : ℕ) [Fact (1 ≤ mz)] (x : ℤ) : (Qd mz) :=
  if x ≤ 0 then ∑ k ∈ Finset.range (x.natAbs / 2), (zK mz) ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : (Qd mz)) ^ 2
  else -∑ k ∈ Finset.range (x.natAbs / 2), ((zK mz) ^ (2 * k + 1))⁻¹ / ((2 * k + 1 : ℕ) : (Qd mz)) ^ 2

/-- The pole coefficient `c_m = g(x_m)/D′(x_m)`. -/
noncomputable def cPole (h : ℕ) (g : ℚ[X]) (m : ℕ) : ℚ := g.eval (poleZ h m : ℚ) / dPrime h m

/-- `A(g)`: the `T⁰` part of `Λ(g) = μ(g/D)`. -/
noncomputable def Afun (mz : ℕ) [Fact (1 ≤ mz)] (h : ℕ) (g : ℚ[X]) : (Qd mz) :=
  muPoly mz (g /ₘ Dpoly h) +
    ∑ m ∈ Finset.range (h + 1), (cPole h g m : (Qd mz)) * (zK mz) ^ (poleZ h m) * Psum mz (poleZ h m)

/-- `B(g)`: the `T¹` part of `Λ(g) = μ(g/D)`. -/
noncomputable def Bfun (mz : ℕ) [Fact (1 ≤ mz)] (h : ℕ) (g : ℚ[X]) : (Qd mz) :=
  -∑ m ∈ Finset.range (h + 1), (cPole h g m : (Qd mz)) * (zK mz) ^ (poleZ h m)

/-- The rational coordinate of `e·√5^{[i odd] − [j odd]}` for `e` with Lemma R parity `σe = (−1)^{i+j} e`. -/
def tildeCoord (i j : ℕ) (e : (Qd mz)) : ℚ :=
  if Even (i + j) then e.re else if Even j then dQ mz * e.im else e.im

/-- `Ã_{ij}`. -/
noncomputable def Atil (mz : ℕ) [Fact (1 ≤ mz)] (h : ℕ) : Matrix (Fin h) (Fin h) ℚ :=
  fun i j => tildeCoord i j (Afun mz h (X ^ ((i : ℕ) + j)))

/-- `B̃_{ij}`. -/
noncomputable def Btil (mz : ℕ) [Fact (1 ≤ mz)] (h : ℕ) : Matrix (Fin h) (Fin h) ℚ :=
  fun i j => tildeCoord i j (Bfun mz h (X ^ ((i : ℕ) + j)))

/-- `Δ_h(X) = det(Ã + X B̃) ∈ ℚ[X]`. -/
noncomputable def Delta (mz : ℕ) [Fact (1 ≤ mz)] (h : ℕ) : ℚ[X] :=
  ((X : ℚ[X]) • (Btil mz h).map C + (Atil mz h).map C).det

lemma natDegree_Delta_le (h : ℕ) : (Delta mz h).natDegree ≤ h := by
  have := natDegree_det_X_add_C_le (Btil mz h) (Atil mz h)
  simpa [Delta] using this

/-- `Δ_h(r) = det(Ã + r B̃)` for rational `r`. -/
lemma eval_Delta (h : ℕ) (r : ℚ) : (Delta mz h).eval r = (Atil mz h + r • Btil mz h).det := by
  unfold Delta
  rw [← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, coe_evalRingHom, eval_add, eval_mul, eval_X, eval_C]
  ring

end Chi2U
