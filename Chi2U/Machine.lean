/-
# The reflection Hankel machine for `χ₂(z)`, `z = √((a/2)² + 1) − a/2` (PROOF_U §1, PROOF_V §1, PROOF_VODD)

Everything is parametrised by the trace `az` (`d = (az/2)² + 1`, `z = √d − az/2`; Theorem U is `az = 4`, Theorem V is
`az = 2m`); only `z` changes.

For `h` even, `J = h/2`, `K = h + 1` poles at the even integers `x_m = 2(m − J)`, `m ≤ h`:
* `D(t) = ∏_{m ≤ h} (t − x_m)`, `D′(x_m) = ∏_{l ≠ m} (x_m − x_l)`;
* partial sums `P(x)` for even `x` (`Psum`): `Σ_{n odd, 0<n<|x|} z^n/n²` for `x < 0`,
  `−Σ_{n odd, −x<n<0} z^n/n²` for `x > 0`, `P(0) = 0`;
* `Λ(g) = μ(g/D) = A(g) + T·B(g)` (Lemma 1′, `PoleExpansion.lean`) with
  `A(g) = μ(g div D) + Σ_m c_m z^{x_m} P(x_m)`, `B(g) = −Σ_m c_m z^{x_m}`, `c_m = g(x_m)/D′(x_m)`;
  both are `ℚ(√d)`-valued;
* the rational matrices `Ã_{ij}, B̃_{ij}`: the `ℚ`-coordinates of `E_{i+j}·√d^{[i odd] − [j odd]}`
  (`tildeCoord`); by Lemma R (`LemmaR.lean`) these are the honest entries of a diagonal conjugate of the Hankel
  matrix, so
* `Δ_h(X) = det(Ã + X·B̃) ∈ ℚ[X]` has `Δ_h(T) = det(Λ(t^{i+j}))` (`LemmaR.aeval_Delta`).

The definitions make sense for every `h`; the theorems assume `h` even.
-/
import Chi2U.Moments

namespace Chi2U

variable {az : ℕ} [Fact (1 ≤ az)]

open Polynomial

/-- The pole `x_m = 2(m − ⌊h/2⌋)` (an even integer). -/
def poleZ (h m : ℕ) : ℤ := 2 * ((m : ℤ) - ((h / 2 : ℕ) : ℤ))

/-- `D(t) = ∏_{m ≤ h} (t − x_m)`. -/
noncomputable def Dpoly (h : ℕ) : ℚ[X] := ∏ m ∈ Finset.range (h + 1), (X - C ((poleZ h m : ℤ) : ℚ))

/-- `D′(x_m) = ∏_{l ≤ h, l ≠ m} (x_m − x_l)`. -/
def dPrime (h m : ℕ) : ℚ :=
  ∏ l ∈ Finset.range (h + 1), if l = m then 1 else ((poleZ h m : ℚ) - poleZ h l)

/-- The partial sums `P(x)` of `T = χ₂(z)` (`x` even). -/
noncomputable def Psum (az : ℕ) [Fact (1 ≤ az)] (x : ℤ) : (Qd az) :=
  if x ≤ 0 then ∑ k ∈ Finset.range (x.natAbs / 2), (zK az) ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : (Qd az)) ^ 2
  else -∑ k ∈ Finset.range (x.natAbs / 2), ((zK az) ^ (2 * k + 1))⁻¹ / ((2 * k + 1 : ℕ) : (Qd az)) ^ 2

/-- The pole coefficient `c_m = g(x_m)/D′(x_m)`. -/
noncomputable def cPole (h : ℕ) (g : ℚ[X]) (m : ℕ) : ℚ := g.eval (poleZ h m : ℚ) / dPrime h m

/-- `A(g)`: the `T⁰` part of `Λ(g) = μ(g/D)`. -/
noncomputable def Afun (az : ℕ) [Fact (1 ≤ az)] (h : ℕ) (g : ℚ[X]) : (Qd az) :=
  muPoly az (g /ₘ Dpoly h) +
    ∑ m ∈ Finset.range (h + 1), (cPole h g m : (Qd az)) * (zK az) ^ (poleZ h m) * Psum az (poleZ h m)

/-- `B(g)`: the `T¹` part of `Λ(g) = μ(g/D)`. -/
noncomputable def Bfun (az : ℕ) [Fact (1 ≤ az)] (h : ℕ) (g : ℚ[X]) : (Qd az) :=
  -∑ m ∈ Finset.range (h + 1), (cPole h g m : (Qd az)) * (zK az) ^ (poleZ h m)

/-- The rational coordinate of `e·√5^{[i odd] − [j odd]}` for `e` with Lemma R parity `σe = (−1)^{i+j} e`. -/
def tildeCoord (i j : ℕ) (e : (Qd az)) : ℚ :=
  if Even (i + j) then e.re else if Even j then dQ az * e.im else e.im

/-- `Ã_{ij}`. -/
noncomputable def Atil (az : ℕ) [Fact (1 ≤ az)] (h : ℕ) : Matrix (Fin h) (Fin h) ℚ :=
  fun i j => tildeCoord i j (Afun az h (X ^ ((i : ℕ) + j)))

/-- `B̃_{ij}`. -/
noncomputable def Btil (az : ℕ) [Fact (1 ≤ az)] (h : ℕ) : Matrix (Fin h) (Fin h) ℚ :=
  fun i j => tildeCoord i j (Bfun az h (X ^ ((i : ℕ) + j)))

/-- `Δ_h(X) = det(Ã + X B̃) ∈ ℚ[X]`. -/
noncomputable def Delta (az : ℕ) [Fact (1 ≤ az)] (h : ℕ) : ℚ[X] :=
  ((X : ℚ[X]) • (Btil az h).map C + (Atil az h).map C).det

lemma natDegree_Delta_le (h : ℕ) : (Delta az h).natDegree ≤ h := by
  have := natDegree_det_X_add_C_le (Btil az h) (Atil az h)
  simpa [Delta] using this

/-- `Δ_h(r) = det(Ã + r B̃)` for rational `r`. -/
lemma eval_Delta (h : ℕ) (r : ℚ) : (Delta az h).eval r = (Atil az h + r • Btil az h).det := by
  unfold Delta
  rw [← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, coe_evalRingHom, eval_add, eval_mul, eval_X, eval_C]
  ring

end Chi2U
