# χ₂(√(m²+1) − m) is irrational for every m ≥ 16: a Lean 4 proof

This repository contains a complete, machine-checked proof in [Lean 4](https://lean-lang.org/) and
[Mathlib](https://github.com/leanprover-community/mathlib4) of the following theorems.

> **Theorem V.** For every integer m ≥ 2 with m ∉ {3, 5, 7, 9, 15}, the value χ₂(√(m² + 1) − m) of Legendre's chi
> function χ₂(z) = Σ_{n≥0} z^{2n+1}/(2n+1)² is irrational. (√(m² + 1) − m is a unit of norm −1 in ℚ(√(m² + 1)).)

> **Corollary (Theorem U, m = 2). Let φ = (1 + √5)/2 be the golden ratio. Then π² − 18 log²φ = 5.70143763069985955388… is irrational.
> Equivalently, χ₂(√5 − 2) = π²/24 − ¾ log²φ = 0.23755990127916081474… is irrational.

In Lean:

```lean
-- Chi2U/V/Defs.lean, Chi2U/V/Interface.lean
def Chi2U.V.TheoremV : Prop :=
  ∀ m : ℕ, 2 ≤ m → m ∉ ({3, 5, 7, 9, 15} : Finset ℕ) → Irrational (chi2 (Real.sqrt ((m : ℝ) ^ 2 + 1) - m))
theorem Chi2U.V.theoremV : Chi2U.V.TheoremV

-- Chi2U/Golden/Corollary.lean
theorem Chi2U.golden_irrational' : Irrational (Real.pi ^ 2 - 18 * Real.log goldenRatio ^ 2)

-- Chi2U/Defs.lean, Chi2U/Statement.lean
noncomputable def chi2Term (z : ℝ) (n : ℕ) : ℝ := z ^ (2 * n + 1) / (2 * (n : ℝ) + 1) ^ 2
noncomputable def chi2 (z : ℝ) : ℝ := ∑' n : ℕ, chi2Term z n
def TheoremU : Prop := Irrational (chi2 (Real.sqrt 5 - 2))

-- Chi2U/Main.lean
theorem Chi2U.chi2_sqrt5_sub_two_irrational : TheoremU

-- Chi2U/Golden/ClosedForm.lean
theorem Chi2U.chi2_sqrt5_sub_two_eq :
    chi2 (Real.sqrt 5 - 2) = Real.pi ^ 2 / 24 - 3 / 4 * Real.log goldenRatio ^ 2
```

```
'Chi2U.V.theoremV' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2U.chi2_sqrt5_sub_two_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2U.golden_irrational'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`goldenRatio` is Mathlib's `(1 + √5)/2` and `Irrational` is Mathlib's. The closed form is itself proved (from Landen's
identity for χ₂ and Euler's reflection and Landen's identity for the dilogarithm), so the golden-ratio form is not a
separate assumption. The proof uses only Lean's three standard axioms. There is no `sorry`, no added `axiom` and no
`native_decide`: the numerical certificate is evaluated by the Lean kernel. See [TRUST.md](TRUST.md).

The paper is [`paper/chi2-quadratic-units-irrationality.pdf`](paper/chi2-quadratic-units-irrationality.pdf) (source `paper/main.tex`).

## Context

We have not found Theorem V, Theorem U, or the irrationality of any number π² + c log²φ with c ∈ ℚ \ {0}, in the
literature. For m ≥ 3 the values χ₂(√(m² + 1) − m) have no expression through π² and logarithms by symbol-preserving
dilogarithm identities (paper, Proposition on the symbol); only m = 1, 2 have a Landen closed form. Explicit linear
independence criteria at algebraic points (David–Hirata-Kohno–Kawashima) cover χ₂(√(m² + 1) − m) only for
m ≥ 4 346 237 by our evaluation.

- **Other golden-ratio values.** The classical dilogarithm evaluations Li₂(φ⁻²), Li₂(φ⁻¹), Li₂(−φ⁻¹), Li₂(−φ) all lie
  in ℚπ² + ℚ log²φ, but with c = −15, −10, −15/2 and +10 in the form π² + c log²φ; Theorem U has c = −18. The
  irrationality of one member of the family says nothing about another.
- **Homogeneous statements.** Gel'fond–Schneider gives log²φ/π² ∉ ℚ̄, i.e. π² and log²φ are linearly independent over
  ℚ; it says nothing about a relation that also involves 1.
- **Criteria at algebraic points.** The linear independence criteria for polylogarithms and Lerch functions at
  algebraic points need a point that is small compared with its height; by our evaluation they are far from applying
  at √5 − 2.
- **The closest analogue** is Li₂(½) = π²/12 − ½ log²2 ∉ ℚ, proved in Lean by Q. Tang
  ([dtq1997/li2-half-irrationality](https://github.com/dtq1997/li2-half-irrationality)) and by S. Liu
  ([Li2Rational](https://github.com/siqiliu-tsinghua/Li2Rational)); both unrefereed.

Our searches covered the web, arXiv, zbMATH Open, OpenAlex, Crossref, Semantic Scholar (partly), the Hexagon repository
and recent Lean repositories, but not MathSciNet or Google Scholar. Please tell us if you know of prior work.

## Outline of the proof

The machine is formalised once with m as a parameter (`mz` in the files: `Qd mz` = ℚ(√(m² + 1)) as
`QuadraticAlgebra ℚ (m² + 1) 0`, `zK mz`, `Delta mz h`). We describe it at m = 2; the changes for general m follow
the outline. The proof transposes the proof of [chi2-irrationality](https://github.com/telaviv/chi2-irrationality)
(χ₂(1/3), χ₂(1/5) ∉ ℚ) to the point z = √5 − 2 = φ⁻³, a unit of norm −1 in ℚ(√5). For even h take the K = h + 1 poles
x_m = 2(m − h/2) (the even integers in [−h, h]), put D(t) = Π_m (t − x_m), and consider

    Λ(g) = Σ_{t odd ≥ 1} z^t (g/D)′(t)      (g ∈ ℚ[t]).

Partial fractions give Λ = A + T·B with T = χ₂(z), so the Hankel determinant det(Λ(t^{i+j}))_{i,j<h} is the value at
X = T of Δ_h(X) = det(A(t^{i+j}) + X·B(t^{i+j})).

1. **Reflection (Lemma R).** The pole set is symmetric under t ↦ −t and the Galois conjugation maps z ↦ −1/z. Together
   they force Δ_h ∈ ℚ[X] although its entries lie in ℚ(√5), so the conjugate place (where the series diverges) costs
   nothing. Files: `Field.lean`, `Moments.lean`, `Machine.lean`, `LemmaR.lean`; Lemma 1′ (Λ = A + T·B) in
   `PoleExpansion.lean`, `Mahler.lean`, `MomentSeries.lean`.
2. **Denominators (Theorem A′): log den_h ≤ (4/3 + ε)h².** Since z is a unit, there are no special primes.
   - Odd p < K/3: a plateau bound 2h·lev(p) + v_p(h!) via a bordered Lagrange Gram identity (Lemmas B, 9′).
     Files: `Arith/LemmaB.lean`, `Arith/Lemma9Levels.lean`, `Arith/OddPrimes.lean`.
   - Odd p ≥ K/3: a class count 3(K − p) (Lemmas 8′, 8A′). Files: `Arith/ClassCount.lean`, `Arith/Lemma8One.lean`,
     `Arith/OddExp.lean`.
   - The prime number theorem sums these to 2/3 + 2/3 = 4/3 per h². Files: `Arith/PrimeSums.lean`, `PNT/`.
   - p = 2 costs only O(h log h), because 1 − z² = 4z (Lemma 10′). Files: `Arith/TwoAdic*.lean`.
   - Assembly of the common denominator: `Arith/Assembly.lean`.
3. **Size (Theorem B′).** |Δ_h(T)| ≤ exp((Φ + ε)h²), with Φ read off a dual certificate for a constrained
   equilibrium problem. The formal proof follows the discrete lattice-energy (Pólya-type) route of chi2-irrationality,
   plus a two-sided Jensen bound for the pole product. The certificate gives Φ ≤ −1.3538792 < −27/20; it is checked by
   `decide +kernel` in rational interval arithmetic. Files: `Analytic/`, `Cert/`, `Interval/`.
4. **Nonvanishing (Lemma P′).** For h = 3ℓ − 1 with ℓ ≥ 7 prime, the Gram matrix in the Lagrange basis is block
   diagonal modulo a prime of ℚ(√5) above ℓ, with 3 × 3 blocks in closed form, so Δ_h(a/b) ≠ 0 whenever ℓ² ∤ b.
   Every prime ℓ ≥ 7 works. Files: `NonVan/`.
5. **Conclusion (Lemma E).** The formal margin is 4/3 − 27/20 = −1/60 per h² (the paper's certificate gives
   −0.02588…). So den_h·Δ_h(T) → 0 faster than any b^{−h}, which contradicts T = a/b. Files: `Criterion.lean`,
   `MainCond.lean`, `Main.lean`.
6. **General m (Theorem V), files `V/`.** z_m = √(m² + 1) − m, 1 − z_m² = 2m·z_m.
   - p = 2 (Lemma 10_ν, ν = 1 + v₂(m)): cost |ν − 2|·log 2/4 per h². Files: `V/Lemma10nu.lean`, `V/TwoAdicNu.lean`.
   - Odd p | m (Lemma S): cost (e/4 + 1/(4(p − 1)))·log p per h², e = v_p(m), from a multi-level Lemma 8′ and the
     Mahler form. Files: `V/LemmaS.lean`, `V/S*.lean`, `V/AKSize.lean`.
   - Analytic part: the shift lemma moves the certificate at z₂ to z_m, gaining ½ log(z₂/z_m). File: `V/Shift.lean`.
   - Margins: negative for every m ≥ 2 outside {3, 5, 7, 9, 15} (closed form for even m ≥ 4 and odd m ≥ 69, the rest
     case by case). File: `V/Margin.lean`.
   - Nonvanishing: Lemma P′ holds for every m and every prime ℓ ≥ 7 with ℓ ∤ 2m (`NonVan/` is generic in m).
   - Assembly: `V/Interface.lean`.
7. **Golden-ratio form.** χ₂(√5 − 2) = π²/24 − ¾ log²φ from Landen's identity for χ₂ at x = √5 − 2 (where
   (1 − x)/(1 + x) = φ⁻¹) and the value of χ₂(φ⁻¹), itself derived from Euler's reflection and Landen's identity for
   Li₂. Files: `Golden/`.

The paper also proves a two-point statement at units of biquadratic fields (Theorem M1); it is computer-assisted and is
**not** formalised here.

## Building and checking

You need [elan](https://github.com/leanprover/elan). The toolchain (Lean v4.35.0) and Mathlib (v4.35.0) are pinned in
`lean-toolchain` and `lakefile.toml`.

```sh
lake exe cache get                 # download prebuilt Mathlib
LEAN_NUM_THREADS=4 lake build      # about 10 minutes once Mathlib is cached (9124 jobs)
lake env lean Axioms.lean          # print the axioms of the main theorems and their ingredients
```

The thread limit follows the author's larger Lean repositories, where a build at Lake's default concurrency once ran out
of memory on Windows; this project is much smaller, so a plain `lake build` should also work on most machines. The
fresh-clone check and its timing are recorded in [TRUST.md](TRUST.md).

The certificate data `Chi2U/Cert/DataU.lean` can be regenerated with `python scripts/gen_cert_u.py 50 8 4
Chi2U/Cert/DataU.lean` (Python with numpy and mpmath). `scripts/check_defs.py` (python-flint) re-implements the Lean
definitions and compares them with the paper's machine; its output is `scripts/check_defs.out`
(`scripts/check_defs_v.py`, `scripts/check_defs_v.out` for general m). `scripts/margins_lean.py` and
`scripts/margin_v_cases.py` evaluate the margins of Theorem V with the Lean constants. The computations of the
paper are in [`scripts/paper/`](scripts/paper/README.md).

## Repository layout

Paths are relative to `Chi2U/`.

| path | content |
|---|---|
| `Defs.lean`, `Statement.lean` | χ₂ and Theorem U |
| `V/` | Theorem V: `Defs` (statement, constants), Lemma 10_ν, Lemma S, shift lemma, margins, Lemma P′_m, `Interface` (assembly) |
| `Golden/` | the closed form π²/24 − ¾ log²φ (Landen, dilogarithm identities) and the golden-ratio corollaries |
| `Field.lean` | ℚ(√(m²+1)) = `QuadraticAlgebra ℚ (m²+1) 0`, z = √(m²+1) − m, conjugation, real embedding |
| `Moments.lean`, `MomentSeries.lean`, `Mahler.lean` | odd moments, the moment functional, the Mahler (forward-difference) form |
| `Machine.lean`, `LemmaR.lean` | poles, D, partial sums, the functionals A, B, Δ_h ∈ ℚ[X]; Lemma R and Corollary R |
| `PoleExpansion.lean` | Lemma 1′: Λ = A + T·B |
| `Criterion.lean`, `MainCond.lean` | Lemma E and the conditional main theorem |
| `Arith/` | Lemmas 8A′, B, 8′, 9′, 10′, Theorem A′, the denominators |
| `PNT/` | prime number theorem (θ(x) ~ x) and prime sums |
| `Analytic/` | Theorem B′: node expansion, slot determinants, lattice energy inequality, pole bound |
| `Interval/`, `Cert/` | rational interval arithmetic, log enclosures, and the kernel-checked dual certificate |
| `NonVan/` | Lemma P′ (every m) |
| `Main.lean` | assembly |
| `../scripts/gen_cert_u.py` | generator for the certificate data (untrusted; see TRUST.md) |
| `../scripts/check_defs.py` | exact check of the definitions against the paper's machine |
| `../scripts/leanchecker.log` | per-module results of the `leanchecker` replay |
| `../scripts/paper/` | the computation scripts of the paper |
| `../Axioms.lean` | axiom audit |
| `../FIDELITY_REFEREE.md`, `../FIDELITY_REFEREE_V.md` | AI referee reports on the fidelity of the statements (U, V) |

Every Lean file starts with a docstring saying what it proves and how. The docstrings cite `PROOF_U §n`, the working
proof notes that the paper was written from. Their sections correspond to the paper's: §1–§2 (machine, reflection,
endgame) → paper §2, and §3–§7 → paper §3–§7 (subsection numbers can differ). These notes, the planning files they mention (`notes/…`) and the project name `lean_chi2u` used in
some provenance headers belong to the development history and are not part of this repository.

## Status and caveats

- The Lean kernel has checked the proof, and every declaration was replayed with `leanchecker` (TRUST.md). **No human
  expert has yet reviewed the mathematics or the Lean code.** The statement definitions (see TRUST.md) are short and
  worth reading.
- The construction, the proofs, the certificate programs, the paper and the Lean formalisation were produced largely by
  AI models (Claude, Anthropic), working under the direction of the author. Apart from the Lean kernel check, all
  verification so far has been done by AI systems.
- The formal margins are thin (−1/60 per h² at m = 2; about −0.0126 at m = 11 and −0.001 of slack in the closed form
  at m = 69). They are certified, not estimated.

## Acknowledgements

- The architecture, and about 7,800 of the roughly 20,100 lines, come from
  [chi2-irrationality](https://github.com/telaviv/chi2-irrationality), the author's Lean proof that χ₂(1/3) and χ₂(1/5)
  are irrational: the definition of χ₂, the criterion, the generic analytic files, `PNT/` and `Interval/`.
- `PNT/` and `Interval/` were ported there from [beta-irrationality](https://github.com/telaviv/beta-irrationality),
  the author's Lean proof that one of β(4), β(6), …, β(36) is irrational.
- `PNT/Port/` comes originally from [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
  (A. Kontorovich, T. Tao et al.), via [domino14/zeta5](https://github.com/domino14/zeta5), under the Apache License
  2.0 (see `PNT/Port/LICENSE`).
- The Hankel-determinant approach follows Q. Tang's Lean proof that Li₂(1/2) is irrational
  ([dtq1997/li2-half-irrationality](https://github.com/dtq1997/li2-half-irrationality)). The analytic part uses ideas
  from logarithmic potential theory (Saff–Totik, *Logarithmic Potentials with External Fields*).

## License

Apache License 2.0 (see [LICENSE](LICENSE)). `Chi2U/PNT/Port/` is derived from PrimeNumberTheoremAnd, also Apache-2.0;
its own `LICENSE` file and the provenance notes in its file headers are kept.
