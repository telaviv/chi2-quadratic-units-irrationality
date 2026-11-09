# Irrationality of χ₂ at units of real quadratic fields of norm −1: a Lean 4 proof

This repository contains a complete, machine-checked proof in [Lean 4](https://lean-lang.org/) and
[Mathlib](https://github.com/leanprover-community/mathlib4) of the theorems below. Theorem V (even trace) and Theorem
V_odd (odd trace) together show that χ₂(ε) is irrational for every unit ε ∈ (0, 1) of norm −1 of a real quadratic
field, except 47 units. The case ε = √5 − 2 is the golden-ratio statement: **π² − 18 log²φ is irrational.**

Here χ₂(z) = Σ_{n≥0} z^{2n+1}/(2n+1)² is Legendre's chi function. Every unit ε ∈ (0, 1) of norm −1 is
ε = (√(a² + 4) − a)/2 with trace a = ε⁻¹ − ε ∈ {1, 2, 3, …}; for even a = 2m this is √(m² + 1) − m.

> **Theorem V (even trace).** For every integer m ≥ 2 with m ∉ {3, 5, 7, 9, 15}, the number χ₂(√(m² + 1) − m) is
> irrational.

> **Theorem V_odd (odd trace).** Let 𝓔_odd = {5, 7, 9, …, 57} ∪ {63, 65, 69, 75, 77, 81, 85, 87, 93, 99, 105, 165}
> (39 values). For every odd integer a ≥ 5 with a ∉ 𝓔_odd, the number χ₂((√(a² + 4) − a)/2) is irrational.

> **Corollary (units of norm −1).** Let ε ∈ (0, 1) be a unit of norm −1 of a real quadratic field and a = ε⁻¹ − ε. If
> a ∉ {1, 3} ∪ 𝓔_odd ∪ {2, 6, 10, 14, 18, 30}, then χ₂(ε) is irrational. The 47 excluded traces are 41 odd ones (a = 1, 3
> and the 39 of 𝓔_odd) and 6 even ones (a = 2m with m = 1 or m ∈ {3, 5, 7, 9, 15}).

> **Corollary (Theorem U, m = 2). Let φ = (1 + √5)/2 be the golden ratio. Then π² − 18 log²φ = 5.70143763069985955388…
> is irrational.** Equivalently, χ₂(√5 − 2) = π²/24 − ¾ log²φ = 0.23755990127916081474… is irrational.

The norm −1 corollary is not a separate Lean statement: it is Theorems V and V_odd together, as stated above. In Lean:

```lean
-- Chi2U/V/Defs.lean, Chi2U/V/Interface.lean
def Chi2U.V.TheoremV : Prop :=
  ∀ m : ℕ, 2 ≤ m → m ∉ ({3, 5, 7, 9, 15} : Finset ℕ) → Irrational (chi2 (Real.sqrt ((m : ℝ) ^ 2 + 1) - m))
theorem Chi2U.V.theoremV : Chi2U.V.TheoremV

-- Chi2U/VOdd/Defs.lean, Chi2U/VOdd/Interface.lean
def Chi2U.VOdd.EOdd : Finset ℕ :=
  {5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33, 35, 37, 39, 41, 43, 45, 47, 49, 51, 53, 55, 57,
    63, 65, 69, 75, 77, 81, 85, 87, 93, 99, 105, 165}
def Chi2U.VOdd.TheoremVOdd : Prop :=
  ∀ a : ℕ, Odd a → 5 ≤ a → a ∉ EOdd → Irrational (chi2 ((Real.sqrt ((a : ℝ) ^ 2 + 4) - a) / 2))
theorem Chi2U.VOdd.theoremVOdd : Chi2U.VOdd.TheoremVOdd

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
'Chi2U.VOdd.theoremVOdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2U.chi2_sqrt5_sub_two_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
'Chi2U.golden_irrational'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`goldenRatio` is Mathlib's `(1 + √5)/2` and `Irrational` is Mathlib's. The closed form is itself proved (from Landen's
identity for χ₂ and Euler's reflection and Landen's identity for the dilogarithm), so the golden-ratio form is not a
separate assumption. The proof uses only Lean's three standard axioms. There is no `sorry`, no added `axiom` and no
`native_decide`: the numerical certificates are evaluated by the Lean kernel. See [TRUST.md](TRUST.md).

The paper, "Irrationality of χ₂ and Ti₂ at units of real quadratic fields", is
[`paper/chi2-quadratic-units-irrationality.pdf`](paper/chi2-quadratic-units-irrationality.pdf) (source `paper/main.tex`).

## Context

We have not found Theorem V, Theorem V_odd, Theorem U, or the irrationality of any number π² + c log²φ with
c ∈ ℚ \ {0}, in the literature. For m ≥ 3 the values χ₂(√(m² + 1) − m) have no expression through π² and logarithms by
symbol-preserving dilogarithm identities (paper, Proposition on the symbol); only m = 1, 2 have a Landen closed form.
Explicit linear independence criteria at algebraic points (David–Hirata-Kohno–Kawashima) cover χ₂(√(m² + 1) − m) only
for m ≥ 4 346 237, and χ₂((√(a² + 4) − a)/2) for odd a only for a ≥ 8 692 474, by our evaluation.

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
and recent Lean repositories, but not MathSciNet or Google Scholar; for odd a they were much shorter (our notes and the
web). Please tell us if you know of prior work.

## Outline of the proof

The machine is formalised once, with the trace a of the unit as a parameter (`az` in the files: z = `zU az` =
(√(a² + 4) − a)/2, `Qd az` = ℚ(√(a² + 4)) as `QuadraticAlgebra ℚ ((a/2)² + 1) 0`, `zK az`, `Delta az h`). Theorem U is
a = 4, Theorem V is a = 2m, Theorem V_odd is odd a. We describe it at a = 4; the changes for other traces follow the
outline. The proof transposes the proof of [chi2-irrationality](https://github.com/telaviv/chi2-irrationality)
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
   plus a two-sided Jensen bound for the pole product. The certificate is in a linear-majorant format (`Cert/Lin.lean`):
   on each cell of the grid of width 1/40 on [0, 4] (160 cells) it gives an affine upper bound of 2U^μ + v, charged by
   the trapezoid rule, and its rational exponent is Φ_Q = −1.3541990… < −1.354. Refining the grid
   (`LinCertU.exists_dual`) turns it into an ordinary dual certificate (`DualCertU`) with Φ ≤ −1.354, below the
   constant Φ_L = −1.3538792 used for the other traces and below −27/20. Every check is done by `decide +kernel` in
   rational interval arithmetic (`Cert/LinInstance.lean`; data `Cert/DataU.lean`; the shared table of 1004 logarithm
   enclosures `Cert/LogTab.lean`). Files: `Analytic/`, `Cert/`, `Interval/`.
4. **Nonvanishing (Lemma P′).** For h = 3ℓ − 1 with ℓ ≥ 7 prime, the Gram matrix in the Lagrange basis is block
   diagonal modulo a prime of ℚ(√5) above ℓ, with 3 × 3 blocks in closed form, so Δ_h(a/b) ≠ 0 whenever ℓ² ∤ b.
   Every prime ℓ ≥ 7 works. Files: `NonVan/`.
5. **Conclusion (Lemma E).** The formal margin is 4/3 − 27/20 = −1/60 per h² (the paper's certificate gives
   −0.02588…). So den_h·Δ_h(T) → 0 faster than any b^{−h}, which contradicts T = a/b. Files: `Criterion.lean`,
   `MainCond.lean`, `Main.lean`.
6. **Even trace (Theorem V), files `V/`.** z_m = √(m² + 1) − m, 1 − z_m² = 2m·z_m.
   - p = 2 (Lemma 10_ν, ν = 1 + v₂(m)): cost |ν − 2|·log 2/4 per h². Files: `V/Lemma10nu.lean`, `V/TwoAdicNu.lean`.
   - Odd p | m (Lemma S): cost (e/4 + 1/(4(p − 1)))·log p per h², e = v_p(m), from a multi-level Lemma 8′ and the
     Mahler form. Files: `V/LemmaS.lean`, `V/S*.lean`, `V/AKSize.lean`.
   - Analytic part: the shift lemma moves Theorem U's certificate from z₂ = √5 − 2 to z_m, gaining ½ log(z₂/z_m), with
     the constant Φ_L = −1.3538792. File: `V/Shift.lean`.
   - Margins: negative for every m ≥ 2 outside {3, 5, 7, 9, 15} (closed form for even m ≥ 4 and odd m ≥ 69, the rest
     case by case). File: `V/Margin.lean`.
   - Nonvanishing: Lemma P′ holds at every trace a and every prime ℓ ≥ 7 with ℓ ∤ a (`NonVan/` is generic in a).
   - Assembly: `V/Interface.lean`.
7. **Odd trace (Theorem V_odd), files `VOdd/`.** z = (√(a² + 4) − a)/2 with a odd, 1 − z² = a·z; the prime 2 is inert
   in ℚ(√(a² + 4)).
   - p = 2 (Lemma 10_0): n₂ ≤ h²/2 + h, a cost of ½ log 2 per h². The entry bounds of Lemma 10_ν at ν = 0, a tent-shaped
     concave minorant and the same weighted Leibniz bound. File: `VOdd/TenZero.lean`.
   - Odd p ∤ a, odd p | a (Lemma S), Theorem B′ and Lemma P′ (with ℓ ∤ a(a² + 4)) are the trace-generic files above.
   - Analytic part: the shift lemma from Theorem U's certificate, except at the 11 traces a = 59, 61, 67, 91, 95, 111,
     117, 123, 135, 147, 195, which have direct certificates in the linear-majorant format (grids 1/20 to 1/100). The
     paper needs ten of them; Lean also needs a = 123, because Φ_L is 0.0053 weaker than the paper's constant
     Φ_U = −1.3592162 and the paper's shift margin at a = 123 is only −0.000034. Files: `VOdd/CertOdd.lean`,
     `VOdd/CertData/A*.lean`.
   - Margins: a closed form for odd a ≥ 275 (the primes 3, 5, 7 are split off), and the 96 odd a < 275 outside 𝓔_odd
     one by one. File: `VOdd/Margin.lean`.
   - Assembly: `VOdd/Interface.lean`.
8. **Golden-ratio form.** χ₂(√5 − 2) = π²/24 − ¾ log²φ from Landen's identity for χ₂ at x = √5 − 2 (where
   (1 − x)/(1 + x) = φ⁻¹) and the value of χ₂(φ⁻¹), itself derived from Euler's reflection and Landen's identity for
   Li₂. Files: `Golden/`.

The paper also proves an extension that is **not** formalised here: Ti₂(m − √(m² − 1)) ∉ ℚ for m ≥ 4,
m ∉ {5, 7, 9, 15}, and Ti₂ at the units of norm +1 with odd trace n ≥ 71 outside 17 values (Theorem V_i, checked by one
AI referee). Its two-point statement at units of biquadratic fields (Theorem M1) is computer-assisted and is not
formalised either.

## Building and checking

You need [elan](https://github.com/leanprover/elan). The toolchain (Lean v4.35.0) and Mathlib (v4.35.0) are pinned in
`lean-toolchain` and `lakefile.toml`.

```sh
lake exe cache get                 # download prebuilt Mathlib
LEAN_NUM_THREADS=4 lake build      # about 10 minutes once Mathlib is cached (9143 jobs)
lake env lean Axioms.lean          # print the axioms of the main theorems and their ingredients
```

The thread limit follows the author's larger Lean repositories, where a build at Lake's default concurrency once ran out
of memory on Windows; this project is much smaller, so a plain `lake build` should also work on most machines. The
fresh-clone check and its timing are recorded in [TRUST.md](TRUST.md).

The generated files (Python with numpy, mpmath and gmpy2; see TRUST.md) are reproduced as follows.
- `python scripts/gen_cert_u.py` (no arguments) writes Theorem U's certificate `Chi2U/Cert/DataU.lean` and the shared
  log table `Chi2U/Cert/LogTab.lean`. It runs `scripts/gen_cert_lin.py 4 10 8 4 --tab LogTab.tab 1004
  Chi2U/Cert/LogTab.lean --tabout --checkfull --checktab --chunk 40 --lean Chi2U/Cert/DataU.lean --ns Chi2U.Cert.DataU`.
- `scripts/gen_cert_lin.py` is the generator of the linear-majorant certificates at any trace. The 11 certificates of
  Theorem V_odd were written by `python scripts/gen_cert_lin.py a N s 4 --tab LogTab.tab 1004 Chi2U/Cert/LogTab.lean
  --chunk 40 --lean Chi2U/VOdd/CertData/A<a>.lean --ns Chi2U.VOdd.CertData.A<a>`, with the parameters (N, s) and the
  chunk size recorded in the first line of each file (`--chunk 50` for a = 135).
- `python scripts/margin_vodd_cases.py --gen` writes the case section of `Chi2U/VOdd/Margin.lean`; without `--gen` it
  recomputes the margins of Theorem V_odd with the Lean constants (60 digits, odd a ≤ 5001) and checks that the set of
  odd a with a nonnegative margin is exactly 𝓔_odd.
- `scripts/margins_lean.py` and `scripts/margin_v_cases.py` evaluate the margins of Theorem V with the Lean constants.
- `scripts/check_defs.py` (python-flint) re-implements the Lean definitions and compares them with the paper's machine;
  its output is `scripts/check_defs.out` (`scripts/check_defs_v.py`, `scripts/check_defs_v.out` for other traces,
  including the odd trace a = 5).

The computations of the paper are in [`scripts/paper/`](scripts/paper/README.md).

## Repository layout

Paths are relative to `Chi2U/`.

| path | content |
|---|---|
| `Defs.lean`, `Statement.lean` | χ₂ and Theorem U |
| `V/` | Theorem V: `Defs` (statement, constants), Lemma 10_ν, Lemma S, shift lemma, margins, Lemma P′_m, `Interface` (assembly) |
| `VOdd/` | Theorem V_odd: `Defs` (statement, 𝓔_odd, constants), `TenZero` (Lemma 10_0), `CertOdd` and `CertData/A*.lean` (the 11 direct certificates), `Margin` (margins), `Interface` (assembly) |
| `Golden/` | the closed form π²/24 − ¾ log²φ (Landen, dilogarithm identities) and the golden-ratio corollaries |
| `Field.lean` | ℚ(√(a² + 4)) = `QuadraticAlgebra ℚ ((a/2)² + 1) 0`, z = (√(a² + 4) − a)/2, conjugation, real embedding |
| `Moments.lean`, `MomentSeries.lean`, `Mahler.lean` | odd moments, the moment functional, the Mahler (forward-difference) form |
| `Machine.lean`, `LemmaR.lean` | poles, D, partial sums, the functionals A, B, Δ_h ∈ ℚ[X]; Lemma R and Corollary R |
| `PoleExpansion.lean` | Lemma 1′: Λ = A + T·B |
| `Criterion.lean`, `MainCond.lean` | Lemma E and the conditional main theorem |
| `Arith/` | Lemmas 8A′, B, 8′, 9′, 10′, Theorem A′, the denominators |
| `PNT/` | prime number theorem (θ(x) ~ x) and prime sums |
| `Analytic/` | Theorem B′: node expansion, slot determinants, lattice energy inequality, pole bound |
| `Interval/`, `Cert/` | rational interval arithmetic, log enclosures, and the kernel-checked dual certificates |
| `Cert/Lin.lean`, `Cert/LinInstance.lean` | linear-majorant certificates, their conversion to `DualCertU` by grid refinement, and the checked data format at any trace |
| `Cert/DataU.lean`, `Cert/LogTab.lean`, `Cert/CertU.lean` | Theorem U's certificate data and checks, the shared log table, `exists_certU` |
| `NonVan/` | Lemma P′ (every trace) |
| `Main.lean` | assembly of Theorem U |
| `../scripts/gen_cert_u.py`, `../scripts/gen_cert_lin.py` | generators of the certificate data (untrusted; see TRUST.md) |
| `../scripts/margin_vodd_cases.py` | generator of the margin cases of Theorem V_odd and the margin recomputation |
| `../scripts/check_defs.py` | exact check of the definitions against the paper's machine |
| `../scripts/leanchecker.log`, `../scripts/leanchecker_v.log`, `../scripts/leanchecker_vodd.log` | per-module results of the `leanchecker` replays |
| `../scripts/paper/` | the computation scripts of the paper |
| `../Axioms.lean` | axiom audit |
| `../FIDELITY_REFEREE.md`, `../FIDELITY_REFEREE_V.md`, `../FIDELITY_REFEREE_VODD.md` | AI referee reports on the fidelity of the statements (U, V, V_odd) |

Every Lean file starts with a docstring saying what it proves and how. The docstrings cite `PROOF_U §n`, `PROOF_V §n` and
`PROOF_VODD §n`, the working proof notes that the paper was written from. The sections of `PROOF_U` correspond to the
paper's: §1–§2 (machine, reflection, endgame) → paper §2, and §3–§7 → paper §3–§7 (subsection numbers can differ);
`PROOF_V` corresponds to the parts of §3–§7 for general m, and `PROOF_VODD` to the paper's section on odd a. These
notes, the planning files they mention (`notes/…`) and the project name `lean_chi2u` used in some provenance headers
belong to the development history and are not part of this repository.

## Status and caveats

- The Lean kernel has checked the proof, and every declaration was replayed with `leanchecker` (TRUST.md). **No human
  expert has yet reviewed the mathematics or the Lean code.** The statement definitions (see TRUST.md) are short and
  worth reading.
- The construction, the proofs, the certificate programs, the paper and the Lean formalisation were produced largely by
  AI models (Claude, Anthropic), working under the direction of the author. Apart from the Lean kernel check, all
  verification so far has been done by AI systems.
- The formal margins are thin: −1/60 per h² at m = 2; about −0.0126 at m = 11 and −0.001 of slack in the closed form
  at m = 69; for odd traces −0.00025 at a = 135 and −0.0014 at a = 59 (both with direct certificates) and −0.0022 at
  a = 115 (shift lemma). They are certified, not estimated.

## Acknowledgements

- The architecture, and about 7,800 of the roughly 23,400 lines (95 modules), come from
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
