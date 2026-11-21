# The irrationality exponent of real elliptic periods

A Lean 4 formalization of the irrationality exponent bound for real periods of elliptic curves over `ℚ`. The
irrationality exponent `μ(ξ)` of a real number `ξ` is the infimum of the `μ` such that `|ξ − p/q| > q^(−μ)` for
all integers `p` and all sufficiently large integers `q`.

## The paper

S. Litsey, *A bound for the irrationality exponent of real elliptic periods* (2026): LaTeX source and PDF in
[`paper/`](paper/) (`elliptic-periods-hexagon.tex` is the single-file version). The proof adapts the interpolation
determinant method of G. and D. Chudnovsky to the one-dimensional grid of integer multiples of the real period.

| Number | μ ≤ | New | Other bound |
|---|---|---|---|
| a nonzero real period `ω` of an elliptic curve over `ℚ` | 3 | first measure | none for curves without complex multiplication |
| `K(k)`, `0 < k < 1`, `k²` rational | 3 | first measure | none, except 2 when the curve has complex multiplication |

The first row is the curve form of the theorem and covers curves with and without complex multiplication. For
example `μ(K(1/2)) ≤ 3`, and the real period of every curve of the Cremona and LMFDB tables, such as `11a1`, has
exponent at most 3. Here `K(k) = π / (2 M(1, √(1−k²)))` is the complete elliptic integral of the first kind and `M` is
the arithmetic-geometric mean. The bound is ineffective.

## The statement

Let `L ⊂ ℂ` be a lattice whose Weierstrass invariants `g₂(L)` and `g₃(L)` are rational. Let `ω ∈ L` be real and
nonzero. For every `ε > 0` and every sufficiently large integer `q`, `|ω − p/q| > q^(−3−ε)` for every integer `p`.
So `μ(ω) ≤ 3`. By uniformization, the curve `y² = x³ − ¼g₂x − ¼g₃` has the lattice `L` as the periods of `dx/(2y)`,
so this is equivalent to the curve form. The Lean development proves the lattice form only. The equivalence is
classical and is not formalized.

```lean
theorem EllipticPeriodMeasure.real_period_measure_three (L : PeriodPair)
    (hg₂ : ∃ r : ℚ, L.g₂ = r) (hg₃ : ∃ r : ℚ, L.g₃ = r)
    (ω : ℝ) (hω : (ω : ℂ) ∈ L.lattice) (h0 : ω ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ, (q : ℝ) ^ (-(3 + ε)) < |ω - p / q|
```

The proof is kernel-checked in Lean and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. It has no
`sorry` and no `native_decide`. The challenge file contains only the statement over Mathlib, with an intentional
`sorry` placeholder. The solution file supplies the proof independently, and ends with an axiom check that does not
permit `sorryAx`.

## Other results in the literature

- G. V. Chudnovsky and D. V. Chudnovsky proved `μ(ω) = 2` for the real periods of curves with complex
  multiplication (arXiv:2610.31112). Their nonvanishing theorem for the interpolation determinant
  (their Corollary 13.5) is proved in this repository.
- The proof builds on OpenAI's proof that the irrationality exponent of π is 2
  ([openai/math](https://github.com/openai/math); preprint dated September 24, 2026, released October 6, 2026) and
  on its Lean formalization, which is vendored here.
- We know of no earlier irrationality exponent bound for a real period of an elliptic curve over `ℚ` without
  complex multiplication.

## What to read

| File | Content |
|---|---|
| [`ChallengeElliptic.lean`](ChallengeElliptic.lean) | the statement, using Mathlib only (namespace `EllipticPeriodMeasure`). This is the whole trusted statement surface |
| [`SolutionElliptic.lean`](SolutionElliptic.lean) | its proof, ending with `#print axioms` for the theorem |
| [`comparator.json`](comparator.json) | configuration for `lake comparator`, stating that `SolutionElliptic` proves exactly the statement of `ChallengeElliptic` with the three permitted axioms. The `comparator` job of the CI workflow [`.github/workflows/ci.yml`](.github/workflows/ci.yml) runs [`scripts/verify-comparator.sh`](scripts/verify-comparator.sh), with Lean's kernel and the NanoDa kernel bundled with the toolchain, the two kernels Palomar requires; the manually dispatched workflow [`comparator-timing.yml`](.github/workflows/comparator-timing.yml) times the same check with each external kernel separately. The proof is kernel-checked; it has not been run through `lake comparator` |
| [`CatalanCore/Elliptic/`](CatalanCore/Elliptic/) | the proof: the lattice and the integral model, the formal chart at the origin, the multiplier, the arithmetic lower bound, the analytic upper bound, the nonvanishing theorem and the counting |
| [`formalization.yaml`](formalization.yaml) | provenance, authorship, automation and scope |

## The proof

For a lattice with rational invariants and a real period `ω`, the proof compares two estimates for a determinant
whose entries are values of a theta multiplier and its jets at the centres `jω/q`. The arithmetic estimate, carried
out over `ℤ` in the chart at the origin, bounds a nonzero minor of the determinant from below through the
denominators of its entries. The analytic estimate bounds it from above. A multiplier made periodic along the real
period removes the Gaussian factor in the transport of the determinant. The analytic estimate then costs a factor
`K²` in place of `K`, where `K` is the number of centres. The two estimates contradict each other for every
exponent larger than 3. The nonvanishing of the determinant is the theorem of G. and D. Chudnovsky. The paper gives
the details.

## Vendored code

Palomar requires Lean v4.35.0-rc2 or later, and every imported file must use Lean's module system. OpenAI's
repository is pinned to Lean v4.34.1 and does not use modules, so 790 files of OpenAI's formalization (from commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` of [openai/math](https://github.com/openai/math)) and the 9 files that
OpenAI adds to PrimeNumberTheoremAnd are copied into `OAI/` and `PrimeNumberTheoremAnd/`. Each was converted to a
module and adjusted for the newer Lean and Mathlib (see [`PORTING.md`](PORTING.md)). One file of
[Tau Ceti](https://github.com/TauCetiProject/TauCeti) (commit `d800e508b1b6f8b860c9395a0ea43dc4f5375b6c`), the
theta-product part of `QPochhammer.lean`, is in `TauCeti/`. Licences and attributions are in [`NOTICE`](NOTICE); all
of this code is under the Apache License 2.0.

## Building and checking

You need [elan](https://github.com/leanprover/elan) and several GiB of free disk.

```text
lake exe cache get
python3 scripts/check-lean-sources.py
lake build
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

`lake build` builds `SolutionElliptic` and `ChallengeElliptic`. The toolchain and the Mathlib revision are pinned in
`lean-toolchain` and `lake-manifest.json`. The comparator script checks `comparator.json`; it needs Linux and
`bwrap` (bubblewrap).

## Authorship and use of AI

The mathematics, the Lean formalization and the text were produced by AI systems at the request of the author, who
posed the problem, directed the work and is responsible for it: Claude Opus 5.5, Claude Sonnet 5.5 and Claude
Fable 5.2 (Anthropic), running in Claude Code. The construction and the nonvanishing theorem are due to G. and D.
Chudnovsky, building on OpenAI's proof for π. The vendored code described above is OpenAI's and Tau Ceti's.

## Submission

This repository follows the [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate).
Submissions to the registry go through the form at https://submit.palomar-registry.org/.

## Licence

Apache License 2.0; see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
