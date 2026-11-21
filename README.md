# A bound for the irrationality exponent of real elliptic periods

S. Litsey, *A bound for the irrationality exponent of real elliptic periods* (2026). LaTeX source and PDF are in
[`paper/`](paper/); `elliptic-periods-hexagon.tex` is the single-file version.

**Theorem.** Every nonzero real period of an elliptic curve over `ℚ`, with or without complex multiplication,
has irrationality exponent at most 3: for every `ε > 0` there is `q₀` such that `|ω − p/q| > q^(−3−ε)` for all
integers `p` and all integers `q ≥ q₀`.

**Equivalent lattice form.** If `L ⊂ ℂ` is a lattice whose Weierstrass invariants `g₂(L)` and `g₃(L)` are
rational, every nonzero real `ω ∈ L` satisfies `μ(ω) ≤ 3`.

**Classical constants.** For every `0 < k < 1` with `k²` rational, the complete elliptic integral
`K(k) = π / (2 M(1, √(1−k²)))` has `μ(K(k)) ≤ 3` (`M` the arithmetic-geometric mean), e.g. `μ(K(1/2)) ≤ 3`. The
same bound holds for the real period of every elliptic curve over `ℚ` in the Cremona/LMFDB tables, e.g. `11a1`.
For curves with complex multiplication the exponent is 2 (G. and D. Chudnovsky).

The bound is ineffective. For curves with complex multiplication, G. and D. Chudnovsky proved exponent 2 (arXiv
2610.31112). The proof here adapts their determinant method to the one-dimensional grid of real multiples of the
period, which exists for every curve.

## Lean formalization

The lattice form of the theorem is formalized in Lean 4 with Mathlib (Lean v4.35.0-rc2, Mathlib v4.35.0-rc2).
The root is `SolutionElliptic.lean`. Lean proves this statement:

```lean
theorem EllipticPeriodMeasure.real_period_measure_three (L : PeriodPair)
    (hg₂ : ∃ r : ℚ, L.g₂ = r) (hg₃ : ∃ r : ℚ, L.g₃ = r)
    (ω : ℝ) (hω : (ω : ℂ) ∈ L.lattice) (h0 : ω ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ, (q : ℝ) ^ (-(3 + ε)) < |ω - p / q|
```

So for every lattice with rational `g₂` and `g₃` and every nonzero real `ω` in it, `μ(ω) ≤ 3`.

The curve form of the theorem and the lattice form are equivalent by classical uniformization: the curve
`y² = x³ − ¼g₂x − ¼g₃` has the periods of `dx/(2y)` as its lattice. The Lean development proves the lattice form
only. It does not formalize this equivalence.

The proof has no `sorry` and no `native_decide`. `#print axioms` reports only `propext`, `Classical.choice` and
`Quot.sound`. `ChallengeElliptic.lean` states the same theorem with one `sorry`, as the statement to be checked.
Comparator is the intended external check: `comparator.json` names
the challenge module, the solution module, the theorem and the permitted axioms.

### Building

You need [elan](https://github.com/leanprover/elan) and several GiB of free disk.

```text
lake exe cache get
lake build
```

`lake build` builds `SolutionElliptic` and `ChallengeElliptic`. The toolchain and the Mathlib revision are pinned
in `lean-toolchain` and `lake-manifest.json`.

### Vendored code

The repository contains 800 files from other projects, all under the Apache License 2.0.

- `OAI/` (790 files) comes from OpenAI's formalization of the irrationality of Catalan's constant,
  [openai/math](https://github.com/openai/math), commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
- `PrimeNumberTheoremAnd/` (9 files) comes from the files that OpenAI's repository adds to
  [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd).
- `TauCeti/` (1 file) comes from [Tau Ceti](https://github.com/TauCetiProject/TauCeti), commit
  `d800e508b1b6f8b860c9395a0ea43dc4f5375b6c`. It keeps the theta-product part of
  `QPochhammer.lean`.

Each file was converted to Lean's module system and adjusted for Lean v4.35.0-rc2. Licences and attributions are
in [`NOTICE`](NOTICE). Everything else in `CatalanCore/` is new work.

## Use of AI

The mathematics, the Lean formalization and the text were produced by AI systems at the request of the author, who
posed the problem, directed the work and is responsible for it: Claude Opus 5.5, Claude Sonnet 5.5 and Claude
Fable 5.2 (Anthropic), running in Claude Code. The construction and the nonvanishing theorem are due to
G. and D. Chudnovsky, building on OpenAI's proof for π. The vendored code described above is OpenAI's and Tau
Ceti's.

## Licence

Apache License 2.0; see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
