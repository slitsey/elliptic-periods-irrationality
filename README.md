# A bound for the irrationality exponent of real elliptic periods

S. Litsey, *A bound for the irrationality exponent of real elliptic periods* (2026). LaTeX source and PDF are in
[`paper/`](paper/); `elliptic-periods-hexagon.tex` is the single-file version.

**Theorem.** Let `L ⊂ ℂ` be a lattice whose Weierstrass invariants `g₂(L)` and `g₃(L)` are rational. Every
nonzero real `ω ∈ L` satisfies `μ(ω) ≤ 3`: for every `ε > 0` there is `q₀` such that `|ω − p/q| > q^(−3−ε)` for
all integers `p` and all integers `q ≥ q₀`.

**Corollary.** Every nonzero real period of an elliptic curve over `ℚ`, with or without complex multiplication,
has irrationality exponent at most 3.

The bound is ineffective. For curves with complex multiplication, G. and D. Chudnovsky proved exponent 2 (arXiv
2610.31112). The proof here adapts their determinant method to the one-dimensional grid of real multiples of the
period, which exists for every curve.

A formalization in Lean 4 is intended to follow.

The use of AI in this work is described at the end of the paper.
