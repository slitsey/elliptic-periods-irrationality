module

public import CatalanCore.Elliptic.Main

public section

/-!
The irrationality exponent of real elliptic periods, lattice form (Theorem 1.2 of the paper): for a
lattice `L` with rational `g₂, g₃` and a nonzero real `ω ∈ L`, every `ε > 0` gives, for all large `q`
and all integers `p`, `|ω − p/q| > q^(-(3+ε))`. That is `μ(ω) ≤ 3`.

The proof is complete: the nonvanishing theorem `thm:epa` (Chudnovsky--Chudnovsky, Cor. 13.5) is proved
(`CatalanCore.Elliptic.EPA.epa`, discharged in `epaStatement_holds`), and the integral model, the
arithmetic lower bound, the analytic upper bound and the counting are proved in this tree.
-/

namespace EllipticPeriodMeasure

open CatalanCore.Elliptic

theorem real_period_measure_three (L : PeriodPair)
    (hg₂ : ∃ r : ℚ, L.g₂ = r) (hg₃ : ∃ r : ℚ, L.g₃ = r)
    (ω : ℝ) (hω : (ω : ℂ) ∈ L.lattice) (h0 : ω ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ, (q : ℝ) ^ (-(3 + ε)) < |ω - p / q| :=
  CatalanCore.Elliptic.real_period_measure_three L hg₂ hg₃ ω hω h0 ε hε

#print axioms real_period_measure_three

end EllipticPeriodMeasure
