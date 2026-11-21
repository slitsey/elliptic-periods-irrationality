module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Order.Filter.AtTopBot.Basic

public section

/-! The elliptic-periods challenge statement (unconditional target; plan D1). The proof placeholder is the challenge-statement
convention (one `sorry`); `SolutionElliptic` proves exactly this statement, with no hypotheses. -/

namespace EllipticPeriodMeasure

theorem real_period_measure_three (L : PeriodPair)
    (hg₂ : ∃ r : ℚ, L.g₂ = r) (hg₃ : ∃ r : ℚ, L.g₃ = r)
    (ω : ℝ) (hω : (ω : ℂ) ∈ L.lattice) (h0 : ω ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ, (q : ℝ) ^ (-(3 + ε)) < |ω - p / q| := by
  sorry

end EllipticPeriodMeasure
