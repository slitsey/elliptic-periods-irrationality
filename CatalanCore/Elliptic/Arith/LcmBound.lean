module

public import Mathlib.NumberTheory.Chebyshev

@[expose] public section

/-!
# E24: the least common multiple of `1, …, n`

`log (lcm 1..n) ≤ c₀ * n` with the absolute constant `c₀ = log 4 + 4`, from Mathlib's
Chebyshev bound `Chebyshev.psi_le_const_mul_self` and `Chebyshev.psi_eq_log_lcmUpto`.
-/

namespace CatalanCore.Elliptic.Arith

/-- Absolute constant of the lcm bound. -/
noncomputable def lcmConst : ℝ := Real.log 4 + 4

theorem lcmConst_pos : 0 < lcmConst := by
  have h : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  unfold lcmConst; linarith

/-- E24: `log (lcm 1..n) ≤ c₀ n`, with `Nat.lcmUpto n = (Finset.Icc 1 n).lcm id`. -/
theorem log_lcmUpto_le (n : ℕ) : Real.log (Nat.lcmUpto n : ℝ) ≤ lcmConst * n := by
  rw [← Chebyshev.psi_eq_log_lcmUpto]
  exact Chebyshev.psi_le_const_mul_self (by positivity)

/-- E24, existential form. -/
theorem exists_log_lcmUpto_le : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ n : ℕ, Real.log (Nat.lcmUpto n : ℝ) ≤ c₀ * n :=
  ⟨lcmConst, lcmConst_pos, log_lcmUpto_le⟩

end CatalanCore.Elliptic.Arith
