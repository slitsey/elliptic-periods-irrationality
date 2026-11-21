module

public import CatalanCore.Elliptic.Analytic.BoundDefs
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# `thm:analytic` (b): the displacement bound `eq:disp` (row E14b)

For `β ≤ ξ`, with `|δ_{ji}| ≤ exp(C_δ - ν w_i)` (`C_δ = ν + log K`) and `|ξ| ≤ H/w_min`,

`|s(β,ξ,j)| ≤ exp(-ν (W(ξ) - W(β)) + H (log 2 + C_δ)/w_min)`,

and `s(β,ξ,j) = 0` unless `β ≤ ξ`. `rpow_neg_le_exp` is the step `K q^{-ν} ≤ exp(C_δ - ν w)` from
`log q > w - 1`.
-/

namespace CatalanCore.Elliptic.Analytic

noncomputable section

theorem sCoef_eq_zero_of_not_le {m K : ℕ} (cen : Fin K → Fin m → ℚ) (Ω : ℝ) (j : Fin K)
    {β ξ : Fin m → ℕ} (h : ¬ ∀ i, β i ≤ ξ i) : sCoef cen Ω j β ξ = 0 := by
  obtain ⟨i, hi⟩ := not_forall.mp h
  unfold sCoef
  have h0 : (((ξ i).choose (β i) : ℕ) : ℂ) = 0 := by
    rw [Nat.choose_eq_zero_of_lt (not_le.mp hi), Nat.cast_zero]
  rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, zero_mul]

/-- `K q^{-ν} ≤ exp((ν + log K) - ν w)` when `log q > w - 1`, `ν ≥ 0`, `K > 0`, `q > 0`. -/
theorem rpow_neg_le_exp {q : ℝ} (hq : 0 < q) {ν w : ℝ} (hν : 0 ≤ ν) (hw : w - 1 < Real.log q)
    {K : ℝ} (hK : 0 < K) : K * q ^ (-ν) ≤ Real.exp ((ν + Real.log K) - ν * w) := by
  rw [Real.rpow_def_of_pos hq]
  have h1 : Real.log q * -ν ≤ ν - ν * w := by
    nlinarith [mul_nonneg hν (sub_nonneg.mpr hw.le)]
  calc K * Real.exp (Real.log q * -ν) ≤ K * Real.exp (ν - ν * w) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1) hK.le
    _ = Real.exp ((ν + Real.log K) - ν * w) := by
        rw [show (ν + Real.log K) - ν * w = Real.log K + (ν - ν * w) by ring, Real.exp_add,
          Real.exp_log hK]

/-- **E14b, `eq:disp`.** -/
theorem norm_sCoef_le {m K : ℕ} (cen : Fin K → Fin m → ℚ) (Ω : ℝ) (j : Fin K)
    {β ξ : Fin m → ℕ} (h : ∀ i, β i ≤ ξ i) {ν Cδ H wmin : ℝ} (hCδ : 0 ≤ Cδ) (wt : Fin m → ℝ)
    (hδ : ∀ i, ‖((cen j i : ℚ) : ℂ) - ((j : ℕ) : ℂ) * (Ω : ℂ)‖ ≤ Real.exp (Cδ - ν * wt i))
    (hwmin : 0 < wmin) (hξ : ∑ i, (ξ i : ℝ) ≤ H / wmin) :
    ‖sCoef cen Ω j β ξ‖ ≤ Real.exp (-ν * (∑ i, wt i * (ξ i : ℝ) - ∑ i, wt i * (β i : ℝ)) +
      H * (Real.log 2 + Cδ) / wmin) := by
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold sCoef
  rw [norm_mul, norm_prod, norm_prod]
  simp only [norm_pow]
  have hA : ∏ i, ‖(((ξ i).choose (β i) : ℕ) : ℂ)‖ ≤ ∏ i, Real.exp ((ξ i : ℝ) * Real.log 2) := by
    refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
    rw [Complex.norm_natCast, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast Nat.choose_le_two_pow (ξ i) (β i)
  have hB : ∏ i, ‖((cen j i : ℚ) : ℂ) - ((j : ℕ) : ℂ) * (Ω : ℂ)‖ ^ (ξ i - β i) ≤
      ∏ i, Real.exp (((ξ i - β i : ℕ) : ℝ) * (Cδ - ν * wt i)) := by
    refine Finset.prod_le_prod₀ (fun i _ => pow_nonneg (norm_nonneg _) _) fun i _ => ?_
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (hδ i) _
  have hpt : ∀ i, (ξ i : ℝ) * Real.log 2 + ((ξ i - β i : ℕ) : ℝ) * (Cδ - ν * wt i) ≤
      (ξ i : ℝ) * (Real.log 2 + Cδ) - ν * (wt i * (ξ i : ℝ) - wt i * (β i : ℝ)) := by
    intro i
    rw [Nat.cast_sub (h i)]
    have h0 : 0 ≤ Cδ * (β i : ℝ) := mul_nonneg hCδ (Nat.cast_nonneg _)
    nlinarith [h0]
  have hsum : ∑ i, ((ξ i : ℝ) * (Real.log 2 + Cδ) - ν * (wt i * (ξ i : ℝ) - wt i * (β i : ℝ))) =
      (∑ i, (ξ i : ℝ)) * (Real.log 2 + Cδ) -
        ν * (∑ i, wt i * (ξ i : ℝ) - ∑ i, wt i * (β i : ℝ)) := by
    first
      | (simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]; done)
      | (simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]; ring)
      | (simp [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]; ring)
  have hmain : ∑ i, (ξ i : ℝ) * Real.log 2 + ∑ i, ((ξ i - β i : ℕ) : ℝ) * (Cδ - ν * wt i) ≤
      -ν * (∑ i, wt i * (ξ i : ℝ) - ∑ i, wt i * (β i : ℝ)) + H * (Real.log 2 + Cδ) / wmin := by
    have h1 : ∑ i, (ξ i : ℝ) * Real.log 2 + ∑ i, ((ξ i - β i : ℕ) : ℝ) * (Cδ - ν * wt i) ≤
        ∑ i, ((ξ i : ℝ) * (Real.log 2 + Cδ) - ν * (wt i * (ξ i : ℝ) - wt i * (β i : ℝ))) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => hpt i
    have h2 := mul_le_mul_of_nonneg_right hξ (add_nonneg hl2 hCδ)
    have e : H * (Real.log 2 + Cδ) / wmin = H / wmin * (Real.log 2 + Cδ) := by ring
    rw [hsum] at h1
    rw [e]
    linarith
  calc _ ≤ (∏ i, Real.exp ((ξ i : ℝ) * Real.log 2)) *
        ∏ i, Real.exp (((ξ i - β i : ℕ) : ℝ) * (Cδ - ν * wt i)) :=
        mul_le_mul hA hB (Finset.prod_nonneg fun i _ => pow_nonneg (norm_nonneg _) _)
          (Finset.prod_nonneg fun i _ => (Real.exp_pos _).le)
    _ = Real.exp (∑ i, (ξ i : ℝ) * Real.log 2 +
          ∑ i, ((ξ i - β i : ℕ) : ℝ) * (Cδ - ν * wt i)) := by
        rw [Real.exp_add, Real.exp_sum, Real.exp_sum]
    _ ≤ _ := Real.exp_le_exp.mpr hmain

end

end CatalanCore.Elliptic.Analytic
