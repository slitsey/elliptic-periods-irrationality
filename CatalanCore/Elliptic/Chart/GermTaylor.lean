module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.RingTheory.PowerSeries.Derivative

@[expose] public section

/-!
# Taylor series of analytic germs at `0` as formal power series (support for row E06)

For `f : ℂ → ℂ` put `tay f = Σ (f⁽ⁿ⁾(0)/n!) Xⁿ ∈ ℂ⟦X⟧`. For functions analytic at `0` this is a
ring homomorphism for `+`, `*`, `^`, constants, `X` and commutes with `d/dz` and with
`Polynomial.aeval`. Also: an analytic local inverse at a point of nonzero derivative.
-/

namespace CatalanCore.Elliptic.Chart

open Filter Topology PowerSeries

noncomputable section

/-- The Taylor series of `f` at `0`. -/
def tay (f : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => iteratedDeriv n f 0 / (n.factorial : ℂ)

theorem coeff_tay (f : ℂ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (tay f) = iteratedDeriv n f 0 / (n.factorial : ℂ) := by
  rw [tay, PowerSeries.coeff_mk]

theorem tay_congr {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 0] g) : tay f = tay g := by
  ext n
  rw [coeff_tay, coeff_tay, h.iteratedDeriv_eq n]

theorem tay_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    tay (fun z => f z + g z) = tay f + tay g := by
  ext n
  rw [coeff_tay, map_add, coeff_tay, coeff_tay,
    iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt, add_div]

theorem tay_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    tay (fun z => f z * g z) = tay f * tay g := by
  ext n
  rw [coeff_tay, iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [coeff_tay, coeff_tay]
  have h := Nat.choose_mul_factorial_mul_factorial hi'
  have hc : ((n.choose i : ℕ) : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ) =
      (n.factorial : ℂ) := by exact_mod_cast h
  have h1 : (i.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : ((n - i).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : ((n.choose i : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hi').ne'
  rw [← hc]
  first | (field_simp; done) | (field_simp; ring)

theorem tay_const (c : ℂ) : tay (fun _ => c) = PowerSeries.C c := by
  ext n
  rw [coeff_tay, iteratedDeriv_const, PowerSeries.coeff_C]
  by_cases h : n = 0
  · subst h; simp
  · simp [h]

theorem tay_id : tay (fun z : ℂ => z) = (PowerSeries.X : PowerSeries ℂ) := by
  ext n
  rw [coeff_tay, iteratedDeriv_fun_id_zero, PowerSeries.coeff_X]
  by_cases h : n = 1
  · subst h; simp
  · simp [h]

theorem tay_pow {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (m : ℕ) :
    tay (fun z => f z ^ m) = tay f ^ m := by
  induction m with
  | zero =>
    simp only [pow_zero]
    rw [tay_const, map_one]
  | succ m ih =>
    have e : (fun z => f z ^ (m + 1)) = fun z => f z ^ m * f z := by
      funext z; ring
    rw [e, tay_mul (f := fun z => f z ^ m) (hf.pow m) hf, ih, pow_succ]

theorem tay_X_pow (m : ℕ) : tay (fun z : ℂ => z ^ m) = (PowerSeries.X : PowerSeries ℂ) ^ m := by
  rw [← tay_id]
  exact tay_pow (f := fun z => z) analyticAt_id m

theorem tay_deriv {f : ℂ → ℂ} (_hf : AnalyticAt ℂ f 0) :
    tay (deriv f) = PowerSeries.derivative (tay f) := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_tay, coeff_tay, ← iteratedDeriv_succ',
    Nat.factorial_succ]
  have h : ((n.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h' : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  first | (field_simp; done) | (field_simp; ring)

theorem analyticAt_aeval {W : ℂ → ℂ} (hW : AnalyticAt ℂ W 0) (p : Polynomial ℤ) :
    AnalyticAt ℂ (fun w => Polynomial.aeval (W w) p) 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have e : (fun w => Polynomial.aeval (W w) (p + q)) =
        fun w => Polynomial.aeval (W w) p + Polynomial.aeval (W w) q := by
      funext w; simp
    rw [e]
    exact hp.add hq
  | monomial n k =>
    have e : (fun w => Polynomial.aeval (W w) (Polynomial.monomial n k)) =
        fun w => (k : ℂ) * W w ^ n := by
      funext w; simp [Polynomial.aeval_monomial]
    rw [e]
    exact analyticAt_const.mul (hW.pow n)

theorem tay_aeval {W : ℂ → ℂ} (hW : AnalyticAt ℂ W 0) (p : Polynomial ℤ) :
    tay (fun w => Polynomial.aeval (W w) p) = Polynomial.aeval (tay W) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have e : (fun w => Polynomial.aeval (W w) (p + q)) =
        fun w => Polynomial.aeval (W w) p + Polynomial.aeval (W w) q := by
      funext w; simp
    rw [e, tay_add (analyticAt_aeval hW p) (analyticAt_aeval hW q), hp, hq, map_add]
  | monomial n k =>
    have e : (fun w => Polynomial.aeval (W w) (Polynomial.monomial n k)) =
        fun w => (k : ℂ) * W w ^ n := by
      funext w; simp [Polynomial.aeval_monomial]
    rw [e, tay_mul (f := fun _ => (k : ℂ)) (g := fun w => W w ^ n) analyticAt_const (hW.pow n),
      tay_const, tay_pow hW]
    simp [Polynomial.aeval_monomial]

/-- A function analytic at `0` whose Taylor coefficients are `c n` has the power series
`∑ cₙ zⁿ`. -/
theorem hasFPowerSeriesAt_of_coeff {f : ℂ → ℂ} {c : ℕ → ℂ} (hf : AnalyticAt ℂ f 0)
    (h : ∀ n, PowerSeries.coeff n (tay f) = c n) :
    HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ c) 0 := by
  obtain rfl : c = fun n => iteratedDeriv n f 0 / (n.factorial : ℂ) :=
    funext fun n => (h n).symm.trans (coeff_tay f n)
  exact hf.hasFPowerSeriesAt

/-- An analytic function with nonvanishing derivative at `0` and `T 0 = 0` has an analytic local
inverse `ψ` with `ψ 0 = 0`. -/
theorem exists_local_inverse {T : ℂ → ℂ} (hT : AnalyticAt ℂ T 0) (h0 : T 0 = 0)
    (hd : deriv T 0 ≠ 0) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ ψ 0 = 0 ∧ (∀ᶠ z in 𝓝 0, ψ (T z) = z) ∧
      (∀ᶠ w in 𝓝 0, T (ψ w) = w) := by
  have hs := hT.hasStrictDerivAt
  refine ⟨hs.localInverse _ _ _ hd, ?_, ?_, hs.eventually_left_inverse hd, ?_⟩
  · have := hT.analyticAt_localInverse hd
    rwa [h0] at this
  · have := (hs.eventually_left_inverse hd).self_of_nhds
    rwa [h0] at this
  · have := hs.eventually_right_inverse hd
    rwa [h0] at this

end

end CatalanCore.Elliptic.Chart
