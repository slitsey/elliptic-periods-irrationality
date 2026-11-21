module

public import TauCeti.Analysis.SpecialFunctions.QPochhammer
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

/-!
# The product theta function on `ℂ / (ℤ + ℤτ)`

`theta τ x := qTheta q (e^{2π i x})` with `q = e^{2π i τ}` (Tau Ceti's theta product). For
`0 < Im τ` it is entire, has period `1`, and satisfies

* `Θ(x + τ) = -e^{-2π i x} Θ(x)` and, for `n : ℤ`,
  `Θ(x + n τ) = exp(π i n - 2π i n x - π i n (n - 1) τ) Θ(x)` (`theta_add_zsmul_tau`);
* `Θ(-x) = -e^{-2π i x} Θ(x)` (`theta_neg`);
* `Θ(x) = 0 ↔ x ∈ ℤ + ℤτ` (`theta_eq_zero_iff`);
* `Θ'(0) = -2π i P²`, `P = ∏' n, (1 - q^(n+1)) ≠ 0` (`hasDerivAt_theta_zero`).
-/

namespace CatalanCore.Elliptic.Theta

open Complex Real TauCeti

/-- The product theta function `Θ_τ(x) = qTheta (e^{2π i τ}) (e^{2π i x})`. -/
noncomputable def theta (τ x : ℂ) : ℂ :=
  qTheta (cexp (2 * π * I * τ)) (cexp (2 * π * I * x))

/-- The Euler function `P = ∏' n, (1 - q^(n+1))` at `q = e^{2π i τ}`. -/
noncomputable def eulerP (τ : ℂ) : ℂ := ∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1))

/-- The multiplier of `Θ` under `x ↦ x + n τ`. -/
noncomputable def thetaMult (τ : ℂ) (n : ℤ) (x : ℂ) : ℂ :=
  cexp (π * I * n - 2 * π * I * n * x - π * I * n * (n - 1) * τ)

/-- The multiplier of `Θ²` under `x ↦ x + m + n τ`. -/
noncomputable def thetaMult2 (τ : ℂ) (n : ℤ) (x : ℂ) : ℂ :=
  cexp (-(4 * π * I * n * x) - 2 * π * I * n * (n - 1) * τ)

variable {τ : ℂ}

lemma norm_nome_lt_one (hτ : 0 < τ.im) : ‖cexp (2 * π * I * τ)‖ < 1 := by
  rw [Complex.norm_exp]
  have h : (2 * (π : ℂ) * I * τ).re = -(2 * π * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h]
  calc Real.exp (-(2 * π * τ.im)) < Real.exp 0 := Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])
    _ = 1 := Real.exp_zero

lemma two_pi_I_ne_zero : (2 * (π : ℂ) * I) ≠ 0 := by
  simp [Real.pi_ne_zero]

lemma neg_one_eq_exp_pi_I : (-1 : ℂ) = cexp (π * I) := (Complex.exp_pi_mul_I).symm

lemma neg_one_eq_exp_neg_pi_I : (-1 : ℂ) = cexp (-(π * I)) := by
  rw [Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num

/-- `Θ` is entire. -/
theorem differentiable_theta (hτ : 0 < τ.im) : Differentiable ℂ (theta τ) :=
  differentiable_qTheta_exp (norm_nome_lt_one hτ)

/-- `Θ(x + 1) = Θ(x)`, in the form for an integer shift. -/
theorem theta_add_int (τ x : ℂ) (m : ℤ) : theta τ (x + m) = theta τ x := by
  unfold theta
  have h : cexp (2 * π * I * (x + m)) = cexp (2 * π * I * x) := by
    have : 2 * (π : ℂ) * I * (x + m) = 2 * π * I * x + m * (2 * π * I) := by ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h]

theorem theta_add_one (τ x : ℂ) : theta τ (x + 1) = theta τ x := by
  simpa using theta_add_int τ x 1

/-- `Θ(x + τ) = -e^{-2π i x} Θ(x)`. -/
theorem theta_add_tau (hτ : 0 < τ.im) (x : ℂ) :
    theta τ (x + τ) = -cexp (-(2 * π * I * x)) * theta τ x := by
  have hq := norm_nome_lt_one hτ
  have hq0 : cexp (2 * π * I * τ) ≠ 0 := Complex.exp_ne_zero _
  have hw0 : cexp (2 * π * I * x) ≠ 0 := Complex.exp_ne_zero _
  unfold theta
  have h : cexp (2 * π * I * (x + τ)) = cexp (2 * π * I * τ) * cexp (2 * π * I * x) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [h, qTheta_mul_left hq hq0 hw0, Complex.exp_neg]

/-- The inverse of the multiplier: `Θ(x - τ) = -e^{2π i (x - τ)} Θ(x)`. -/
theorem theta_sub_tau (hτ : 0 < τ.im) (x : ℂ) :
    theta τ (x - τ) = -cexp (2 * π * I * (x - τ)) * theta τ x := by
  have h3 := theta_add_tau hτ (x - τ)
  rw [sub_add_cancel] at h3
  have e1 : cexp (2 * π * I * (x - τ)) * cexp (-(2 * π * I * (x - τ))) = 1 := by
    rw [← Complex.exp_add]; simp
  linear_combination (cexp (2 * π * I * (x - τ))) * h3 + (-(theta τ (x - τ))) * e1

private lemma theta_step_up (hτ : 0 < τ.im) (n : ℤ)
    (ih : ∀ x, theta τ (x + n * τ) = thetaMult τ n x * theta τ x) :
    ∀ x, theta τ (x + ((n + 1 : ℤ) : ℂ) * τ) = thetaMult τ (n + 1) x * theta τ x := by
  intro x
  have h1 : x + ((n + 1 : ℤ) : ℂ) * τ = (x + n * τ) + τ := by push_cast; ring
  rw [h1, theta_add_tau hτ, ih x]
  have h2 : thetaMult τ (n + 1) x =
      cexp (π * I) * cexp (-(2 * π * I * (x + n * τ))) * thetaMult τ n x := by
    unfold thetaMult
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h2, Complex.exp_pi_mul_I]
  ring

private lemma theta_step_down (hτ : 0 < τ.im) (n : ℤ)
    (ih : ∀ x, theta τ (x + n * τ) = thetaMult τ n x * theta τ x) :
    ∀ x, theta τ (x + ((n - 1 : ℤ) : ℂ) * τ) = thetaMult τ (n - 1) x * theta τ x := by
  intro x
  have h1 : x + ((n - 1 : ℤ) : ℂ) * τ = (x - τ) + n * τ := by push_cast; ring
  rw [h1, ih (x - τ), theta_sub_tau hτ x]
  have h2 : thetaMult τ (n - 1) x =
      thetaMult τ n (x - τ) * (cexp (-(π * I)) * cexp (2 * π * I * (x - τ))) := by
    unfold thetaMult
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h2, ← neg_one_eq_exp_neg_pi_I]
  ring

/-- **Quasi-periodicity (T4).**
`Θ(x + n τ) = exp(π i n - 2π i n x - π i n (n - 1) τ) Θ(x)` for `n : ℤ`. -/
theorem theta_add_zsmul_tau (hτ : 0 < τ.im) (n : ℤ) (x : ℂ) :
    theta τ (x + n * τ) = thetaMult τ n x * theta τ x := by
  revert x
  refine Int.induction_on n ?_ ?_ ?_
  · intro x
    simp [thetaMult]
  · intro i ih
    exact theta_step_up hτ i ih
  · intro i ih
    exact theta_step_down hτ _ ih

/-- `Θ(x + m + n τ) = thetaMult τ n x * Θ(x)` for `m n : ℤ`. -/
theorem theta_add_int_add_zsmul_tau (hτ : 0 < τ.im) (m n : ℤ) (x : ℂ) :
    theta τ (x + m + n * τ) = thetaMult τ n x * theta τ x := by
  have h1 : x + m + n * τ = (x + n * τ) + m := by ring
  rw [h1, theta_add_int, theta_add_zsmul_tau hτ]

/-- The multipliers are compatible with the translation `x ↦ x ± y`. -/
theorem thetaMult_sub_mul_add (τ : ℂ) (n : ℤ) (x y : ℂ) :
    thetaMult τ n (x - y) * thetaMult τ n (x + y) = thetaMult τ n x ^ 2 := by
  unfold thetaMult
  rw [← Complex.exp_add, sq, ← Complex.exp_add]
  congr 1
  ring

theorem thetaMult_ne_zero (τ : ℂ) (n : ℤ) (x : ℂ) : thetaMult τ n x ≠ 0 :=
  Complex.exp_ne_zero _

/-- **Quasi-periodicity of the square.** -/
theorem theta_sq_add_int_add_zsmul_tau (hτ : 0 < τ.im) (m n : ℤ) (x : ℂ) :
    theta τ (x + m + n * τ) ^ 2 = thetaMult2 τ n x * theta τ x ^ 2 := by
  have h1 : x + m + n * τ = (x + n * τ) + m := by ring
  rw [h1, theta_add_int, theta_add_zsmul_tau hτ, mul_pow]
  congr 1
  unfold thetaMult thetaMult2
  rw [sq, ← Complex.exp_add]
  have : π * I * n - 2 * π * I * n * x - π * I * n * (n - 1) * τ +
      (π * I * n - 2 * π * I * n * x - π * I * n * (n - 1) * τ) =
      n * (2 * π * I) + (-(4 * π * I * n * x) - 2 * π * I * n * (n - 1) * τ) := by ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

/-- `Θ(0) = 0`. -/
@[simp] theorem theta_zero (τ : ℂ) : theta τ 0 = 0 := by
  simp [theta]

/-- **Reflection (T5).** For `w ≠ 0`, `θ_q(w⁻¹) = -w⁻¹ θ_q(w)`. -/
theorem qTheta_inv_eq (q : ℂ) {w : ℂ} (hw : w ≠ 0) :
    qTheta q w⁻¹ = -w⁻¹ * qTheta q w := by
  rw [qTheta_def, qTheta_def, inv_inv]
  have h : ∏' n : ℕ, (1 - q ^ (n + 1) * w⁻¹) * (1 - q ^ (n + 1) * w) =
      ∏' n : ℕ, (1 - q ^ (n + 1) * w) * (1 - q ^ (n + 1) * w⁻¹) :=
    tprod_congr fun n => mul_comm _ _
  rw [h]
  have h2 : (1 - w⁻¹) = -w⁻¹ * (1 - w) := by
    rw [neg_mul, mul_sub, mul_one, inv_mul_cancel₀ hw]; ring
  rw [h2]
  ring

/-- `Θ(-x) = -e^{-2π i x} Θ(x)`. -/
theorem theta_neg (τ x : ℂ) : theta τ (-x) = -cexp (-(2 * π * I * x)) * theta τ x := by
  unfold theta
  have h : cexp (2 * π * I * -x) = (cexp (2 * π * I * x))⁻¹ := by
    rw [← Complex.exp_neg]; congr 1; ring
  rw [h, qTheta_inv_eq _ (Complex.exp_ne_zero _), ← Complex.exp_neg]

/-- **Zero set (T6).** `Θ(x) = 0` iff `x ∈ ℤ + ℤτ`. -/
theorem theta_eq_zero_iff (hτ : 0 < τ.im) (x : ℂ) :
    theta τ x = 0 ↔ ∃ m n : ℤ, x = m + n * τ := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    refine qTheta_ne_zero (norm_nome_lt_one hτ) (fun k hk => ?_) h
    rw [← Complex.exp_int_mul] at hk
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 hk
    apply hne m k
    apply mul_left_cancel₀ two_pi_I_ne_zero
    linear_combination hm
  · rintro ⟨m, n, rfl⟩
    have h1 := theta_add_zsmul_tau hτ n (m : ℂ)
    have h2 : theta τ (m : ℂ) = 0 := by
      have := theta_add_int τ 0 m
      rw [zero_add, theta_zero] at this
      exact this
    rw [h1, h2, mul_zero]

/-- **Derivative at `0` (T7a).** `Θ'(0) = -2π i P²`. -/
theorem hasDerivAt_theta_zero (hτ : 0 < τ.im) :
    HasDerivAt (theta τ) (-(2 * π * I) * eulerP τ ^ 2) 0 :=
  hasDerivAt_qTheta_exp_zero (norm_nome_lt_one hτ)

theorem eulerP_ne_zero (hτ : 0 < τ.im) : eulerP τ ≠ 0 :=
  tprod_one_sub_pow_ne_zero (norm_nome_lt_one hτ)

theorem deriv_theta_zero (hτ : 0 < τ.im) : deriv (theta τ) 0 = -(2 * π * I) * eulerP τ ^ 2 :=
  (hasDerivAt_theta_zero hτ).deriv

/-- `Θ'(0) ≠ 0`. -/
theorem deriv_theta_zero_ne_zero (hτ : 0 < τ.im) : deriv (theta τ) 0 ≠ 0 := by
  rw [deriv_theta_zero hτ]
  exact mul_ne_zero (neg_ne_zero.2 two_pi_I_ne_zero) (pow_ne_zero 2 (eulerP_ne_zero hτ))

end CatalanCore.Elliptic.Theta
