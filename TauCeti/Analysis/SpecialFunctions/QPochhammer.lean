/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Vendored from https://github.com/TauCetiProject/TauCeti, commit
d800e508b1b6f8b860c9395a0ea43dc4f5375b6c, file
`TauCeti/Analysis/SpecialFunctions/QPochhammer.lean` (Apache-2.0; see NOTICE).
Modifications (backport to Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2): the imports are narrowed to
what the retained declarations use; the declarations about Euler's identity, odd and level-two or
level-three products, the norm bounds, and the `UpperHalfPlane` limit are removed together with
the imports they needed (`TauCeti.Algebra.Ring.Parity`, `TauCeti.Analysis.Normed.Ring.InfiniteProd`
and, through it, `TauCeti.Analysis.Normed.Ring.Ultra`, `TauCeti.Topology.Algebra.InfiniteSum.NatInt`,
`Mathlib.Analysis.Complex.Periodic`, `…UpperHalfPlane.FunctionsBoundedAtInfty`); the one lemma used
from `TauCeti.Analysis.Normed.Ring.Basic` (`norm_pow_lt_one`) is reproved here for normed fields.
The retained proofs are unchanged.
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The theta product `θ_q(w) = (1 - w) ∏_{n ≥ 1} (1 - qⁿ w) (1 - qⁿ w⁻¹)`

For `‖q‖ < 1` in a complete normed field the products `∏_{n ≥ 1} (1 - qⁿ w)` converge, and the
theta product `qTheta q w` is nonzero off the powers of `q`, vanishes at `w = 1`, satisfies
`θ_q(q w) = -w⁻¹ θ_q(w)`, and for `q w : ℂ` the function `z ↦ θ_q(e^{2π i z})` is entire with
derivative `-2π i (∏_{n ≥ 1} (1 - qⁿ))²` at `0`.

## Main results

* `TauCeti.qTheta`, `TauCeti.qTheta_one`, `TauCeti.qTheta_mul_left`, `TauCeti.qTheta_ne_zero`.
* `TauCeti.tprod_one_sub_pow_ne_zero`: the Euler function `∏_{n ≥ 1} (1 - qⁿ)` is nonzero.
* `TauCeti.differentiable_qTheta_exp`, `TauCeti.hasDerivAt_qTheta_exp_zero`.
-/

@[expose] public section

namespace TauCeti

section NormedField

variable {𝕜 : Type*} [NormedField 𝕜]

/-- For `‖q‖ < 1` and `n ≠ 0`, `‖q ^ n‖ < 1` (reproved here for normed fields). -/
theorem norm_pow_lt_one {q : 𝕜} (hq : ‖q‖ < 1) {n : ℕ} (hn : n ≠ 0) : ‖q ^ n‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg q) hq hn

/-- For `‖q‖ < 1` the norms `‖qⁿ⁺¹ w‖` are summable. -/
theorem summable_norm_pow_succ_mul {q : 𝕜} (hq : ‖q‖ < 1) (w : 𝕜) :
    Summable fun n : ℕ ↦ ‖q ^ (n + 1) * w‖ := by
  simpa [norm_pow, pow_succ, mul_assoc] using
    (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_right (‖q‖ * ‖w‖)

/-- The **theta product** `θ_q(w) = (w; q)_∞ (q w⁻¹; q)_∞`, written as
`(1 - w) ∏_{n ≥ 1} (1 - qⁿ w) (1 - qⁿ w⁻¹)`. The product converges for `‖q‖ < 1`; otherwise the
value is a junk value. -/
noncomputable def qTheta (q w : 𝕜) : 𝕜 :=
  (1 - w) * ∏' n : ℕ, (1 - q ^ (n + 1) * w) * (1 - q ^ (n + 1) * w⁻¹)

/-- The defining product of the theta product `θ_q(w)`. -/
theorem qTheta_def (q w : 𝕜) :
    qTheta q w = (1 - w) * ∏' n : ℕ, (1 - q ^ (n + 1) * w) * (1 - q ^ (n + 1) * w⁻¹) :=
  (rfl)

/-- The theta product vanishes at `w = 1`. -/
@[simp]
theorem qTheta_one (q : 𝕜) : qTheta q 1 = 0 := by
  simp [qTheta_def]

variable [CompleteSpace 𝕜]

/-- For `‖q‖ < 1` the product `∏_{n ≥ 1} (1 - qⁿ w)` converges. -/
theorem multipliable_one_sub_pow_mul {q : 𝕜} (hq : ‖q‖ < 1) (w : 𝕜) :
    Multipliable fun n : ℕ ↦ 1 - q ^ (n + 1) * w :=
  multipliable_one_sub_of_summable (summable_norm_pow_succ_mul hq w)

/-- Shifting the product: `∏_{n ≥ 1} (1 - qⁿ w) = (1 - q w) ∏_{n ≥ 1} (1 - qⁿ (q w))`. -/
theorem tprod_one_sub_pow_mul_eq {q : 𝕜} (hq : ‖q‖ < 1) (w : 𝕜) :
    ∏' n : ℕ, (1 - q ^ (n + 1) * w) = (1 - q * w) * ∏' n : ℕ, (1 - q ^ (n + 1) * (q * w)) := by
  rw [tprod_eq_zero_mul' (by simpa [pow_succ, mul_assoc] using
    multipliable_one_sub_pow_mul hq (q * w))]
  simp [pow_succ, mul_assoc]

/-- Shifting the product with an inverted argument:
`∏_{n ≥ 1} (1 - qⁿ (q w)⁻¹) = (1 - w⁻¹) ∏_{n ≥ 1} (1 - qⁿ w⁻¹)` for `q ≠ 0`. -/
theorem tprod_one_sub_pow_mul_inv_eq {q : 𝕜} (hq : ‖q‖ < 1) (hq₀ : q ≠ 0) (w : 𝕜) :
    ∏' n : ℕ, (1 - q ^ (n + 1) * (q * w)⁻¹) = (1 - w⁻¹) * ∏' n : ℕ, (1 - q ^ (n + 1) * w⁻¹) := by
  have h : ∀ n : ℕ, q ^ (n + 1) * (q * w)⁻¹ = q ^ n * w⁻¹ := fun n ↦ by
    rw [mul_inv, pow_succ]
    field_simp
  simp_rw [h]
  rw [tprod_eq_zero_mul' (f := fun n ↦ 1 - q ^ n * w⁻¹) (multipliable_one_sub_pow_mul hq w⁻¹)]
  simp

omit [CompleteSpace 𝕜] in
/-- If the factors `1 - qⁿ⁺¹ w` are nonzero, so is `∏_{n ≥ 1} (1 - qⁿ w)`. If the product is not
multipliable, it is `1` by convention. -/
theorem tprod_one_sub_pow_mul_ne_zero {q : 𝕜} (hq : ‖q‖ < 1) {w : 𝕜}
    (h : ∀ n : ℕ, 1 - q ^ (n + 1) * w ≠ 0) : ∏' n : ℕ, (1 - q ^ (n + 1) * w) ≠ 0 := by
  by_cases hm : Multipliable fun n : ℕ ↦ 1 - q ^ (n + 1) * w
  swap
  · rw [tprod_eq_one_of_not_multipliable hm]
    exact one_ne_zero
  intro h0
  -- transport the product along the isometric embedding of `𝕜` into its completion
  let ι : 𝕜 →+* UniformSpace.Completion 𝕜 := UniformSpace.Completion.coeRingHom
  have hι : Continuous ι := UniformSpace.Completion.continuous_coe 𝕜
  have hmap := (hm.hasProd.map ι hι).tprod_eq
  rw [Function.comp_def, h0, map_zero] at hmap
  refine tprod_one_add_ne_zero_of_summable
    (f := fun n : ℕ ↦ -(ι q ^ (n + 1) * ι w)) (fun n ↦ ?_) ?_ ?_
  · rw [← sub_eq_add_neg, ← map_pow, ← map_mul, ← map_one ι, ← map_sub]
    exact (map_ne_zero ι).2 (h n)
  · have hnorm : ∀ x : 𝕜, ‖ι x‖ = ‖x‖ := UniformSpace.Completion.norm_coe
    simpa only [norm_neg, ← map_pow, ← map_mul, hnorm] using summable_norm_pow_succ_mul hq w
  · convert hmap using 3 with n
    simp [ι, sub_eq_add_neg]

omit [CompleteSpace 𝕜] in
/-- For `‖q‖ < 1` the Euler function `∏_{n ≥ 1} (1 - qⁿ)` is nonzero. -/
theorem tprod_one_sub_pow_ne_zero {q : 𝕜} (hq : ‖q‖ < 1) : ∏' n : ℕ, (1 - q ^ (n + 1)) ≠ 0 := by
  refine (tprod_congr fun n ↦ by rw [mul_one]).symm.trans_ne
    (tprod_one_sub_pow_mul_ne_zero hq (w := 1) fun n h ↦ ?_)
  have h1 := norm_pow_lt_one hq n.succ_ne_zero
  rw [mul_one, sub_eq_zero] at h
  simp [← h] at h1

/-- For `‖q‖ < 1` the product `∏_{n ≥ 1} (1 - qⁿ w) (1 - qⁿ w⁻¹)` in the theta product
converges. -/
theorem multipliable_qTheta {q : 𝕜} (hq : ‖q‖ < 1) (w : 𝕜) :
    Multipliable fun n : ℕ ↦ (1 - q ^ (n + 1) * w) * (1 - q ^ (n + 1) * w⁻¹) :=
  (multipliable_one_sub_pow_mul hq w).mul (multipliable_one_sub_pow_mul hq w⁻¹)

/-- For `‖q‖ < 1` the theta product `θ_q(w)` is `1 - w` times its two half products
`∏_{n ≥ 1} (1 - qⁿ w)` and `∏_{n ≥ 1} (1 - qⁿ w⁻¹)`. -/
theorem qTheta_eq_mul_tprod_mul_tprod {q : 𝕜} (hq : ‖q‖ < 1) (w : 𝕜) :
    qTheta q w = (1 - w) *
      ((∏' n : ℕ, (1 - q ^ (n + 1) * w)) * ∏' n : ℕ, (1 - q ^ (n + 1) * w⁻¹)) := by
  rw [qTheta_def, (multipliable_one_sub_pow_mul hq _).tprod_mul (multipliable_one_sub_pow_mul hq _)]

omit [CompleteSpace 𝕜] in
/-- For `‖q‖ < 1` the theta product `θ_q(w)` is nonzero when `w` is not an integral power of
`q`. If the defining product is not multipliable, it is `1` by convention. -/
theorem qTheta_ne_zero {q : 𝕜} (hq : ‖q‖ < 1) {w : 𝕜} (hw : ∀ k : ℤ, w ≠ q ^ k) :
    qTheta q w ≠ 0 := by
  rw [qTheta_def]
  refine mul_ne_zero (sub_ne_zero.mpr fun h ↦ hw 0 (by simp [← h])) ?_
  by_cases hm : Multipliable fun n : ℕ ↦ (1 - q ^ (n + 1) * w) * (1 - q ^ (n + 1) * w⁻¹)
  swap
  · rw [tprod_eq_one_of_not_multipliable hm]
    exact one_ne_zero
  have h₁ : ∀ n : ℕ, 1 - q ^ (n + 1) * w ≠ 0 := fun n h ↦ hw (-(n + 1 : ℕ)) (by
    rw [zpow_neg, zpow_natCast]
    exact eq_inv_of_mul_eq_one_right (sub_eq_zero.mp h).symm)
  have h₂ : ∀ n : ℕ, 1 - q ^ (n + 1) * w⁻¹ ≠ 0 := fun n h ↦ hw (n + 1 : ℕ) (by
    rw [zpow_natCast, ← inv_inj]
    exact eq_inv_of_mul_eq_one_right (sub_eq_zero.mp h).symm)
  intro h0
  -- transport the product along the isometric embedding of `𝕜` into its completion
  let ι : 𝕜 →+* UniformSpace.Completion 𝕜 := UniformSpace.Completion.coeRingHom
  have hι : Continuous ι := UniformSpace.Completion.continuous_coe 𝕜
  have hq' : ‖ι q‖ < 1 := by
    have hnorm : ∀ x : 𝕜, ‖ι x‖ = ‖x‖ := UniformSpace.Completion.norm_coe
    rwa [hnorm]
  have hmap := (hm.hasProd.map ι hι).tprod_eq
  rw [Function.comp_def, h0, map_zero] at hmap
  simp only [map_mul, map_sub, map_one, map_pow, map_inv₀] at hmap
  rw [(multipliable_one_sub_pow_mul hq' _).tprod_mul (multipliable_one_sub_pow_mul hq' _)] at hmap
  rcases mul_eq_zero.1 hmap with h | h
  · refine tprod_one_sub_pow_mul_ne_zero hq' (fun n ↦ ?_) h
    simpa only [map_mul, map_sub, map_one, map_pow] using (map_ne_zero ι).2 (h₁ n)
  · refine tprod_one_sub_pow_mul_ne_zero hq' (fun n ↦ ?_) h
    simpa only [map_mul, map_sub, map_one, map_pow, map_inv₀] using (map_ne_zero ι).2 (h₂ n)

/-- **Quasi-periodicity of the theta product**: `θ_q(q w) = -w⁻¹ θ_q(w)` for `0 < ‖q‖ < 1` and
`w ≠ 0`. -/
theorem qTheta_mul_left {q : 𝕜} (hq : ‖q‖ < 1) (hq₀ : q ≠ 0) {w : 𝕜} (hw : w ≠ 0) :
    qTheta q (q * w) = -w⁻¹ * qTheta q w := by
  rw [qTheta_def, qTheta_def,
    (multipliable_one_sub_pow_mul hq _).tprod_mul (multipliable_one_sub_pow_mul hq _),
    (multipliable_one_sub_pow_mul hq _).tprod_mul (multipliable_one_sub_pow_mul hq _),
    tprod_one_sub_pow_mul_inv_eq hq hq₀, tprod_one_sub_pow_mul_eq hq w]
  field_simp
  ring

end NormedField

section LocallyUniform

variable {q w : ℂ → ℂ} {U : Set ℂ}

/-- For `q` and `w` continuous on an open set `U` with `‖q‖ < 1` on `U`, the product
`∏_{n ≥ 1} (1 - q(τ)ⁿ w(τ))` converges locally uniformly on `U`. -/
theorem hasProdLocallyUniformlyOn_one_sub_pow_mul (hU : IsOpen U) (hq : ContinuousOn q U)
    (hq₁ : ∀ τ ∈ U, ‖q τ‖ < 1) (hw : ContinuousOn w U) :
    HasProdLocallyUniformlyOn (fun (n : ℕ) τ ↦ 1 - q τ ^ (n + 1) * w τ)
      (fun τ ↦ ∏' n : ℕ, (1 - q τ ^ (n + 1) * w τ)) U := by
  simp_rw [sub_eq_add_neg]
  refine hasProdLocallyUniformlyOn_of_forall_compact hU fun S hSU hS ↦ ?_
  obtain ⟨ρ, hρ₀, hρ₁, hρ⟩ : ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ τ ∈ S, ‖q τ‖ ≤ ρ := by
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, le_rfl, one_pos, by simp⟩
    obtain ⟨τ₀, hτ₀, hmax⟩ := hS.exists_isMaxOn hne (hq.mono hSU).norm
    exact ⟨_, norm_nonneg _, hq₁ τ₀ (hSU hτ₀), hmax⟩
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn (hw.mono hSU)
  refine ((summable_geometric_of_lt_one hρ₀ hρ₁).mul_left (ρ * M)).hasProdUniformlyOn_nat_one_add
    hS (.of_forall fun n τ hτ ↦ ?_) fun n ↦ by
      have := hq.mono hSU
      have := hw.mono hSU
      fun_prop
  calc ‖-(q τ ^ (n + 1) * w τ)‖
      = ‖q τ‖ ^ (n + 1) * ‖w τ‖ := by simp [norm_pow]
    _ ≤ ρ ^ (n + 1) * M :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hρ τ hτ) _) (hM τ hτ) (norm_nonneg _)
        (pow_nonneg hρ₀ _)
    _ = ρ * M * ρ ^ n := by ring

/-- For `q` and `w` holomorphic on an open set `U` with `‖q‖ < 1` on `U`, the product
`∏_{n ≥ 1} (1 - q(τ)ⁿ w(τ))` is holomorphic on `U`. -/
theorem differentiableOn_tprod_one_sub_pow_mul (hU : IsOpen U) (hq : DifferentiableOn ℂ q U)
    (hq₁ : ∀ τ ∈ U, ‖q τ‖ < 1) (hw : DifferentiableOn ℂ w U) :
    DifferentiableOn ℂ (fun τ ↦ ∏' n : ℕ, (1 - q τ ^ (n + 1) * w τ)) U :=
  (hasProdLocallyUniformlyOn_one_sub_pow_mul hU hq.continuousOn hq₁
    hw.continuousOn).differentiableOn (.of_forall fun s ↦ by
      simpa [Finset.prod_fn] using DifferentiableOn.finsetProd fun _ _ ↦ by fun_prop) hU

end LocallyUniform

section Holomorphic

variable {q : ℂ}

/-- The product of the two half products of `θ_q(w)` is holomorphic on `ℂ \ {0}`. -/
private theorem differentiableOn_tprod_mul_tprod (hq : ‖q‖ < 1) :
    DifferentiableOn ℂ (fun w : ℂ ↦
      (∏' n : ℕ, (1 - q ^ (n + 1) * w)) * ∏' n : ℕ, (1 - q ^ (n + 1) * w⁻¹)) {0}ᶜ :=
  (differentiableOn_tprod_one_sub_pow_mul (q := fun _ ↦ q) isOpen_compl_singleton
    (differentiableOn_const q) (fun _ _ ↦ hq) differentiableOn_id).mul
    (differentiableOn_tprod_one_sub_pow_mul (q := fun _ ↦ q) isOpen_compl_singleton
      (differentiableOn_const q) (fun _ _ ↦ hq) (differentiableOn_inv.mono fun _ h ↦ h))

/-- For `‖q‖ < 1` the theta product `w ↦ θ_q(w)` is holomorphic on `ℂ \ {0}`. -/
theorem differentiableOn_qTheta (hq : ‖q‖ < 1) : DifferentiableOn ℂ (qTheta q) {0}ᶜ := by
  rw [show qTheta q = _ from funext (qTheta_eq_mul_tprod_mul_tprod hq)]
  exact (differentiableOn_const 1 |>.sub differentiableOn_id).mul
    (differentiableOn_tprod_mul_tprod hq)

/-- For `‖q‖ < 1` the theta product has a simple zero at `w = 1`: its derivative there is
`-(∏_{n ≥ 1} (1 - qⁿ))²`. -/
theorem hasDerivAt_qTheta_one (hq : ‖q‖ < 1) :
    HasDerivAt (qTheta q) (-(∏' n : ℕ, (1 - q ^ (n + 1))) ^ 2) 1 := by
  have h := ((hasDerivAt_id (1 : ℂ)).const_sub 1).mul
    (((differentiableOn_tprod_mul_tprod hq).differentiableAt
      (isOpen_compl_singleton.mem_nhds one_ne_zero)).hasDerivAt)
  rw [show qTheta q = _ from funext (qTheta_eq_mul_tprod_mul_tprod hq)]
  convert h using 1
  · funext w
    simp
  · simp [sq]

open Complex in
open scoped Real in
/-- For `‖q‖ < 1`, `z ↦ θ_q(e^{2π i z})` is an entire function. -/
theorem differentiable_qTheta_exp (hq : ‖q‖ < 1) :
    Differentiable ℂ fun z : ℂ ↦ qTheta q (cexp (2 * π * I * z)) := fun z ↦
  ((differentiableOn_qTheta hq).differentiableAt
    (isOpen_compl_singleton.mem_nhds (exp_ne_zero _))).comp (f := fun z ↦ cexp (2 * π * I * z)) z
    (by fun_prop)

open Complex in
open scoped Real in
/-- For `‖q‖ < 1` the derivative of `z ↦ θ_q(e^{2π i z})` at `z = 0` is
`-2π i (∏_{n ≥ 1} (1 - qⁿ))²`. -/
theorem hasDerivAt_qTheta_exp_zero (hq : ‖q‖ < 1) :
    HasDerivAt (fun z : ℂ ↦ qTheta q (cexp (2 * π * I * z)))
      (-(2 * π * I) * (∏' n : ℕ, (1 - q ^ (n + 1))) ^ 2) 0 := by
  have h := (hasDerivAt_qTheta_one hq).comp_of_eq (0 : ℂ)
    ((hasDerivAt_id (0 : ℂ)).const_mul (2 * π * I)).cexp (by simp)
  convert h using 1
  · funext z
    simp
  · simp only [id, mul_zero, Complex.exp_zero, mul_one]
    ring

end Holomorphic

end TauCeti
