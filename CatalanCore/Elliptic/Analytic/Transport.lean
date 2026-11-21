module

public import CatalanCore.Elliptic.Interfaces
public import CatalanCore.Elliptic.Chart.Germ
public import CatalanCore.Elliptic.EPA.Packet
public import CatalanCore.Elliptic.Analytic.Collision
public import CatalanCore.Elliptic.Analytic.Multiplier

@[expose] public section

/-!
# Determinant transport (row E12, `lem:transport`)

Paper: `work/paper-elliptic/elliptic-periods.tex`, `lem:transport`.

Let `M : Multiplier Λ Ω Ω' a` (`F₀ = ψ`, `F₁ = ψ u`, `F₂ = ψ² t`), `D ∈ ℕ`, centres
`c_{ji} = cen j i ∈ ℚ` and `δ_{ji} = c_{ji} - jΩ`. For a column `col = (k, b, α)` with
`k + 2b ≤ D` put `g̃_{k,b} = F₀^{D-k-2b} F₁^k F₂^b` (`gTilde`). The analytic matrix has entries

`Ã_{(j,s,β),col} = [z^s] g̃_{k,b}(jΩ + z) · C(α,β) · ∏ᵢ (jΩ + z + δ_{ji})^{αᵢ - βᵢ}`

(`transportEntry`, `transportMatrix`; `[z^s]` is `taylorCoeff s` of `Collision`).

* `transport_det_eq`: for every column selection `sel`,
  `det Ã_sel = (∏_ρ (-1)^{s_ρ}) · ψ(0)^{D J_H K} · Δ`, with `Δ = packetDelta` the packet minor (D1).
* `transport_norm`: `|det Ã_sel| = |Δ| · |ψ(0)|^{D J_H K}`, the statement of `lem:transport`.
* `IntegralModel.transport_norm`: the same for the multiplier of an integral model with
  `D = ⌈H/(2 w₀)⌉`.

Proof (the paper's). Near `0`, by `prop:germ` (A3 `Chart.germ`): `u = U∘τ`, `L∘τ = id`, `τ' (0) = -1`,
so `g̃(jΩ+z) C ∏(c_{ji}+z)^{·} = ψ(z)^D C Φ(τ(z))` with the analytic germ
`Φ(T) = fU(T)^k T^b ∏(c_{ji} + fL(T))^{α-β}` whose Taylor series is the packet series (eq:packet).
Taylor coefficients of a composition (`coeff_mul_tay_comp`) give
`Ã_{(j,s,β),col} = Σ_{s'} [z^s](ψ^D τ^{s'}) · A_{(j,s',β),col}`: left multiplication by a matrix `R`,
block diagonal over the pairs `(j,β)`, lower triangular in `s`, with diagonal `ψ(0)^D (-1)^s`.
`det R = ∏ ρ R_{ρρ}` (`det_of_grp_triangular`) gives the claim.
-/

namespace CatalanCore.Elliptic.Analytic

open Filter Topology CatalanCore.Elliptic.Chart CatalanCore.Elliptic.Lattice

noncomputable section

/-! ### Taylor series of germs: sums, products, coefficients -/

theorem constantCoeff_tay (f : ℂ → ℂ) : PowerSeries.constantCoeff (tay f) = f 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_tay]
  simp

theorem coeff_one_tay {f : ℂ → ℂ} {d : ℂ} (h : HasDerivAt f d 0) :
    PowerSeries.coeff 1 (tay f) = d := by
  rw [coeff_tay, iteratedDeriv_one, h.deriv]
  simp

theorem tay_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) 0) :
    tay (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, tay (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have e : (fun z : ℂ => ∑ i ∈ (∅ : Finset ι), f i z) = fun _ => (0 : ℂ) := by
      funext z; simp
    rw [e, tay_const]
    simp
  | insert a s ha ih =>
    have e : (fun z : ℂ => ∑ i ∈ insert a s, f i z) = fun z => f a z + ∑ i ∈ s, f i z := by
      funext z; rw [Finset.sum_insert ha]
    rw [e, tay_add (hf a (Finset.mem_insert_self a s))
      (Finset.analyticAt_fun_sum s (fun i hi => hf i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)), Finset.sum_insert ha]

theorem tay_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) 0) :
    tay (fun z => ∏ i ∈ s, f i z) = ∏ i ∈ s, tay (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have e : (fun z : ℂ => ∏ i ∈ (∅ : Finset ι), f i z) = fun _ => (1 : ℂ) := by
      funext z; simp
    rw [e, tay_const]
    simp
  | insert a s ha ih =>
    have e : (fun z : ℂ => ∏ i ∈ insert a s, f i z) = fun z => f a z * ∏ i ∈ s, f i z := by
      funext z; rw [Finset.prod_insert ha]
    rw [e, tay_mul (hf a (Finset.mem_insert_self a s))
      (Finset.analyticAt_fun_prod s (fun i hi => hf i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)), Finset.prod_insert ha]

/-- The Taylor coefficients of a function with the power series `∑ cₙ zⁿ` are the `cₙ`. -/
theorem coeff_tay_of_hasFPowerSeriesAt {f : ℂ → ℂ} {c : ℕ → ℂ}
    (h : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ c) 0) (n : ℕ) :
    PowerSeries.coeff n (tay f) = c n := by
  have h3 := h.eq_formalMultilinearSeries h.analyticAt.hasFPowerSeriesAt
  have h4 := FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ h3
  rw [coeff_tay]
  exact (congrFun h4 n).symm

theorem tay_eq_map {f : ℂ → ℂ} {P : PowerSeries ℚ}
    (h : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ fun n => ((PowerSeries.coeff n P : ℚ) : ℂ)) 0) :
    tay f = PowerSeries.map (Rat.castHom ℂ) P := by
  ext n
  rw [coeff_tay_of_hasFPowerSeriesAt h n, PowerSeries.coeff_map]
  rfl

/-- Coefficients of a composition: for `Φ`, `τ` analytic at `0` with `τ 0 = 0`,
`[z^N] (P · tay (Φ∘τ)) = ∑_{n ≤ N} [T^n] tay Φ · [z^N] (P · (tay τ)^n)`. -/
theorem coeff_mul_tay_comp {Φ τ : ℂ → ℂ} (hΦ : AnalyticAt ℂ Φ 0) (hτ : AnalyticAt ℂ τ 0)
    (hτ0 : τ 0 = 0) (P : PowerSeries ℂ) (N : ℕ) :
    PowerSeries.coeff N (P * tay (fun z => Φ (τ z))) =
      ∑ n ∈ Finset.range (N + 1),
        PowerSeries.coeff n (tay Φ) * PowerSeries.coeff N (P * tay τ ^ n) := by
  obtain ⟨r, hr, hΦr⟩ := exists_taylor_remainder_zero hΦ.hasFPowerSeriesAt (N + 1)
  have hfun : (fun z => Φ (τ z)) = fun z =>
      (∑ k ∈ Finset.range (N + 1), PowerSeries.coeff k (tay Φ) * τ z ^ k) +
        τ z ^ (N + 1) * r (τ z) := by
    funext z
    rw [hΦr (τ z)]
    simp [coeff_tay]
  have ha : ∀ k ∈ Finset.range (N + 1),
      AnalyticAt ℂ (fun z => PowerSeries.coeff k (tay Φ) * τ z ^ k) 0 :=
    fun k _ => analyticAt_const.mul (hτ.pow k)
  have hr' : AnalyticAt ℂ (fun z => r (τ z)) 0 := hr.comp_of_eq hτ hτ0
  have hsum : AnalyticAt ℂ
      (fun z => ∑ k ∈ Finset.range (N + 1), PowerSeries.coeff k (tay Φ) * τ z ^ k) 0 :=
    Finset.analyticAt_fun_sum _ ha
  have h2 : AnalyticAt ℂ (fun z => τ z ^ (N + 1) * r (τ z)) 0 := (hτ.pow _).mul hr'
  have htay : tay (fun z => Φ (τ z)) =
      (∑ k ∈ Finset.range (N + 1), PowerSeries.C (PowerSeries.coeff k (tay Φ)) * tay τ ^ k) +
        tay τ ^ (N + 1) * tay (fun z => r (τ z)) := by
    rw [congrArg tay hfun, tay_add hsum h2,
      tay_sum (Finset.range (N + 1)) (fun k z => PowerSeries.coeff k (tay Φ) * τ z ^ k) ha,
      tay_mul (f := fun z => τ z ^ (N + 1)) (g := fun z => r (τ z)) (hτ.pow (N + 1)) hr',
      tay_pow hτ]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [tay_mul (f := fun _ : ℂ => PowerSeries.coeff k (tay Φ)) (g := fun z => τ z ^ k)
      analyticAt_const (hτ.pow k), tay_const, tay_pow hτ]
  have hX : (PowerSeries.X : PowerSeries ℂ) ∣ tay τ := by
    rw [PowerSeries.X_dvd_iff, constantCoeff_tay, hτ0]
  obtain ⟨h, hh⟩ := pow_dvd_pow_of_dvd hX (N + 1)
  have hz : PowerSeries.coeff N (P * (tay τ ^ (N + 1) * tay (fun z => r (τ z)))) = 0 := by
    rw [hh]
    have e : P * (PowerSeries.X ^ (N + 1) * h * tay (fun z => r (τ z))) =
        PowerSeries.X ^ (N + 1) * (P * h * tay (fun z => r (τ z))) := by ring
    rw [e, PowerSeries.coeff_X_pow_mul']
    simp
  rw [htay, mul_add, map_add, Finset.mul_sum, map_sum, hz, add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show P * (PowerSeries.C (PowerSeries.coeff k (tay Φ)) * tay τ ^ k) =
      PowerSeries.C (PowerSeries.coeff k (tay Φ)) * (P * tay τ ^ k) by ring,
    PowerSeries.coeff_C_mul]

/-- `[z^s] (P Q^{s'}) = 0` for `s < s'` when `Q(0) = 0`. -/
theorem coeff_mul_pow_zero (P Q : PowerSeries ℂ) (hQ : PowerSeries.constantCoeff Q = 0)
    {s s' : ℕ} (h : s < s') : PowerSeries.coeff s (P * Q ^ s') = 0 := by
  obtain ⟨Q', hQ'⟩ := PowerSeries.X_dvd_iff.mpr hQ
  rw [hQ', mul_pow, show P * (PowerSeries.X ^ s' * Q' ^ s') =
    PowerSeries.X ^ s' * (P * Q' ^ s') by ring, PowerSeries.coeff_X_pow_mul']
  rw [if_neg (not_le.mpr h)]

/-- `[z^s] (P Q^s) = P(0) · (Q'(0))^s` when `Q(0) = 0`. -/
theorem coeff_mul_pow_diag (P Q : PowerSeries ℂ) (hQ : PowerSeries.constantCoeff Q = 0)
    (s : ℕ) :
    PowerSeries.coeff s (P * Q ^ s) =
      PowerSeries.constantCoeff P * (PowerSeries.coeff 1 Q) ^ s := by
  obtain ⟨Q', hQ'⟩ := PowerSeries.X_dvd_iff.mpr hQ
  have h1 : PowerSeries.coeff 1 Q = PowerSeries.constantCoeff Q' := by
    rw [hQ', show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [h1, hQ', mul_pow, show P * (PowerSeries.X ^ s * Q' ^ s) =
    PowerSeries.X ^ s * (P * Q' ^ s) by ring, PowerSeries.coeff_X_pow_mul', if_pos le_rfl,
    Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow]

/-! ### Eventual equalities near `0` -/

theorem eventuallyEq_nhds_of_punctured {f g : ℂ → ℂ} {x : ℂ} (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) (h : ∀ᶠ z in 𝓝[≠] x, f z = g z) : ∀ᶠ z in 𝓝 x, f z = g z := by
  have h0 : f x = g x :=
    tendsto_nhds_unique_of_eventuallyEq (hf.tendsto.mono_left nhdsWithin_le_nhds)
      (hg.tendsto.mono_left nhdsWithin_le_nhds) h
  filter_upwards [eventually_nhdsWithin_iff.mp h] with z hz
  by_cases hzx : z = x
  · subst hzx; exact h0
  · exact hz hzx

/-- `℘ z ≠ a` on a punctured neighbourhood of `0` (`℘` has a double pole at `0`). -/
theorem eventually_wp_ne (Λ : PeriodPair) (a : ℂ) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), Λ.weierstrassP z ≠ a := by
  obtain ⟨g, hg, hg1, hge⟩ := chartU_laurent_lattice Λ a (zero_mem Λ.lattice)
  have hgne : ∀ᶠ z in 𝓝 (0 : ℂ), g z ≠ 0 :=
    hg.continuousAt.eventually_ne (by rw [hg1]; exact one_ne_zero)
  filter_upwards [hgne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hz0
  have hz0' : z ≠ 0 := hz0
  intro hP
  have h1 : chartU Λ a z = 0 := by simp [chartU, hP]
  have h2 : (z - 0) ^ 2 * g z ≠ 0 := mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.2 hz0')) hz
  apply h2
  rw [← hge z hz0', h1]

/-! ### The functions `g̃`, the entries and the matrix `Ã` -/

section Defs

variable {Λ : PeriodPair} {Ω : ℝ} {Ω' : ℂ} {a : ℤ}

/-- `g̃_{D,k,b} = F₀^{D-k-2b} F₁^k F₂^b` (`ψ̃^D u^k t^b`). -/
def gTilde (M : Multiplier Λ Ω Ω' a) (D k b : ℕ) (z : ℂ) : ℂ :=
  M.F₀ z ^ (D - k - 2 * b) * M.F₁ z ^ k * M.F₂ z ^ b

/-- The entry `Ã_{(j,s,β),c} = [z^s] g̃_{D,k_c,b_c}(jΩ + z) · C(α_c,β) · ∏ᵢ (jΩ + z + δ_{ji})^{α_ci - βᵢ}`
with `r = (s, β)` (`r 0 = s`, `r i.succ = βᵢ`) and `δ_{ji} = c_{ji} - jΩ`, `c_{ji} = cen j i`. -/
def transportEntry {m K : ℕ} (M : Multiplier Λ Ω Ω' a) (D : ℕ) (cen : Fin K → Fin m → ℚ)
    (j : Fin K) (r : Fin (m + 1) → ℕ) (col : ColIdx m) : ℂ :=
  taylorCoeff (r 0) (fun z =>
    gTilde M D col.1 col.2.1.val (((j : ℕ) : ℂ) * (Ω : ℂ) + z) *
      (∏ i : Fin m, (((col.2.2 i).choose (r i.succ) : ℕ) : ℂ)) *
      ∏ i : Fin m, (((j : ℕ) : ℂ) * (Ω : ℂ) + z +
        (((cen j i : ℚ) : ℂ) - ((j : ℕ) : ℂ) * (Ω : ℂ))) ^ (col.2.2 i - r i.succ))

/-- The analytic matrix `Ã` of `lem:transport`: rows `(j, s, β)`, columns of `ℱ_H`. -/
def transportMatrix {m K : ℕ} (W : Weights m) (M : Multiplier Λ Ω Ω' a) (D : ℕ)
    (cen : Fin K → Fin m → ℚ) (H : ℝ) : Matrix (Row W K H) (Col W H) ℂ :=
  fun ρ col => transportEntry M D cen ρ.1 ρ.2.1 col.1

theorem F_add_nat {F : ℂ → ℂ} (hF : ∀ z, F (z + (Ω : ℂ)) = F z) (j : ℕ) (z : ℂ) :
    F ((j : ℂ) * (Ω : ℂ) + z) = F z := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : ((j + 1 : ℕ) : ℂ) * (Ω : ℂ) + z = ((j : ℂ) * (Ω : ℂ) + z) + (Ω : ℂ) := by
      push_cast; ring
    rw [e, hF, ih]

theorem gTilde_add_nat (M : Multiplier Λ Ω Ω' a) (D k b j : ℕ) (z : ℂ) :
    gTilde M D k b ((j : ℂ) * (Ω : ℂ) + z) = gTilde M D k b z := by
  unfold gTilde
  rw [F_add_nat M.per₀ j z, F_add_nat M.per₁ j z, F_add_nat M.per₂ j z]

/-- Near `0`: `g̃ = ψ^D u^k t^b` (`F₁ = ψ u`, `F₂ = ψ² t` off `Λ` and `℘ = a`). -/
theorem gTilde_germ (M : Multiplier Λ Ω Ω' a) (D k b : ℕ) (hkb : k + 2 * b ≤ D) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), gTilde M D k b z =
      M.F₀ z ^ D * (chartU Λ (a : ℂ) z ^ k * chartT Λ (a : ℂ) z ^ b) := by
  filter_upwards [eventually_not_mem_lattice Λ, eventually_wp_ne Λ (a : ℂ)] with z hz hP
  have h1 := M.eq_u z hz hP
  have h2 := M.eq_t z hz hP
  obtain ⟨e, rfl⟩ : ∃ e, D = e + k + 2 * b := ⟨D - k - 2 * b, by omega⟩
  have he : e + k + 2 * b - k - 2 * b = e := by omega
  unfold gTilde
  rw [h1, h2, he]
  simp only [chartT, chartU]
  ring

theorem differentiable_Gfun (M : Multiplier Λ Ω Ω' a) (D k b j : ℕ) {m : ℕ}
    (cj : Fin m → ℚ) (ex : Fin m → ℕ) (Cc : ℂ) :
    Differentiable ℂ (fun z => gTilde M D k b ((j : ℂ) * (Ω : ℂ) + z) * Cc *
      ∏ i : Fin m, ((j : ℂ) * (Ω : ℂ) + z + (((cj i : ℚ) : ℂ) - (j : ℂ) * (Ω : ℂ))) ^ ex i) := by
  have hs : ∀ F : ℂ → ℂ, Differentiable ℂ F →
      Differentiable ℂ (fun z => F ((j : ℂ) * (Ω : ℂ) + z)) := fun F hF =>
    hF.comp ((differentiable_const _).add differentiable_id)
  have h0 := hs _ M.diff₀
  have h1 := hs _ M.diff₁
  have h2 := hs _ M.diff₂
  unfold gTilde
  exact ((((h0.pow _).mul (h1.pow _)).mul (h2.pow _)).mul (differentiable_const _)).mul
    (Differentiable.fun_finsetProd fun i _ =>
      (((differentiable_const _).add differentiable_id).add (differentiable_const _)).pow _)


/-! ### The germ part: `g̃(jΩ + z) C ∏ (c_{ji} + z)^{·} = ψ(z)^D C Φ(τ(z))` -/

/-- Existence of the analytic germ `Φ(T) = fU(T)^k T^b ∏ (c_i + fL(T))^{e_i}` (whose Taylor series
is the packet series) with `tay (g̃(jΩ+·) C ∏ …) = tay ψ ^ D · (C · tay (Φ ∘ τ))`. -/
theorem exists_Phi (M : Multiplier Λ Ω Ω' a) {c : OriginChart} (ser : OriginSeries c)
    (hg₂ : Λ.g₂ = -4 * (c.A : ℂ)) (hg₃ : Λ.g₃ = -4 * (c.B : ℂ)) (hca : c.a = a)
    (D k b : ℕ) (hkb : k + 2 * b ≤ D) (j : ℕ) {m : ℕ} (cj : Fin m → ℚ) (ex : Fin m → ℕ)
    (Cc : ℂ) :
    ∃ Φ : ℂ → ℂ, AnalyticAt ℂ Φ 0 ∧
      tay Φ = PowerSeries.map (Rat.castHom ℂ)
        (ser.U ^ k * PowerSeries.X ^ b * ∏ i : Fin m, (PowerSeries.C (cj i) + ser.L) ^ ex i) ∧
      tay (fun z => gTilde M D k b ((j : ℂ) * (Ω : ℂ) + z) * Cc *
          ∏ i : Fin m, ((j : ℂ) * (Ω : ℂ) + z + (((cj i : ℚ) : ℂ) - (j : ℂ) * (Ω : ℂ))) ^ ex i) =
        tay M.F₀ ^ D * (PowerSeries.C Cc * tay (fun z => Φ (tGerm Λ (c.a : ℂ) z))) := by
  subst hca
  obtain ⟨hτ, hτd, fU, fL, hfU, hfL, hu, hL⟩ := Chart.germ Λ c hg₂ hg₃ ser
  have hfU' : AnalyticAt ℂ fU 0 := hfU.analyticAt
  have hfL' : AnalyticAt ℂ fL 0 := hfL.analyticAt
  have hτ0 : tGerm Λ (c.a : ℂ) 0 = 0 := tGerm_zero Λ _
  have hF₀ : AnalyticAt ℂ M.F₀ 0 := M.diff₀.analyticAt 0
  have hprod : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      AnalyticAt ℂ (fun T : ℂ => (((cj i : ℚ) : ℂ) + fL T) ^ ex i) 0 :=
    fun i _ => (analyticAt_const.add hfL').pow _
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℂ → ℂ, Φ = fun T : ℂ =>
      fU T ^ k * T ^ b * ∏ i : Fin m, (((cj i : ℚ) : ℂ) + fL T) ^ ex i := ⟨_, rfl⟩
  have hΦz : ∀ T, Φ T = fU T ^ k * T ^ b * ∏ i : Fin m, (((cj i : ℚ) : ℂ) + fL T) ^ ex i :=
    fun T => by rw [hΦ]
  have hΦan : AnalyticAt ℂ Φ 0 := by
    rw [hΦ]
    exact ((hfU'.pow k).mul (analyticAt_id.pow b)).mul (Finset.analyticAt_fun_prod _ hprod)
  refine ⟨Φ, hΦan, ?_, ?_⟩
  · have hU : tay fU = PowerSeries.map (Rat.castHom ℂ) ser.U := tay_eq_map hfU
    have hL' : tay fL = PowerSeries.map (Rat.castHom ℂ) ser.L := tay_eq_map hfL
    have h3 : ∀ i : Fin m, tay (fun T : ℂ => (((cj i : ℚ) : ℂ) + fL T) ^ ex i) =
        (PowerSeries.C ((cj i : ℚ) : ℂ) + tay fL) ^ ex i := fun i => by
      rw [tay_pow (f := fun T : ℂ => ((cj i : ℚ) : ℂ) + fL T) (analyticAt_const.add hfL'),
        tay_add analyticAt_const hfL', tay_const]
    rw [hΦ]
    rw [tay_mul (f := fun T : ℂ => fU T ^ k * T ^ b)
      (g := fun T : ℂ => ∏ i : Fin m, (((cj i : ℚ) : ℂ) + fL T) ^ ex i)
      ((hfU'.pow k).mul (analyticAt_id.pow b)) (Finset.analyticAt_fun_prod _ hprod),
      tay_mul (f := fun T : ℂ => fU T ^ k) (g := fun T : ℂ => T ^ b) (hfU'.pow k)
        (analyticAt_id.pow b),
      tay_pow hfU', tay_X_pow, tay_prod _ _ hprod]
    simp only [h3, hU, hL', map_mul, map_pow, map_prod, map_add, PowerSeries.map_C,
      PowerSeries.map_X, Rat.coe_castHom]
  · have hΦτ : AnalyticAt ℂ (fun z => Φ (tGerm Λ (c.a : ℂ) z)) 0 := hΦan.comp_of_eq hτ hτ0
    have hHan : AnalyticAt ℂ
        (fun z => M.F₀ z ^ D * (Cc * Φ (tGerm Λ (c.a : ℂ) z))) 0 :=
      (hF₀.pow D).mul (analyticAt_const.mul hΦτ)
    have hpunct : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
        gTilde M D k b ((j : ℂ) * (Ω : ℂ) + z) * Cc *
          ∏ i : Fin m, ((j : ℂ) * (Ω : ℂ) + z + (((cj i : ℚ) : ℂ) - (j : ℂ) * (Ω : ℂ))) ^ ex i =
        M.F₀ z ^ D * (Cc * Φ (tGerm Λ (c.a : ℂ) z)) := by
      filter_upwards [gTilde_germ M D k b hkb, hu.filter_mono nhdsWithin_le_nhds,
        hL.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hg h1 h2' hz0
      have hz0' : z ≠ 0 := hz0
      have e1 : chartU Λ (c.a : ℂ) z = fU (tGerm Λ (c.a : ℂ) z) := by
        rw [← uGerm_of_ne _ _ hz0']; exact h1
      have e2 : chartT Λ (c.a : ℂ) z = tGerm Λ (c.a : ℂ) z := (tGerm_of_ne _ _ hz0').symm
      have e3 : ∀ i : Fin m, (((cj i : ℚ) : ℂ) + fL (tGerm Λ (c.a : ℂ) z)) =
          ((cj i : ℚ) : ℂ) + z := fun i => by rw [h2']
      have e4 : ∀ i : Fin m, (j : ℂ) * (Ω : ℂ) + z + (((cj i : ℚ) : ℂ) - (j : ℂ) * (Ω : ℂ)) =
          ((cj i : ℚ) : ℂ) + z := fun i => by ring
      rw [gTilde_add_nat M D k b j z, hg, e1, e2, hΦz]
      simp only [e3, e4]
      ring
    have hev := eventuallyEq_nhds_of_punctured
      (differentiable_Gfun M D k b j cj ex Cc).continuous.continuousAt hHan.continuousAt hpunct
    rw [tay_congr hev,
      tay_mul (f := fun z => M.F₀ z ^ D)
        (g := fun z => Cc * Φ (tGerm Λ (c.a : ℂ) z)) (hF₀.pow D)
        (analyticAt_const.mul hΦτ), tay_pow hF₀,
      tay_mul (f := fun _ : ℂ => Cc) (g := fun z => Φ (tGerm Λ (c.a : ℂ) z))
        analyticAt_const hΦτ, tay_const]

/-- The packet entry (eq:entry) with the `T`-exponent replaced by `n`, as a cast of a coefficient
of the packet series. -/
theorem cast_packetEntry_update {m K : ℕ} {ch : OriginChart} (ser : OriginSeries ch)
    (cen : Fin K → Fin m → ℚ) (j : Fin K) (r : Fin (m + 1) → ℕ) (n : ℕ) (col : ColIdx m) :
    ((packetEntry ser cen j (Function.update r 0 n) col : ℚ) : ℂ) =
      (∏ i : Fin m, (((col.2.2 i).choose (r i.succ) : ℕ) : ℂ)) *
        PowerSeries.coeff n (PowerSeries.map (Rat.castHom ℂ)
          (ser.U ^ col.1 * PowerSeries.X ^ col.2.1.val *
            ∏ i : Fin m, (PowerSeries.C (cen j i) + ser.L) ^ (col.2.2 i - r i.succ))) := by
  have h : ∀ i : Fin m, Function.update r 0 n i.succ = r i.succ := fun i =>
    Function.update_of_ne (Fin.succ_ne_zero i) _ _
  simp only [packetEntry, h, Function.update_self, Rat.cast_mul, Rat.cast_prod,
    Rat.cast_natCast, PowerSeries.coeff_map, Rat.coe_castHom]

/-- One row of `Ã` as a combination of rows of the packet matrix `A`:
`Ã_{(j,s,β),c} = ∑_{s' ≤ s} [z^s](ψ^D τ^{s'}) · A_{(j,s',β),c}`. -/
theorem transportEntry_eq_sum (M : Multiplier Λ Ω Ω' a) {c : OriginChart} (ser : OriginSeries c)
    (hg₂ : Λ.g₂ = -4 * (c.A : ℂ)) (hg₃ : Λ.g₃ = -4 * (c.B : ℂ)) (hca : c.a = a) {m K : ℕ}
    (cen : Fin K → Fin m → ℚ) (D : ℕ) (j : Fin K) (r : Fin (m + 1) → ℕ) (col : ColIdx m)
    (hkb : col.1 + 2 * col.2.1.val ≤ D) :
    transportEntry M D cen j r col =
      ∑ n ∈ Finset.range (r 0 + 1),
        PowerSeries.coeff (r 0) (tay M.F₀ ^ D * tay (tGerm Λ (c.a : ℂ)) ^ n) *
          ((packetEntry ser cen j (Function.update r 0 n) col : ℚ) : ℂ) := by
  obtain ⟨Φ, hΦ, hΦt, hG⟩ := exists_Phi M ser hg₂ hg₃ hca D col.1 col.2.1.val hkb
    ((j : ℕ)) (cen j) (fun i => col.2.2 i - r i.succ)
    (∏ i : Fin m, (((col.2.2 i).choose (r i.succ) : ℕ) : ℂ))
  have hτ : AnalyticAt ℂ (tGerm Λ (c.a : ℂ)) 0 := (Chart.germ Λ c hg₂ hg₃ ser).1
  have hτ0 : tGerm Λ (c.a : ℂ) 0 = 0 := tGerm_zero Λ _
  have hdiff := differentiable_Gfun M D col.1 col.2.1.val ((j : ℕ)) (cen j)
    (fun i => col.2.2 i - r i.succ) (∏ i : Fin m, (((col.2.2 i).choose (r i.succ) : ℕ) : ℂ))
  have e : ∀ (A B : PowerSeries ℂ) (x : ℂ),
      A * (PowerSeries.C x * B) = PowerSeries.C x * (A * B) := fun A B x => by ring
  unfold transportEntry
  rw [taylorCoeff_eq_iteratedDeriv hdiff, ← coeff_tay, hG, e, PowerSeries.coeff_C_mul,
    coeff_mul_tay_comp hΦ hτ hτ0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [cast_packetEntry_update ser cen j r n col, hΦt]
  ring

/-! ### The row operation `R` and its determinant -/

theorem update_mem_rowSet {m : ℕ} (W : Weights m) {H : ℝ} {a : Fin (m + 1) → ℕ}
    (ha : a ∈ W.rowSet H) {n : ℕ} (hn : n ≤ a 0) : Function.update a 0 n ∈ W.rowSet H := by
  rw [W.mem_rowSet_iff] at ha ⊢
  refine lt_of_le_of_lt (Finset.sum_le_sum fun i _ => ?_) ha
  by_cases hi : i = 0
  · subst hi
    rw [Function.update_self]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hn) (W.rowWeights_pos 0).le
  · simp only [Function.update_of_ne hi, le_refl]

/-- The representative `(j, (0, β))` of the block of a row `(j, (s, β))`. -/
def repRow {m K : ℕ} {W : Weights m} {H : ℝ} (ρ : Row W K H) : Row W K H :=
  (ρ.1, ⟨Function.update ρ.2.1 0 0, update_mem_rowSet W ρ.2.2 (Nat.zero_le _)⟩)

/-- The row operation `R`: block diagonal over the pairs `(j, β)`, with entry
`Rs s s'` between the rows `(j, s, β)` and `(j, s', β)`. -/
def transportRowMatrix {m : ℕ} (W : Weights m) (K : ℕ) (H : ℝ) (Rs : ℕ → ℕ → ℂ) :
    Matrix (Row W K H) (Row W K H) ℂ :=
  fun ρ ρ' =>
    if ρ'.1 = ρ.1 ∧ (fun i : Fin m => ρ'.2.1 i.succ) = (fun i : Fin m => ρ.2.1 i.succ) then
      Rs (ρ.2.1 0) (ρ'.2.1 0) else 0

theorem det_of_key_triangular {ι κ : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder κ]
    (R : Matrix ι ι ℂ) (key : ι → κ) (hk : Function.Injective key)
    (h : ∀ i j, R i j ≠ 0 → ¬ key i < key j) : R.det = ∏ i, R i i := by
  letI : LinearOrder ι := LinearOrder.lift' key hk
  have hlow : R.IsLowerTriangular := by
    intro i j hij
    by_contra hne
    have hij' : i < j := hij
    exact h i j hne hij'
  convert Matrix.det_of_isLowerTriangular R hlow

theorem det_of_grp_triangular {ι : Type*} [Fintype ι] [DecidableEq ι] (R : Matrix ι ι ℂ)
    (grp : ι → ι) (s : ι → ℕ) (hinj : ∀ i i', grp i = grp i' → s i = s i' → i = i')
    (h : ∀ i i', R i i' ≠ 0 → grp i' = grp i ∧ s i' ≤ s i) : R.det = ∏ i, R i i := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine det_of_key_triangular R (fun i => toLex (e (grp i), s i)) ?_ ?_
  · intro i i' hii
    obtain ⟨h1, h2⟩ := Prod.mk.inj (toLex.injective hii)
    exact hinj i i' (e.injective h1) h2
  · intro i j hne hlt
    obtain ⟨h1, h2⟩ := h i j hne
    rcases Prod.Lex.toLex_lt_toLex.mp hlt with h3 | ⟨_, h4⟩
    · have h3' : e (grp i) < e (grp j) := h3
      rw [h1] at h3'
      exact lt_irrefl _ h3'
    · have h4' : s i < s j := h4
      exact absurd h4' (not_lt.mpr h2)

theorem det_transportRowMatrix {m : ℕ} (W : Weights m) (K : ℕ) (H : ℝ) (Rs : ℕ → ℕ → ℂ)
    (hRs : ∀ s s', s < s' → Rs s s' = 0) :
    (transportRowMatrix W K H Rs).det = ∏ ρ : Row W K H, Rs (ρ.2.1 0) (ρ.2.1 0) := by
  have hinj : ∀ ρ ρ' : Row W K H, repRow ρ = repRow ρ' → ρ.2.1 0 = ρ'.2.1 0 → ρ = ρ' := by
    rintro ⟨j, a, ha⟩ ⟨j', a', ha'⟩ hr hs
    have h1 : j = j' := congrArg Prod.fst hr
    have h2 : Function.update a 0 0 = Function.update a' 0 0 := congrArg (fun x => x.2.1) hr
    have h3 : a 0 = a' 0 := hs
    subst h1
    have h4 : a = a' := by
      funext i
      induction i using Fin.cases with
      | zero => exact h3
      | succ i =>
        have := congrFun h2 i.succ
        rwa [Function.update_of_ne (Fin.succ_ne_zero i),
          Function.update_of_ne (Fin.succ_ne_zero i)] at this
    subst h4
    rfl
  have htri : ∀ ρ ρ' : Row W K H, transportRowMatrix W K H Rs ρ ρ' ≠ 0 →
      repRow ρ' = repRow ρ ∧ ρ'.2.1 0 ≤ ρ.2.1 0 := by
    intro ρ ρ' hne
    by_cases hc : ρ'.1 = ρ.1 ∧
        (fun i : Fin m => ρ'.2.1 i.succ) = (fun i : Fin m => ρ.2.1 i.succ)
    · have hval : transportRowMatrix W K H Rs ρ ρ' = Rs (ρ.2.1 0) (ρ'.2.1 0) := by
        simp only [transportRowMatrix, if_pos hc]
      refine ⟨?_, ?_⟩
      · obtain ⟨hj, ht⟩ := hc
        unfold repRow
        refine Prod.ext hj (Subtype.ext ?_)
        show Function.update ρ'.2.1 0 0 = Function.update ρ.2.1 0 0
        funext i
        induction i using Fin.cases with
        | zero => simp
        | succ i =>
          rw [Function.update_of_ne (Fin.succ_ne_zero i),
            Function.update_of_ne (Fin.succ_ne_zero i)]
          exact congrFun ht i
      · by_contra hlt
        exact hne (by rw [hval]; exact hRs _ _ (not_le.mp hlt))
    · exfalso
      apply hne
      simp only [transportRowMatrix, if_neg hc]
  rw [det_of_grp_triangular (transportRowMatrix W K H Rs) repRow (fun ρ => ρ.2.1 0) hinj htri]
  refine Finset.prod_congr rfl fun ρ _ => ?_
  simp [transportRowMatrix]

/-! ### Reindexing the sum over rows -/

theorem sum_row_eq {m K : ℕ} (W : Weights m) (H : ℝ)
    (g : Fin K → (Fin (m + 1) → ℕ) → ℂ) :
    ∑ ρ : Row W K H, g ρ.1 ρ.2.1 = ∑ j : Fin K, ∑ x ∈ W.rowSet H, g j x := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Finset.sum_coe_sort (W.rowSet H) (g j)

theorem sum_reindex {m K : ℕ} (W : Weights m) (H : ℝ) (j : Fin K) (a : Fin (m + 1) → ℕ)
    (ha : a ∈ W.rowSet H) (Rs : ℕ → ℂ) (hRs : ∀ n, a 0 < n → Rs n = 0)
    (Y : Fin K → (Fin (m + 1) → ℕ) → ℂ) :
    ∑ ρ : Row W K H,
        (if ρ.1 = j ∧ (fun i : Fin m => ρ.2.1 i.succ) = (fun i : Fin m => a i.succ)
          then Rs (ρ.2.1 0) else 0) * Y ρ.1 ρ.2.1 =
      ∑ n ∈ Finset.range (a 0 + 1), Rs n * Y j (Function.update a 0 n) := by
  refine Eq.trans (sum_row_eq W H (fun j' r =>
    (if j' = j ∧ (fun i : Fin m => r i.succ) = (fun i : Fin m => a i.succ)
      then Rs (r 0) else 0) * Y j' r)) ?_
  refine Eq.trans (Finset.sum_eq_single j ?_ ?_) ?_
  · intro b _ hb
    refine Finset.sum_eq_zero fun x _ => ?_
    have hc : ¬ (b = j ∧ (fun i : Fin m => x i.succ) = (fun i : Fin m => a i.succ)) :=
      fun h => hb h.1
    rw [if_neg hc, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h
  · have hsub : (Finset.range (a 0 + 1)).image (fun n => Function.update a 0 n) ⊆
        W.rowSet H := by
      intro x hx
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
      exact update_mem_rowSet W ha (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
    have hinj : Set.InjOn (fun n => Function.update a 0 n) (↑(Finset.range (a 0 + 1))) := by
      intro n _ n' _ h
      have := congrFun h 0
      simpa using this
    refine Eq.trans (Finset.sum_subset hsub ?_).symm ?_
    · intro x hx hxn
      by_cases ht : (fun i : Fin m => x i.succ) = (fun i : Fin m => a i.succ)
      · have hx0 : a 0 < x 0 := by
          by_contra hle
          apply hxn
          refine Finset.mem_image.mpr ⟨x 0, Finset.mem_range.mpr (by omega), ?_⟩
          funext i
          induction i using Fin.cases with
          | zero => simp
          | succ i =>
            rw [Function.update_of_ne (Fin.succ_ne_zero i)]
            exact (congrFun ht i).symm
        rw [if_pos ⟨rfl, ht⟩, hRs _ hx0, zero_mul]
      · have hc : ¬ (j = j ∧ (fun i : Fin m => x i.succ) = (fun i : Fin m => a i.succ)) :=
          fun h => ht h.2
        rw [if_neg hc, zero_mul]
    · rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun n _ => ?_
      have h1 : (fun i : Fin m => Function.update a 0 n i.succ) = (fun i : Fin m => a i.succ) := by
        funext i
        exact Function.update_of_ne (Fin.succ_ne_zero i) _ _
      show (if j = j ∧ (fun i : Fin m => Function.update a 0 n i.succ) =
          (fun i : Fin m => a i.succ) then Rs (Function.update a 0 n 0) else 0) *
            Y j (Function.update a 0 n) = Rs n * Y j (Function.update a 0 n)
      rw [if_pos ⟨rfl, h1⟩, Function.update_self]

/-! ### `Ã = R · A` and the determinant -/

theorem transportMatrix_eq_mul (M : Multiplier Λ Ω Ω' a) {c : OriginChart}
    (ser : OriginSeries c) (hg₂ : Λ.g₂ = -4 * (c.A : ℂ)) (hg₃ : Λ.g₃ = -4 * (c.B : ℂ))
    (hca : c.a = a) {m K : ℕ} (W : Weights m) (cen : Fin K → Fin m → ℚ) (H : ℝ) (D : ℕ)
    (hD : ∀ col ∈ W.colSet H, col.1 + 2 * col.2.1.val ≤ D) :
    transportMatrix W M D cen H =
      transportRowMatrix W K H
          (fun s n => PowerSeries.coeff s (tay M.F₀ ^ D * tay (tGerm Λ (c.a : ℂ)) ^ n)) *
        (packetMatrix W ser cen H).map (Rat.castHom ℂ) := by
  have hτ0' : PowerSeries.constantCoeff (tay (tGerm Λ (c.a : ℂ))) = 0 := by
    rw [constantCoeff_tay]; exact tGerm_zero Λ _
  ext ρ col
  obtain ⟨j, a₀, ha⟩ := ρ
  have h1 := transportEntry_eq_sum M ser hg₂ hg₃ hca cen D j a₀ col.1 (hD col.1 col.2)
  have h2 := sum_reindex W H j a₀ ha
    (fun n => PowerSeries.coeff (a₀ 0) (tay M.F₀ ^ D * tay (tGerm Λ (c.a : ℂ)) ^ n))
    (fun n hn => coeff_mul_pow_zero _ _ hτ0' hn)
    (fun j' r => ((packetEntry ser cen j' r col.1 : ℚ) : ℂ))
  calc transportMatrix W M D cen H (j, ⟨a₀, ha⟩) col = transportEntry M D cen j a₀ col.1 := rfl
    _ = _ := h1
    _ = _ := h2.symm
    _ = _ := by rw [Matrix.mul_apply]; rfl

/-- **E12, `lem:transport` (with sign).** For every selection of columns, `det Ã_sel` is
`(∏_ρ (-1)^{s_ρ}) · ψ(0)^{D J_H K} · Δ`, where `Δ` is the packet minor. -/
theorem transport_det_eq (M : Multiplier Λ Ω Ω' a) {c : OriginChart} (ser : OriginSeries c)
    (hg₂ : Λ.g₂ = -4 * (c.A : ℂ)) (hg₃ : Λ.g₃ = -4 * (c.B : ℂ)) (hca : c.a = a) {m K : ℕ}
    (W : Weights m) (cen : Fin K → Fin m → ℚ) (H : ℝ) (D : ℕ)
    (hD : ∀ col ∈ W.colSet H, col.1 + 2 * col.2.1.val ≤ D) (sel : Row W K H → Col W H) :
    ((transportMatrix W M D cen H).submatrix id sel).det =
      (∏ ρ : Row W K H, (-1 : ℂ) ^ (ρ.2.1 0)) * M.F₀ 0 ^ (D * W.J H * K) *
        ((packetDelta W ser cen H sel : ℚ) : ℂ) := by
  have hmat := transportMatrix_eq_mul M ser hg₂ hg₃ hca W cen H D hD
  have hτ0' : PowerSeries.constantCoeff (tay (tGerm Λ (c.a : ℂ))) = 0 := by
    rw [constantCoeff_tay]; exact tGerm_zero Λ _
  have hτd : PowerSeries.coeff 1 (tay (tGerm Λ (c.a : ℂ))) = -1 :=
    coeff_one_tay (Chart.germ Λ c hg₂ hg₃ ser).2.1
  have hdetR : (transportRowMatrix W K H
      (fun s n => PowerSeries.coeff s (tay M.F₀ ^ D * tay (tGerm Λ (c.a : ℂ)) ^ n))).det =
        ∏ ρ : Row W K H, (M.F₀ 0 ^ D * (-1 : ℂ) ^ (ρ.2.1 0)) := by
    rw [det_transportRowMatrix W K H _ (fun s s' h => coeff_mul_pow_zero _ _ hτ0' h)]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    rw [coeff_mul_pow_diag _ _ hτ0', hτd, map_pow, constantCoeff_tay]
  have hsub : (transportMatrix W M D cen H).submatrix id sel =
      transportRowMatrix W K H
          (fun s n => PowerSeries.coeff s (tay M.F₀ ^ D * tay (tGerm Λ (c.a : ℂ)) ^ n)) *
        (((packetMatrix W ser cen H).map (Rat.castHom ℂ)).submatrix id sel) := by
    rw [hmat]
    ext ρ ρ'
    first
      | rfl
      | simp only [Matrix.submatrix_apply, Matrix.mul_apply, id_eq]
  have hΔ : ((packetDelta W ser cen H sel : ℚ) : ℂ) =
      (((packetMatrix W ser cen H).map (Rat.castHom ℂ)).submatrix id sel).det := by
    have h := RingHom.map_det (Rat.castHom ℂ) ((packetMatrix W ser cen H).submatrix id sel)
    rw [RingHom.mapMatrix_apply] at h
    exact h
  have hcard : Fintype.card (Row W K H) = K * W.J H := W.card_row K H
  rw [hsub, Matrix.det_mul, hdetR, ← hΔ, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, hcard]
  ring

/-- **E12, `lem:transport`.** `|det Ã| = |Δ| · |ψ(0)|^{D J_H K}`. -/
theorem transport_norm (M : Multiplier Λ Ω Ω' a) {c : OriginChart} (ser : OriginSeries c)
    (hg₂ : Λ.g₂ = -4 * (c.A : ℂ)) (hg₃ : Λ.g₃ = -4 * (c.B : ℂ)) (hca : c.a = a) {m K : ℕ}
    (W : Weights m) (cen : Fin K → Fin m → ℚ) (H : ℝ) (D : ℕ)
    (hD : ∀ col ∈ W.colSet H, col.1 + 2 * col.2.1.val ≤ D) (sel : Row W K H → Col W H) :
    ‖((transportMatrix W M D cen H).submatrix id sel).det‖ =
      ‖((packetDelta W ser cen H sel : ℚ) : ℂ)‖ * ‖M.F₀ 0‖ ^ (D * W.J H * K) := by
  have h1 : ‖∏ ρ : Row W K H, (-1 : ℂ) ^ (ρ.2.1 0)‖ = 1 := by
    rw [norm_prod]
    simp
  rw [transport_det_eq M ser hg₂ hg₃ hca W cen H D hD sel, norm_mul, norm_mul, h1, one_mul,
    norm_pow, mul_comm]

/-- Every column of `ℱ_H` has `k + 2b ≤ ⌈H/(2 w₀)⌉`. -/
theorem col_le_ceil {m : ℕ} (W : Weights m) {H : ℝ} {col : ColIdx m} (hc : col ∈ W.colSet H) :
    col.1 + 2 * col.2.1.val ≤ ⌈H / (2 * (W.w₀ : ℝ))⌉₊ := by
  have hS := (W.mem_colSet_iff H col).mp hc
  have hw0 : (0 : ℝ) < W.w₀ := by exact_mod_cast W.w₀_pos
  have hnn := W.wt_nonneg col.2.2
  have h1 : ((col.1 + 2 * col.2.1.val : ℕ) : ℝ) ≤ H / (2 * (W.w₀ : ℝ)) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * (W.w₀ : ℝ))]
    push_cast
    nlinarith [hS, hnn]
  exact Nat.cast_le.mp (h1.trans (Nat.le_ceil _))

end Defs

end

end CatalanCore.Elliptic.Analytic

namespace CatalanCore.Elliptic

open CatalanCore.Elliptic.Analytic

/-- **E12 for an integral model** (`lem:transport`): with the multiplier `ψ` of `IntegralModel.multiplier`
and `D = ⌈H/(2 w₀)⌉`, `|det Ã| = |Δ| |ψ(0)|^{D J_H K}`. -/
theorem IntegralModel.transport_norm (M : IntegralModel) (ser : OriginSeries M.chart) {m K : ℕ}
    (W : Weights m) (cen : Fin K → Fin m → ℚ) (H : ℝ) (sel : Row W K H → Col W H) :
    ‖((transportMatrix W M.multiplier (⌈H / (2 * (W.w₀ : ℝ))⌉₊) cen H).submatrix id sel).det‖ =
      ‖((packetDelta W ser cen H sel : ℚ) : ℂ)‖ *
        ‖M.multiplier.F₀ 0‖ ^ (⌈H / (2 * (W.w₀ : ℝ))⌉₊ * W.J H * K) :=
  Analytic.transport_norm M.multiplier ser M.g₂_eq M.g₃_eq rfl W cen H _
    (fun col hcol => Analytic.col_le_ceil W hcol) sel

end CatalanCore.Elliptic
