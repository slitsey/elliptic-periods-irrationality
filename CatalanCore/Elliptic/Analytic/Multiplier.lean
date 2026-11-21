module

public import CatalanCore.Elliptic.Lattice.Divisor

@[expose] public section

/-!
# The multiplier `ψ̂ = e^{-2π i z/Ω} Θ_Λ(z)² (℘(z) - a)` (row E07, `lem:mult` in theta form)

For `L : PeriodPair` with `0 < Im (ω₂/ω₁)` (so `Θ_Λ = thetaL L` is Tau Ceti's product theta in
lattice coordinates) and `a : ℂ` put, off `Λ`,

* `ψ̂   = psiHat0 L a z = e^{-2π i z/ω₁} Θ_Λ(z)² (℘(z) - a)`,
* `ψ̂ u = psiHat1 L z   = e^{-2π i z/ω₁} Θ_Λ(z)²`        (entire already),
* `ψ̂² t = psiHat2 L z  = (ψ̂ u)² ℘'(z)/2`, `t = (℘'/2) u²`, `u = (℘ - a)⁻¹`.

The factor `e^{-2π i z/ω₁}` (the theta-multiplier derivation, Remark 5.3) turns the transport factor
`n(n-1)` of `Θ_Λ²(℘ - a)` into the paper's `n²`.

* `exists_coreSpec`: entire extensions `F₀, F₂` of `ψ̂`, `ψ̂² t` (Liouville toolbox `L2′`) with
  exact `ω₁`-periodicity, the transport `F(z + n ω₂) = F(z) · exp(-(2π i/ω₁)(2 n z + n² ω₂))`
  (squared for `F₂`), `F₀ 0 = Θ_Λ'(0)² = -4π² P⁴/ω₁²`, `F₀ ≠ 0` on `Λ`.
* `multF₀_eq_zero_iff`: the zero set of `ψ̂` is `±z_Q + Λ`.
* `Multiplier.ofLattice`: the contract structure `Multiplier Λ Ω Ω' a` of
  `CatalanCore.Elliptic.Interfaces`; `IntegralModel.multiplier` for an integral model.
* `Multiplier.translate₀/₁/₂`: the translate formula for `λ = kΩ + nΩ'`.
-/

namespace CatalanCore.Elliptic.Analytic

open Complex Real Filter Topology Function Set
open CatalanCore.Elliptic.Theta CatalanCore.Elliptic.Lattice

noncomputable section

/-! ### Definitions -/

/-- `e^{-2π i z/ω₁}`. -/
def expo (L : PeriodPair) (z : ℂ) : ℂ := cexp (-(2 * π * I * (z / L.ω₁)))

/-- `ψ̂ u = e^{-2π i z/ω₁} Θ_Λ(z)²`. -/
def psiHat1 (L : PeriodPair) : ℂ → ℂ := fun z => expo L z * thetaL L z ^ 2

/-- `ψ̂ = e^{-2π i z/ω₁} Θ_Λ(z)² (℘(z) - a)` (junk value `0`-extension off the entire extension). -/
def psiHat0 (L : PeriodPair) (a : ℂ) : ℂ → ℂ := fun z => psiHat1 L z * (L.weierstrassP z - a)

/-- `ψ̂² t = (ψ̂ u)² ℘'/2`. -/
def psiHat2 (L : PeriodPair) : ℂ → ℂ := fun z => psiHat1 L z ^ 2 * (L.derivWeierstrassP z / 2)

/-- The transport factor `exp(-(2π i/ω₁)(2 n z + n² ω₂))`. -/
def Etr (L : PeriodPair) (n : ℤ) (z : ℂ) : ℂ :=
  cexp (-(2 * π * I / L.ω₁) * (2 * n * z + n ^ 2 * L.ω₂))

/-! ### Elementary facts -/

lemma expo_add (L : PeriodPair) (z y : ℂ) : expo L (z + y) = expo L z * expo L y := by
  unfold expo
  rw [← Complex.exp_add]
  congr 1
  ring

lemma expo_zero (L : PeriodPair) : expo L 0 = 1 := by simp [expo]

lemma expo_omega1 (L : PeriodPair) : expo L L.ω₁ = 1 := by
  have hω := ω₁_ne_zero L
  unfold expo
  rw [div_self hω, mul_one, Complex.exp_neg, Complex.exp_two_pi_mul_I]
  simp

lemma expo_ne_zero (L : PeriodPair) (z : ℂ) : expo L z ≠ 0 := Complex.exp_ne_zero _

lemma differentiable_expo (L : PeriodPair) : Differentiable ℂ (expo L) := by
  show Differentiable ℂ (fun z => cexp (-(2 * π * I * (z / L.ω₁))))
  fun_prop

lemma continuous_Etr (L : PeriodPair) (n : ℤ) : Continuous (Etr L n) := by
  show Continuous (fun z => cexp (-(2 * π * I / L.ω₁) * (2 * n * z + n ^ 2 * L.ω₂)))
  fun_prop

lemma natω₂_mem (L : PeriodPair) (n : ℤ) : (n : ℂ) * L.ω₂ ∈ L.lattice :=
  PeriodPair.mem_lattice.2 ⟨0, n, by simp⟩

lemma wp_add_lattice {L : PeriodPair} {l : ℂ} (hl : l ∈ L.lattice) (z : ℂ) :
    L.weierstrassP (z + l) = L.weierstrassP z := L.weierstrassP_add_coe z ⟨l, hl⟩

lemma dwp_add_lattice {L : PeriodPair} {l : ℂ} (hl : l ∈ L.lattice) (z : ℂ) :
    L.derivWeierstrassP (z + l) = L.derivWeierstrassP z := L.derivWeierstrassP_add_coe z ⟨l, hl⟩

lemma differentiable_psiHat1 {L : PeriodPair} (hτ : TauPos L) : Differentiable ℂ (psiHat1 L) := by
  have h1 := differentiable_expo L
  have h2 := differentiable_thetaL hτ
  show Differentiable ℂ (fun z => expo L z * thetaL L z ^ 2)
  fun_prop

/-! ### Lattice translates -/

open Classical in
/-- The integer `n` with `l = m ω₁ + n ω₂` (chosen). -/
def latN {L : PeriodPair} (hτ : TauPos L) (l : ℂ) : ℤ :=
  if hl : l ∈ L.lattice then Classical.choose (thetaL_add_lattice hτ hl) else 0

lemma thetaL_add_latN {L : PeriodPair} (hτ : TauPos L) {l : ℂ} (hl : l ∈ L.lattice) (z : ℂ) :
    thetaL L (z + l) = thetaMult (L.ω₂ / L.ω₁) (latN hτ l) (z / L.ω₁) * thetaL L z := by
  have h := Classical.choose_spec (thetaL_add_lattice hτ hl) z
  unfold latN
  rw [dif_pos hl]
  exact h

/-- The multiplier of `ψ̂ u` under `z ↦ z + l`. -/
def mulFn {L : PeriodPair} (hτ : TauPos L) (l z : ℂ) : ℂ :=
  expo L l * thetaMult (L.ω₂ / L.ω₁) (latN hτ l) (z / L.ω₁) ^ 2

lemma mulFn_ne_zero {L : PeriodPair} (hτ : TauPos L) (l z : ℂ) : mulFn hτ l z ≠ 0 :=
  mul_ne_zero (expo_ne_zero L l) (pow_ne_zero 2 (thetaMult_ne_zero _ _ _))

lemma differentiable_mulFn {L : PeriodPair} (hτ : TauPos L) (l : ℂ) :
    Differentiable ℂ (mulFn hτ l) := by
  have h := differentiable_thetaMult (L.ω₂ / L.ω₁) (latN hτ l)
  show Differentiable ℂ (fun z => expo L l * thetaMult (L.ω₂ / L.ω₁) (latN hτ l) (z / L.ω₁) ^ 2)
  fun_prop

lemma psiHat1_add_lattice {L : PeriodPair} (hτ : TauPos L) {l : ℂ} (hl : l ∈ L.lattice) (z : ℂ) :
    psiHat1 L (z + l) = mulFn hτ l z * psiHat1 L z := by
  simp only [psiHat1, mulFn]
  rw [expo_add, thetaL_add_latN hτ hl]
  ring

lemma psiHat0_add_lattice {L : PeriodPair} (hτ : TauPos L) (a : ℂ) {l : ℂ} (hl : l ∈ L.lattice)
    (z : ℂ) : psiHat0 L a (z + l) = mulFn hτ l z * psiHat0 L a z := by
  simp only [psiHat0]
  rw [psiHat1_add_lattice hτ hl, wp_add_lattice hl]
  ring

lemma psiHat2_add_lattice {L : PeriodPair} (hτ : TauPos L) {l : ℂ} (hl : l ∈ L.lattice) (z : ℂ) :
    psiHat2 L (z + l) = mulFn hτ l z ^ 2 * psiHat2 L z := by
  simp only [psiHat2]
  rw [psiHat1_add_lattice hτ hl, dwp_add_lattice hl]
  ring

/-! ### Exact `ω₁`-periodicity and `ω₂`-transport -/

lemma thetaL_add_ω₁ (L : PeriodPair) (z : ℂ) : thetaL L (z + L.ω₁) = thetaL L z := by
  have hω := ω₁_ne_zero L
  unfold thetaL
  rw [add_div, div_self hω]
  exact theta_add_one _ _

lemma psiHat1_add_ω₁ (L : PeriodPair) (z : ℂ) : psiHat1 L (z + L.ω₁) = psiHat1 L z := by
  simp only [psiHat1]
  rw [expo_add, expo_omega1, thetaL_add_ω₁]
  ring

lemma thetaL_sq_add_zsmul_ω₂ {L : PeriodPair} (hτ : TauPos L) (n : ℤ) (z : ℂ) :
    thetaL L (z + n * L.ω₂) ^ 2 =
      thetaMult2 (L.ω₂ / L.ω₁) n (z / L.ω₁) * thetaL L z ^ 2 := by
  have hω := ω₁_ne_zero L
  have h : (z + n * L.ω₂) / L.ω₁ = z / L.ω₁ + ((0 : ℤ) : ℂ) + n * (L.ω₂ / L.ω₁) := by
    push_cast
    ring
  unfold thetaL
  rw [h]
  exact theta_sq_add_int_add_zsmul_tau hτ 0 n _

lemma psiHat1_add_zsmul_ω₂ {L : PeriodPair} (hτ : TauPos L) (n : ℤ) (z : ℂ) :
    psiHat1 L (z + n * L.ω₂) = psiHat1 L z * Etr L n z := by
  have key : expo L (z + n * L.ω₂) * thetaMult2 (L.ω₂ / L.ω₁) n (z / L.ω₁) =
      expo L z * Etr L n z := by
    unfold expo thetaMult2 Etr
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  simp only [psiHat1]
  rw [thetaL_sq_add_zsmul_ω₂ hτ]
  linear_combination (thetaL L z ^ 2) * key

lemma psiHat0_add_ω₁ (L : PeriodPair) (a z : ℂ) : psiHat0 L a (z + L.ω₁) = psiHat0 L a z := by
  simp only [psiHat0]
  rw [psiHat1_add_ω₁, wp_add_lattice L.ω₁_mem_lattice]

lemma psiHat2_add_ω₁ (L : PeriodPair) (z : ℂ) : psiHat2 L (z + L.ω₁) = psiHat2 L z := by
  simp only [psiHat2]
  rw [psiHat1_add_ω₁, dwp_add_lattice L.ω₁_mem_lattice]

lemma psiHat0_add_zsmul_ω₂ {L : PeriodPair} (hτ : TauPos L) (a : ℂ) (n : ℤ) (z : ℂ) :
    psiHat0 L a (z + n * L.ω₂) = psiHat0 L a z * Etr L n z := by
  simp only [psiHat0]
  rw [psiHat1_add_zsmul_ω₂ hτ, wp_add_lattice (natω₂_mem L n)]
  ring

lemma psiHat2_add_zsmul_ω₂ {L : PeriodPair} (hτ : TauPos L) (n : ℤ) (z : ℂ) :
    psiHat2 L (z + n * L.ω₂) = psiHat2 L z * Etr L n z ^ 2 := by
  simp only [psiHat2]
  rw [psiHat1_add_zsmul_ω₂ hτ, dwp_add_lattice (natω₂_mem L n)]
  ring

/-! ### Extension by density -/

lemma eq_of_eq_off_lattice (L : PeriodPair) {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ z, z ∉ L.lattice → f z = g z) : f = g :=
  Continuous.ext_on (dense_compl_lattice L) hf hg (fun z hz => h z hz)

lemma ext_shift (L : PeriodPair) {F g c : ℂ → ℂ} {s : ℂ} (hs : s ∈ L.lattice)
    (hF : Continuous F) (hc : Continuous c) (hFg : ∀ z, z ∉ L.lattice → F z = g z)
    (hg : ∀ z, g (z + s) = g z * c z) (z : ℂ) : F (z + s) = F z * c z := by
  have h := eq_of_eq_off_lattice L (f := fun z => F (z + s)) (g := fun z => F z * c z)
    (hF.comp (continuous_id.add continuous_const)) (hF.mul hc) (fun z hz => by
      show F (z + s) = F z * c z
      rw [hFg (z + s) (fun h => hz ((add_mem_lattice_iff L hs).1 h)), hFg z hz]
      exact hg z)
  exact congrFun h z

lemma ext_period (L : PeriodPair) {F g : ℂ → ℂ} {s : ℂ} (hs : s ∈ L.lattice)
    (hF : Continuous F) (hFg : ∀ z, z ∉ L.lattice → F z = g z)
    (hg : ∀ z, g (z + s) = g z) (z : ℂ) : F (z + s) = F z := by
  have h := eq_of_eq_off_lattice L (f := fun z => F (z + s)) (g := F)
    (hF.comp (continuous_id.add continuous_const)) hF (fun z hz => by
      show F (z + s) = F z
      rw [hFg (z + s) (fun h => hz ((add_mem_lattice_iff L hs).1 h)), hFg z hz]
      exact hg z)
  exact congrFun h z

lemma ext_value_at_zero (L : PeriodPair) {g k F : ℂ → ℂ} (hF : Continuous F)
    (hk : ContinuousAt k 0) (hFg : ∀ z, z ∉ L.lattice → F z = g z)
    (hgk : g =ᶠ[𝓝[≠] (0 : ℂ)] k) : F 0 = k 0 := by
  have h1 : Tendsto F (𝓝[≠] (0 : ℂ)) (𝓝 (F 0)) :=
    hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto k (𝓝[≠] (0 : ℂ)) (𝓝 (k 0)) := hk.tendsto.mono_left nhdsWithin_le_nhds
  have h3 : F =ᶠ[𝓝[≠] (0 : ℂ)] k := by
    filter_upwards [hgk, eventually_not_mem_lattice L] with z hz1 hz2
    rw [hFg z hz2, hz1]
  exact tendsto_nhds_unique (h1.congr' h3) h2

/-! ### Germs at `0` -/

lemma psiHat0_germ {L : PeriodPair} (hτ : TauPos L) (a : ℂ) :
    ∃ k : ℂ → ℂ, ContinuousAt k 0 ∧ k 0 = deriv (thetaL L) 0 ^ 2 ∧
      psiHat0 L a =ᶠ[𝓝[≠] (0 : ℂ)] k := by
  have h1 : Continuous (expo L) := (differentiable_expo L).continuous
  have h2 : Continuous (thetaD L) := (differentiable_thetaD hτ).continuous
  have h3 : ContinuousAt (L.weierstrassPExcept 0) 0 :=
    (L.analyticAt_weierstrassPExcept 0).continuousAt
  refine ⟨fun z => expo L z * thetaD L z ^ 2 * (1 + z ^ 2 * (L.weierstrassPExcept 0 z - a)),
    ?_, ?_, ?_⟩
  · fun_prop
  · show expo L 0 * thetaD L 0 ^ 2 * (1 + (0 : ℂ) ^ 2 * (L.weierstrassPExcept 0 0 - a)) = _
    rw [expo_zero, thetaD_zero (L := L)]
    simp
  · filter_upwards [eventually_not_mem_lattice L, self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    simp only [psiHat0, psiHat1]
    rw [weierstrassP_eq_inv_sq_add L z, thetaL_eq_mul_thetaD (L := L) z]
    have hi : z ^ 2 * (z ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 hz0')
    linear_combination (expo L z * thetaD L z ^ 2) * hi

lemma psiHat2_germ {L : PeriodPair} (hτ : TauPos L) :
    ∃ k : ℂ → ℂ, ContinuousAt k 0 ∧ k 0 = 0 ∧ psiHat2 L =ᶠ[𝓝[≠] (0 : ℂ)] k := by
  have h1 : Continuous (expo L) := (differentiable_expo L).continuous
  have h2 : Continuous (thetaD L) := (differentiable_thetaD hτ).continuous
  have h3 : ContinuousAt (L.derivWeierstrassPExcept 0) 0 :=
    (L.analyticAt_derivWeierstrassPExcept 0).continuousAt
  refine ⟨fun z => expo L z ^ 2 *
      (thetaD L z ^ 4 * ((z ^ 4 * L.derivWeierstrassPExcept 0 z - 2 * z) / 2)), ?_, ?_, ?_⟩
  · fun_prop
  · simp
  · filter_upwards [eventually_not_mem_lattice L, self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    simp only [psiHat2, psiHat1]
    rw [derivWeierstrassP_eq_sub L z, thetaL_eq_mul_thetaD (L := L) z]
    have hi : z ^ 3 * (z ^ 3)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 3 hz0')
    linear_combination (-(expo L z ^ 2 * thetaD L z ^ 4 * z)) * hi

/-! ### The core specification -/

/-- Everything the structure `Multiplier` needs, for a lattice with `0 < Im (ω₂/ω₁)`. -/
structure CoreSpec (L : PeriodPair) (a : ℂ) (F₀ F₁ F₂ : ℂ → ℂ) : Prop where
  diff₀ : Differentiable ℂ F₀
  diff₁ : Differentiable ℂ F₁
  diff₂ : Differentiable ℂ F₂
  per₀ : ∀ z, F₀ (z + L.ω₁) = F₀ z
  per₁ : ∀ z, F₁ (z + L.ω₁) = F₁ z
  per₂ : ∀ z, F₂ (z + L.ω₁) = F₂ z
  tr₀ : ∀ (n : ℤ) (z : ℂ), F₀ (z + n * L.ω₂) = F₀ z * Etr L n z
  tr₁ : ∀ (n : ℤ) (z : ℂ), F₁ (z + n * L.ω₂) = F₁ z * Etr L n z
  tr₂ : ∀ (n : ℤ) (z : ℂ), F₂ (z + n * L.ω₂) = F₂ z * Etr L n z ^ 2
  off₀ : ∀ z, z ∉ L.lattice → F₀ z = psiHat0 L a z
  off₁ : ∀ z, F₁ z = psiHat1 L z
  off₂ : ∀ z, z ∉ L.lattice → F₂ z = psiHat2 L z
  val₀ : F₀ 0 = deriv (thetaL L) 0 ^ 2
  ne_lat : ∀ l ∈ L.lattice, F₀ l ≠ 0

theorem exists_coreSpec {L : PeriodPair} (hτ : TauPos L) (a : ℂ) :
    ∃ F₀ F₂ : ℂ → ℂ, CoreSpec L a F₀ (psiHat1 L) F₂ := by
  obtain ⟨k₀, hk₀c, hk₀v, hk₀g⟩ := psiHat0_germ hτ a
  obtain ⟨k₂, hk₂c, hk₂v, hk₂g⟩ := psiHat2_germ hτ
  have hd0 : DifferentiableOn ℂ (psiHat0 L a) ((L.lattice : Set ℂ)ᶜ) :=
    (differentiable_psiHat1 hτ).differentiableOn.mul
      (L.differentiableOn_weierstrassP.sub_const a)
  have hdd : DifferentiableOn ℂ L.derivWeierstrassP ((L.lattice : Set ℂ)ᶜ) := fun z hz =>
    (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.differentiableWithinAt
  have hd2 : DifferentiableOn ℂ (psiHat2 L) ((L.lattice : Set ℂ)ᶜ) :=
    ((differentiable_psiHat1 hτ).pow 2).differentiableOn.mul (hdd.div_const 2)
  obtain ⟨F₀, hF₀d, hF₀e, hF₀t⟩ := exists_entire_extension_multiplier L (psiHat0 L a)
    (mulFn hτ) hd0 (fun l _ => differentiable_mulFn hτ l)
    (fun l hl z _ => psiHat0_add_lattice hτ a hl z) (bounded_near_zero_of_germ hk₀c hk₀g)
  obtain ⟨F₂, hF₂d, hF₂e, hF₂t⟩ := exists_entire_extension_multiplier L (psiHat2 L)
    (fun l z => mulFn hτ l z ^ 2) hd2 (fun l _ => (differentiable_mulFn hτ l).pow 2)
    (fun l hl z _ => psiHat2_add_lattice hτ hl z) (bounded_near_zero_of_germ hk₂c hk₂g)
  have hv₀ : F₀ 0 = deriv (thetaL L) 0 ^ 2 := by
    rw [ext_value_at_zero L hF₀d.continuous hk₀c hF₀e hk₀g, hk₀v]
  refine ⟨F₀, F₂, ?_⟩
  exact
    { diff₀ := hF₀d
      diff₁ := differentiable_psiHat1 hτ
      diff₂ := hF₂d
      per₀ := fun z => ext_period L L.ω₁_mem_lattice hF₀d.continuous hF₀e
        (fun z => psiHat0_add_ω₁ L a z) z
      per₁ := fun z => psiHat1_add_ω₁ L z
      per₂ := fun z => ext_period L L.ω₁_mem_lattice hF₂d.continuous hF₂e
        (fun z => psiHat2_add_ω₁ L z) z
      tr₀ := fun n z => ext_shift L (natω₂_mem L n) hF₀d.continuous (continuous_Etr L n) hF₀e
        (fun z => psiHat0_add_zsmul_ω₂ hτ a n z) z
      tr₁ := fun n z => psiHat1_add_zsmul_ω₂ hτ n z
      tr₂ := fun n z => ext_shift L (natω₂_mem L n) hF₂d.continuous
        ((continuous_Etr L n).pow 2) hF₂e (fun z => psiHat2_add_zsmul_ω₂ hτ n z) z
      off₀ := hF₀e
      off₁ := fun z => rfl
      off₂ := hF₂e
      val₀ := hv₀
      ne_lat := fun l hl => by
        have h := hF₀t l hl 0
        rw [zero_add] at h
        rw [h, hv₀]
        exact mul_ne_zero (mulFn_ne_zero hτ l 0)
          (pow_ne_zero 2 (deriv_thetaL_zero_ne_zero hτ)) }

/-- The entire function `ψ̂`. -/
def multF₀ {L : PeriodPair} (hτ : TauPos L) (a : ℂ) : ℂ → ℂ := (exists_coreSpec hτ a).choose

/-- The entire function `ψ̂² t`. -/
def multF₂ {L : PeriodPair} (hτ : TauPos L) (a : ℂ) : ℂ → ℂ :=
  (exists_coreSpec hτ a).choose_spec.choose

theorem multSpec {L : PeriodPair} (hτ : TauPos L) (a : ℂ) :
    CoreSpec L a (multF₀ hτ a) (psiHat1 L) (multF₂ hτ a) :=
  (exists_coreSpec hτ a).choose_spec.choose_spec

theorem CoreSpec.eq_u {L : PeriodPair} {a : ℂ} {F₀ F₁ F₂ : ℂ → ℂ} (h : CoreSpec L a F₀ F₁ F₂)
    {z : ℂ} (hz : z ∉ L.lattice) (hne : L.weierstrassP z ≠ a) :
    F₁ z = F₀ z * (L.weierstrassP z - a)⁻¹ := by
  have hw : L.weierstrassP z - a ≠ 0 := sub_ne_zero.2 hne
  rw [h.off₁, h.off₀ z hz]
  simp only [psiHat0]
  rw [mul_assoc, mul_inv_cancel₀ hw, mul_one]

theorem CoreSpec.eq_t {L : PeriodPair} {a : ℂ} {F₀ F₁ F₂ : ℂ → ℂ} (h : CoreSpec L a F₀ F₁ F₂)
    {z : ℂ} (hz : z ∉ L.lattice) (hne : L.weierstrassP z ≠ a) :
    F₂ z = F₀ z ^ 2 * (L.derivWeierstrassP z / 2 * ((L.weierstrassP z - a)⁻¹) ^ 2) := by
  have hw : L.weierstrassP z - a ≠ 0 := sub_ne_zero.2 hne
  have hi : (L.weierstrassP z - a) * (L.weierstrassP z - a)⁻¹ = 1 := mul_inv_cancel₀ hw
  rw [h.off₂ z hz, h.off₀ z hz]
  simp only [psiHat0, psiHat2]
  linear_combination (-(psiHat1 L z ^ 2 * (L.derivWeierstrassP z / 2)) *
    ((L.weierstrassP z - a) * (L.weierstrassP z - a)⁻¹ + 1)) * hi

/-- `ψ̂(0) = Θ_Λ'(0)² = -4π² P⁴ / ω₁²`, `P = ∏ (1 - q^(n+1))`. -/
theorem multF₀_zero {L : PeriodPair} (hτ : TauPos L) (a : ℂ) :
    multF₀ hτ a 0 = -(4 * (π : ℂ) ^ 2) * eulerP (L.ω₂ / L.ω₁) ^ 4 / L.ω₁ ^ 2 := by
  rw [(multSpec hτ a).val₀, (hasDerivAt_thetaL_zero hτ).deriv]
  linear_combination (4 * (π : ℂ) ^ 2 * eulerP (L.ω₂ / L.ω₁) ^ 4 / L.ω₁ ^ 2) * Complex.I_sq

theorem multF₀_zero_ne_zero {L : PeriodPair} (hτ : TauPos L) (a : ℂ) : multF₀ hτ a 0 ≠ 0 := by
  rw [(multSpec hτ a).val₀]
  exact pow_ne_zero 2 (deriv_thetaL_zero_ne_zero hτ)

/-- **Zero set of `ψ̂`.** If `z_Q ∉ Λ` and `℘(z_Q) = a`, then `ψ̂(z) = 0` iff
`z ∈ (z_Q + Λ) ∪ (-z_Q + Λ)` (no zeros on `Λ`). -/
theorem multF₀_eq_zero_iff {L : PeriodPair} (hτ : TauPos L) {a zQ : ℂ} (hzQ : zQ ∉ L.lattice)
    (hP : L.weierstrassP zQ = a) (z : ℂ) :
    multF₀ hτ a z = 0 ↔ z - zQ ∈ L.lattice ∨ z + zQ ∈ L.lattice := by
  have hS := multSpec hτ a
  by_cases hz : z ∈ L.lattice
  · have h1 : multF₀ hτ a z ≠ 0 := hS.ne_lat z hz
    have h2 : ¬ (z - zQ ∈ L.lattice ∨ z + zQ ∈ L.lattice) := by
      rintro (h | h)
      · apply hzQ
        simpa using L.lattice.sub_mem hz h
      · apply hzQ
        simpa using L.lattice.sub_mem h hz
    exact iff_of_false h1 h2
  · rw [hS.off₀ z hz]
    simp only [psiHat0, psiHat1]
    have hθ := thetaL_ne_zero hτ hz
    have he := expo_ne_zero L z
    rw [← weierstrassP_eq_iff_general L hzQ hz, hP]
    constructor
    · intro h
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h (mul_ne_zero he (pow_ne_zero 2 hθ))
      · exact sub_eq_zero.1 h
    · intro h
      rw [h, sub_self, mul_zero]

end

end CatalanCore.Elliptic.Analytic

/-! ### The contract structure -/

namespace CatalanCore.Elliptic

open Complex Real CatalanCore.Elliptic.Analytic CatalanCore.Elliptic.Theta
  CatalanCore.Elliptic.Lattice

noncomputable section

/-- The period pair `⟨Ω, Ω'⟩` with `Ω > 0` real and `Im Ω' > 0`. -/
def lat (Ω : ℝ) (Ω' : ℂ) (hΩ : 0 < Ω) (hY : 0 < Ω'.im) : PeriodPair where
  ω₁ := (Ω : ℂ)
  ω₂ := Ω'
  indep := by
    refine LinearIndependent.pair_iff.2 fun s t h => ?_
    have h1 : t * Ω'.im = 0 := by simpa using congrArg Complex.im h
    have ht : t = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h hY.ne'
    subst ht
    have h2 : s * Ω = 0 := by simpa using congrArg Complex.re h
    refine ⟨?_, rfl⟩
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd h hΩ.ne'

lemma lat_lattice (Ω : ℝ) (Ω' : ℂ) (hΩ : 0 < Ω) (hY : 0 < Ω'.im) :
    (lat Ω Ω' hΩ hY).lattice = Submodule.span ℤ {(Ω : ℂ), Ω'} := rfl

lemma lat_tauPos (Ω : ℝ) (Ω' : ℂ) (hΩ : 0 < Ω) (hY : 0 < Ω'.im) : TauPos (lat Ω Ω' hΩ hY) := by
  show 0 < (Ω' / (Ω : ℂ)).im
  rw [Complex.div_ofReal_im]
  exact div_pos hY hΩ

/-- **E07.** The multiplier package `F₀ = ψ̂`, `F₁ = ψ̂ u`, `F₂ = ψ̂² t` of the contract type
`Multiplier`, for a lattice `Λ = ℤΩ + ℤΩ'` with `Ω > 0` and `Im Ω' > 0`. -/
def Multiplier.ofLattice (Λ : PeriodPair) (Ω : ℝ) (Ω' : ℂ) (a : ℤ) (hΩ : 0 < Ω)
    (hY : 0 < Ω'.im) (hΛ : Λ.lattice = Submodule.span ℤ {(Ω : ℂ), Ω'}) :
    Multiplier Λ Ω Ω' a where
  F₀ := multF₀ (lat_tauPos Ω Ω' hΩ hY) (a : ℂ)
  F₁ := psiHat1 (lat Ω Ω' hΩ hY)
  F₂ := multF₂ (lat_tauPos Ω Ω' hΩ hY) (a : ℂ)
  diff₀ := (multSpec (lat_tauPos Ω Ω' hΩ hY) (a : ℂ)).diff₀
  diff₁ := (multSpec (lat_tauPos Ω Ω' hΩ hY) (a : ℂ)).diff₁
  diff₂ := (multSpec (lat_tauPos Ω Ω' hΩ hY) (a : ℂ)).diff₂
  per₀ := (multSpec (lat_tauPos Ω Ω' hΩ hY) (a : ℂ)).per₀
  per₁ := (multSpec (lat_tauPos Ω Ω' hΩ hY) (a : ℂ)).per₁
  per₂ := (multSpec (lat_tauPos Ω Ω' hΩ hY) (a : ℂ)).per₂
  transport₀ := (multSpec (lat_tauPos Ω Ω' hΩ hY) (a : ℂ)).tr₀
  transport₁ := (multSpec (lat_tauPos Ω Ω' hΩ hY) (a : ℂ)).tr₁
  transport₂ := (multSpec (lat_tauPos Ω Ω' hΩ hY) (a : ℂ)).tr₂
  eq_u := fun z hz hne => by
    have hLam : Λ.lattice = (lat Ω Ω' hΩ hY).lattice := hΛ
    have hP : Λ.weierstrassP = (lat Ω Ω' hΩ hY).weierstrassP := weierstrassP_congr_lattice hLam
    rw [hLam] at hz
    rw [hP] at hne ⊢
    exact (multSpec (lat_tauPos Ω Ω' hΩ hY) (a : ℂ)).eq_u hz hne
  eq_t := fun z hz hne => by
    have hLam : Λ.lattice = (lat Ω Ω' hΩ hY).lattice := hΛ
    have hP : Λ.weierstrassP = (lat Ω Ω' hΩ hY).weierstrassP := weierstrassP_congr_lattice hLam
    have hD : Λ.derivWeierstrassP = (lat Ω Ω' hΩ hY).derivWeierstrassP :=
      derivWeierstrassP_congr_lattice hLam
    rw [hLam] at hz
    rw [hP] at hne ⊢
    rw [hD]
    exact (multSpec (lat_tauPos Ω Ω' hΩ hY) (a : ℂ)).eq_t hz hne
  ne_zero := multF₀_zero_ne_zero (lat_tauPos Ω Ω' hΩ hY) (a : ℂ)

/-- `ψ̂(0) = -4π² P⁴/Ω²`, with `P = ∏' n, (1 - q^(n+1))`, `q = e^{2π i Ω'/Ω}`. -/
theorem Multiplier.ofLattice_F₀_zero (Λ : PeriodPair) (Ω : ℝ) (Ω' : ℂ) (a : ℤ) (hΩ : 0 < Ω)
    (hY : 0 < Ω'.im) (hΛ : Λ.lattice = Submodule.span ℤ {(Ω : ℂ), Ω'}) :
    (Multiplier.ofLattice Λ Ω Ω' a hΩ hY hΛ).F₀ 0 =
      -(4 * (π : ℂ) ^ 2) * (∏' n : ℕ, (1 - cexp (2 * π * I * (Ω' / Ω)) ^ (n + 1))) ^ 4 /
        (Ω : ℂ) ^ 2 :=
  multF₀_zero (lat_tauPos Ω Ω' hΩ hY) (a : ℂ)

/-- `ψ̂ ≠ 0` on the lattice. -/
theorem Multiplier.ofLattice_F₀_ne_zero_of_mem (Λ : PeriodPair) (Ω : ℝ) (Ω' : ℂ) (a : ℤ)
    (hΩ : 0 < Ω) (hY : 0 < Ω'.im) (hΛ : Λ.lattice = Submodule.span ℤ {(Ω : ℂ), Ω'}) {l : ℂ}
    (hl : l ∈ Λ.lattice) : (Multiplier.ofLattice Λ Ω Ω' a hΩ hY hΛ).F₀ l ≠ 0 :=
  (multSpec (lat_tauPos Ω Ω' hΩ hY) (a : ℂ)).ne_lat l (by rwa [hΛ] at hl)

/-- **Zero set of `ψ̂`** (E07): for `z_Q ∉ Λ` with `℘_Λ(z_Q) = a`, `ψ̂(z) = 0` iff
`z ∈ (z_Q + Λ) ∪ (-z_Q + Λ)`. -/
theorem Multiplier.ofLattice_F₀_eq_zero_iff (Λ : PeriodPair) (Ω : ℝ) (Ω' : ℂ) (a : ℤ)
    (hΩ : 0 < Ω) (hY : 0 < Ω'.im) (hΛ : Λ.lattice = Submodule.span ℤ {(Ω : ℂ), Ω'}) {zQ : ℂ}
    (hzQ : zQ ∉ Λ.lattice) (hP : Λ.weierstrassP zQ = (a : ℂ)) (z : ℂ) :
    (Multiplier.ofLattice Λ Ω Ω' a hΩ hY hΛ).F₀ z = 0 ↔
      z - zQ ∈ Λ.lattice ∨ z + zQ ∈ Λ.lattice := by
  have hLam : Λ.lattice = (lat Ω Ω' hΩ hY).lattice := hΛ
  have hP' : Λ.weierstrassP = (lat Ω Ω' hΩ hY).weierstrassP := weierstrassP_congr_lattice hLam
  rw [hLam]
  rw [hLam] at hzQ
  rw [hP'] at hP
  exact multF₀_eq_zero_iff (lat_tauPos Ω Ω' hΩ hY) hzQ hP z

/-- The multiplier package of an integral model. -/
def IntegralModel.multiplier (M : IntegralModel) : M.Mult :=
  Multiplier.ofLattice M.Λ M.Ω M.Ω' M.a M.Ω_pos M.Y_pos M.lattice_basis

/-- Zero set of `ψ̂` for an integral model: `±z_Q + Λ`. -/
theorem IntegralModel.multiplier_F₀_eq_zero_iff (M : IntegralModel) (z : ℂ) :
    M.multiplier.F₀ z = 0 ↔ z - M.zQ ∈ M.Λ.lattice ∨ z + M.zQ ∈ M.Λ.lattice :=
  Multiplier.ofLattice_F₀_eq_zero_iff M.Λ M.Ω M.Ω' M.a M.Ω_pos M.Y_pos M.lattice_basis
    M.zQ_not_mem M.wp_zQ z

theorem IntegralModel.multiplier_F₀_ne_zero_of_mem (M : IntegralModel) {l : ℂ}
    (hl : l ∈ M.Λ.lattice) : M.multiplier.F₀ l ≠ 0 :=
  Multiplier.ofLattice_F₀_ne_zero_of_mem M.Λ M.Ω M.Ω' M.a M.Ω_pos M.Y_pos M.lattice_basis hl

/-! ### The translate formula `λ = kΩ + nΩ'` -/

namespace Multiplier

variable {Λ : PeriodPair} {Ω : ℝ} {Ω' : ℂ} {a : ℤ}

lemma translate_aux (hΩ : (Ω : ℂ) ≠ 0) {f : ℂ → ℂ} (j : ℕ) (per : ∀ z, f (z + Ω) = f z)
    (tr : ∀ (n : ℤ) (z : ℂ), f (z + n * Ω') =
      f z * Complex.exp (-(2 * Real.pi * Complex.I / Ω) * (2 * n * z + n ^ 2 * Ω')) ^ j)
    (k n : ℤ) (z : ℂ) :
    f (z + k * Ω + n * Ω') =
      f z * Complex.exp (-(2 * Real.pi * Complex.I / Ω) * (2 * n * z + n ^ 2 * Ω')) ^ j := by
  have hper : Function.Periodic f (Ω : ℂ) := per
  rw [tr n (z + k * Ω), (hper.int_mul k) z]
  have hA : (2 * Real.pi * Complex.I / Ω) * Ω = 2 * Real.pi * Complex.I := div_mul_cancel₀ _ hΩ
  have e : Complex.exp (-(2 * Real.pi * Complex.I / Ω) * (2 * n * (z + k * Ω) + n ^ 2 * Ω')) =
      Complex.exp (-(2 * Real.pi * Complex.I / Ω) * (2 * n * z + n ^ 2 * Ω')) := by
    have h : -(2 * Real.pi * Complex.I / Ω) * (2 * n * (z + k * Ω) + n ^ 2 * Ω') =
        -(2 * Real.pi * Complex.I / Ω) * (2 * n * z + n ^ 2 * Ω') +
          ((-2 * n * k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      linear_combination (-(2 * (n : ℂ) * k)) * hA
    rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [e]

/-- Translate formula for `F₀`: `F₀(z + kΩ + nΩ') = F₀(z) · exp(-(2π i/Ω)(2 n z + n² Ω'))`. -/
theorem translate₀ (M : Multiplier Λ Ω Ω' a) (hΩ : (Ω : ℂ) ≠ 0) (k n : ℤ) (z : ℂ) :
    M.F₀ (z + k * Ω + n * Ω') =
      M.F₀ z * Complex.exp (-(2 * Real.pi * Complex.I / Ω) * (2 * n * z + n ^ 2 * Ω')) := by
  have h := translate_aux hΩ (f := M.F₀) 1 M.per₀
    (fun n z => by rw [pow_one]; exact M.transport₀ n z) k n z
  rwa [pow_one] at h

theorem translate₁ (M : Multiplier Λ Ω Ω' a) (hΩ : (Ω : ℂ) ≠ 0) (k n : ℤ) (z : ℂ) :
    M.F₁ (z + k * Ω + n * Ω') =
      M.F₁ z * Complex.exp (-(2 * Real.pi * Complex.I / Ω) * (2 * n * z + n ^ 2 * Ω')) := by
  have h := translate_aux hΩ (f := M.F₁) 1 M.per₁
    (fun n z => by rw [pow_one]; exact M.transport₁ n z) k n z
  rwa [pow_one] at h

theorem translate₂ (M : Multiplier Λ Ω Ω' a) (hΩ : (Ω : ℂ) ≠ 0) (k n : ℤ) (z : ℂ) :
    M.F₂ (z + k * Ω + n * Ω') =
      M.F₂ z * Complex.exp (-(2 * Real.pi * Complex.I / Ω) * (2 * n * z + n ^ 2 * Ω')) ^ 2 :=
  translate_aux hΩ (f := M.F₂) 2 M.per₂ M.transport₂ k n z

end Multiplier

end

end CatalanCore.Elliptic
