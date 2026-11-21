module

public import CatalanCore.Elliptic.Interfaces
public import CatalanCore.Elliptic.Theta.Addition

@[expose] public section

/-!
# The polar point and the divisor of `℘ - a` (rows E20, E22)

For `L : PeriodPair`, `Λ = L.lattice`, `a : ℂ`, put
`u = chartU L a = (℘ - a)⁻¹` and `t = chartT L a = (℘'/2) u²` (total functions; junk values on `Λ`).

* **E20 (D4)** `exists_polar_point`: there is `z_Q ∉ Λ` with `℘(z_Q) = a`.
  (Liouville: `h = (℘ - a)⁻¹` would be entire, `Λ`-periodic, hence constant `0`.)
* **Corollary 4.2** for every `L` (not only `Im(ω₂/ω₁) > 0`, `exists_tauPos_lattice`):
  `weierstrassP_eq_iff_general` (`℘ z = ℘ c ↔ z - c ∈ Λ ∨ z + c ∈ Λ`) and
  `derivWeierstrassP_eq_zero_iff` (`℘'(c) = 0 ↔ 2c ∈ Λ`, for `c ∉ Λ`).
* **E22 (i)-(iv)** (`derivWeierstrassP_ne_zero_of_wp_eq`, `two_mul_not_mem_of_wp_eq`,
  `wp_eq_iff_cosets`, `cosets_disjoint`): if `℘(z_Q) = a`, `z_Q ∉ Λ` and `4a³ - g₂ a - g₃ ≠ 0`
  then `℘'(z_Q) ≠ 0`, `2 z_Q ∉ Λ`, `{℘ = a} = (z_Q + Λ) ∪ (-z_Q + Λ)` off `Λ`, and the two
  cosets are disjoint.
* **E22 (v)** pole and zero structure of `u`, `t`: `chartU_laurent_lattice`,
  `chartT_laurent_lattice` (order `2`, `1` at lattice points), `chartU_laurent_polar`,
  `chartT_laurent_polar` (simple pole with residue `1/℘'(z₀)`, double pole with leading
  coefficient `1/(2℘'(z₀))` at `℘(z₀) = a`), the `meromorphicOrderAt_*` forms, and
  `meromorphicOrderAt_chartU_neg_iff`, `meromorphicOrderAt_chartT_neg_iff` (poles exactly at
  `±z_Q + Λ`); `chartU_analyticAt`, `chartT_analyticAt` elsewhere.
* **E22 (vi)** Laurent expansions at `0` (`g₂ = -4A`, `g₃ = -4B` gives `g₂/20 = -A/5`,
  `g₃/28 = -B/7`): `weierstrassP_laurent_zero`, `derivWeierstrassP_laurent_zero`,
  `chartU_expansion` (`u = z² + a z⁴ + (a² - g₂/20) z⁶ + z⁸ ρ`),
  `chartT_expansion` (`t = -z - 2a z³ + z⁵ τ`), with `ρ, τ` analytic at `0`.
* Consequences for `IntegralModel` (`IntegralModel.deriv_zQ_ne_zero`, `two_zQ_not_mem`,
  `wp_eq_a_iff`).
-/

namespace CatalanCore.Elliptic.Lattice

open Filter Topology CatalanCore.Elliptic.Theta

noncomputable section

/-- `u = (℘ - a)⁻¹`. -/
def chartU (L : PeriodPair) (a z : ℂ) : ℂ := (L.weierstrassP z - a)⁻¹

/-- `t = (℘'/2) u²`. -/
def chartT (L : PeriodPair) (a z : ℂ) : ℂ := L.derivWeierstrassP z / 2 * chartU L a z ^ 2

/-! ### Preliminaries -/

section Prelim

variable (L : PeriodPair)

theorem eventually_not_mem_lattice : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice := by
  have hs := nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ))
    (L.compl_lattice_sdiff_singleton_mem_nhds (0 : ℂ))
  filter_upwards [hs, self_mem_nhdsWithin] with z hz hz0
  have hz0' : z ≠ 0 := hz0
  exact fun h => hz ⟨h, hz0'⟩

theorem weierstrassP_eq_inv_sq_add (z : ℂ) :
    L.weierstrassP z = (z ^ 2)⁻¹ + L.weierstrassPExcept 0 z := by
  have hP := L.weierstrassPExcept_add 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero, one_div, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, inv_zero] at hP
  rw [← hP]
  ring

theorem derivWeierstrassP_eq_sub (z : ℂ) :
    L.derivWeierstrassP z = L.derivWeierstrassPExcept 0 z - 2 * (z ^ 3)⁻¹ := by
  have h := L.derivWeierstrassPExcept_sub 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero] at h
  rw [← h]
  ring

theorem hasDerivAt_weierstrassP_of_not_mem {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
  have hd : DifferentiableAt ℂ L.weierstrassP z :=
    L.differentiableOn_weierstrassP.differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hz)
  have h := hd.hasDerivAt
  rwa [show deriv L.weierstrassP z = L.derivWeierstrassP z from
    congrFun L.deriv_weierstrassP z] at h

theorem chartU_add_lattice {l : ℂ} (hl : l ∈ L.lattice) (a z : ℂ) :
    chartU L a (z + l) = chartU L a z := by
  have h : L.weierstrassP (z + l) = L.weierstrassP z := L.weierstrassP_add_coe z ⟨l, hl⟩
  simp only [chartU, h]

theorem chartT_add_lattice {l : ℂ} (hl : l ∈ L.lattice) (a z : ℂ) :
    chartT L a (z + l) = chartT L a z := by
  have h : L.derivWeierstrassP (z + l) = L.derivWeierstrassP z :=
    L.derivWeierstrassP_add_coe z ⟨l, hl⟩
  simp only [chartT, chartU_add_lattice L hl a z, h]

theorem chartU_neg (a z : ℂ) : chartU L a (-z) = chartU L a z := by
  simp only [chartU, L.weierstrassP_neg]

theorem chartT_neg (a z : ℂ) : chartT L a (-z) = -chartT L a z := by
  simp only [chartT, chartU_neg L, L.derivWeierstrassP_neg]
  ring

theorem chartU_analyticAt (a : ℂ) {z : ℂ} (hz : z ∉ L.lattice) (h : L.weierstrassP z ≠ a) :
    AnalyticAt ℂ (chartU L a) z :=
  ((L.analyticOnNhd_weierstrassP z hz).sub analyticAt_const).inv (sub_ne_zero.2 h)

theorem chartT_analyticAt (a : ℂ) {z : ℂ} (hz : z ∉ L.lattice) (h : L.weierstrassP z ≠ a) :
    AnalyticAt ℂ (chartT L a) z := by
  have hu := chartU_analyticAt L a hz h
  have hd : AnalyticAt ℂ L.derivWeierstrassP z := L.analyticOnNhd_derivWeierstrassP z hz
  exact (hd.div analyticAt_const two_ne_zero).mul (hu.pow 2)

end Prelim

/-! ### Taylor remainders at `0` -/

/-- A function with a power series at `0` is its Taylor polynomial plus `z ^ n * r z`,
`r` analytic at `0`. -/
theorem exists_taylor_remainder_zero {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (h : HasFPowerSeriesAt f p 0) (n : ℕ) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r 0 ∧
      ∀ z, f z = (∑ k ∈ Finset.range n, p.coeff k * z ^ k) + z ^ n * r z := by
  induction n generalizing f p with
  | zero => exact ⟨f, h.analyticAt, fun z => by simp⟩
  | succ n ih =>
    obtain ⟨r, hr, hz⟩ := ih h.has_fpower_series_dslope_fslope
    refine ⟨r, hr, fun z => ?_⟩
    have h1 := sub_smul_dslope f 0 z
    rw [smul_eq_mul, sub_zero] at h1
    have hp0 : p.coeff 0 = f 0 := h.coeff_zero 1
    have e1 : f z = f 0 + z * dslope f 0 z := by linear_combination -h1
    have hz' := hz z
    simp only [FormalMultilinearSeries.coeff_fslope] at hz'
    have S : z * (∑ k ∈ Finset.range n, p.coeff (k + 1) * z ^ k) =
        ∑ k ∈ Finset.range n, p.coeff (k + 1) * z ^ (k + 1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [Finset.sum_range_succ', e1, hz']
    linear_combination S - hp0

section Expansion

variable (L : PeriodPair)

theorem sumInvPow_zero_apply (r : ℕ) : L.sumInvPow 0 r = L.G r := by
  rw [L.sumInvPow_zero]

/-- `℘[L - 0](z) = (g₂/20) z² + (g₃/28) z⁴ + z⁶ r(z)` with `r` analytic at `0`. -/
theorem weierstrassPExcept_zero_expansion :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r 0 ∧ ∀ z, L.weierstrassPExcept 0 z =
      L.g₂ / 20 * z ^ 2 + L.g₃ / 28 * z ^ 4 + z ^ 6 * r z := by
  obtain ⟨p, hp, hpc⟩ : ∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (L.weierstrassPExcept 0) p 0 ∧
      ∀ k : ℕ, p.coeff k = if k = 0 then L.weierstrassPExcept 0 0
        else ((k : ℂ) + 1) * L.sumInvPow 0 (k + 2) :=
    ⟨_, L.hasFPowerSeriesAt_weierstrassPExcept 0, fun k => FormalMultilinearSeries.coeff_ofScalars⟩
  have hG3 : L.G 3 = 0 := L.G_eq_zero_of_odd 3 ⟨1, by norm_num⟩
  have hG5 : L.G 5 = 0 := L.G_eq_zero_of_odd 5 ⟨2, by norm_num⟩
  have hG7 : L.G 7 = 0 := L.G_eq_zero_of_odd 7 ⟨3, by norm_num⟩
  have c0 : p.coeff 0 = 0 := by rw [hpc 0]; simp
  have c1 : p.coeff 1 = 0 := by
    rw [hpc 1, if_neg (by norm_num : (1 : ℕ) ≠ 0), sumInvPow_zero_apply]
    show _ * L.G 3 = 0
    rw [hG3, mul_zero]
  have c2 : p.coeff 2 = L.g₂ / 20 := by
    rw [hpc 2, if_neg (by norm_num : (2 : ℕ) ≠ 0), sumInvPow_zero_apply]
    have e : L.G (2 + 2) = L.G 4 := rfl
    rw [e, PeriodPair.g₂]
    push_cast
    ring
  have c3 : p.coeff 3 = 0 := by
    rw [hpc 3, if_neg (by norm_num : (3 : ℕ) ≠ 0), sumInvPow_zero_apply]
    show _ * L.G 5 = 0
    rw [hG5, mul_zero]
  have c4 : p.coeff 4 = L.g₃ / 28 := by
    rw [hpc 4, if_neg (by norm_num : (4 : ℕ) ≠ 0), sumInvPow_zero_apply]
    have e : L.G (4 + 2) = L.G 6 := rfl
    rw [e, PeriodPair.g₃]
    push_cast
    ring
  have c5 : p.coeff 5 = 0 := by
    rw [hpc 5, if_neg (by norm_num : (5 : ℕ) ≠ 0), sumInvPow_zero_apply]
    show _ * L.G 7 = 0
    rw [hG7, mul_zero]
  obtain ⟨r, hr, h⟩ := exists_taylor_remainder_zero hp 6
  refine ⟨r, hr, fun z => ?_⟩
  rw [h z]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0, c1, c2, c3, c4, c5]
  ring

/-- `℘'[L - 0](z) = (g₂/10) z + (g₃/7) z³ + z⁵ s(z)` with `s` analytic at `0`. -/
theorem derivWeierstrassPExcept_zero_expansion :
    ∃ s : ℂ → ℂ, AnalyticAt ℂ s 0 ∧ ∀ z, L.derivWeierstrassPExcept 0 z =
      L.g₂ / 10 * z + L.g₃ / 7 * z ^ 3 + z ^ 5 * s z := by
  obtain ⟨p, hp, hpc⟩ : ∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (L.derivWeierstrassPExcept 0) p 0 ∧
      ∀ k : ℕ, p.coeff k = ((k : ℂ) + 1) * ((k : ℂ) + 2) * L.sumInvPow 0 (k + 3) :=
    ⟨_, L.hasFPowerSeriesAt_derivWeierstrassPExcept 0, fun k => FormalMultilinearSeries.coeff_ofScalars⟩
  have hG3 : L.G 3 = 0 := L.G_eq_zero_of_odd 3 ⟨1, by norm_num⟩
  have hG5 : L.G 5 = 0 := L.G_eq_zero_of_odd 5 ⟨2, by norm_num⟩
  have hG7 : L.G 7 = 0 := L.G_eq_zero_of_odd 7 ⟨3, by norm_num⟩
  have c0 : p.coeff 0 = 0 := by
    rw [hpc 0, sumInvPow_zero_apply]
    show _ * L.G 3 = 0
    rw [hG3, mul_zero]
  have c1 : p.coeff 1 = L.g₂ / 10 := by
    rw [hpc 1, sumInvPow_zero_apply]
    have e : L.G (1 + 3) = L.G 4 := rfl
    rw [e, PeriodPair.g₂]
    push_cast
    ring
  have c2 : p.coeff 2 = 0 := by
    rw [hpc 2, sumInvPow_zero_apply]
    show _ * L.G 5 = 0
    rw [hG5, mul_zero]
  have c3 : p.coeff 3 = L.g₃ / 7 := by
    rw [hpc 3, sumInvPow_zero_apply]
    have e : L.G (3 + 3) = L.G 6 := rfl
    rw [e, PeriodPair.g₃]
    push_cast
    ring
  have c4 : p.coeff 4 = 0 := by
    rw [hpc 4, sumInvPow_zero_apply]
    show _ * L.G 7 = 0
    rw [hG7, mul_zero]
  obtain ⟨s, hs, h⟩ := exists_taylor_remainder_zero hp 5
  refine ⟨s, hs, fun z => ?_⟩
  rw [h z]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0, c1, c2, c3, c4]
  ring

/-- Laurent expansion of `℘` at `0` (E22 (vi)): `℘ = z⁻² + (g₂/20) z² + (g₃/28) z⁴ + z⁶ r`. -/
theorem weierstrassP_laurent_zero :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r 0 ∧ ∀ z, L.weierstrassP z =
      (z ^ 2)⁻¹ + L.g₂ / 20 * z ^ 2 + L.g₃ / 28 * z ^ 4 + z ^ 6 * r z := by
  obtain ⟨r, hr, h⟩ := weierstrassPExcept_zero_expansion L
  refine ⟨r, hr, fun z => ?_⟩
  rw [weierstrassP_eq_inv_sq_add L z, h z]
  ring

/-- Laurent expansion of `℘'/2` at `0` (E22 (vi)):
`℘'/2 = -z⁻³ + (g₂/20) z + (g₃/14) z³ + z⁵ s`. -/
theorem derivWeierstrassP_laurent_zero :
    ∃ s : ℂ → ℂ, AnalyticAt ℂ s 0 ∧ ∀ z, L.derivWeierstrassP z / 2 =
      -(z ^ 3)⁻¹ + L.g₂ / 20 * z + L.g₃ / 14 * z ^ 3 + z ^ 5 * s z := by
  obtain ⟨s', hs', h⟩ := derivWeierstrassPExcept_zero_expansion L
  refine ⟨fun z => s' z * (1 / 2), hs'.mul analyticAt_const, fun z => ?_⟩
  show L.derivWeierstrassP z / 2 =
    -(z ^ 3)⁻¹ + L.g₂ / 20 * z + L.g₃ / 14 * z ^ 3 + z ^ 5 * (s' z * (1 / 2))
  rw [derivWeierstrassP_eq_sub L z, h z]
  ring

end Expansion

/-! ### Laurent expansions of `u` and `t` at lattice points and at points with `℘ = a` -/

section Laurent

variable (L : PeriodPair)

/-- At `l ∈ Λ`: `u = (z - l)² g` with `g` analytic, `g l = 1`. -/
theorem chartU_laurent_lattice (a : ℂ) {l : ℂ} (hl : l ∈ L.lattice) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g l ∧ g l = 1 ∧
      ∀ z, z ≠ l → chartU L a z = (z - l) ^ 2 * g z := by
  have hEan : AnalyticAt ℂ (L.weierstrassPExcept l) l := L.analyticAt_weierstrassPExcept l
  obtain ⟨w, hw⟩ : ∃ w : ℂ → ℂ, ∀ z, w z =
      1 + (z - l) ^ 2 * (L.weierstrassPExcept l z - (l ^ 2)⁻¹ - a) := ⟨_, fun _ => rfl⟩
  have hwan : AnalyticAt ℂ w l := by
    have : w = fun z => 1 + (z - l) ^ 2 * (L.weierstrassPExcept l z - (l ^ 2)⁻¹ - a) := funext hw
    rw [this]
    fun_prop
  have hwl : w l = 1 := by rw [hw]; simp
  have hw0 : w l ≠ 0 := by rw [hwl]; exact one_ne_zero
  refine ⟨fun z => (w z)⁻¹, hwan.inv hw0, ?_, fun z hz => ?_⟩
  · show (w l)⁻¹ = 1
    rw [hwl, inv_one]
  · have hX : (z - l) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 hz)
    have hP : L.weierstrassPExcept l z + (1 / (z - l) ^ 2 - 1 / l ^ 2) = L.weierstrassP z :=
      L.weierstrassPExcept_add ⟨l, hl⟩ z
    have hinv : ((z - l) ^ 2)⁻¹ * (z - l) ^ 2 = 1 := inv_mul_cancel₀ hX
    have h1 : L.weierstrassP z - a = ((z - l) ^ 2)⁻¹ * w z := by
      rw [hw z]
      linear_combination (-1 : ℂ) * hP - (L.weierstrassPExcept l z - (l ^ 2)⁻¹ - a) * hinv
    show (L.weierstrassP z - a)⁻¹ = (z - l) ^ 2 * (w z)⁻¹
    rw [h1, mul_inv, inv_inv]

/-- At `l ∈ Λ`: `t = (z - l) s` with `s` analytic, `s l = -1`. -/
theorem chartT_laurent_lattice (a : ℂ) {l : ℂ} (hl : l ∈ L.lattice) :
    ∃ s : ℂ → ℂ, AnalyticAt ℂ s l ∧ s l = -1 ∧
      ∀ z, z ≠ l → chartT L a z = (z - l) * s z := by
  obtain ⟨g, hg, hg1, hge⟩ := chartU_laurent_lattice L a hl
  have hE' : AnalyticAt ℂ (L.derivWeierstrassPExcept l) l := L.analyticAt_derivWeierstrassPExcept l
  refine ⟨fun z => ((z - l) ^ 3 * L.derivWeierstrassPExcept l z * (1 / 2) - 1) * g z ^ 2,
    ?_, ?_, fun z hz => ?_⟩
  · have h3 : AnalyticAt ℂ (fun z : ℂ => (z - l) ^ 3 * L.derivWeierstrassPExcept l z * (1 / 2) - 1)
        l := by fun_prop
    exact h3.mul (hg.pow 2)
  · show (((l - l) ^ 3 * L.derivWeierstrassPExcept l l * (1 / 2) - 1) * g l ^ 2) = -1
    rw [hg1]
    simp
  · have hX : z - l ≠ 0 := sub_ne_zero.2 hz
    have hP' : L.derivWeierstrassPExcept l z - 2 / (z - l) ^ 3 = L.derivWeierstrassP z :=
      L.derivWeierstrassPExcept_sub ⟨l, hl⟩ z
    have hu := hge z hz
    show L.derivWeierstrassP z / 2 * chartU L a z ^ 2 =
      (z - l) * (((z - l) ^ 3 * L.derivWeierstrassPExcept l z * (1 / 2) - 1) * g z ^ 2)
    rw [hu, ← hP']
    generalize z - l = X at hX ⊢
    have hi : X⁻¹ * X = 1 := inv_mul_cancel₀ hX
    linear_combination (-(g z) ^ 2 * X * (1 + X⁻¹ * X + (X⁻¹) ^ 2 * X ^ 2)) * hi

/-- At `z₀ ∉ Λ` with `℘ z₀ = a`, `℘' z₀ ≠ 0`: `u = (z - z₀)⁻¹ g`, `g z₀ = 1/℘'(z₀)`. -/
theorem chartU_laurent_polar (a : ℂ) {z₀ : ℂ} (hz₀ : z₀ ∉ L.lattice)
    (ha : L.weierstrassP z₀ = a) (hd : L.derivWeierstrassP z₀ ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ = (L.derivWeierstrassP z₀)⁻¹ ∧
      ∀ z, chartU L a z = (z - z₀)⁻¹ * g z := by
  have hs : ((L.lattice : Set ℂ)ᶜ) ∈ 𝓝 z₀ := L.isClosed_lattice.isOpen_compl.mem_nhds hz₀
  have hDan : AnalyticAt ℂ (dslope L.weierstrassP z₀) z₀ :=
    ((Complex.differentiableOn_dslope hs).2 L.differentiableOn_weierstrassP).analyticAt hs
  have hD0 : dslope L.weierstrassP z₀ z₀ = L.derivWeierstrassP z₀ := by
    rw [dslope_same]
    exact congrFun L.deriv_weierstrassP z₀
  have hD0' : dslope L.weierstrassP z₀ z₀ ≠ 0 := by rw [hD0]; exact hd
  have key : ∀ z, L.weierstrassP z - a = (z - z₀) * dslope L.weierstrassP z₀ z := by
    intro z
    have h := sub_smul_dslope L.weierstrassP z₀ z
    rw [smul_eq_mul] at h
    rw [← ha]
    exact h.symm
  refine ⟨fun z => (dslope L.weierstrassP z₀ z)⁻¹, hDan.inv hD0', ?_, fun z => ?_⟩
  · show (dslope L.weierstrassP z₀ z₀)⁻¹ = (L.derivWeierstrassP z₀)⁻¹
    rw [hD0]
  · show (L.weierstrassP z - a)⁻¹ = (z - z₀)⁻¹ * (dslope L.weierstrassP z₀ z)⁻¹
    rw [key z, mul_inv]

/-- At `z₀ ∉ Λ` with `℘ z₀ = a`, `℘' z₀ ≠ 0`: `t = ((z - z₀)²)⁻¹ g`, `g z₀ = 1/(2℘'(z₀))`. -/
theorem chartT_laurent_polar (a : ℂ) {z₀ : ℂ} (hz₀ : z₀ ∉ L.lattice)
    (ha : L.weierstrassP z₀ = a) (hd : L.derivWeierstrassP z₀ ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ = (2 * L.derivWeierstrassP z₀)⁻¹ ∧
      ∀ z, chartT L a z = ((z - z₀) ^ 2)⁻¹ * g z := by
  obtain ⟨g₁, hg₁, hg₁0, hg₁e⟩ := chartU_laurent_polar L a hz₀ ha hd
  have hdan : AnalyticAt ℂ L.derivWeierstrassP z₀ := L.analyticOnNhd_derivWeierstrassP z₀ hz₀
  refine ⟨fun z => L.derivWeierstrassP z / 2 * g₁ z ^ 2, ?_, ?_, fun z => ?_⟩
  · exact (hdan.div analyticAt_const two_ne_zero).mul (hg₁.pow 2)
  · show L.derivWeierstrassP z₀ / 2 * g₁ z₀ ^ 2 = (2 * L.derivWeierstrassP z₀)⁻¹
    rw [hg₁0]
    linear_combination (1 / 2 * (L.derivWeierstrassP z₀)⁻¹) * inv_mul_cancel₀ hd
  · show L.derivWeierstrassP z / 2 * chartU L a z ^ 2 =
      ((z - z₀) ^ 2)⁻¹ * (L.derivWeierstrassP z / 2 * g₁ z ^ 2)
    rw [hg₁e z]
    generalize z - z₀ = X
    ring

end Laurent

/-! ### Orders -/

theorem zpow_neg_two_eq (x : ℂ) : x ^ (-2 : ℤ) = (x ^ 2)⁻¹ := by
  rw [zpow_neg, zpow_two, sq]

theorem zpow_two_eq (x : ℂ) : x ^ (2 : ℤ) = x ^ 2 := by
  rw [zpow_two, sq]

/-- A function equal to `(z - x)ⁿ g` off `x`, with `g` analytic and nonzero at `x`, has
meromorphic order `n`. -/
theorem meromorphicOrderAt_eq_of_laurent {f g : ℂ → ℂ} {x : ℂ} {n : ℤ} (hg : AnalyticAt ℂ g x)
    (hg0 : g x ≠ 0) (hf : ∀ z, z ≠ x → f z = (z - x) ^ n * g z) :
    meromorphicOrderAt f x = n := by
  have hev : f =ᶠ[𝓝[≠] x] fun z => (z - x) ^ n * g z := by
    filter_upwards [self_mem_nhdsWithin] with z hz using hf z hz
  have hm : MeromorphicAt (fun z => (z - x) ^ n * g z) x := by fun_prop
  have hm' : MeromorphicAt f x := hm.congr hev.symm
  rw [meromorphicOrderAt_eq_int_iff hm']
  refine ⟨g, hg, hg0, ?_⟩
  filter_upwards [hev] with z hz
  exact hz.trans (smul_eq_mul _ _).symm

section Orders

variable (L : PeriodPair)

/-- `u` has a double zero at each lattice point. -/
theorem meromorphicOrderAt_chartU_lattice (a : ℂ) {l : ℂ} (hl : l ∈ L.lattice) :
    meromorphicOrderAt (chartU L a) l = ((2 : ℤ) : WithTop ℤ) := by
  obtain ⟨g, hg, hg1, hge⟩ := chartU_laurent_lattice L a hl
  exact meromorphicOrderAt_eq_of_laurent hg (by rw [hg1]; exact one_ne_zero)
    (fun z hz => by rw [hge z hz, zpow_two_eq])

/-- `t` has a simple zero at each lattice point. -/
theorem meromorphicOrderAt_chartT_lattice (a : ℂ) {l : ℂ} (hl : l ∈ L.lattice) :
    meromorphicOrderAt (chartT L a) l = ((1 : ℤ) : WithTop ℤ) := by
  obtain ⟨s, hs, hs1, hse⟩ := chartT_laurent_lattice L a hl
  exact meromorphicOrderAt_eq_of_laurent hs (by rw [hs1]; exact neg_ne_zero.2 one_ne_zero)
    (fun z hz => by rw [hse z hz, zpow_one])

/-- `u` has a simple pole at each `z₀ ∉ Λ` with `℘ z₀ = a` and `℘' z₀ ≠ 0`. -/
theorem meromorphicOrderAt_chartU_polar (a : ℂ) {z₀ : ℂ} (hz₀ : z₀ ∉ L.lattice)
    (ha : L.weierstrassP z₀ = a) (hd : L.derivWeierstrassP z₀ ≠ 0) :
    meromorphicOrderAt (chartU L a) z₀ = ((-1 : ℤ) : WithTop ℤ) := by
  obtain ⟨g, hg, hg0, hge⟩ := chartU_laurent_polar L a hz₀ ha hd
  exact meromorphicOrderAt_eq_of_laurent hg (by rw [hg0]; exact inv_ne_zero hd)
    (fun z _ => by rw [hge z, zpow_neg_one])

/-- `t` has a double pole at each `z₀ ∉ Λ` with `℘ z₀ = a` and `℘' z₀ ≠ 0`. -/
theorem meromorphicOrderAt_chartT_polar (a : ℂ) {z₀ : ℂ} (hz₀ : z₀ ∉ L.lattice)
    (ha : L.weierstrassP z₀ = a) (hd : L.derivWeierstrassP z₀ ≠ 0) :
    meromorphicOrderAt (chartT L a) z₀ = ((-2 : ℤ) : WithTop ℤ) := by
  obtain ⟨g, hg, hg0, hge⟩ := chartT_laurent_polar L a hz₀ ha hd
  exact meromorphicOrderAt_eq_of_laurent hg
    (by rw [hg0]; exact inv_ne_zero (mul_ne_zero two_ne_zero hd))
    (fun z _ => by rw [hge z, zpow_neg_two_eq])

/-- The residue of `u` at `z₀`: `(z - z₀) u(z) → 1/℘'(z₀)`. -/
theorem tendsto_residue_chartU (a : ℂ) {z₀ : ℂ} (hz₀ : z₀ ∉ L.lattice)
    (ha : L.weierstrassP z₀ = a) (hd : L.derivWeierstrassP z₀ ≠ 0) :
    Tendsto (fun z => (z - z₀) * chartU L a z) (𝓝[≠] z₀) (𝓝 (L.derivWeierstrassP z₀)⁻¹) := by
  obtain ⟨g, hg, hg0, hge⟩ := chartU_laurent_polar L a hz₀ ha hd
  have h1 : Tendsto g (𝓝[≠] z₀) (𝓝 (g z₀)) :=
    hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [hg0] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz' : z - z₀ ≠ 0 := sub_ne_zero.2 hz
  rw [hge z, ← mul_assoc, mul_inv_cancel₀ hz', one_mul]

end Orders

/-! ### E20: the polar point -/

section PolarPoint

variable (L : PeriodPair)

/-- **E20 (D4).** For every `a` there is `z_Q ∉ Λ` with `℘(z_Q) = a`. -/
theorem exists_polar_point (a : ℂ) : ∃ z : ℂ, z ∉ L.lattice ∧ L.weierstrassP z = a := by
  by_contra hne
  have hne' : ∀ z, z ∉ L.lattice → L.weierstrassP z ≠ a := fun z hz h => hne ⟨z, hz, h⟩
  have hgd : DifferentiableOn ℂ (chartU L a) ((L.lattice : Set ℂ)ᶜ) := by
    intro z hz
    have h1 : DifferentiableOn ℂ (fun z => L.weierstrassP z - a) ((L.lattice : Set ℂ)ᶜ) :=
      L.differentiableOn_weierstrassP.sub_const a
    exact (h1.inv (fun z hz => sub_ne_zero.2 (hne' z hz))) z hz
  have hgp : ∀ l ∈ L.lattice, ∀ z, z ∉ L.lattice → chartU L a (z + l) = chartU L a z :=
    fun l hl z _ => chartU_add_lattice L hl a z
  obtain ⟨g₀, hg₀, hg₀1, hg₀e⟩ := chartU_laurent_lattice L a (zero_mem L.lattice)
  have hk : ContinuousAt (fun z : ℂ => (z - 0) ^ 2 * g₀ z) 0 :=
    ((continuousAt_id.sub continuousAt_const).pow 2).mul hg₀.continuousAt
  have hgk : chartU L a =ᶠ[𝓝[≠] (0 : ℂ)] fun z => (z - 0) ^ 2 * g₀ z := by
    filter_upwards [self_mem_nhdsWithin] with z hz using hg₀e z hz
  obtain ⟨G, hGd, hGg, hGp⟩ := exists_entire_extension_periodic L (chartU L a) hgd hgp
    (bounded_near_zero_of_germ hk hgk)
  have hG0 : G 0 = 0 := by
    have hGev : G =ᶠ[𝓝[≠] (0 : ℂ)] fun z => (z - 0) ^ 2 * g₀ z := by
      filter_upwards [eventually_not_mem_lattice L, hgk] with z hz hz2
      rw [hGg z hz]
      exact hz2
    have h1 : Tendsto G (𝓝[≠] (0 : ℂ)) (𝓝 (G 0)) :=
      hGd.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun z : ℂ => (z - 0) ^ 2 * g₀ z) (𝓝[≠] (0 : ℂ))
        (𝓝 ((0 - 0) ^ 2 * g₀ 0)) := hk.tendsto.mono_left nhdsWithin_le_nhds
    have := tendsto_nhds_unique_of_eventuallyEq h1 h2 hGev
    simpa using this
  have hhalf := L.ω₁_div_two_notMem_lattice
  have hconst := periodic_entire_const L hGd (fun z l hl => hGp l hl z) (L.ω₁ / 2) 0
  have h0 : chartU L a (L.ω₁ / 2) = 0 := by rw [← hGg _ hhalf, hconst, hG0]
  have h00 : L.weierstrassP (L.ω₁ / 2) - a = 0 := inv_eq_zero.mp h0
  exact hne' _ hhalf (sub_eq_zero.mp h00)

end PolarPoint

/-! ### Lattices with `Im (ω₂/ω₁) > 0`, and Corollary 4.2 for every lattice -/

section TauPos

lemma weierstrassP_congr_lattice {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    L.weierstrassP = L'.weierstrassP := by
  funext z
  rw [PeriodPair.weierstrassP, PeriodPair.weierstrassP, h]

lemma derivWeierstrassP_congr_lattice {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    L.derivWeierstrassP = L'.derivWeierstrassP := by
  funext z
  rw [PeriodPair.derivWeierstrassP, PeriodPair.derivWeierstrassP, h]

/-- The ratio of the two periods is not real. -/
lemma im_ratio_ne_zero (L : PeriodPair) : (L.ω₂ / L.ω₁).im ≠ 0 := by
  intro h
  have hω := ω₁_ne_zero L
  have hr : ((L.ω₂ / L.ω₁).re : ℂ) = L.ω₂ / L.ω₁ := Complex.ext (by simp) (by simp [h])
  have e : (L.ω₂ / L.ω₁) * L.ω₁ = L.ω₂ := div_mul_cancel₀ _ hω
  obtain ⟨-, h1⟩ := LinearIndependent.pair_iff.mp L.indep (-(L.ω₂ / L.ω₁).re) 1 (by
    simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_one, hr]
    linear_combination (-1 : ℂ) * e)
  exact one_ne_zero h1

/-- Every lattice is the lattice of a period pair with `Im (ω₂/ω₁) > 0`. -/
theorem exists_tauPos_lattice (L : PeriodPair) :
    ∃ L' : PeriodPair, L'.lattice = L.lattice ∧ TauPos L' := by
  rcases lt_or_gt_of_ne (im_ratio_ne_zero L) with hneg | hpos
  · have hind : LinearIndependent ℝ ![L.ω₁, -L.ω₂] := by
      refine LinearIndependent.pair_iff.mpr fun s t hst => ?_
      have h2 : s • L.ω₁ + (-t) • L.ω₂ = 0 := by
        rw [neg_smul]
        rwa [smul_neg] at hst
      obtain ⟨h3, h4⟩ := LinearIndependent.pair_iff.mp L.indep s (-t) h2
      exact ⟨h3, neg_eq_zero.mp h4⟩
    have key : ∀ x, x ∈ (⟨L.ω₁, -L.ω₂, hind⟩ : PeriodPair).lattice ↔ x ∈ L.lattice := by
      intro x
      rw [PeriodPair.mem_lattice, PeriodPair.mem_lattice]
      try dsimp only
      constructor
      · rintro ⟨m, n, h⟩
        exact ⟨m, -n, by push_cast; linear_combination h⟩
      · rintro ⟨m, n, h⟩
        exact ⟨m, -n, by push_cast; linear_combination h⟩
    refine ⟨⟨L.ω₁, -L.ω₂, hind⟩, ?_, ?_⟩
    · ext x
      exact key x
    · show 0 < ((-L.ω₂) / L.ω₁).im
      rw [neg_div, Complex.neg_im]
      linarith
  · exact ⟨L, rfl, hpos⟩

variable (L : PeriodPair)

/-- **Corollary 4.2(a)**, for every lattice: `℘ z = ℘ c ↔ z - c ∈ Λ ∨ z + c ∈ Λ`. -/
theorem weierstrassP_eq_iff_general {c z : ℂ} (hc : c ∉ L.lattice) (hz : z ∉ L.lattice) :
    L.weierstrassP z = L.weierstrassP c ↔ z - c ∈ L.lattice ∨ z + c ∈ L.lattice := by
  obtain ⟨L', hL', hτ⟩ := exists_tauPos_lattice L
  have e := weierstrassP_congr_lattice hL'
  rw [← hL'] at hc hz ⊢
  rw [← e]
  exact CatalanCore.Elliptic.Theta.weierstrassP_eq_iff hτ hc hz

theorem two_mul_not_mem_of_deriv_ne {z : ℂ} (h : L.derivWeierstrassP z ≠ 0) :
    2 * z ∉ L.lattice := by
  intro hl
  apply h
  have h1 : L.derivWeierstrassP (z - 2 * z) = L.derivWeierstrassP z :=
    L.derivWeierstrassP_sub_coe z ⟨2 * z, hl⟩
  have h2 : z - 2 * z = -z := by ring
  rw [h2, L.derivWeierstrassP_neg] at h1
  linear_combination (-1 / 2 : ℂ) * h1

/-- Differentiating Proposition 4.1 at `c`: `℘'(c) = 0` forces `2c ∈ Λ`. -/
theorem two_mul_mem_of_deriv_eq_zero_aux (hτ : TauPos L) {c : ℂ} (hc : c ∉ L.lattice)
    (h : L.derivWeierstrassP c = 0) : 2 * c ∈ L.lattice := by
  have hθ := differentiable_thetaL hτ
  have hd := hasDerivAt_weierstrassP_of_not_mem L hc
  have h1 : HasDerivAt (fun z => thetaL L (z - c)) (deriv (thetaL L) (c - c)) c :=
    (hθ (c - c)).hasDerivAt.comp_sub_const c c
  have h2 : HasDerivAt (fun z => thetaL L (z + c)) (deriv (thetaL L) (c + c)) c :=
    (hθ (c + c)).hasDerivAt.comp_add_const c c
  have hl := h1.mul h2
  have hF : DifferentiableAt ℂ (fun z => thetaKappa L c * thetaL L z ^ 2) c :=
    ((hθ c).pow 2).const_mul _
  have hB : HasDerivAt (fun z => L.weierstrassP z - L.weierstrassP c)
      (L.derivWeierstrassP c) c := hd.sub_const _
  have hr := hF.hasDerivAt.mul hB
  have hev : (fun z => thetaL L (z - c) * thetaL L (z + c)) =ᶠ[𝓝 c]
      fun z => thetaKappa L c * thetaL L z ^ 2 * (L.weierstrassP z - L.weierstrassP c) := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hc] with z hz
    exact thetaL_sub_mul_add hτ hc hz
  have key := hl.unique (hr.congr_of_eventuallyEq hev)
  have h3 : deriv (thetaL L) 0 * thetaL L (c + c) = 0 := by
    simpa [h] using key
  rcases mul_eq_zero.1 h3 with h0 | h0
  · exact absurd h0 (deriv_thetaL_zero_ne_zero hτ)
  · have := (thetaL_eq_zero_iff hτ _).1 h0
    rwa [← two_mul] at this

/-- **Corollary 4.2(b)(c)**, for every lattice: for `c ∉ Λ`, `℘'(c) = 0 ↔ 2c ∈ Λ`. -/
theorem derivWeierstrassP_eq_zero_iff {c : ℂ} (hc : c ∉ L.lattice) :
    L.derivWeierstrassP c = 0 ↔ 2 * c ∈ L.lattice := by
  constructor
  · intro h
    obtain ⟨L', hL', hτ⟩ := exists_tauPos_lattice L
    have e := derivWeierstrassP_congr_lattice hL'
    rw [← hL'] at hc ⊢
    rw [← e] at h
    exact two_mul_mem_of_deriv_eq_zero_aux L' hτ hc h
  · intro hl
    by_contra h
    exact two_mul_not_mem_of_deriv_ne L h hl

end TauPos

/-! ### E22: the divisor of `℘ - a` -/

section Divisor

variable (L : PeriodPair)

/-- (ii) `℘'(z)² = 4 f(℘ z)`: if `℘ z = a ≠` a root of the cubic, `℘' z ≠ 0`. -/
theorem derivWeierstrassP_ne_zero_of_wp_eq {a z : ℂ} (hz : z ∉ L.lattice)
    (ha : L.weierstrassP z = a) (hf : 4 * a ^ 3 - L.g₂ * a - L.g₃ ≠ 0) :
    L.derivWeierstrassP z ≠ 0 := by
  intro h
  apply hf
  have := L.derivWeierstrassP_sq z hz
  rw [h, ha] at this
  linear_combination (-1 : ℂ) * this

/-- (iii) `2 z_Q ∉ Λ`. -/
theorem two_mul_not_mem_of_wp_eq {a z : ℂ} (hz : z ∉ L.lattice)
    (ha : L.weierstrassP z = a) (hf : 4 * a ^ 3 - L.g₂ * a - L.g₃ ≠ 0) :
    2 * z ∉ L.lattice :=
  two_mul_not_mem_of_deriv_ne L (derivWeierstrassP_ne_zero_of_wp_eq L hz ha hf)

/-- (iv) the zero set of `℘ - a` off `Λ` is `(z_Q + Λ) ∪ (-z_Q + Λ)`. -/
theorem wp_eq_iff_cosets {a zQ : ℂ} (hzQ : zQ ∉ L.lattice) (hP : L.weierstrassP zQ = a)
    {z : ℂ} (hz : z ∉ L.lattice) :
    L.weierstrassP z = a ↔ z - zQ ∈ L.lattice ∨ z + zQ ∈ L.lattice := by
  rw [← hP]
  exact weierstrassP_eq_iff_general L hzQ hz

/-- (iii) the cosets `z_Q + Λ` and `-z_Q + Λ` are disjoint. -/
theorem cosets_disjoint {a zQ : ℂ} (hzQ : zQ ∉ L.lattice) (hP : L.weierstrassP zQ = a)
    (hf : 4 * a ^ 3 - L.g₂ * a - L.g₃ ≠ 0) (z : ℂ) :
    ¬ (z - zQ ∈ L.lattice ∧ z + zQ ∈ L.lattice) := by
  rintro ⟨h1, h2⟩
  apply two_mul_not_mem_of_wp_eq L hzQ hP hf
  have e : 2 * zQ = (z + zQ) - (z - zQ) := by ring
  rw [e]
  exact L.lattice.sub_mem h2 h1

/-- Bundle of E22 (i)-(iv). -/
theorem polar_point_facts {a zQ : ℂ} (hzQ : zQ ∉ L.lattice) (hP : L.weierstrassP zQ = a)
    (hf : 4 * a ^ 3 - L.g₂ * a - L.g₃ ≠ 0) :
    L.derivWeierstrassP zQ ≠ 0 ∧ 2 * zQ ∉ L.lattice ∧
      (∀ z, z ∉ L.lattice → (L.weierstrassP z = a ↔ z - zQ ∈ L.lattice ∨ z + zQ ∈ L.lattice)) ∧
      (∀ z, ¬ (z - zQ ∈ L.lattice ∧ z + zQ ∈ L.lattice)) :=
  ⟨derivWeierstrassP_ne_zero_of_wp_eq L hzQ hP hf, two_mul_not_mem_of_wp_eq L hzQ hP hf,
    fun _ hz => wp_eq_iff_cosets L hzQ hP hz, cosets_disjoint L hzQ hP hf⟩

/-- (v) the poles of `u` are exactly `±z_Q + Λ`. -/
theorem meromorphicOrderAt_chartU_neg_iff {a zQ : ℂ} (hzQ : zQ ∉ L.lattice)
    (hP : L.weierstrassP zQ = a) (hf : 4 * a ^ 3 - L.g₂ * a - L.g₃ ≠ 0) (z : ℂ) :
    meromorphicOrderAt (chartU L a) z < 0 ↔ z - zQ ∈ L.lattice ∨ z + zQ ∈ L.lattice := by
  by_cases hz : z ∈ L.lattice
  · rw [meromorphicOrderAt_chartU_lattice L a hz]
    constructor
    · intro h
      exact absurd h (not_lt.2 (by exact_mod_cast (show (0 : ℤ) ≤ 2 by norm_num)))
    · rintro (h | h)
      · exact absurd (by simpa using L.lattice.sub_mem hz h) hzQ
      · exact absurd (by simpa using L.lattice.sub_mem h hz) hzQ
  · have hiff := wp_eq_iff_cosets L hzQ hP hz
    by_cases h : L.weierstrassP z = a
    · have hd := derivWeierstrassP_ne_zero_of_wp_eq L hz h hf
      rw [meromorphicOrderAt_chartU_polar L a hz h hd]
      constructor
      · intro _
        exact hiff.1 h
      · intro _
        exact_mod_cast (show (-1 : ℤ) < 0 by norm_num)
    · have han := chartU_analyticAt L a hz h
      constructor
      · intro hlt
        exact absurd hlt (not_lt.2 han.meromorphicOrderAt_nonneg)
      · intro hc
        exact absurd (hiff.2 hc) h

/-- (v) the poles of `t` are exactly `±z_Q + Λ`. -/
theorem meromorphicOrderAt_chartT_neg_iff {a zQ : ℂ} (hzQ : zQ ∉ L.lattice)
    (hP : L.weierstrassP zQ = a) (hf : 4 * a ^ 3 - L.g₂ * a - L.g₃ ≠ 0) (z : ℂ) :
    meromorphicOrderAt (chartT L a) z < 0 ↔ z - zQ ∈ L.lattice ∨ z + zQ ∈ L.lattice := by
  by_cases hz : z ∈ L.lattice
  · rw [meromorphicOrderAt_chartT_lattice L a hz]
    constructor
    · intro h
      exact absurd h (not_lt.2 (by exact_mod_cast (show (0 : ℤ) ≤ 1 by norm_num)))
    · rintro (h | h)
      · exact absurd (by simpa using L.lattice.sub_mem hz h) hzQ
      · exact absurd (by simpa using L.lattice.sub_mem h hz) hzQ
  · have hiff := wp_eq_iff_cosets L hzQ hP hz
    by_cases h : L.weierstrassP z = a
    · have hd := derivWeierstrassP_ne_zero_of_wp_eq L hz h hf
      rw [meromorphicOrderAt_chartT_polar L a hz h hd]
      constructor
      · intro _
        exact hiff.1 h
      · intro _
        exact_mod_cast (show (-2 : ℤ) < 0 by norm_num)
    · have han := chartT_analyticAt L a hz h
      constructor
      · intro hlt
        exact absurd hlt (not_lt.2 han.meromorphicOrderAt_nonneg)
      · intro hc
        exact absurd (hiff.2 hc) h

end Divisor

/-! ### E22 (vi): expansions of `u` and `t` at `0` -/

section Origin

variable (L : PeriodPair)

/-- `u = z² + a z⁴ + (a² - g₂/20) z⁶ + z⁸ ρ` near `0` (`g₂ = -4A`: `a² + A/5`). -/
theorem chartU_expansion (a : ℂ) :
    ∃ ρ : ℂ → ℂ, AnalyticAt ℂ ρ 0 ∧ ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      chartU L a z = z ^ 2 + a * z ^ 4 + (a ^ 2 - L.g₂ / 20) * z ^ 6 + z ^ 8 * ρ z := by
  obtain ⟨r, hr, hrz⟩ := weierstrassP_laurent_zero L
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = L.g₂ / 20 := ⟨_, rfl⟩
  obtain ⟨c₄, hc₄⟩ : ∃ c₄ : ℂ, c₄ = L.g₃ / 28 := ⟨_, rfl⟩
  rw [← hc, ← hc₄] at hrz
  rw [← hc]
  obtain ⟨w, hw⟩ : ∃ w : ℂ → ℂ, ∀ z, w z =
      1 - a * z ^ 2 + c * z ^ 4 + z ^ 6 * (c₄ + z ^ 2 * r z) := ⟨_, fun _ => rfl⟩
  have hwan : AnalyticAt ℂ w 0 := by
    have : w = fun z => 1 - a * z ^ 2 + c * z ^ 4 + z ^ 6 * (c₄ + z ^ 2 * r z) := funext hw
    rw [this]
    fun_prop
  have hw0 : w 0 = 1 := by rw [hw]; simp
  have hw0' : w 0 ≠ 0 := by rw [hw0]; exact one_ne_zero
  have hwne : ∀ᶠ z in 𝓝[≠] (0 : ℂ), w z ≠ 0 :=
    (hwan.continuousAt.eventually_ne hw0').filter_mono nhdsWithin_le_nhds
  have hv : AnalyticAt ℂ (fun z => (w z)⁻¹) 0 := hwan.inv hw0'
  have hK : AnalyticAt ℂ (fun z : ℂ =>
      (c₄ + z ^ 2 * r z) + 2 * a * c - a ^ 3 + z ^ 2 * (a * (c₄ + z ^ 2 * r z) + c * (a ^ 2 - c)) +
        z ^ 4 * ((a ^ 2 - c) * (c₄ + z ^ 2 * r z))) 0 := by fun_prop
  refine ⟨fun z => -(w z)⁻¹ * ((c₄ + z ^ 2 * r z) + 2 * a * c - a ^ 3 +
      z ^ 2 * (a * (c₄ + z ^ 2 * r z) + c * (a ^ 2 - c)) +
        z ^ 4 * ((a ^ 2 - c) * (c₄ + z ^ 2 * r z))), hv.neg.mul hK, ?_⟩
  filter_upwards [hwne, self_mem_nhdsWithin] with z hwz hz0
  have hz0' : z ≠ 0 := hz0
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz0'
  have hinv : (z ^ 2)⁻¹ * z ^ 2 = 1 := inv_mul_cancel₀ hz2
  have h1 : L.weierstrassP z - a = (z ^ 2)⁻¹ * w z := by
    rw [hw z]
    linear_combination hrz z + (a - c * z ^ 2 - z ^ 4 * (c₄ + z ^ 2 * r z)) * hinv
  have hu : chartU L a z = z ^ 2 * (w z)⁻¹ := by
    show (L.weierstrassP z - a)⁻¹ = _
    rw [h1, mul_inv, inv_inv]
  obtain ⟨v, hvdef⟩ : ∃ v, v = (w z)⁻¹ := ⟨_, rfl⟩
  have hvw : v * w z = 1 := by rw [hvdef]; exact inv_mul_cancel₀ hwz
  rw [hu, ← hvdef]
  rw [hw z] at hvw
  linear_combination (z ^ 2 * (1 + a * z ^ 2 + (a ^ 2 - c) * z ^ 4)) * hvw

/-- `t = -z - 2a z³ + z⁵ τ` near `0`. -/
theorem chartT_expansion (a : ℂ) :
    ∃ τ : ℂ → ℂ, AnalyticAt ℂ τ 0 ∧ ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      chartT L a z = -z - 2 * a * z ^ 3 + z ^ 5 * τ z := by
  obtain ⟨ρ, hρ, hρe⟩ := chartU_expansion L a
  obtain ⟨s, hs, hse⟩ := derivWeierstrassP_laurent_zero L
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = L.g₂ / 20 := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℂ, d = L.g₃ / 14 := ⟨_, rfl⟩
  rw [← hc] at hρe
  rw [← hc, ← hd] at hse
  have hτ : AnalyticAt ℂ (fun z : ℂ => -((a ^ 2 + 2 * ((a ^ 2 - c) + z ^ 2 * ρ z) +
      2 * a * z ^ 2 * ((a ^ 2 - c) + z ^ 2 * ρ z) + z ^ 4 * ((a ^ 2 - c) + z ^ 2 * ρ z) ^ 2) +
      (-c - d * z ^ 2 - z ^ 4 * s z) *
        (1 + a * z ^ 2 + z ^ 4 * ((a ^ 2 - c) + z ^ 2 * ρ z)) ^ 2)) 0 := by fun_prop
  refine ⟨fun z => -((a ^ 2 + 2 * ((a ^ 2 - c) + z ^ 2 * ρ z) +
      2 * a * z ^ 2 * ((a ^ 2 - c) + z ^ 2 * ρ z) + z ^ 4 * ((a ^ 2 - c) + z ^ 2 * ρ z) ^ 2) +
      (-c - d * z ^ 2 - z ^ 4 * s z) *
        (1 + a * z ^ 2 + z ^ 4 * ((a ^ 2 - c) + z ^ 2 * ρ z)) ^ 2), hτ, ?_⟩
  filter_upwards [hρe, self_mem_nhdsWithin] with z hz hz0
  have hz0' : z ≠ 0 := hz0
  have hi3 : (z ^ 3)⁻¹ * z ^ 3 = 1 := inv_mul_cancel₀ (pow_ne_zero 3 hz0')
  show L.derivWeierstrassP z / 2 * chartU L a z ^ 2 = _
  rw [hz, hse z]
  linear_combination
    (-z * (1 + a * z ^ 2 + z ^ 4 * ((a ^ 2 - c) + z ^ 2 * ρ z)) ^ 2) * hi3

end Origin

/-! ### The integral model -/

section Integral

open CatalanCore.Elliptic

theorem _root_.CatalanCore.Elliptic.IntegralModel.four_f_ne (M : IntegralModel) :
    4 * (M.a : ℂ) ^ 3 - M.Λ.g₂ * (M.a : ℂ) - M.Λ.g₃ ≠ 0 := by
  rw [M.g₂_eq, M.g₃_eq]
  have h : ((M.a ^ 3 + M.A * M.a + M.B : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr M.fa_ne
  push_cast at h
  intro h0
  apply h
  linear_combination (1 / 4 : ℂ) * h0

/-- E22 (ii): `℘'(z_Q) ≠ 0`. -/
theorem _root_.CatalanCore.Elliptic.IntegralModel.deriv_zQ_ne_zero (M : IntegralModel) :
    M.Λ.derivWeierstrassP M.zQ ≠ 0 :=
  derivWeierstrassP_ne_zero_of_wp_eq M.Λ M.zQ_not_mem M.wp_zQ M.four_f_ne

/-- E22 (iii): `2 z_Q ∉ Λ`. -/
theorem _root_.CatalanCore.Elliptic.IntegralModel.two_zQ_not_mem (M : IntegralModel) :
    2 * M.zQ ∉ M.Λ.lattice :=
  two_mul_not_mem_of_wp_eq M.Λ M.zQ_not_mem M.wp_zQ M.four_f_ne

/-- E22 (iv): `℘ z = a ↔ z ∈ ±z_Q + Λ` off the lattice. -/
theorem _root_.CatalanCore.Elliptic.IntegralModel.wp_eq_a_iff (M : IntegralModel) {z : ℂ}
    (hz : z ∉ M.Λ.lattice) :
    M.Λ.weierstrassP z = (M.a : ℂ) ↔ z - M.zQ ∈ M.Λ.lattice ∨ z + M.zQ ∈ M.Λ.lattice :=
  wp_eq_iff_cosets M.Λ M.zQ_not_mem M.wp_zQ hz

end Integral

end

end CatalanCore.Elliptic.Lattice
