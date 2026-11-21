module

public import CatalanCore.Elliptic.Interfaces
public import CatalanCore.Elliptic.Chart.Formal
public import CatalanCore.Elliptic.Chart.GermTaylor
public import CatalanCore.Elliptic.Lattice.Divisor

@[expose] public section

/-!
# The germ identity (row E06, `prop:germ`, CM Props 3.2–3.3)

Paper: `work/paper-elliptic/elliptic-periods.tex`, `prop:germ`.

Let `L : PeriodPair` have `g₂ = −4A`, `g₃ = −4B`, let `c : OriginChart` have these `A, B` and the
chart point `a`, and let `s : OriginSeries c` be the formal series `U, L` of `prop:chart`.
With `u = chartU L a = (℘ − a)⁻¹` and `t = chartT L a = (℘′/2) u²` and their values at the
lattice point `0` set to `0` (`uGerm`, `tGerm`), we prove (`germ`):

* `τ = tGerm` is analytic at `0` with `τ′(0) = −1`;
* the formal series `U`, `L` (coefficients cast `ℚ → ℂ`) converge near `0`, to functions
  `fU`, `fL` (`HasFPowerSeriesAt`);
* `u = fU ∘ τ` and `fL ∘ τ = id` as germs at `0`.

Proof (the paper's): `u = z² + …`, `t = −z + …` (A5 `chartU_expansion`, `chartT_expansion`) so `τ`
is a local coordinate; `t² = F(u)` (`chartT_sq`); with `ψ` the analytic local inverse of `τ`
and `W = u ∘ ψ`, one has `F(W(T)) = T²`, so the Taylor series of `W` is `U` by uniqueness
(`OriginChart.eq_Useries` over `ℂ`); from `u′ = −2t` and `t² = F(u)` one gets `τ′ = −F′(u)`, hence
`ψ′ F′(W) = −1` and the Taylor series of `ψ` is `L`. Taylor series of germs form a ring
homomorphism (`GermTaylor`).
-/

namespace CatalanCore.Elliptic.Chart

open Filter Topology PowerSeries CatalanCore.Elliptic.Lattice

noncomputable section

/-- `u = (℘ − a)⁻¹`, with the junk value at `0` replaced by `0`. -/
def uGerm (L : PeriodPair) (a : ℂ) : ℂ → ℂ := Function.update (chartU L a) 0 0

/-- `t = (℘′/2) u²`, with the junk value at `0` replaced by `0`. -/
def tGerm (L : PeriodPair) (a : ℂ) : ℂ → ℂ := Function.update (chartT L a) 0 0

theorem uGerm_zero (L : PeriodPair) (a : ℂ) : uGerm L a 0 = 0 := by simp [uGerm]

theorem tGerm_zero (L : PeriodPair) (a : ℂ) : tGerm L a 0 = 0 := by simp [tGerm]

theorem uGerm_of_ne (L : PeriodPair) (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    uGerm L a z = chartU L a z := by simp [uGerm, Function.update_apply, hz]

theorem tGerm_of_ne (L : PeriodPair) (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    tGerm L a z = chartT L a z := by simp [tGerm, Function.update_apply, hz]

/-! ### The identity `t² = F(u)` -/

theorem chartT_sq (L : PeriodPair) (c : OriginChart) (hg₂ : L.g₂ = -4 * (c.A : ℂ))
    (hg₃ : L.g₃ = -4 * (c.B : ℂ)) {z : ℂ} (hz : z ∉ L.lattice) :
    chartT L (c.a : ℂ) z ^ 2 = Polynomial.aeval (chartU L (c.a : ℂ) z) c.F := by
  have hsq := L.derivWeierstrassP_sq z hz
  rw [hg₂, hg₃] at hsq
  rw [OriginChart.aeval_F]
  by_cases h : L.weierstrassP z - (c.a : ℂ) = 0
  · have hu : chartU L (c.a : ℂ) z = 0 := by simp [chartU, h]
    simp [chartT, hu]
  · obtain ⟨q, hq⟩ : ∃ q : ℂ, q = L.weierstrassP z - (c.a : ℂ) := ⟨_, rfl⟩
    have hq0 : q ≠ 0 := by rw [hq]; exact h
    have hp : L.weierstrassP z = q + (c.a : ℂ) := by rw [hq]; ring
    have hu : chartU L (c.a : ℂ) z = q⁻¹ := by rw [hq]; rfl
    have ht : chartT L (c.a : ℂ) z = L.derivWeierstrassP z / 2 * q⁻¹ ^ 2 := by
      show L.derivWeierstrassP z / 2 * chartU L (c.a : ℂ) z ^ 2 = _
      rw [hu]
    have hd2 : L.derivWeierstrassP z ^ 2 =
        4 * (q + (c.a : ℂ)) ^ 3 + 4 * (c.A : ℂ) * (q + (c.a : ℂ)) + 4 * (c.B : ℂ) := by
      rw [hsq, hp]; ring
    have hv : q * q⁻¹ = 1 := mul_inv_cancel₀ hq0
    rw [ht, hu]
    linear_combination (1 / 4 * q⁻¹ ^ 4) * hd2 +
      (q⁻¹ * (q ^ 2 * q⁻¹ ^ 2 + q * q⁻¹ + 1) + 3 * (c.a : ℂ) * q⁻¹ ^ 2 * (q * q⁻¹ + 1) +
        3 * (c.a : ℂ) ^ 2 * q⁻¹ ^ 3 + (c.A : ℂ) * q⁻¹ ^ 3) * hv

theorem aux_inv_sq (d q : ℂ) : -d / q ^ 2 = -2 * (d / 2 * q⁻¹ ^ 2) := by ring

/-! ### Data at `0` -/

theorem germ_data (L : PeriodPair) (c : OriginChart) (hg₂ : L.g₂ = -4 * (c.A : ℂ))
    (hg₃ : L.g₃ = -4 * (c.B : ℂ)) :
    ∃ U0 T0 : ℂ → ℂ, AnalyticAt ℂ U0 0 ∧ AnalyticAt ℂ T0 0 ∧ U0 0 = 0 ∧ T0 0 = 0 ∧
      HasDerivAt T0 (-1) 0 ∧
      (∀ᶠ z in 𝓝 0, uGerm L (c.a : ℂ) z = U0 z) ∧ (∀ᶠ z in 𝓝 0, tGerm L (c.a : ℂ) z = T0 z) ∧
      (∀ᶠ z in 𝓝 0, T0 z ^ 2 = Polynomial.aeval (U0 z) c.F) ∧
      (∀ᶠ z in 𝓝 0, z ≠ 0 → deriv U0 z = -2 * T0 z) ∧
      (∀ᶠ z in 𝓝 0, z ≠ 0 → T0 z ≠ 0) := by
  obtain ⟨ρ, hρ, hρe⟩ := chartU_expansion L (c.a : ℂ)
  obtain ⟨τ', hτ', hτe⟩ := chartT_expansion L (c.a : ℂ)
  obtain ⟨V, hV⟩ : ∃ V : ℂ → ℂ, ∀ z, V z =
      1 + (c.a : ℂ) * z ^ 2 + ((c.a : ℂ) ^ 2 - L.g₂ / 20) * z ^ 4 + z ^ 6 * ρ z :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℂ → ℂ, ∀ z, S z =
      -1 - 2 * (c.a : ℂ) * z ^ 2 + z ^ 4 * τ' z := ⟨_, fun _ => rfl⟩
  have hVan : AnalyticAt ℂ V 0 := by
    have : V = fun z => 1 + (c.a : ℂ) * z ^ 2 + ((c.a : ℂ) ^ 2 - L.g₂ / 20) * z ^ 4 +
        z ^ 6 * ρ z := funext hV
    rw [this]; fun_prop
  have hSan : AnalyticAt ℂ S 0 := by
    have : S = fun z => -1 - 2 * (c.a : ℂ) * z ^ 2 + z ^ 4 * τ' z := funext hS
    rw [this]; fun_prop
  have hV0 : V 0 = 1 := by rw [hV]; simp
  have hS0 : S 0 = -1 := by rw [hS]; simp
  obtain ⟨U0, hU0def⟩ : ∃ U0 : ℂ → ℂ, ∀ z, U0 z = z ^ 2 * V z := ⟨_, fun _ => rfl⟩
  obtain ⟨T0, hT0def⟩ : ∃ T0 : ℂ → ℂ, ∀ z, T0 z = z * S z := ⟨_, fun _ => rfl⟩
  have hUan : AnalyticAt ℂ U0 0 := by
    have : U0 = fun z => z ^ 2 * V z := funext hU0def
    rw [this]; fun_prop
  have hTan : AnalyticAt ℂ T0 0 := by
    have : T0 = fun z => z * S z := funext hT0def
    rw [this]; fun_prop
  have hU00 : U0 0 = 0 := by rw [hU0def]; simp
  have hT00 : T0 0 = 0 := by rw [hT0def]; simp
  have hTd : HasDerivAt T0 (-1) 0 := by
    have : T0 = fun z => z * S z := funext hT0def
    rw [this]
    have h : HasDerivAt (fun z => z * S z) (1 * S 0 + 0 * deriv S 0) 0 :=
      (hasDerivAt_id' (0 : ℂ)).mul hSan.differentiableAt.hasDerivAt
    have e : (1 : ℂ) * S 0 + 0 * deriv S 0 = -1 := by rw [hS0]; ring
    rwa [e] at h
  have hUp : ∀ᶠ z in 𝓝[≠] (0 : ℂ), chartU L (c.a : ℂ) z = U0 z := by
    filter_upwards [hρe] with z hz
    rw [hz, hU0def, hV]; ring
  have hTp : ∀ᶠ z in 𝓝[≠] (0 : ℂ), chartT L (c.a : ℂ) z = T0 z := by
    filter_upwards [hτe] with z hz
    rw [hz, hT0def, hS]; ring
  have hVne : ∀ᶠ z in 𝓝 (0 : ℂ), V z ≠ 0 :=
    hVan.continuousAt.eventually_ne (by rw [hV0]; exact one_ne_zero)
  have hSne : ∀ᶠ z in 𝓝 (0 : ℂ), S z ≠ 0 :=
    hSan.continuousAt.eventually_ne (by rw [hS0]; norm_num)
  have hp : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice ∧ chartU L (c.a : ℂ) z = U0 z ∧
      chartT L (c.a : ℂ) z = T0 z := by
    filter_upwards [hUp, hTp, eventually_not_mem_lattice L] with z h1 h2 h3
    exact ⟨h3, h1, h2⟩
  have hp' := eventually_nhdsWithin_iff.1 hp
  have hQ : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → (z ∉ L.lattice ∧ chartU L (c.a : ℂ) z = U0 z ∧
      chartT L (c.a : ℂ) z = T0 z ∧ U0 z ≠ 0 ∧ T0 z ≠ 0) := by
    filter_upwards [hp', hVne, hSne] with z hz hV' hS' hz0
    obtain ⟨h1, h2, h3⟩ := hz hz0
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · rw [hU0def]; exact mul_ne_zero (pow_ne_zero 2 hz0) hV'
    · rw [hT0def]; exact mul_ne_zero hz0 hS'
  refine ⟨U0, T0, hUan, hTan, hU00, hT00, hTd, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hQ] with z hz
    by_cases hz0 : z = 0
    · subst hz0; rw [uGerm_zero, hU00]
    · rw [uGerm_of_ne _ _ hz0]; exact (hz hz0).2.1
  · filter_upwards [hQ] with z hz
    by_cases hz0 : z = 0
    · subst hz0; rw [tGerm_zero, hT00]
    · rw [tGerm_of_ne _ _ hz0]; exact (hz hz0).2.2.1
  · filter_upwards [hQ] with z hz
    by_cases hz0 : z = 0
    · subst hz0
      rw [hT00, hU00, OriginChart.aeval_F]
      simp
    · obtain ⟨hnl, hu, ht, -, -⟩ := hz hz0
      rw [← hu, ← ht]
      exact chartT_sq L c hg₂ hg₃ hnl
  · filter_upwards [hQ.eventually_nhds] with z hz hz0
    have hzn : ∀ᶠ y in 𝓝 z, y ≠ 0 := eventually_ne_nhds hz0
    obtain ⟨hnl, hu, ht, hU0ne, -⟩ := hz.self_of_nhds hz0
    have hUeq : ∀ᶠ y in 𝓝 z, chartU L (c.a : ℂ) y = U0 y := by
      filter_upwards [hz, hzn] with y hy hy0
      exact (hy hy0).2.1
    have hq : L.weierstrassP z - (c.a : ℂ) ≠ 0 := by
      intro h
      apply hU0ne
      rw [← hu]
      simp [chartU, h]
    have hd1 : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z :=
      hasDerivAt_weierstrassP_of_not_mem L hnl
    have hd2 : HasDerivAt (fun y => (L.weierstrassP y - (c.a : ℂ))⁻¹)
        (-(L.derivWeierstrassP z) / (L.weierstrassP z - (c.a : ℂ)) ^ 2) z :=
      (hd1.sub_const (c.a : ℂ)).inv hq
    have hd3 : HasDerivAt U0 (-(L.derivWeierstrassP z) / (L.weierstrassP z - (c.a : ℂ)) ^ 2) z :=
      hd2.congr_of_eventuallyEq (hUeq.mono fun y hy => hy.symm)
    rw [hd3.deriv, ← ht]
    exact aux_inv_sq _ _
  · filter_upwards [hQ] with z hz hz0
    exact (hz hz0).2.2.2.2

/-! ### The abstract germ argument -/

theorem germ_abstract (c : OriginChart) (s : OriginSeries c) {U0 T0 : ℂ → ℂ}
    (hU : AnalyticAt ℂ U0 0) (hT : AnalyticAt ℂ T0 0) (hU0 : U0 0 = 0) (hT0 : T0 0 = 0)
    (hd : HasDerivAt T0 (-1) 0)
    (h1 : ∀ᶠ z in 𝓝 0, T0 z ^ 2 = Polynomial.aeval (U0 z) c.F)
    (h2 : ∀ᶠ z in 𝓝 0, z ≠ 0 → deriv U0 z = -2 * T0 z)
    (h3 : ∀ᶠ z in 𝓝 0, z ≠ 0 → T0 z ≠ 0) :
    ∃ W ψ : ℂ → ℂ,
      HasFPowerSeriesAt W
        (FormalMultilinearSeries.ofScalars ℂ fun n => ((coeff n s.U : ℚ) : ℂ)) 0 ∧
      HasFPowerSeriesAt ψ
        (FormalMultilinearSeries.ofScalars ℂ fun n => ((coeff n s.L : ℚ) : ℂ)) 0 ∧
      (∀ᶠ z in 𝓝 0, U0 z = W (T0 z)) ∧ (∀ᶠ z in 𝓝 0, ψ (T0 z) = z) := by
  have hd0 : deriv T0 0 = -1 := hd.deriv
  have hdne : deriv T0 0 ≠ 0 := by rw [hd0]; norm_num
  obtain ⟨ψ, hψ, hψ0, hleft, hright⟩ := exists_local_inverse hT hT0 hdne
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℂ → ℂ,
      ∀ z, Φ z = Polynomial.aeval (U0 z) (Polynomial.derivative c.F) := ⟨_, fun _ => rfl⟩
  have hΦan : AnalyticAt ℂ Φ 0 := by
    have : Φ = fun z => Polynomial.aeval (U0 z) (Polynomial.derivative c.F) := funext hΦ
    rw [this]; exact analyticAt_aeval hU _
  have hΦ0 : Φ 0 = 1 := by
    rw [hΦ, hU0, Polynomial.aeval_def, Polynomial.eval₂_at_zero, c.derivative_F_coeff_zero]
    simp
  have hTan : ∀ᶠ z in 𝓝 0, AnalyticAt ℂ T0 z := hT.eventually_analyticAt
  have hUan : ∀ᶠ z in 𝓝 0, AnalyticAt ℂ U0 z := hU.eventually_analyticAt
  have hΦne : ∀ᶠ z in 𝓝 0, Φ z ≠ 0 :=
    hΦan.continuousAt.eventually_ne (by rw [hΦ0]; exact one_ne_zero)
  -- `τ′ = −F′(u)` near `0`
  have hTder : ∀ᶠ z in 𝓝 0, deriv T0 z = -Φ z := by
    filter_upwards [hTan, hUan, h1.eventually_nhds, h2, h3] with z hTz hUz h1z h2z h3z
    by_cases hz : z = 0
    · subst hz
      rw [hd0, hΦ0]
    · have hA : HasDerivAt (fun y => T0 y * T0 y) (deriv T0 z * T0 z + T0 z * deriv T0 z) z :=
        hTz.differentiableAt.hasDerivAt.mul hTz.differentiableAt.hasDerivAt
      have hB : HasDerivAt (fun y => Polynomial.aeval (U0 y) c.F) (Φ z * deriv U0 z) z := by
        rw [hΦ]
        exact (c.F.hasDerivAt_aeval (U0 z)).comp z hUz.differentiableAt.hasDerivAt
      have hB' : HasDerivAt (fun y => T0 y * T0 y) (Φ z * deriv U0 z) z :=
        hB.congr_of_eventuallyEq (h1z.mono fun y hy => by rw [sq] at hy; exact hy)
      have hEq := hA.unique hB'
      rw [h2z hz] at hEq
      have hm : T0 z * (deriv T0 z + Φ z) = 0 := by linear_combination (1 / 2 : ℂ) * hEq
      rcases mul_eq_zero.1 hm with h | h
      · exact absurd h (h3z hz)
      · linear_combination h
  have hψc : Tendsto ψ (𝓝 0) (𝓝 0) := by
    have := hψ.continuousAt.tendsto
    rwa [hψ0] at this
  -- `ψ′ = −1/F′(W)` near `0`
  have hψder : ∀ᶠ w in 𝓝 0, deriv ψ w = (-Φ (ψ w))⁻¹ := by
    filter_upwards [hright.eventually_nhds, hψ.eventually_analyticAt, hψc.eventually hTan,
      hψc.eventually hTder, hψc.eventually hΦne] with w hrw hψw hTw hdw hnew
    have hne : deriv T0 (ψ w) ≠ 0 := by rw [hdw]; exact neg_ne_zero.2 hnew
    have h := HasDerivAt.of_local_left_inverse hψw.continuousAt
      hTw.differentiableAt.hasDerivAt hne hrw
    rw [hdw] at h
    exact h.deriv
  obtain ⟨W, hWdef⟩ : ∃ W : ℂ → ℂ, ∀ w, W w = U0 (ψ w) := ⟨_, fun _ => rfl⟩
  have hWan : AnalyticAt ℂ W 0 := by
    have h0 : AnalyticAt ℂ U0 (ψ 0) := by rw [hψ0]; exact hU
    have : W = U0 ∘ ψ := funext hWdef
    rw [this]; exact h0.comp hψ
  have hW0 : W 0 = 0 := by rw [hWdef, hψ0, hU0]
  have hsq : ∀ᶠ w in 𝓝 0, w ^ 2 = Polynomial.aeval (W w) c.F := by
    filter_upwards [hψc.eventually h1, hright] with w hw hrw
    rw [hrw] at hw
    rw [hWdef]; exact hw
  have hsq' : (X : PowerSeries ℂ) ^ 2 = Polynomial.aeval (tay W) c.F := by
    rw [← tay_aeval hWan,
      ← tay_congr (f := fun w => w ^ 2) (g := fun w => Polynomial.aeval (W w) c.F) hsq,
      tay_X_pow]
  have hc0 : constantCoeff (tay W) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_tay]
    simp [hW0]
  have hŪ : PowerSeries.map (Rat.castHom ℂ) s.U = c.Useries ℂ := by
    apply c.eq_Useries
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
        s.U_zero]
      simp
    · have h := ringHom_aeval (PowerSeries.map (Rat.castHom ℂ)) s.U c.F
      rw [← h, s.U_eq]
      simp
  have hWU : tay W = c.Useries ℂ := c.eq_Useries hc0 hsq'.symm
  have hdmap : ∀ p : PowerSeries ℚ, PowerSeries.derivative (PowerSeries.map (Rat.castHom ℂ) p) =
      PowerSeries.map (Rat.castHom ℂ) (PowerSeries.derivative p) := by
    intro p
    ext n
    simp [PowerSeries.coeff_derivative, coeff_map]
  have hLbar : PowerSeries.derivative (PowerSeries.map (Rat.castHom ℂ) s.L) *
      Polynomial.aeval (tay W) (Polynomial.derivative c.F) = -1 := by
    have h := congrArg (PowerSeries.map (Rat.castHom ℂ)) s.L_deriv
    rw [map_mul, map_neg, map_one,
      ringHom_aeval (PowerSeries.map (Rat.castHom ℂ)) s.U (Polynomial.derivative c.F)] at h
    rw [hdmap, hWU, ← hŪ]
    exact h
  have hPder : PowerSeries.derivative (tay ψ) *
      Polynomial.aeval (tay W) (Polynomial.derivative c.F) = -1 := by
    have hdψ : AnalyticAt ℂ (deriv ψ) 0 := hψ.deriv
    have hΦW : AnalyticAt ℂ (fun w => Polynomial.aeval (W w) (Polynomial.derivative c.F)) 0 :=
      analyticAt_aeval hWan _
    have e1 : tay (fun w => deriv ψ w * Polynomial.aeval (W w) (Polynomial.derivative c.F)) =
        tay (deriv ψ) * Polynomial.aeval (tay W) (Polynomial.derivative c.F) := by
      rw [tay_mul hdψ hΦW, tay_aeval hWan]
    have e2 : (fun w => deriv ψ w * Polynomial.aeval (W w) (Polynomial.derivative c.F)) =ᶠ[𝓝 0]
        fun _ => (-1 : ℂ) := by
      filter_upwards [hψder, hψc.eventually hΦne] with w hw hne
      have hΦW' : Φ (ψ w) = Polynomial.aeval (W w) (Polynomial.derivative c.F) := by
        rw [hΦ, hWdef]
      show deriv ψ w * Polynomial.aeval (W w) (Polynomial.derivative c.F) = -1
      rw [← hΦW', hw, inv_neg, neg_mul, inv_mul_cancel₀ hne]
    rw [← tay_deriv hψ, ← e1, tay_congr e2, tay_const, map_neg, map_one]
  have hunit : IsUnit (Polynomial.aeval (tay W) (Polynomial.derivative c.F)) :=
    IsUnit.of_mul_eq_one (-(PowerSeries.derivative (tay ψ)))
      (by linear_combination (-1 : PowerSeries ℂ) * hPder)
  have hPL : PowerSeries.derivative (tay ψ) =
      PowerSeries.derivative (PowerSeries.map (Rat.castHom ℂ) s.L) :=
    (hunit.mul_left_inj).1 (hPder.trans hLbar.symm)
  have hψc0 : constantCoeff (tay ψ) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_tay]
    simp [hψ0]
  have hLc0 : constantCoeff (PowerSeries.map (Rat.castHom ℂ) s.L) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      s.L_zero]
    simp
  have hψL : tay ψ = PowerSeries.map (Rat.castHom ℂ) s.L :=
    PowerSeries.derivative.ext hPL (hψc0.trans hLc0.symm)
  have hWU' : tay W = PowerSeries.map (Rat.castHom ℂ) s.U := hWU.trans hŪ.symm
  refine ⟨W, ψ, ?_, ?_, ?_, hleft⟩
  · exact hasFPowerSeriesAt_of_coeff hWan (fun n => by simp [hWU', coeff_map])
  · exact hasFPowerSeriesAt_of_coeff hψ (fun n => by simp [hψL, coeff_map])
  · filter_upwards [hleft] with z hz
    rw [hWdef, hz]

/-! ### The germ identity -/

/-- **E06, `prop:germ`.** With `τ = t` the germ at `0` (`tGerm`): `τ′(0) = −1`, the formal series
`U, L` of `prop:chart` converge near `0` to `fU, fL`, and `u = fU ∘ τ`, `fL ∘ τ = id` as germs
at `0` (`uGerm` is `u`). -/
theorem germ (L : PeriodPair) (c : OriginChart) (hg₂ : L.g₂ = -4 * (c.A : ℂ))
    (hg₃ : L.g₃ = -4 * (c.B : ℂ)) (s : OriginSeries c) :
    AnalyticAt ℂ (tGerm L (c.a : ℂ)) 0 ∧ HasDerivAt (tGerm L (c.a : ℂ)) (-1) 0 ∧
      ∃ fU fL : ℂ → ℂ,
        HasFPowerSeriesAt fU
          (FormalMultilinearSeries.ofScalars ℂ fun n => ((coeff n s.U : ℚ) : ℂ)) 0 ∧
        HasFPowerSeriesAt fL
          (FormalMultilinearSeries.ofScalars ℂ fun n => ((coeff n s.L : ℚ) : ℂ)) 0 ∧
        (∀ᶠ z in 𝓝 0, uGerm L (c.a : ℂ) z = fU (tGerm L (c.a : ℂ) z)) ∧
        (∀ᶠ z in 𝓝 0, fL (tGerm L (c.a : ℂ) z) = z) := by
  obtain ⟨U0, T0, hU, hT, hU0, hT0, hd, huG, htG, h1, h2, h3⟩ := germ_data L c hg₂ hg₃
  obtain ⟨W, ψ, hW, hψ, hUW, hψT⟩ := germ_abstract c s hU hT hU0 hT0 hd h1 h2 h3
  refine ⟨hT.congr (htG.mono fun z hz => hz.symm), hd.congr_of_eventuallyEq htG,
    W, ψ, hW, hψ, ?_, ?_⟩
  · filter_upwards [huG, htG, hUW] with z h1 h2 h3
    rw [h2, h1]
    exact h3
  · filter_upwards [htG, hψT] with z h1 h2
    rw [h1]
    exact h2

/-- `prop:germ` in the form of the paper: on a punctured neighbourhood of `0`, `u = fU(t)` and
`fL(t) = z` for the functions `u = chartU`, `t = chartT`. -/
theorem germ_punctured (L : PeriodPair) (c : OriginChart) (hg₂ : L.g₂ = -4 * (c.A : ℂ))
    (hg₃ : L.g₃ = -4 * (c.B : ℂ)) (s : OriginSeries c) :
    ∃ fU fL : ℂ → ℂ,
      HasFPowerSeriesAt fU
        (FormalMultilinearSeries.ofScalars ℂ fun n => ((coeff n s.U : ℚ) : ℂ)) 0 ∧
      HasFPowerSeriesAt fL
        (FormalMultilinearSeries.ofScalars ℂ fun n => ((coeff n s.L : ℚ) : ℂ)) 0 ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), chartU L (c.a : ℂ) z = fU (chartT L (c.a : ℂ) z)) ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), fL (chartT L (c.a : ℂ) z) = z) := by
  obtain ⟨-, -, fU, fL, hU, hL, h1, h2⟩ := germ L c hg₂ hg₃ s
  refine ⟨fU, fL, hU, hL, ?_, ?_⟩
  · filter_upwards [h1.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    rw [uGerm_of_ne _ _ hz0', tGerm_of_ne _ _ hz0'] at hz
    exact hz
  · filter_upwards [h2.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    rw [tGerm_of_ne _ _ hz0'] at hz
    exact hz

end

end CatalanCore.Elliptic.Chart

namespace CatalanCore.Elliptic.IntegralModel

open Filter Topology PowerSeries CatalanCore.Elliptic.Chart CatalanCore.Elliptic.Lattice

/-- E06 for an integral model: `τ′(0) = −1`, `u = U ∘ τ`, `L ∘ τ = z` as germs at `0`. -/
theorem germ (M : IntegralModel) (s : OriginSeries M.chart) :
    AnalyticAt ℂ (tGerm M.Λ (M.a : ℂ)) 0 ∧ HasDerivAt (tGerm M.Λ (M.a : ℂ)) (-1) 0 ∧
      ∃ fU fL : ℂ → ℂ,
        HasFPowerSeriesAt fU
          (FormalMultilinearSeries.ofScalars ℂ fun n => ((coeff n s.U : ℚ) : ℂ)) 0 ∧
        HasFPowerSeriesAt fL
          (FormalMultilinearSeries.ofScalars ℂ fun n => ((coeff n s.L : ℚ) : ℂ)) 0 ∧
        (∀ᶠ z in 𝓝 0, uGerm M.Λ (M.a : ℂ) z = fU (tGerm M.Λ (M.a : ℂ) z)) ∧
        (∀ᶠ z in 𝓝 0, fL (tGerm M.Λ (M.a : ℂ) z) = z) :=
  Chart.germ M.Λ M.chart M.g₂_eq M.g₃_eq s

end CatalanCore.Elliptic.IntegralModel
