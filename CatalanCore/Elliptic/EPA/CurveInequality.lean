module

public import CatalanCore.Elliptic.EPA.FibreBridge
public import CatalanCore.Elliptic.EPA.Excess
public import OAI.NumberTheory.PiExponent.Geometry.CurveInequality

/-!
# The curve inequality (row E09.9)

Labels refer to `D2-DESIGN-2026-11-20.md` §5 E09.9 and to CM (arXiv 2610.31112) Theorem
`origin-curve-inequality` (§12, `cm-2610.31112-nolean.tex` l.3246-3290; ordinary fibre §11,
l.2756-3014). Template: OAI `Geometry/CurveInequality` (openai/math fd4aeeb2, Apache License 2.0,
Copyright OpenAI).

**`ell_curve_inequality`.** Let `E` be a function field over `ℂ` (hypotheses `hres`, `hfinite` of OAI
`CurveContactSum`), `z = (u, t, Z) : Fin (m+2) → E` with `t² = F(u)` and a transcendental
coordinate, `c_j ∈ ℂ^m` centres, coordinatewise injective. Under `EpaSigma` and `EpaThresholds`,
the places `p` centred at some `(0, 0, c_j)` with contact `μ_p` satisfy

  `(1 + σ) Σ_p μ_p ≤ d_C`,   `d_C = CurveContactSum.weightedDegree z (srcWt W)`.

Proof (CM l.3285-3289). If `d_C < (1+σ) Σ_p μ_p`, E09.8 (`excess_implies_origin_fibre`) gives
`u = t = 0`, so `z = (0, 0, x)`. By `FibreBridge.lean` the elliptic places, contacts and weighted
degree are those of the ordinary fibre `x` (OAI `CurveContactFamily`, weights `radWt`, `jetWt`), the
hypotheses of the OAI ordinary-fibre theorems hold (`fibre_vol`, `fibre_separated`, `fibre_ratio`,
the height bound), and `excess_implies_fibre_coordinate_constant` makes some `Z_i` constant, which
`no_fibre_excess_of_constant_coordinate` (centres coordinatewise distinct, `(1+σ) θ < 1`) excludes.

Deviations from the design statement (each at least as strong): `hbase`, `hgen`, `htrdeg` are not
needed (as in E09.8) and are omitted.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

open CatalanCore.Elliptic OAI.PiExponent CurveValuationCenter CurveCenters PlaceValuationRing

variable {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ} {ch : OriginChart}

/-- **Row E09.9** (CM Theorem `origin-curve-inequality`, l.3269). -/
theorem ell_curve_inequality (W : Weights m) {σ : ℚ} (hσ : EpaSigma m K W σ)
    (hthr : EpaThresholds W σ) (s : OriginSeries ch)
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m + 2) → E) (c : Fin K → Fin m → ℂ)
    (hc : ∀ i, Function.Injective fun j => c j i)
    (hz : ∃ i, Transcendental ℂ (z i)) (hrel : IsEllBranch ch z) :
    (1 + (σ : ℝ)) * ∑ p ∈ ellPlaces hfinite z c hz,
        (ellPlaceContact hres hfinite s z c hz (jetWt W) p : ℝ) ≤
      CurveContactSum.weightedDegree hfinite z (srcWt W) := by
  by_contra hcon
  have hexcess := not_le.mp hcon
  obtain ⟨h0, h1⟩ := excess_implies_origin_fibre W hσ hthr s hres hfinite z c hz hrel hexcess
  obtain ⟨x, rfl⟩ := exists_ellPad z h0 h1
  have hx : ∃ i, Transcendental ℂ (x i) := exists_transcendental_of_ellPad hz
  have hz' : ∃ i, Transcendental ℂ (CurveContactFamily.fibre x i) := transcendental_fibre hx
  have hsum : ∑ p ∈ ellPlaces hfinite (ellPad x) c hz,
        (ellPlaceContact hres hfinite s (ellPad x) c hz (jetWt W) p : ℝ) =
      ∑ p ∈ CurveContactFamily.places hfinite (CurveContactFamily.fibre x) c hz',
        (CurveContactFamily.contact hres hfinite (CurveContactFamily.fibre x) c hz'
          (jetWt W) p : ℝ) := by
    refine Finset.sum_congr (ellPlaces_ellPad hfinite x c hz hz') (fun p hp => ?_)
    exact congrArg (fun q : ℚ => (q : ℝ))
      (ellPlaceContact_ellPad hres hfinite s x c hz hz' (jetWt W) p
        (by rwa [ellPlaces_ellPad hfinite x c hz hz']))
  have hexcess' : CurveContactSum.weightedDegree hfinite (CurveContactFamily.fibre x) (radWt W) <
      (1 + (σ : ℝ)) * ∑ p ∈ CurveContactFamily.places hfinite (CurveContactFamily.fibre x) c hz',
        (CurveContactFamily.contact hres hfinite (CurveContactFamily.fibre x) c hz'
          (jetWt W) p : ℝ) := by
    rw [← weightedDegree_ellPad_srcWt hfinite W x, ← hsum]
    exact hexcess
  have hconst := CurveInequality.excess_implies_fibre_coordinate_constant hres hfinite x c hz'
    (coordinateKernel_height_le x) (radWt W) (jetWt W) (fb_radWt_pos W) (fb_jetWt_pos W) σ hσ.pos
    (fibre_vol W hσ) (fibre_separated W hσ.pos hthr) hexcess'
  exact CurveInequality.no_fibre_excess_of_constant_coordinate hres hfinite x c hc hz'
    (radWt W) (jetWt W) (fb_radWt_pos W) (fb_jetWt_pos W) σ hσ.pos (fibre_ratio W hσ) hconst
    hexcess'

end CatalanCore.Elliptic.EPA
