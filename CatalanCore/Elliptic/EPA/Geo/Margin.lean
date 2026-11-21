module

public import CatalanCore.Elliptic.EPA.Geo.CurveModelExists
public import CatalanCore.Elliptic.EPA.CurveInequality
public import OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin
public import OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel
public import OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField

/-!
# Curve degrees and the uniform margin (row E09.10d, part 1)

Labels refer to `D2-DESIGN-2026-11-20.md` (§5 E09.10d, §A4) and to the OpenAI/Apache-2.0 files
`Ampleness/AdmissibleBlowupMargin.lean` (`uniform_margin_of_affine_curve_data`),
`Ampleness/AdmissibleBlowupPolarization.lean`, `Ampleness/BlowupCurveMargin.lean` and
`Geometry/PlaceLocalRing.lean` (`residue_integral`, copied below because that leaf is not vendored).

Let `Y = Bl_𝓘 P` with `A = π^* 𝒪(1)`, `𝒥` the exceptional bundle, `H = A^q ⊗ 𝒥` ample.

* `curve_nonneg`: for every integral curve `C ⊂ Y` that is not contracted and meets the chart,
  `deg_C A + (1 + σ) deg_C 𝒥 ≥ 0`.  Over `X` (`t² = F(u)`): `deg 𝒥 = −D Σ μ_p`
  (E09.10c), `deg A = D d_C`, and the curve inequality `(1+σ) Σ μ_p ≤ d_C` (E09.9).  Off `X`:
  `−deg 𝒥 ≤ 8 w₀ d_C` (E09.10c, `polynomial_contact_sum_le`) and `D ≥ 8 w₀ (1+σ)` (`EpaScale.D_ge`).
* `uniform_margin`: `ε_q · deg_C H ≤ deg_C (A ⊗ 𝒥)` for every integral curve `C ⊂ Y`, with
  `ε_q = σ / (q (1+σ) − 1)` (OAI `marginCoefficient`); the three cases contracted / outside the chart /
  in the chart are those of OAI `uniform_margin_of_affine_curve_data`, the last being `curve_nonneg`.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

namespace Geo

open CatalanCore.Elliptic
open AlgebraicGeometry CategoryTheory TopologicalSpace
open OAI.PiExponent
open OAI.PiExponentSeshadri
open OAI.PiExponentSeshadri.Geometry
open CurveZeroPole CurveValuationCenter PlaceParameterModel

/-! ### Integrality of residue fields of places (copy of OAI `PlaceLocalRing.residue_integral`) -/

theorem residue_integral_of_algEquiv
    {F A B : Type*} [Field F] [CommRing A] [CommRing B]
    [Algebra F A] [Algebra F B] [IsLocalRing A] [IsLocalRing B]
    [Algebra.IsIntegral F (IsLocalRing.ResidueField A)] (e : A ≃ₐ[F] B) :
    Algebra.IsIntegral F (IsLocalRing.ResidueField B) := by
  constructor
  intro x
  obtain ⟨y, rfl⟩ := (IsLocalRing.ResidueField.mapAlgEquiv e).surjective x
  exact (Algebra.IsIntegral.isIntegral y).map (IsLocalRing.ResidueField.mapAlgEquiv e).toAlgHom

theorem residue_integral
    {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (htrdeg : Algebra.trdeg ℂ E ≤ 1) (p : NormalizedPlace ℂ E) :
    Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring p)) := by
  let f := parameter p
  have hf : Transcendental ℂ f := parameter_transcendental p
  let := CurveParameterFinite.finiteDimensional_adjoin_singleton ℂ E htrdeg hf
  let := ParameterResidueField.parameterChartConstants f hf
  let q := parameterCenterPlace f hf p.valuation p.constants_nonneg (parameter_positive p)
  let := ParameterResidueField.parameter_residue_integral f hf q
  exact residue_integral_of_algEquiv (A := Localization.AtPrime q.1)
    (parameterCenterLocalAlgEquiv f hf p (parameter_positive p))

/-! ### Non-negativity of `A + (1+σ) 𝒥` along curves -/

variable {m K : ℕ} {W : Weights m} {σ : ℚ} {ch : OriginChart}
variable {sc : EpaScale W σ} {s : OriginSeries ch} {c : Fin K → Fin m → ℂ}

/-- **Row E09.10d, `curve_nonneg`.** For an integral curve of the blow-up that is not contracted and
meets the chart, `deg A + (1+σ) deg 𝒥 ≥ 0`. -/
theorem curve_nonneg (hσ : EpaSigma m K W σ) (hthr : EpaThresholds W σ) (h1m : 1 ≤ m)
    (hc : ∀ i, Function.Injective fun j => c j i)
    (C : NumericalAmpleness.IntegralCurve (blowup sc s c))
    (hn : ¬ ∃ x : ambX sc, Set.range (C.embedding ≫ blowupProj sc s c) ⊆ {x})
    (hm : ∃ y : C.scheme, (C.embedding ≫ blowupProj sc s c) y ∈ (ambChart sc).opensRange) :
    0 ≤ (NumericalAmpleness.curveDegree (blowupStructureMap sc s c) (A sc s c) C : ℝ) +
      (1 + (σ : ℝ)) *
        (NumericalAmpleness.curveDegree (blowupStructureMap sc s c) (J sc s c) C : ℝ) := by
  obtain ⟨r⟩ := existsEllModelData C hn hm
  have hfinite := CurveParameterFinite.finite_over_every_parameter ℂ r.E r.trdeg_one
  have hres := residue_integral (E := r.E) r.trdeg_one.le
  have hcinj : Function.Injective c := fun j j' h => hc ⟨0, h1m⟩ (congrFun h ⟨0, h1m⟩)
  have hA := ell_hyperplane_degree r hfinite
  have hdn := CurveContactSum.weightedDegree_nonneg hfinite r.z (srcWt W)
  have hσ0 : (0 : ℝ) < σ := by exact_mod_cast hσ.pos
  have hD0 : (0 : ℝ) ≤ (sc.D : ℝ) := Nat.cast_nonneg _
  by_cases hrel : MvPolynomial.aeval r.z (relation (m := m) ch) = 0
  · have hb := (aeval_relation_eq_zero_iff r.z).mp hrel
    have hJ := ell_curveDegree_J_over_X r hcinj hres hfinite hb
    have hI := ell_curve_inequality W hσ hthr s hres hfinite r.z c hc r.coord_transcendental hb
    rw [hA, hJ]
    have h2 := mul_nonneg hD0 (sub_nonneg.mpr hI)
    nlinarith [h2]
  · have hJ := ell_curveDegree_J_off_X r hcinj hres hfinite hrel
    have hD : 8 * (W.w₀ : ℝ) * (1 + (σ : ℝ)) ≤ (sc.D : ℝ) := by exact_mod_cast sc.D_ge
    rw [hA]
    have h1 := mul_le_mul_of_nonneg_left hJ (by linarith : (0 : ℝ) ≤ 1 + (σ : ℝ))
    have h2 := mul_nonneg hdn (sub_nonneg.mpr hD)
    nlinarith [h1, h2]

/-! ### The uniform margin -/

/-- **Row E09.10d, `uniform_margin`.** Every integral curve `C ⊂ Y` satisfies
`ε_q · deg_C H ≤ deg_C (A ⊗ 𝒥)`, `H = A^q ⊗ 𝒥`, `ε_q = σ / (q (1+σ) − 1) > 0`. -/
theorem uniform_margin (hσ : EpaSigma m K W σ) (hthr : EpaThresholds W σ) (h1m : 1 ≤ m)
    (hc : ∀ i, Function.Injective fun j => c j i)
    (C : NumericalAmpleness.IntegralCurve (blowup sc s c)) :
    BlowupCurveMargin.marginCoefficient (ampleExponent sc s c) (σ : ℝ) *
        (NumericalAmpleness.curveDegree (blowupStructureMap sc s c) (H sc s c) C : ℝ) ≤
      (NumericalAmpleness.curveDegree (blowupStructureMap sc s c)
        ((A sc s c).tensor (J sc s c)) C : ℝ) := by
  classical
  have hσ0 : (0 : ℝ) < σ := by exact_mod_cast hσ.pos
  by_cases hct : ∃ x : ambX sc, Set.range (C.embedding ≫ blowupProj sc s c) ⊆ {x}
  · obtain ⟨x, hx⟩ := hct
    exact BlowupCurveMargin.margin_of_contracted (blowupStructureMap sc s c) (blowupProj sc s c)
      (hyp sc) (J sc s c) (ampleExponent sc s c) (one_lt_ampleExponent sc s c) (H_ample sc s c)
      (σ : ℝ) hσ0 C x hx
  · by_cases hm : ∃ y : C.scheme, (C.embedding ≫ blowupProj sc s c) y ∈ (ambChart sc).opensRange
    · exact BlowupCurveMargin.margin_of_nonnegative_degree (blowupStructureMap sc s c)
        (A sc s c) (J sc s c) (ampleExponent sc s c) (one_lt_ampleExponent sc s c)
        (H_ample sc s c) (σ : ℝ) hσ0 C (curve_nonneg hσ hthr h1m hc C hct hm)
    · exact BlowupCurveMargin.margin_of_image_outside_chart (blowupStructureMap sc s c)
        (centreIdeal sc s c) (blowupProj sc s c) (A sc s c) (J sc s c) (exceptionalInclusion sc s c)
        (exceptional_presents sc s c) (ampleExponent sc s c) (one_lt_ampleExponent sc s c)
        (H_ample sc s c) (σ : ℝ) hσ0 C (ambChart sc).opensRange
        (centreIdeal_support_subset_chart sc s c) (fun y hy => hm ⟨y, hy⟩)

end Geo

end CatalanCore.Elliptic.EPA
