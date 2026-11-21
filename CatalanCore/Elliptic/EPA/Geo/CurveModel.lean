module

public import CatalanCore.Elliptic.EPA.Geo.ExceptionalDegree
public import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer
public import OAI.NumberTheory.PiExponent.Geometry.CurveParameterFinite
public import OAI.NumberTheory.PiExponent.Geometry.CurveMonomialMap
public import OAI.NumberTheory.PiExponent.Ampleness.BlowupAmpleTwist
public import OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness

/-!
# Curve model data and the degrees of `𝒪(1)` and `𝒥` along a curve (row E09.10c)

Labels refer to `D2-DESIGN-2026-11-20.md` (§5 E09.10c, §A3, §A6(3)) and to the OpenAI/Apache-2.0
files `Geometry/AdmissibleCurveModel.lean` (`ModelData`) and `Ampleness/AdmissibleCurveModelDegrees`
(`degreeData`), `Ampleness/AdmissibleBlowupPolarization` (`H`, `H_ample`).

* `ampleExponent`, `H = (A^q) ⊗ 𝒥`, `H_ample`: the ample polarisation of the blow-up
  (OAI `exists_ample_exceptional_power_gt_one`); used only to compute degrees on the normalisation.
* `EllModelData sc s c C`: the function field `E` of `C`, its coordinates `z = (u, t, Z)`, a
  parameter `f`, the normalisation `parameterCurve f ⟶ C` and the identification of the generic
  point with the chart (template `AdmissibleCurveModel.ModelData`).
* `ell_hyperplane_degree`: `deg_C 𝒪(1) = D · d_C`, `d_C` the weighted pole degree of `z`
  (OAI `weighted_curveDegree` at `R = D`, powers `D / srcWt`, pure monomials `x_i^{D/w_i}`).
* `ell_curveDegree_J_over_X`, `ell_curveDegree_J_off_X`: the degree of `𝒥` along `C`
  (`Geo/ExceptionalDegree.lean`).
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

namespace Geo

open CatalanCore.Elliptic
open AlgebraicGeometry CategoryTheory TopologicalSpace
open OAI.PiExponent
open OAI.PiExponentSeshadri
open OAI.PiExponentSeshadri.Geometry
open CurveNormalizationModel CurveValuationCenter PlaceValuationRing

variable {m K : ℕ} {W : Weights m} {σ : ℚ} {ch : OriginChart}
variable (sc : EpaScale W σ) (s : OriginSeries ch) (c : Fin K → Fin m → ℂ)

/-! ### The polarisation of the blow-up -/

theorem exists_ampleExponent :
    ∃ a : ℕ, 1 < a ∧ (((A sc s c).pow a).tensor (J sc s c)).IsAmple :=
  BlowupGluing.exists_ample_exceptional_power_gt_one (centreIdeal sc s c)
    (centreIdeal_support_ne_top sc s c) (hyp sc) (hyp_ample sc)

/-- The exponent `q > 1` with `(A^q) ⊗ 𝒥` ample. -/
noncomputable def ampleExponent : ℕ := (exists_ampleExponent sc s c).choose

theorem one_lt_ampleExponent : 1 < ampleExponent sc s c := (exists_ampleExponent sc s c).choose_spec.1

/-- The ample polarisation `H = (A^q) ⊗ 𝒥` of the blow-up. -/
noncomputable def H : LineBundle (blowup sc s c) :=
  ((A sc s c).pow (ampleExponent sc s c)).tensor (J sc s c)

theorem H_ample : (H sc s c).IsAmple := (exists_ampleExponent sc s c).choose_spec.2

/-! ### Model data -/

/-- The data of an integral curve `C ⊂ Y` meeting the chart, with a normalisation `parameterCurve f
⟶ C` and the coordinates `z = (u, t, Z)` of its generic point (template OAI
`AdmissibleCurveModel.ModelData`). -/
structure EllModelData (C : NumericalAmpleness.IntegralCurve (blowup sc s c)) where
  E : Type
  [field : Field E]
  [algebra : Algebra ℂ E]
  [essFiniteType : Algebra.EssFiniteType ℂ E]
  z : Fin (m + 2) → E
  generate : IntermediateField.adjoin ℂ (Set.range z) = ⊤
  trdeg_one : Algebra.trdeg ℂ E = 1
  parameter : E
  parameter_transcendental : Transcendental ℂ parameter
  [parameterFinite : FiniteDimensional (IntermediateField.adjoin ℂ {parameter}) E]
  normalization : parameterCurve parameter parameter_transcendental ⟶ C.scheme
  [normalizationFinite : IsFinite normalization]
  normalization_over : normalization ≫ C.embedding ≫ blowupStructureMap sc s c =
    parameterCurveStructureMap parameter parameter_transcendental
  chart : C.scheme.Opens
  chart_nonempty : chart ≠ ⊥
  [chartIso : IsIso (normalization ∣_ chart)]
  generic_coordinates : parameterCurveGenericPoint parameter parameter_transcendental ≫
      (normalization ≫ C.embedding ≫ blowupProj sc s c) =
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ ambChart sc

attribute [instance] EllModelData.field EllModelData.algebra EllModelData.essFiniteType
  EllModelData.parameterFinite EllModelData.normalizationFinite EllModelData.chartIso

variable {sc s c}
variable {C : NumericalAmpleness.IntegralCurve (blowup sc s c)}

/-- Some coordinate of `z` is transcendental over `ℂ` (the curve is not a point). -/
theorem EllModelData.coord_transcendental (r : EllModelData sc s c C) :
    ∃ i, Transcendental ℂ (r.z i) :=
  CurveCenters.exists_transcendental_coordinate r.z r.generate
    ⟨r.parameter, r.parameter_transcendental⟩

theorem EllModelData.genericOver (r : EllModelData sc s c C) :
    GenericOver sc s c (r.normalization ≫ C.embedding) r.z := by
  unfold GenericOver
  simpa only [Category.assoc] using r.generic_coordinates

/-! ### Degrees along the curve -/

/-- `deg_C 𝒪(1) = D · d_C` (design E09.10c, §A6(3); OAI `weighted_curveDegree`). -/
theorem ell_hyperplane_degree (r : EllModelData sc s c C)
    (hfinite : ∀ q : r.E, Transcendental ℂ q →
      FiniteDimensional (IntermediateField.adjoin ℂ {q}) r.E) :
    (NumericalAmpleness.curveDegree (blowupStructureMap sc s c) (A sc s c) C : ℝ) =
      (sc.D : ℝ) * CurveContactSum.weightedDegree hfinite r.z (srcWt W) := by
  have h := CurveNormalizedDegreeTransfer.weighted_curveDegree (ambExponents sc) r.z
    (constantIndex sc) (ambExponents_constant sc) (coordinateIndex sc)
    (ambExponents_coordinate sc) (blowupStructureMap sc s c) (H sc s c) (H_ample sc s c) C
    r.parameter r.parameter_transcendental r.normalization r.normalization_over r.chart
    r.chart_nonempty (blowupProj sc s c) r.generic_coordinates (srcWt W) (srcWt_pos W)
    (R := (sc.D : ℚ)) (by exact_mod_cast sc.D_pos) sc.src_e sc.src_eq (pureIndex sc)
    (ambExponents_pure sc) (ambExponents_weight_le sc) hfinite
  rw [Rat.cast_natCast] at h
  exact h

/-- The degree of `𝒥` on `C` is the exceptional degree on the normalisation. -/
theorem ell_curveDegree_J_eq (r : EllModelData sc s c C) :
    NumericalAmpleness.curveDegree (blowupStructureMap sc s c) (J sc s c) C =
      exceptionalDegree sc s c (r.normalization ≫ C.embedding) :=
  CurveNormalizedDegreeTransfer.curveDegree_eq_normalized (blowupStructureMap sc s c) (H sc s c)
    (H_ample sc s c) C r.parameter r.parameter_transcendental r.normalization
    r.normalization_over r.chart r.chart_nonempty (J sc s c)

/-- Over `X` (`t² = F(u)`): `deg_C 𝒥 = −D Σ_p μ_p`, the sum over the places centred at some
`(0, 0, c_j)` (CM l.3563-3589). -/
theorem ell_curveDegree_J_over_X (r : EllModelData sc s c C)
    (hcinj : Function.Injective c)
    (hres : ∀ p : NormalizedPlace ℂ r.E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ q : r.E, Transcendental ℂ q →
      FiniteDimensional (IntermediateField.adjoin ℂ {q}) r.E)
    (hrel : IsEllBranch ch r.z) :
    ((NumericalAmpleness.curveDegree (blowupStructureMap sc s c) (J sc s c) C : ℤ) : ℝ) =
      -(sc.D : ℝ) * ∑ p ∈ ellPlaces hfinite r.z c r.coord_transcendental,
        ((ellPlaceContact hres hfinite s r.z c r.coord_transcendental (jetWt W) p : ℚ) : ℝ) := by
  have h := ell_exceptional_degree_over_X sc s c r.genericOver hcinj hres hfinite
    r.coord_transcendental hrel
  rw [← ell_curveDegree_J_eq r] at h
  exact_mod_cast h

/-- Off `X` (`f(z) ≠ 0`): `−deg_C 𝒥 ≤ 8 w₀ · d_C` (design P3(i), §A4). -/
theorem ell_curveDegree_J_off_X (r : EllModelData sc s c C)
    (hcinj : Function.Injective c)
    (hres : ∀ p : NormalizedPlace ℂ r.E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ q : r.E, Transcendental ℂ q →
      FiniteDimensional (IntermediateField.adjoin ℂ {q}) r.E)
    (hne : MvPolynomial.aeval r.z (relation (m := m) ch) ≠ 0) :
    -((NumericalAmpleness.curveDegree (blowupStructureMap sc s c) (J sc s c) C : ℤ) : ℝ) ≤
      8 * (W.w₀ : ℝ) * CurveContactSum.weightedDegree hfinite r.z (srcWt W) := by
  have h := ell_exceptional_degree_off_X sc s c r.genericOver hcinj hres hfinite
    r.coord_transcendental hne
  rw [← ell_curveDegree_J_eq r] at h
  exact h

end Geo

end CatalanCore.Elliptic.EPA
