module

public import CatalanCore.Elliptic.EPA.Geo.CurveModel
public import OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage
public import OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineCoordinates
public import OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineChart
public import OAI.NumberTheory.PiExponent.Geometry.CurveImageOpenLocus
public import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism
public import OAI.NumberTheory.PiExponent.Geometry.CurveParameterFinite
public import OAI.NumberTheory.PiExponent.Jets.CompactJetIdealCoherent

/-!
# Existence of the curve model (row E09.10c)

Labels refer to `D2-DESIGN-2026-11-20.md` (§5 E09.10c) and to the OpenAI/Apache-2.0 files
`Geometry/AdmissibleCurveImage.lean`, `Geometry/AdmissibleCurveCoordinates.lean` and
`Geometry/AdmissibleCurveModel.lean` (`existsModelData`), which are followed line by line with the
log compactification replaced by the ambient compactification `P` and the chart `ambChart`.

Let `C ⊂ Y` be an integral curve of the blow-up that is not contracted to a point of `P` and meets
the chart.  Since `Y → P` is an isomorphism over the complement of the (closed) centres, the image
curve `C' ⊂ P` is birational to `C` (`functionFieldIso`); the coordinates `z = (u, t, Z)` are the
coordinates of the affine part of `C'` in the chart, transported to `C`.

* `existsEllModelData`: `Nonempty (EllModelData sc s c C)` (needs: not contracted, meets the chart).

Dependencies (vendored OAI modules not in the D2-vendor closure at the time of writing; see the
NOTES): `Ampleness.CurveBlowupImage` (+ `CurveBlowupImageBase`, `Geometry.CurveImageOpenLocus`,
`LocalAlgebra.OpenIsoFunctionField`, `Geometry.CurveProperImageDimension`),
`Geometry.CurveImageAffineCoordinates`, `Geometry.CurveImageAffineChart`.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

namespace Geo

open CatalanCore.Elliptic
open AlgebraicGeometry CategoryTheory TopologicalSpace
open OAI.PiExponent
open OAI.PiExponentSeshadri
open OAI.PiExponentSeshadri.Geometry
open CurveNormalizationModel CurveBlowupImage CurveImageAffineCoordinates

variable {m K : ℕ} {W : Weights m} {σ : ℚ} {ch : OriginChart}
variable (sc : EpaScale W σ) (s : OriginSeries ch) (c : Fin K → Fin m → ℂ)

/-! ### Curves not contracted: the image curve and the function-field identification -/

theorem centre_point_isClosed (x : ambX sc) (hx : x ∈ (centreIdeal sc s c).support) :
    IsClosed ({x} : Set (ambX sc)) := by
  change x ∈ ((centreIdeal sc s c).support : Set (ambX sc)) at hx
  rw [centreIdeal_support] at hx
  obtain ⟨j, z, rfl⟩ := Set.mem_iUnion.mp hx
  let q := ambPoint (c j) ≫ ambChart sc
  let : IsClosedImmersion q := CompactJetIdeal.section_isClosedImmersion (ambProj sc) q (by
    dsimp [q]
    rw [Category.assoc, ambChart_over, ambPoint_section])
  have he : Set.range q = {q z} := by
    ext x
    constructor
    · rintro ⟨z', rfl⟩
      exact congrArg q (Subsingleton.elim z' z)
    · rintro rfl
      exact ⟨z, rfl⟩
  rw [← he]
  exact q.isClosedEmbedding.isClosed_range

variable {sc s c}
variable (C : NumericalAmpleness.IntegralCurve (blowup sc s c))
variable (hn : ¬ ∃ x : ambX sc, Set.range (C.embedding ≫ blowupProj sc s c) ⊆ {x})

include hn in
theorem meets_centre_complement :
    ∃ y : C.scheme, (C.embedding ≫ blowupProj sc s c) y ∈ (centreIdeal sc s c).support.compl :=
  exists_image_outside_closed_points (C.embedding ≫ blowupProj sc s c)
    (centreIdeal sc s c).support (centre_point_isClosed sc s c) hn

instance blowupProj_restrict_isIso : IsIso (blowupProj sc s c ∣_ (centreIdeal sc s c).support.compl) :=
  blowup_restrict_isIso (isBlowup sc s c)

/-- The image curve `C' ⊂ P`. -/
noncomputable abbrev imageCurve : NumericalAmpleness.IntegralCurve (ambX sc) :=
  CurveBlowupImage.imageCurve (blowupProj sc s c) C hn

/-- `K(C') ≅ K(C)`: `Y → P` is an isomorphism away from the centres. -/
noncomputable def functionFieldIso :
    (imageCurve C hn).scheme.functionField ≅ C.scheme.functionField :=
  imageFunctionFieldIso (blowupProj sc s c) C hn (centreIdeal sc s c).support.compl
    (meets_centre_complement C hn)

theorem functionFieldIso_generic :
    Spec.map (functionFieldIso C hn).hom ≫
      (imageCurve C hn).scheme.fromSpecStalk (genericPoint (imageCurve C hn).scheme) ≫
      (imageCurve C hn).embedding =
    C.scheme.fromSpecStalk (genericPoint C.scheme) ≫ C.embedding ≫ blowupProj sc s c :=
  imageFunctionFieldIso_generic (blowupProj sc s c) C hn (centreIdeal sc s c).support.compl
    (meets_centre_complement C hn)

theorem image_meets_chart
    (hm : ∃ y : C.scheme, (C.embedding ≫ blowupProj sc s c) y ∈ (ambChart sc).opensRange) :
    ∃ y : (imageCurve C hn).scheme, (imageCurve C hn).embedding y ∈ (ambChart sc).opensRange := by
  obtain ⟨y, hy⟩ := hm
  refine ⟨CurveBlowupImage.imageMap (blowupProj sc s c) C hn y, ?_⟩
  simpa only [← Scheme.Hom.comp_apply, CurveBlowupImage.imageMap_comp] using hy

/-! ### Coordinates -/

noncomputable abbrev sourceStructure := C.embedding ≫ blowupStructureMap sc s c

noncomputable abbrev imageStructure := (imageCurve C hn).embedding ≫ ambProj sc

/-- The `ℂ`-algebra structure on `K(C)`. -/
@[instance_reducible] noncomputable def sourceAlgebra : Algebra ℂ C.scheme.functionField :=
  IntegralAffineOpenDimension.functionFieldAlgebra (sourceStructure C)

/-- The `ℂ`-algebra structure on `K(C')`. -/
@[instance_reducible] noncomputable def imageAlgebra :
    Algebra ℂ (imageCurve C hn).scheme.functionField :=
  IntegralAffineOpenDimension.functionFieldAlgebra (imageStructure C hn)

/-- `K(C') ≃ₐ[ℂ] K(C)`. -/
noncomputable def fieldEquiv :
    letI := imageAlgebra C hn
    letI := sourceAlgebra C
    (imageCurve C hn).scheme.functionField ≃ₐ[ℂ] C.scheme.functionField :=
  fieldAlgEquiv (imageStructure C hn) (sourceStructure C)
    (functionFieldIso C hn) (by
      simpa only [imageStructure, sourceStructure, blowupStructureMap, Category.assoc] using
        congrArg (fun f => f ≫ ambProj sc) (functionFieldIso_generic C hn))

/-- The affine part of the image curve in the chart. -/
noncomputable abbrev imageChart := affinePart (imageCurve C hn).embedding (ambChart sc)

noncomputable abbrev imageChartPresentation := affinePresentation (imageCurve C hn).embedding (ambChart sc)

variable (hm : ∃ y : C.scheme, (C.embedding ≫ blowupProj sc s c) y ∈ (ambChart sc).opensRange)

include hm in
theorem imageChart_nonempty : Nonempty (imageChart C hn).1 :=
  affinePart_nonempty _ _ (image_meets_chart C hn hm)

/-- The coordinates `(u, t, Z)` of the image curve in the chart. -/
noncomputable def imageCoordinates : Fin (m + 2) → (imageCurve C hn).scheme.functionField :=
  letI := imageChart_nonempty C hn hm
  CurveImageAffineCoordinates.coordinates (imageChart C hn) (imageChartPresentation C hn)

/-- The coordinates `z = (u, t, Z)` in `K(C)`. -/
noncomputable def coordinatesOf : Fin (m + 2) → C.scheme.functionField :=
  letI := imageAlgebra C hn
  letI := sourceAlgebra C
  fieldEquiv C hn ∘ imageCoordinates C hn hm

theorem coordinates_field_properties :
    letI := sourceAlgebra C
    Algebra.EssFiniteType ℂ C.scheme.functionField ∧
      Algebra.trdeg ℂ C.scheme.functionField = 1 ∧
      IntermediateField.adjoin ℂ (Set.range (coordinatesOf C hn hm)) = ⊤ := by
  let := sourceAlgebra C
  let := imageAlgebra C hn
  let := imageChart_nonempty C hn hm
  have hj : ambChart sc ≫ ambProj sc = Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : ℂ →+* MvPolynomial (Fin (m + 2)) ℂ)) := ambChart_over sc
  obtain ⟨ht, hd, hg⟩ := CurveImageAffineCoordinates.field_properties
    (imageStructure C hn) (imageCurve C hn).dimension
    (imageChart C hn) (imageChartPresentation C hn)
    (affinePresentation_over (ambProj sc) _ _ hj)
  let := ht
  exact transport_field_properties (fieldEquiv C hn) (imageCoordinates C hn hm) hd hg

theorem coordinatesOf_generic_map :
    letI := sourceAlgebra C
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℂ) (coordinatesOf C hn hm)).toRingHom) ≫
      ambChart sc = C.scheme.fromSpecStalk (genericPoint C.scheme) ≫ C.embedding ≫
        blowupProj sc s c := by
  let := sourceAlgebra C
  let := imageAlgebra C hn
  let := imageChart_nonempty C hn hm
  have hj : ambChart sc ≫ ambProj sc = Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : ℂ →+* MvPolynomial (Fin (m + 2)) ℂ)) := ambChart_over sc
  have himage := CurveImageAffineCoordinates.coordinates_generic_map
    (imageStructure C hn) (imageChart C hn) (imageChartPresentation C hn)
    (affinePresentation_over (ambProj sc) _ _ hj)
    (ambChart sc) (imageCurve C hn).embedding (affinePresentation_comp _ _)
  have he : (MvPolynomial.aeval (R := ℂ) (coordinatesOf C hn hm)).toRingHom =
      (functionFieldIso C hn).hom.hom.comp
        (MvPolynomial.aeval (R := ℂ) (imageCoordinates C hn hm)).toRingHom := by
    apply congrArg AlgHom.toRingHom
      (show MvPolynomial.aeval (R := ℂ) (coordinatesOf C hn hm) =
        (fieldEquiv C hn).toAlgHom.comp
          (MvPolynomial.aeval (R := ℂ) (imageCoordinates C hn hm)) from ?_)
    apply MvPolynomial.algHom_ext
    intro i
    simp only [MvPolynomial.aeval_X, AlgHom.comp_apply]
    rfl
  rw [he, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc]
  rw [show Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (R := ℂ) (imageCoordinates C hn hm)).toRingHom) ≫ ambChart sc =
      (imageCurve C hn).scheme.fromSpecStalk (genericPoint (imageCurve C hn).scheme) ≫
        (imageCurve C hn).embedding from himage]
  exact functionFieldIso_generic C hn

/-! ### Existence of the model -/

/-- A curve of the blow-up that is not contracted and meets the chart has an `EllModelData`
(OAI `AdmissibleCurveModel.existsModelData`). -/
theorem existsEllModelData (C : NumericalAmpleness.IntegralCurve (blowup sc s c))
    (hn : ¬ ∃ x : ambX sc, Set.range (C.embedding ≫ blowupProj sc s c) ⊆ {x})
    (hm : ∃ y : C.scheme, (C.embedding ≫ blowupProj sc s c) y ∈ (ambChart sc).opensRange) :
    Nonempty (EllModelData sc s c C) := by
  let := sourceAlgebra C
  have hp := coordinates_field_properties C hn hm
  let := hp.1
  let z := coordinatesOf C hn hm
  have hfinite := CurveParameterFinite.finite_over_every_parameter ℂ C.scheme.functionField hp.2.1
  have hE : ∃ q : C.scheme.functionField, Transcendental ℂ q := by
    have : Algebra.Transcendental ℂ C.scheme.functionField :=
      trdeg_ne_zero_iff.mp (by rw [hp.2.1]; exact one_ne_zero)
    exact Algebra.Transcendental.transcendental (R := ℂ) (A := C.scheme.functionField)
  obtain ⟨i, hi⟩ := CurveCenters.exists_transcendental_coordinate z hp.2.2 hE
  let f := z i
  have hf : Transcendental ℂ f := hi
  let := hfinite f hf
  obtain ⟨g, hg, hgeneric, hgfinite, W', hW, hWiso⟩ :=
    CurveNormalizationMorphism.exists_intrinsic_normalization_morphism
      (C.embedding ≫ blowupStructureMap sc s c) C.dimension f hf
  let := hgfinite
  let := hWiso
  have hWne : W' ≠ ⊥ := by
    intro he
    simp only [he, Opens.mem_bot] at hW
  have hc : parameterCurveGenericPoint f hf ≫ (g ≫ C.embedding ≫ blowupProj sc s c) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ ambChart sc := by
    rw [← Category.assoc, ← Category.assoc, hgeneric]
    simpa only [Category.assoc] using (coordinatesOf_generic_map C hn hm).symm
  exact ⟨{ E := C.scheme.functionField
           field := inferInstance
           algebra := inferInstance
           essFiniteType := hp.1
           z := z
           generate := hp.2.2
           trdeg_one := hp.2.1
           parameter := f
           parameter_transcendental := hf
           parameterFinite := inferInstance
           normalization := g
           normalizationFinite := hgfinite
           normalization_over := hg
           chart := W'
           chart_nonempty := hWne
           chartIso := hWiso
           generic_coordinates := hc }⟩

end Geo

end CatalanCore.Elliptic.EPA
