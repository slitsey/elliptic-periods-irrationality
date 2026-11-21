-- Modified for this repository (D2-vendor, 20 Nov 2026): declarations that depend on the Admissible* modules are removed; see D2-DESIGN §6.1.
module

public import OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin
public import OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily
public import OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor
public import OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionOrder
public import OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch
public import OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames
public import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers
public import OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso
public import OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Length
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.Algebra.Category.Grp.Zero
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Field.Equiv
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Algebra.Module.SnakeLemma
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Regular.Defs
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.Analysis.Normed.Group.Rat
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Sym.Card
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.DirectSum.Finite
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.Order.Minimal
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.HilbertPoly
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.SetTheory.Cardinal.ToNat
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Conv
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace OAI

namespace PiExponent.ExceptionalCurveDegree
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal PiExponent.SectionImageIdeal
variable {X Y : Scheme.{0}}

def inverseSection (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) :
    GlobalSections Y J.inverse.sheaf :=
  (lineTensorInverseIso J).inv ≫ tensorInclusion J J.inverse ι

theorem inverseSection_zeroIdeal (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    [J.sheaf.IsQuasicoherent] :
    zeroIdeal J.inverse (inverseSection J ι) = imageIdealSheaf ι := by
  classical
  have hc (y : Y) := common_affine_frames J J.inverse y
  choose U hy e f using hc
  let e' y := (e y).some
  let f' y := (f y).some
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hy y⟩
  · intro y
    let V := U y
    let a := Scheme.Modules.restrictUnitIso V.1.ι
    let b := tensorFrame J J.inverse V.1 (e' y) (f' y)
    rw [zeroIdeal_on_frame J.inverse (inverseSection J ι) V (f' y),
      imageIdealSheaf_on_frame ι V (e' y)]
    change Ideal.span {(affineMapCoefficient V a (f' y)
      ((lineTensorInverseIso J).inv ≫ tensorInclusion J J.inverse ι))} = _
    erw [affineMapCoefficient_comp V a b (f' y),
      ← Ideal.span_singleton_mul_span_singleton]
    have hu : IsUnit (affineMapCoefficient V a b (lineTensorInverseIso J).inv) := by
      apply IsUnit.map V.1.topIso.hom.hom
      exact (end_isIso_iff _).mp
        (a.symm ≪≫ ((Scheme.Modules.restrictFunctor V.1.ι).mapIso
          (lineTensorInverseIso J)).symm ≪≫ b).isIso_hom
    rw [Ideal.span_singleton_eq_top.mpr hu, Ideal.top_mul]
    exact tensor_inclusion_ideal J J.inverse ι V (e' y) (f' y)

theorem inverseSection_zeroIdeal_eq_comap
    (I : X.IdealSheafData) (π : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    (hJ : PresentsPullbackIdeal I π J ι) :
    zeroIdeal J.inverse (inverseSection J ι) = I.comap π := by
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation J
  rw [inverseSection_zeroIdeal, PresentedIdealIso.imageIdealSheaf_eq_comap I π J ι hJ]

theorem zeroIdeal_pullback (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (f : Y ⟶ X) :
    zeroIdeal (L.pullback f) (pullbackSection f s) = (zeroIdeal L s).comap f := by
  classical
  have hlocal (y : Y) : ∃ V : Y.affineOpens, y ∈ V.1 ∧
      (zeroIdeal (L.pullback f) (pullbackSection f s)).ideal V =
        ((zeroIdeal L s).comap f).ideal V := by
    obtain ⟨U, hU, ⟨e⟩⟩ := PiExponentSeshadri.InvertibleLocal.affine_frame L (f y)
    obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset
      (show y ∈ f ⁻¹ᵁ U.1 from hU)
    let g := f.resLE U.1 V hVU
    obtain ⟨eF, he⟩ := exists_restricted_pullback_frame_all_of_factor f U.1 V g
      (Scheme.Hom.resLE_comp_ι f hVU).symm e
    refine ⟨⟨V, hV⟩, hyV, ?_⟩
    rw [zeroIdeal_on_frame (L.pullback f) (pullbackSection f s) ⟨V, hV⟩ eF,
      PiExponentSeshadri.IdealPullback.comap_ideal (zeroIdeal L s) f ⟨V, hV⟩ U hVU,
      zeroIdeal_on_frame L s U e, Ideal.map_span, Set.image_singleton]
    erw [he s]
    congr 2
    change V.topIso.hom ((f.resLE U.1 V hVU).appTop _) = _
    have ht : (f.resLE U.1 V hVU).appTop = U.1.topIso.hom ≫
        f.appLE U.1 V hVU ≫ V.topIso.inv := by
      simpa only [Scheme.Hom.appTop, Scheme.Hom.appLE_eq_app] using!
        (Scheme.Hom.resLE_app_top f hVU)
    rw [ht]
    simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  choose V hy hV using hlocal
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top V
  · apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hy y⟩
  · exact hV

theorem zeroIdeal_zero (L : LineBundle X) : zeroIdeal L 0 = ⊥ := by
  classical
  choose U hx e using fun x : X => PiExponentSeshadri.InvertibleLocal.affine_frame L x
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  · intro x
    rw [zeroIdeal_on_frame L 0 (U x) (e x).some]
    erw [restrictSection_zero, coefficient_zero, map_zero, Ideal.span_singleton_zero]
    rfl

theorem pullback_inverseSection_zeroIdeal
    (I : X.IdealSheafData) (π : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    (hJ : PresentsPullbackIdeal I π J ι)
    {Z : Scheme.{0}} (g : Z ⟶ Y) :
    zeroIdeal (J.inverse.pullback g) (pullbackSection g (inverseSection J ι)) =
      I.comap (g ≫ π) := by
  rw [zeroIdeal_pullback, inverseSection_zeroIdeal_eq_comap I π J ι hJ,
    Scheme.IdealSheafData.comap_comp]

theorem pullback_inverseSection_ne_zero
    (I : X.IdealSheafData) (π : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    (hJ : PresentsPullbackIdeal I π J ι)
    {Z : Scheme.{0}} (g : Z ⟶ Y) (hg : I.comap (g ≫ π) ≠ ⊥) :
    pullbackSection g (inverseSection J ι) ≠ 0 := by
  intro hs
  have h := pullback_inverseSection_zeroIdeal I π J ι hJ g
  rw [hs] at h
  exact hg (h.symm.trans (zeroIdeal_zero _))

theorem zeroIdeal_spec_top {A : Type} [CommRing A]
    (L : LineBundle (Spec (CommRingCat.of A)))
    (s : GlobalSections _ L.sheaf) (e : L.sheaf ≅ O (Spec (CommRingCat.of A))) :
    ((zeroIdeal L s).ideal ⟨⊤, isAffineOpen_top _⟩).map
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom =
        Ideal.span {LocalSectionOrder.localCoefficient e s} := by
  change (imageIdeal (L.dualSection s) ⊤).map _ = _
  rw [imageIdeal_top_of_frame (L.dualSection s)
    (InverseFrames.pairingFrame (lineTensorInverseIso L) e)]
  change (Ideal.span {(endValue ((InverseFrames.pairingFrame (lineTensorInverseIso L) e).inv ≫
    InverseFrames.dualMap (lineTensorInverseIso L) s))}).map _ = _
  erw [InverseFrames.dualMap_coefficient]
  rw [Ideal.map_span, Set.image_singleton]
  rfl

def localIdeal {A : Type} [CommRing A] (I : X.IdealSheafData)
    (q : Spec (CommRingCat.of A) ⟶ X) : Ideal A :=
  ((I.comap q).ideal ⟨⊤, isAffineOpen_top _⟩).map
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom

theorem localIdeal_specIdeal {A B : Type} [CommRing A] [CommRing B]
    (I : Ideal B) (φ : B →+* A) :
    localIdeal (PiExponentSeshadri.IdealPullback.specIdeal I)
      (Spec.map (CommRingCat.ofHom φ)) = I.map φ := by
  unfold localIdeal
  rw [PiExponentSeshadri.IdealPullback.specIdeal_comap,
    PiExponentSeshadri.IdealPullback.specIdeal_top, Ideal.map_map]
  have he : (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom = RingHom.id A := by
    ext a
    exact (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply a
  rw [he, Ideal.map_id]

theorem localIdeal_eq_top_of_not_mem {A : Type} [CommRing A] [IsLocalRing A]
    (I : X.IdealSheafData) (q : Spec (CommRingCat.of A) ⟶ X)
    (hq : q (IsLocalRing.closedPoint A) ∉ I.support) : localIdeal I q = ⊤ := by
  have havoid (a : Spec (CommRingCat.of A)) : q a ∉ I.support :=
    ((IsLocalRing.specializes_closedPoint a).map q.continuous).mem_open
      I.support.isClosed.isOpen_compl hq
  have ht := CompactJetIdeal.restrict_eq_top_of_disjoint I q havoid
  unfold localIdeal
  rw [ht]
  exact Ideal.map_top _

section Curve
open CurveNormalizationModel CurveValuationCenter CurvePlaceCenter
open LocalSectionOrder
variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

theorem divisor_eq_localIdeal_length
    (L : LineBundle (parameterCurve f hf))
    (s : GlobalSections _ L.sheaf) (hs : s ≠ 0) (p : NormalizedPlace ℂ E) :
    CurvePlaceSectionDivisor.divisor f hf L s hs p =
      (Module.length (PlaceValuationRing.ring p)
        ((PlaceValuationRing.ring p) ⧸ localIdeal (zeroIdeal L s) (centerMorphism f hf p))).toNat := by
  let q := centerMorphism f hf p
  obtain ⟨e, he⟩ := LocalPullbackSectionOrder.exists_frame_coefficient_germ q L
  have hn : localCoefficient e (pullbackSection q s) ≠ 0 := by
    rw [he s]
    apply (map_ne_zero_iff _
      (ConcreteCategory.bijective_of_isIso (Scheme.stalkClosedPointTo q)).injective).mpr
    exact SectionZeroStalk.sectionGerm_ne_zero L s hs
      (CurveSectionDegree.affineFrameAt L (q (IsLocalRing.closedPoint _))).openSet
      (CurveSectionDegree.affineFrameAt L (q (IsLocalRing.closedPoint _))).frame _
      (CurveSectionDegree.affineFrameAt L (q (IsLocalRing.closedPoint _))).mem
  have hi : localIdeal (zeroIdeal L s) q =
      Ideal.span {localCoefficient e (pullbackSection q s)} := by
    unfold localIdeal
    rw [← zeroIdeal_pullback L s q]
    exact zeroIdeal_spec_top (L.pullback q) (pullbackSection q s) e
  rw [CurvePlaceSectionOrder.divisor_eq_local_order f hf L s hs p e, hi,
    CurveLocalOrder.length_quotient_span_eq_addVal hn]
  rfl

variable (I : X.IdealSheafData) (π : Y ⟶ X)
variable (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
variable (hJ : PresentsPullbackIdeal I π J ι)
variable (g : parameterCurve f hf ⟶ Y) (hg : I.comap (g ≫ π) ≠ ⊥)

def idealDivisor : NormalizedPlace ℂ E →₀ ℕ :=
  CurvePlaceSectionDivisor.divisor f hf (J.inverse.pullback g)
    (pullbackSection g (inverseSection J ι))
    (pullback_inverseSection_ne_zero I π J ι hJ g hg)

theorem idealDivisor_apply (p : NormalizedPlace ℂ E) :
    idealDivisor f hf I π J ι hJ g hg p =
      (Module.length (PlaceValuationRing.ring p)
        ((PlaceValuationRing.ring p) ⧸
          localIdeal I (centerMorphism f hf p ≫ g ≫ π))).toNat := by
  erw [idealDivisor, divisor_eq_localIdeal_length]
  have hi : localIdeal
      (zeroIdeal (J.inverse.pullback g) (pullbackSection g (inverseSection J ι)))
        (centerMorphism f hf p) = localIdeal I (centerMorphism f hf p ≫ g ≫ π) := by
    simp only [localIdeal, pullback_inverseSection_zeroIdeal I π J ι hJ g,
      Scheme.IdealSheafData.comap_comp]
  rw [hi]

theorem degree_eq_neg_idealDivisor_sum :
    eulerCharacteristic (parameterCurveStructureMap f hf) 1 (J.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) =
      -(idealDivisor f hf I π J ι hJ g hg).sum (fun _ n => (n : ℤ)) := by
  have hd := CurvePlaceSectionDivisor.degree_eq_euler_difference_full f hf
    (J.inverse.pullback g) (pullbackSection g (inverseSection J ι))
    (pullback_inverseSection_ne_zero I π J ι hJ g hg)
  have ht := parameterCurve_tensor_euler_add f hf (J.pullback g) (J.inverse.pullback g)
  let e : ((J.pullback g).tensor (J.inverse.pullback g)).sheaf ≅
      structureSheaf (parameterCurve f hf) :=
    (PiExponentSeshadri.PullbackTensor.iso g J J.inverse).symm ≪≫
      (Scheme.Modules.pullback g).mapIso (lineTensorInverseIso J) ≪≫ pullbackUnitIso g
  have he := eulerCharacteristic_iso (parameterCurveStructureMap f hf) e 1
  change _ = -(CurvePlaceSectionDivisor.divisor f hf (J.inverse.pullback g)
    (pullbackSection g (inverseSection J ι)) _).sum (fun _ n => (n : ℤ))
  omega

end Curve

end
end PiExponent.ExceptionalCurveDegree

end OAI
