-- Modified for this repository (D2-vendor, 20 Nov 2026): the local-irreducible attribute for Admissible* declarations is removed; see D2-DESIGN §6.1 / AUDIT-D2-DESIGN.
module

public import OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveLineBundle
public import OAI.NumberTheory.PiExponent.Approximation.WeightedFrameDegree
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface
public import OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame
public import OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientInterface
public import OAI.NumberTheory.PiExponent.Polynomials.GlobalPolynomialWeightedBound
public import OAI.NumberTheory.PiExponent.Polynomials.WeightedHomogeneousSubstitution
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

noncomputable section
namespace PiExponent.WeightedPullbackDegree
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.Projective
open PiExponent.WeightedCompactification PiExponent.WeightedSliceDegree
open PiExponent.AffineJetPolynomial PiExponent.AffineJetCoefficientFrame
open PiExponent.AffineJetCoefficientInterface
variable {K ι σ : Type} [Field K]
attribute [local irreducible] Frame Sections AffineJetCoefficientInterface.coefficient
  WeightedCompactification.affineChartMap
  ProjectiveO1.lineBundle ProjectiveO1.coordinateSection ProjectiveO1.scalars
  ProjectiveO1.coordinateCocycle PiExponentSeshadri.Projective.sectionsMorphism
  PiExponentSeshadri.Projective.CoordinateAtlas.morphism PiExponentSeshadri.Projective.atlasOfFramedSections
  ProjectiveO1.globalSectionChartPolynomial
  ProjectiveIntrinsicCoefficientLaw.CoordinateData.polynomial
  ProjectiveIntrinsicCoefficientLaw.CoordinateData.frame
  ProjectiveIntrinsicCoefficientLaw.CoordinateData.ringEquiv

theorem pullback_supportBound (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (ρ : ι → ℝ) (B : ℝ) (ha : ∀ j, Finsupp.weight ρ (a j) ≤ B) (n : ℕ)
    (e : Frame (affineChartMap (R := K) a z hz coordinate hcoordinate)
      (lineBundle (R := K) a))
    (s : Sections (ProjectiveO1.lineBundle (R := K) (σ := σ)) n)
    (p : MvPolynomial.homogeneousSubmodule σ K n)
    (hp : dehomogenize z p.val = ProjectiveO1.globalSectionChartPolynomial (R := K) (σ := σ) n z
      (ProjectiveSectionInterface.sectionHom (ProjectiveO1.lineBundle (R := K) (σ := σ)) n s)) :
    SupportBound ρ ((n : ℝ) * B)
      (AffineJetCoefficientInterface.coefficient (affineChartMap (R := K) a z hz coordinate hcoordinate)
        (lineBundle (R := K) a) n e
        (ProjectiveSectionInterface.pullback (ProjectiveO1.lineBundle (R := K) (σ := σ))
          (projectiveMonomialMap (R := K) a) n s)) := by
  let D := ProjectiveIntrinsicCoefficientLaw.intrinsicData (R := K) (σ := σ)
  let ev : MvPolynomial (ChartVariables z) K →+* MvPolynomial ι K :=
    (MvPolynomial.aeval (R := K) (fun j : ChartVariables z =>
      MvPolynomial.monomial (a j.val) (1 : K))).toRingHom
  have hbound : SupportBound ρ ((n : ℝ) * B) (ev (D.polynomial n z (ProjectiveSectionInterface.sectionHom
      (ProjectiveO1.lineBundle (R := K) (σ := σ)) n s))) := by
    dsimp only [D]
    rw [ProjectiveIntrinsicCoefficientLaw.intrinsic_polynomial]
    rw [← hp]
    change SupportBound ρ ((n : ℝ) * B)
      (MvPolynomial.aeval (fun j : ChartVariables z =>
        MvPolynomial.monomial (a j.val) (1 : K)) (dehomogenize z p.val))
    rw [WeightedHomogeneousSubstitution.dehomogenize_substitution a z hz]
    exact WeightedHomogeneousSubstitution.supportBound_substitution ρ B a ha n p
  exact GlobalPolynomialWeightedBound.coefficient_bound
    (X := Proj (imageGrade (R := K) a)) (Y := D.scheme) (K := K) (ι := ι)
    (B := MvPolynomial (ChartVariables z) K)
    (ProjectiveIntrinsicCoefficientLaw.intrinsicBundle (R := K) (σ := σ))
    (projectiveMonomialMap (R := K) a)
    (affineChartMap (R := K) a z hz coordinate hcoordinate)
    (D.chartOpen z) (WeightedChartRingEvaluation.chartFactor (R := K) a z hz coordinate hcoordinate)
    (WeightedChartRingEvaluation.chartFactor_comp (R := K) a z hz coordinate hcoordinate) n
    (D.frame n z) (D.ringEquiv z) (D.polynomial n z)
    (ProjectiveIntrinsicCoefficientLaw.intrinsic_law (R := K) n z) ev
    (by
      intro q
      dsimp only [D]
      rw [ProjectiveIntrinsicCoefficientLaw.intrinsic_ringEquiv]
      exact WeightedChartRingEvaluation.chartFactor_pullback (R := K) a z hz coordinate hcoordinate q)
    ρ ((n : ℝ) * B) e s hbound

end PiExponent.WeightedPullbackDegree
end

end OAI
