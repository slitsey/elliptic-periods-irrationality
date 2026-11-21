-- Modified for this repository (D2-vendor, 20 Nov 2026): declarations that depend on the Admissible* modules are removed; see D2-DESIGN §6.1.
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import OAI.NumberTheory.PiExponent.Ampleness.AmpleCurveDegreePositive
public import OAI.NumberTheory.PiExponent.Ampleness.NefAmple
public import OAI.NumberTheory.PiExponent.Approximation.ConstantPullbackDegree
public import OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway
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

noncomputable section
namespace PiExponent.BlowupCurveMargin
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open NumericalAmpleness
variable {B X : Scheme.{0}}

theorem curve_degree_laws (p : B ⟶ Spec (.of ℂ)) [IsProper p]
    (H : LineBundle B) (hH : H.IsAmple) (C : IntegralCurve B) :
    (∀ L M : LineBundle B, curveDegree p (L.tensor M) C =
      curveDegree p L C + curveDegree p M C) ∧
    (∀ (L : LineBundle B) (n : ℕ), curveDegree p (L.pow n) C =
      (n : ℤ) * curveDegree p L C) := by
  let HC := H.pullback C.embedding
  have hHC : HC.IsAmple := LineBundle.IsAmple.pullback_closedImmersion H hH C.embedding
  have hfinite := CurveDegree.finite_line_cohomology_of_ample (C.embedding ≫ p) HC hHC
  have hH2 : CurveDegree.LineCohomologyTwoZero C.scheme := by
    intro M
    exact ⟨fun a b =>
      (lineBundle_cohomology_zero_of_dimension_le 1 (C.embedding ≫ p) HC hHC M
        C.dimension.le 2 (by omega) a).trans
      (lineBundle_cohomology_zero_of_dimension_le 1 (C.embedding ≫ p) HC hHC M
        C.dimension.le 2 (by omega) b).symm⟩
  exact ⟨fun L M => curveDegree_tensor p H hH L M C hfinite hH2,
    fun L n => curveDegree_pow p H hH L C hfinite hH2 n⟩

def marginCoefficient (a : ℕ) (σ : ℝ) : ℝ := σ / ((a : ℝ) * (1 + σ) - 1)

theorem marginCoefficient_pos {a : ℕ} (ha : 1 < a) {σ : ℝ} (hσ : 0 < σ) :
    0 < marginCoefficient a σ := by
  apply div_pos hσ
  exact NefAmple.combination_denominator_pos (by exact_mod_cast ha) hσ

theorem margin_of_nonnegative_degree
    (p : B ⟶ Spec (.of ℂ)) [IsProper p] (A J : LineBundle B)
    (a : ℕ) (ha : 1 < a) (hample : ((A.pow a).tensor J).IsAmple)
    (σ : ℝ) (hσ : 0 < σ) (C : IntegralCurve B)
    (hn : 0 ≤ (curveDegree p A C : ℝ) + (1 + σ) * (curveDegree p J C : ℝ)) :
    marginCoefficient a σ * (curveDegree p ((A.pow a).tensor J) C : ℝ) ≤
      (curveDegree p (A.tensor J) C : ℝ) := by
  obtain ⟨ht,hp⟩ := curve_degree_laws p ((A.pow a).tensor J) hample C
  rw [ht, hp, ht]
  push_cast
  unfold marginCoefficient
  have ha' : 1 < (a : ℝ) := by exact_mod_cast ha
  have hd := NefAmple.combination_denominator_pos ha' hσ
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).mpr
  have hn' := mul_nonneg (sub_pos.mpr ha').le hn
  nlinarith

theorem curveDegree_zero_of_frame (p : B ⟶ Spec (.of ℂ))
    (J : LineBundle B) (C : IntegralCurve B)
    (e : (J.pullback C.embedding).sheaf ≅ structureSheaf C.scheme) :
    curveDegree p J C = 0 := by
  unfold curveDegree
  change eulerCharacteristic (C.embedding ≫ p) 1 (J.pullback C.embedding).sheaf - _ = 0
  rw [eulerCharacteristic_iso (C.embedding ≫ p) e 1]
  exact sub_self _

theorem margin_of_exceptional_frame
    (p : B ⟶ Spec (.of ℂ)) [IsProper p] (A J : LineBundle B)
    (a : ℕ) (ha : 1 < a) (hample : ((A.pow a).tensor J).IsAmple)
    (σ : ℝ) (hσ : 0 < σ) (C : IntegralCurve B)
    (e : (J.pullback C.embedding).sheaf ≅ structureSheaf C.scheme) :
    marginCoefficient a σ * (curveDegree p ((A.pow a).tensor J) C : ℝ) ≤
      (curveDegree p (A.tensor J) C : ℝ) := by
  have hj := curveDegree_zero_of_frame p J C e
  have hpos := curveDegree_pos_of_ample p ((A.pow a).tensor J) hample C
  obtain ⟨ht,hp⟩ := curve_degree_laws p ((A.pow a).tensor J) hample C
  rw [ht, hp, hj, add_zero] at hpos
  have ha' : (0 : ℤ) < a := by exact_mod_cast (Nat.zero_lt_of_lt ha)
  have hA := (mul_pos_iff_of_pos_left ha').mp hpos
  apply margin_of_nonnegative_degree p A J a ha hample σ hσ C
  rw [hj]
  simpa using (show (0 : ℝ) ≤ (curveDegree p A C : ℝ) by exact_mod_cast hA.le)

theorem margin_of_avoids_center
    (p : B ⟶ Spec (.of ℂ)) [IsProper p]
    (I : X.IdealSheafData) (π : B ⟶ X) (A J : LineBundle B)
    (ι : J.sheaf ⟶ structureSheaf B) (hJ : PresentsPullbackIdeal I π J ι)
    (a : ℕ) (ha : 1 < a) (hample : ((A.pow a).tensor J).IsAmple)
    (σ : ℝ) (hσ : 0 < σ) (C : IntegralCurve B)
    (havoid : ∀ c : C.scheme, (C.embedding ≫ π) c ∉ I.support) :
    marginCoefficient a σ * (curveDegree p ((A.pow a).tensor J) C : ℝ) ≤
      (curveDegree p (A.tensor J) C : ℝ) :=
  margin_of_exceptional_frame p A J a ha hample σ hσ C
    (InvertibleIdealAway.pullbackIsoOfAvoids I π J ι hJ C.embedding havoid)

theorem margin_of_image_outside_chart
    (p : B ⟶ Spec (.of ℂ)) [IsProper p]
    (I : X.IdealSheafData) (π : B ⟶ X) (A J : LineBundle B)
    (ι : J.sheaf ⟶ structureSheaf B) (hJ : PresentsPullbackIdeal I π J ι)
    (a : ℕ) (ha : 1 < a) (hample : ((A.pow a).tensor J).IsAmple)
    (σ : ℝ) (hσ : 0 < σ) (C : IntegralCurve B)
    (U : X.Opens) (hsupport : (I.support : Set X) ⊆ U)
    (hmiss : ∀ c : C.scheme, (C.embedding ≫ π) c ∉ U) :
    marginCoefficient a σ * (curveDegree p ((A.pow a).tensor J) C : ℝ) ≤
      (curveDegree p (A.tensor J) C : ℝ) :=
  margin_of_avoids_center p I π A J ι hJ a ha hample σ hσ C
    (fun c hc => hmiss c (hsupport hc))

theorem margin_of_contracted
    (p : B ⟶ Spec (.of ℂ)) [IsProper p] (π : B ⟶ X)
    (L : LineBundle X) (J : LineBundle B)
    (a : ℕ) (ha : 1 < a) (hample : (((L.pullback π).pow a).tensor J).IsAmple)
    (σ : ℝ) (hσ : 0 < σ) (C : IntegralCurve B)
    (x : X) (hc : Set.range (C.embedding ≫ π) ⊆ ({x} : Set X)) :
    marginCoefficient a σ * (curveDegree p (((L.pullback π).pow a).tensor J) C : ℝ) ≤
      (curveDegree p ((L.pullback π).tensor J) C : ℝ) := by
  have hA := ConstantPullbackDegree.curveDegree_eq_zero_of_contracted p L π C x hc
  have hpos := curveDegree_pos_of_ample p (((L.pullback π).pow a).tensor J) hample C
  obtain ⟨ht,hp⟩ := curve_degree_laws p (((L.pullback π).pow a).tensor J) hample C
  rw [ht, hp, hA, mul_zero, zero_add] at hpos
  apply margin_of_nonnegative_degree p (L.pullback π) J a ha hample σ hσ C
  rw [hA]
  exact add_nonneg (by norm_num) (mul_nonneg (by linarith)
    (by exact_mod_cast hpos.le))

end PiExponent.BlowupCurveMargin

end

end OAI
