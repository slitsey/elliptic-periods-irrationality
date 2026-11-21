module

public import OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomialBase
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

@[expose] public section

namespace OAI

namespace PiExponentJets.W64

variable {k σ : Type*} [Field k] [Fintype σ]

theorem quotientSection_finrank_zero_of_no_variables
    (hσ : Fintype.card σ = 0) (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Module.finrank k (quotientSection I (n+1)) = 0 := by
  have h := Submodule.finrank_map_le (Ideal.Quotient.mkₐ k I).toLinearMap
    (MvPolynomial.homogeneousSubmodule σ k (n+1))
  rw [homogeneousSection_finrank, card_exponents_degree, hσ,
    Nat.multichoose_zero_succ] at h
  exact Nat.eq_zero_of_le_zero h

theorem sectionHilbertSeries_no_variables
    (hσ : Fintype.card σ = 0) (I : Ideal (MvPolynomial σ k)) :
    sectionHilbertSeries I = PowerSeries.C (Module.finrank k (quotientSection I 0) : ℤ) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_sectionHilbertSeries, quotientSection_finrank_zero_of_no_variables hσ I n]
    simp only [PowerSeries.coeff_C, Nat.succ_ne_zero, ite_false, Nat.cast_zero]

theorem exists_hilbert_numerator_no_variables
    (hσ : Fintype.card σ = 0) (I : Ideal (MvPolynomial σ k)) :
    ∃ P : Polynomial ℤ, sectionHilbertSeries I =
      (P : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val := by
  refine ⟨Polynomial.C (Module.finrank k (quotientSection I 0) : ℤ), ?_⟩
  simpa only [hσ, PowerSeries.invOneSubPow_zero, Units.val_one, mul_one,
    Polynomial.coe_C] using sectionHilbertSeries_no_variables hσ I

end PiExponentJets.W64

end OAI
