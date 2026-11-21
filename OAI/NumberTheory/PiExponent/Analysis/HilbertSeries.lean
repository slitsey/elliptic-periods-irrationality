module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic.NormNum
public import OAI.NumberTheory.PiExponent.LocalAlgebra.RegularHilbertStep
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

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def sectionHilbertSeries (I : Ideal (MvPolynomial σ k)) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (Module.finrank k (quotientSection I n) : ℤ))

omit [Finite σ] in
@[simp] theorem coeff_sectionHilbertSeries (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    PowerSeries.coeff n (sectionHilbertSeries I) =
      (Module.finrank k (quotientSection I n) : ℤ) :=
  PowerSeries.coeff_mk _ _

theorem sectionHilbertSeries_regular_step (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hreg : IsRightRegular (Ideal.Quotient.mk I f)) :
    sectionHilbertSeries (Ideal.span {f} ⊔ I) =
      (1 - PowerSeries.X ^ d) * sectionHilbertSeries I := by
  ext n
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul']
  simp only [coeff_sectionHilbertSeries]
  by_cases hdn : d ≤ n
  · rw [ite_eq_left hdn]
    have h := regular_hilbert_step I hI f hf hreg (n-d)
    rw [Nat.sub_add_cancel hdn] at h
    apply eq_sub_of_add_eq
    exact_mod_cast h
  · rw [ite_eq_right hdn, sub_zero]
    exact congrArg (fun m : ℕ => (m : ℤ))
      (hilbert_step_of_degree_lt I hI f hf (Nat.lt_of_not_ge hdn))

end PiExponentJets.W64

end OAI
