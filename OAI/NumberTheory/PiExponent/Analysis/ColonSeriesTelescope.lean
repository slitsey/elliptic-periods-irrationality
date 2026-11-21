module

public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import OAI.NumberTheory.PiExponent.LocalAlgebra.ColonHilbertStep
public import OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFactor
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

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k]

noncomputable def iteratedColon (I : Ideal (MvPolynomial σ k)) (f : MvPolynomial σ k) :
    ℕ → Ideal (MvPolynomial σ k)
  | 0 => I
  | n+1 => (iteratedColon I f n).colon {f}

@[simp] theorem iteratedColon_zero (I : Ideal (MvPolynomial σ k)) (f : MvPolynomial σ k) :
    iteratedColon I f 0 = I := rfl

@[simp] theorem iteratedColon_succ (I : Ideal (MvPolynomial σ k)) (f : MvPolynomial σ k)
    (n : ℕ) : iteratedColon I f (n+1) = (iteratedColon I f n).colon {f} := rfl

theorem iteratedColon_homogeneous (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (n : ℕ) :
    (iteratedColon I f n).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  induction n with
  | zero => exact hI
  | succ n ih => exact PiExponentJets.W22.homogeneous_colon_singleton _ ih hf

variable [Finite σ]

theorem iteratedColon_series_telescope (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (f : MvPolynomial σ k) (hf : f.IsHomogeneous 1) (m : ℕ) :
    sectionHilbertSeries I =
      (∑ j ∈ Finset.range m, PowerSeries.X ^ j *
        sectionHilbertSeries (Ideal.span {f} ⊔ iteratedColon I f j)) +
      PowerSeries.X ^ m * sectionHilbertSeries (iteratedColon I f m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hs := sectionHilbertSeries_colon_step (iteratedColon I f m)
      (iteratedColon_homogeneous I hI f hf m) f hf
    simp only [pow_one, ← iteratedColon_succ] at hs
    rw [ih, hs, Finset.sum_range_succ, pow_succ]
    ring

theorem stableColon_series (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (f : MvPolynomial σ k) (hf : f.IsHomogeneous 1)
    (hstable : I.colon {f} = I) :
    sectionHilbertSeries I = sectionHilbertSeries (Ideal.span {f} ⊔ I) *
      (PowerSeries.invOneSubPow ℤ 1).val := by
  have hs := sectionHilbertSeries_colon_step I hI f hf
  rw [hstable, pow_one] at hs
  have he : (1 - PowerSeries.X) * sectionHilbertSeries I =
      sectionHilbertSeries (Ideal.span {f} ⊔ I) := by
    linear_combination hs
  have hunit : (1 - (PowerSeries.X : PowerSeries ℤ)) *
      (PowerSeries.invOneSubPow ℤ 1).val = 1 := by
    rw [← pow_one (1 - (PowerSeries.X : PowerSeries ℤ)),
      ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
    exact (PowerSeries.invOneSubPow ℤ 1).inv_val
  calc
    sectionHilbertSeries I = ((1-PowerSeries.X) * sectionHilbertSeries I) *
        (PowerSeries.invOneSubPow ℤ 1).val := by
          rw [mul_right_comm, hunit, one_mul]
    _ = _ := by rw [he]

theorem stabilized_iteratedColon_series (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (f : MvPolynomial σ k) (hf : f.IsHomogeneous 1) (m : ℕ)
    (hstable : iteratedColon I f (m+1) = iteratedColon I f m) :
    sectionHilbertSeries I =
      (∑ j ∈ Finset.range m, PowerSeries.X ^ j *
        sectionHilbertSeries (Ideal.span {f} ⊔ iteratedColon I f j)) +
      PowerSeries.X ^ m *
        (sectionHilbertSeries (Ideal.span {f} ⊔ iteratedColon I f m) *
          (PowerSeries.invOneSubPow ℤ 1).val) := by
  rw [iteratedColon_series_telescope I hI f hf m,
    stableColon_series (iteratedColon I f m)
      (iteratedColon_homogeneous I hI f hf m) f hf hstable]

end PiExponentJets.W64

end OAI
