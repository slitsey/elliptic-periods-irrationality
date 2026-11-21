module

public import Mathlib.RingTheory.Regular.RegularSequence
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

namespace PiExponentSiegel.W20

section Ring

variable {R : Type*} [CommRing R]

theorem prefixIdeal_succ (rs : List R) (i : Fin rs.length) :
    Ideal.ofList (rs.take (i.val + 1)) =
      Ideal.span {rs[i]} ⊔ Ideal.ofList (rs.take i.val) := by
  rw [List.take_succ_eq_append_getElem i.isLt, Ideal.ofList_append,
    Ideal.ofList_singleton, sup_comm]
  simp only [Fin.getElem_fin]

theorem regular_next_mod_prefix (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (i : Fin rs.length) :
    IsRightRegular (Ideal.Quotient.mk (Ideal.ofList (rs.take i.val)) rs[i]) := by
  have hsmul := hreg.toIsWeaklyRegular.regular_mod_prev i.val i.isLt
  have htop : (Ideal.ofList (rs.take i.val) • (⊤ : Submodule R R)) =
      Ideal.ofList (rs.take i.val) := by
    exact (Ideal.ofList (rs.take i.val)).mul_top
  rw [htop] at hsmul
  intro x y hxy
  apply hsmul
  simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_comm,
    Fin.getElem_fin] using hxy

theorem prefixIdeal_zero (rs : List R) : Ideal.ofList (rs.take 0) = ⊥ := by
  simp

theorem prefixIdeal_length (rs : List R) :
    Ideal.ofList (rs.take rs.length) = Ideal.ofList rs := by
  simp

end Ring

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem prefixIdeal_homogeneous
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i)) (n : ℕ) :
    (Ideal.ofList (rs.take n)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ k) := by
  apply Ideal.homogeneous_span (MvPolynomial.homogeneousSubmodule σ k)
  intro f hf
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (List.mem_of_mem_take hf)
  exact ⟨degrees ⟨i, hi⟩, hhom ⟨i, hi⟩⟩

theorem regular_prefix_hilbert_recurrence
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (i : Fin rs.length) (n : ℕ) :
    Module.finrank k
        (PiExponentJets.W64.quotientSection
          (Ideal.ofList (rs.take (i.val + 1))) (n + degrees i)) +
      Module.finrank k
        (PiExponentJets.W64.quotientSection (Ideal.ofList (rs.take i.val)) n) =
      Module.finrank k
        (PiExponentJets.W64.quotientSection
          (Ideal.ofList (rs.take i.val)) (n + degrees i)) := by
  rw [prefixIdeal_succ rs i]
  exact PiExponentJets.W64.regular_hilbert_step
    (Ideal.ofList (rs.take i.val))
    (prefixIdeal_homogeneous rs degrees hhom i.val)
    rs[i] (hhom i) (regular_next_mod_prefix rs hreg i) n

end PiExponentSiegel.W20

end OAI
