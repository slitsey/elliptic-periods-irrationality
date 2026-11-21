module

public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# The trace commutes with a derivation

Let `F/P` be a finite extension of fields and `D : F → F` an additive map satisfying the Leibniz
rule that preserves `P`, acting there as an additive map `d`.  Then `d (Tr_{F/P} w) = Tr_{F/P} (D w)`
(CM, proof of `prop:origin-finite-extension-nonexact`: "trace commutes with this derivation").

Paper proof (matrix form, no normal closure or uniqueness of extensions).  Fix a `P`-basis `(b_j)`
of `F`.  Let `M = (M_{lj})` be the matrix of multiplication by `w` (`w b_j = Σ_l M_{lj} b_l`) and
`C = (C_{lj})` the matrix of `D b_j = Σ_l C_{lj} b_l`.  Applying `D` to `w b_j` and expanding in
the basis gives, with `M^{Dw}` the matrix of `D w`,
`M^{Dw} + M C = d(M) + C M`, hence `M^{Dw} = d(M) + C M - M C`.  Taking traces,
`Tr(M^{Dw}) = d(Tr M)` because `Tr(C M) = Tr(M C)`.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA.NoPrimitive

open Module Matrix

variable {P F : Type*} [Field P] [Field F] [Algebra P F]

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (D : F →+ F) (d : P →+ P) (hleib : ∀ f g : F, D (f * g) = D f * g + f * D g)
  (hd : ∀ p : P, D (algebraMap P F p) = algebraMap P F (d p))
  (b : Basis ι P F)

/-- Coordinates of a product: `(w y)_l = Σ_i (w b_i)_l y_i`. -/
lemma repr_mul (w y : F) (l : ι) :
    b.repr (w * y) l = ∑ i, b.repr (w * b i) l * b.repr y i := by
  have := congrFun (Algebra.leftMulMatrix_mulVec_repr b w y) l
  simpa [Matrix.mulVec, dotProduct, Algebra.leftMulMatrix_eq_repr_mul] using this.symm

include hleib hd in
/-- Coordinates of `D f`: `(D f)_l = d (f_l) + Σ_i C_{li} f_i`. -/
lemma repr_D (f : F) (l : ι) :
    b.repr (D f) l = d (b.repr f l) + ∑ i, b.repr (D (b i)) l * b.repr f i := by
  have hf : D f = ∑ i, (algebraMap P F (d (b.repr f i)) * b i
      + algebraMap P F (b.repr f i) * D (b i)) := by
    conv_lhs => rw [← b.sum_repr f]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, hleib, hd]
  rw [hf, map_sum, Finsupp.finsetSum_apply]
  simp only [map_add, Finsupp.add_apply, Finset.sum_add_distrib]
  have e1 : ∀ i, b.repr (algebraMap P F (d (b.repr f i)) * b i) l =
      if i = l then d (b.repr f l) else 0 := by
    intro i
    rw [← Algebra.smul_def, map_smul, Basis.repr_self]
    by_cases h : i = l
    · subst h; simp
    · simp [h]
  have e2 : ∀ i, b.repr (algebraMap P F (b.repr f i) * D (b i)) l =
      b.repr (D (b i)) l * b.repr f i := by
    intro i
    rw [← Algebra.smul_def, map_smul]
    simp [mul_comm]
  simp only [e1, e2, Finset.sum_ite_eq', Finset.mem_univ, if_true]

include hleib hd in
/-- Matrix identity `M^{Dw} = d(M) + C M - M C`, entrywise. -/
lemma repr_D_mul (w : F) (l j : ι) :
    b.repr (D w * b j) l = d (b.repr (w * b j) l)
      + ∑ i, b.repr (D (b i)) l * b.repr (w * b j) i
      - ∑ i, b.repr (w * b i) l * b.repr (D (b j)) i := by
  have ha := repr_D D d hleib hd b (w * b j) l
  have hb : b.repr (D (w * b j)) l = b.repr (D w * b j) l + b.repr (w * D (b j)) l := by
    rw [hleib, map_add, Finsupp.add_apply]
  rw [repr_mul b w (D (b j)) l] at hb
  rw [hb] at ha
  linear_combination ha

include hleib hd in
/-- The trace commutes with the derivation. -/
theorem trace_derivation_comm [Module.Finite P F] (w : F) :
    d (Algebra.trace P F w) = Algebra.trace P F (D w) := by
  classical
  let b := Module.finBasis P F
  rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace b]
  simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul]
  simp only [repr_D_mul D d hleib hd b, Finset.sum_add_distrib, Finset.sum_sub_distrib, map_sum]
  have : ∑ l, ∑ i, b.repr (D (b i)) l * b.repr (w * b l) i
      = ∑ l, ∑ i, b.repr (w * b i) l * b.repr (D (b l)) i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [this]
  abel

end

end CatalanCore.Elliptic.EPA.NoPrimitive
