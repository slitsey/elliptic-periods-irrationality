module

public import CatalanCore.Elliptic.EPA.Local.FixedBezout
public import OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison
public import OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent

/-!
# Generic prime-local fixed-hypersurface bound (row E09.4a, prime level)

Labels refer to `D2-DESIGN-2026-11-20.md` §5 E09.4a and to CM Theorem
`thm:p1-generic-prime-upper` (`cm-2610.31112-nolean.tex`, l.1218–1262).

For a prime `Q` of `ℂ[X₁..X_n]` that is minimal over `I = (f_j)`, a coordinate normal basis `A`
of cardinality `r ≥ 1`, and a fixed equation `h ∈ I` with nonzero slice `sl_A(h)`: if
`deg_ρ h ≤ d₀` and `deg_ρ f_j ≤ M`, then `ℓ_Q(I) ≤ d₀ M^{r-1} / ∏_{i ∈ A} ρ_i`.

The proof is that of OAI `PrimeWeightedBezout.weighted_prime_length_bound`
(openai/math fd4aeeb2, Apache License 2.0, Copyright OpenAI), with the point-level bound
`rational_pointLength_bound` replaced by `rational_pointLength_fixed_bound`
(`FixedBezout.lean`), applied to the sliced fixed equation `sl_A(h)`.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA.Local

open scoped BigOperators
open OAI OAI.PiExponent OAI.PiExponent.WeightedBezout
open OAI.PiExponent.CoordinateSliceComparison OAI.PiExponent.NormalBasisRigidity
open OAI.PiExponent.CoordinateFiniteSlice OAI.PiExponent.WeightedSliceDegree

/-- CM Theorem `thm:p1-generic-prime-upper`: the generic prime-local fixed-hypersurface bound. -/
theorem prime_length_fixed_equation_le {n : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) ℂ)) [Q.IsPrime]
    (A : Finset (Fin n))
    (hA : IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (Pi.basisFun Q.ResidueField _ i)) A)
    {J : Type*} (f : J → MvPolynomial (Fin n) ℂ)
    (hQ : Q ∈ (Ideal.span (Set.range f)).minimalPrimes)
    (h : MvPolynomial (Fin n) ℂ) (hh : h ∈ Ideal.span (Set.range f))
    (hslice : enumeratedSliceMap A (residueCoordinates Q) h ≠ 0)
    (ρ : Fin n → ℚ) (hρ : ∀ i, 0 < ρ i) (d₀ M : ℝ) (hd₀ : 0 ≤ d₀) (hM : 0 ≤ M)
    (hk : 0 < A.card)
    (hdh : ∀ d ∈ h.support, (∑ i ∈ d.support, (d i : ℝ) * (ρ i : ℝ)) ≤ d₀)
    (hdf : ∀ j, ∀ d ∈ (f j).support, (∑ i ∈ d.support, (d i : ℝ) * (ρ i : ℝ)) ≤ M) :
    ∃ L : ℕ, primeLength Q (Ideal.span (Set.range f)) = L ∧
      (L : ℝ) ≤ d₀ * M ^ (A.card - 1) / ∏ i ∈ A, (ρ i : ℝ) := by
  let : Infinite Q.ResidueField := Infinite.of_injective
    (algebraMap ℂ Q.ResidueField) (algebraMap ℂ Q.ResidueField).injective
  have hminimal := sliceFamily_mem_minimalPrimes_of_normalBasis Q A hA f hQ
  have hlength := length_eq_sliceFamily_of_normalBasis Q A hA f
  have hrhoR (i : Fin n) : (0 : ℝ) < ρ i := by exact_mod_cast hρ i
  have hsliceDegree : ∀ j, ∀ d ∈
      (enumeratedSliceMap A (residueCoordinates Q) (f j)).support,
      (∑ i ∈ d.support, (d i : ℝ) * (ρ (A.equivFin.symm i) : ℝ)) ≤ M := by
    intro j
    exact supportBound_enumeratedSliceMap_sum A (residueCoordinates Q)
      (fun i => (ρ i : ℝ)) (fun i => (hrhoR i).le) M (f j) (hdf j)
  have hsliceDegreeH : ∀ d ∈ (enumeratedSliceMap A (residueCoordinates Q) h).support,
      (∑ i ∈ d.support, (d i : ℝ) * (ρ (A.equivFin.symm i) : ℝ)) ≤ d₀ :=
    supportBound_enumeratedSliceMap_sum A (residueCoordinates Q)
      (fun i => (ρ i : ℝ)) (fun i => (hrhoR i).le) d₀ h hdh
  have hsliceMem : enumeratedSliceMap A (residueCoordinates Q) h ∈
      Ideal.span (Set.range (fun j =>
        enumeratedSliceMap A (residueCoordinates Q) (f j))) := by
    have hm := Ideal.mem_map_of_mem
      (enumeratedSliceMap (C := ℂ) A (residueCoordinates Q)).toRingHom hh
    rw [map_span_sliceFamily] at hm
    exact hm
  obtain ⟨L, hL, hupper⟩ := rational_pointLength_fixed_bound Q.ResidueField hk
    (fun j => enumeratedSliceMap A (residueCoordinates Q) (f j))
    (slicePoint Q A)
    (enumeratedSliceMap A (residueCoordinates Q) h) hsliceMem hslice
    (fun i => ρ (A.equivFin.symm i)) (fun i => hρ _) d₀ M hd₀ hM
    hsliceDegreeH hsliceDegree hminimal
  refine ⟨L, hlength.trans hL, ?_⟩
  have hp : (∏ i : Fin A.card, (ρ (A.equivFin.symm i) : ℝ)) =
      ∏ i ∈ A, (ρ i : ℝ) := by
    calc
      _ = ∏ i : A, (ρ i : ℝ) :=
        Fintype.prod_equiv A.equivFin.symm _ _ (fun _ => rfl)
      _ = _ := Finset.prod_coe_sort A (fun i => (ρ i : ℝ))
  simpa only [hp] using hupper

end CatalanCore.Elliptic.EPA.Local
