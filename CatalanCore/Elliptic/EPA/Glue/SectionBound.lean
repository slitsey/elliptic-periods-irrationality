module

public import CatalanCore.Elliptic.EPA.Geo.Compactification
public import OAI.NumberTheory.PiExponent.Approximation.WeightedGlobalSectionBound
public import OAI.NumberTheory.PiExponent.Ampleness.WeightedAffineFrame
public import OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientInterface

/-!
# The eventual source-degree bound of section coefficients (row E09.11, part 2)

Labels refer to the proof design (§5 E09.11, §A6(2)). Template: OpenAI (Apache-2.0,
openai/math fd4aeeb2) `Approximation/WeightedGlobalSectionBound.eventual_supportBound` (generic in the
exponent family) and `Approximation/AdmissibleMatrixFrame.monomialFrame_exists`.

* `eventual_srcDeg`: for `n ≥ N` every global section `t` of `𝒪(n)` on the compactification has chart
  coefficient (a polynomial in `ℂ[u,t,Z]`) of source degree `≤ n D` (`SrcDeg W (n D)`); the exponent
  family is `Geo.ambExponents sc`, all of source weight `≤ D`.
* `ambFrame_nonempty`: the frame of `𝒪(1)` over the chart `𝔸^{m+2} → P` exists.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

namespace Glue

open CatalanCore.Elliptic AlgebraicGeometry CategoryTheory
open OAI.PiExponent OAI.PiExponentSeshadri.Geometry

variable {m : ℕ} {W : Weights m} {σ : ℚ}

/-- Every exponent of the compactification has source weight `≤ D`, as reals. -/
theorem ambExponents_weight_srcRho_le (sc : Geo.EpaScale W σ) (j : Geo.Idx sc) :
    Finsupp.weight (srcRho W) (Geo.ambExponents sc j) ≤ (sc.D : ℝ) := by
  have h := Geo.ambExponents_weight_le sc j
  have e : ∑ i, (Geo.ambExponents sc j) i • srcRho W i =
      ((∑ i, srcWt W i * ((Geo.ambExponents sc j i : ℕ) : ℚ) : ℚ) : ℝ) := by
    rw [Rat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [nsmul_eq_mul, Rat.cast_mul, Rat.cast_natCast, srcRho, mul_comm]
  rw [Finsupp.weight_eq_sum, e]
  exact_mod_cast h

/-- **Row E09.11 (section bound).** For `n ≥ N`, the chart coefficient of every global section of
`𝒪(1)^n` has source degree `≤ n D`. -/
theorem eventual_srcDeg (sc : Geo.EpaScale W σ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (e : AffineJetCoefficientInterface.Frame (Geo.ambChart sc) (Geo.hyp sc))
        (t : AffineJetCoefficientInterface.Sections (Geo.hyp sc) n),
        SrcDeg W ((n * sc.D : ℕ) : ℝ)
          (AffineJetCoefficientInterface.coefficient (Geo.ambChart sc) (Geo.hyp sc) n e t) := by
  obtain ⟨N, hN⟩ := WeightedGlobalSectionBound.eventual_supportBound (K := ℂ) (ι := Fin (m + 2))
    (Geo.ambExponents sc) (Geo.constantIndex sc) (Geo.ambExponents_constant sc)
    (Geo.coordinateIndex sc) (Geo.ambExponents_coordinate sc) (srcRho W) (sc.D : ℝ)
    (ambExponents_weight_srcRho_le sc)
  refine ⟨N, fun n hn e t => ?_⟩
  have h := hN n hn e t
  rw [Nat.cast_mul]
  exact h

section Frame

attribute [local irreducible] WeightedCompactification.lineBundle
  WeightedCompactification.affineChartMap AffineJetCoefficientInterface.Frame

theorem frame_exists_of_actual {X : Scheme} {R : Type} [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j] (A : LineBundle X)
    (h : Nonempty (A.sheaf.restrict j.opensRange.ι ≅ structureSheaf j.opensRange.toScheme)) :
    Nonempty (AffineJetCoefficientInterface.Frame j A) := by
  unfold AffineJetCoefficientInterface.Frame
  exact h

theorem monomialFrame_exists {R ι σ : Type} [CommRing R]
    (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    Nonempty (AffineJetCoefficientInterface.Frame
      (WeightedCompactification.affineChartMap (R := R) a z hz coordinate hcoordinate)
      (WeightedCompactification.lineBundle (R := R) a)) :=
  frame_exists_of_actual
    (X := Proj (WeightedCompactification.imageGrade (R := R) a))
    (R := MvPolynomial ι R)
    (WeightedCompactification.affineChartMap (R := R) a z hz coordinate hcoordinate)
    (WeightedCompactification.lineBundle (R := R) a)
    (WeightedAffineFrame.affineFrame_nonempty (R := R) a z hz coordinate hcoordinate)

end Frame

/-- The frame of `𝒪(1)` over the chart `𝔸^{m+2} → P` (the argument of the coefficient map). -/
theorem ambFrame_nonempty (sc : Geo.EpaScale W σ) :
    Nonempty (AffineJetCoefficientInterface.Frame (Geo.ambChart sc) (Geo.hyp sc)) :=
  monomialFrame_exists (R := ℂ) (Geo.ambExponents sc) (Geo.constantIndex sc)
    (Geo.ambExponents_constant sc) (Geo.coordinateIndex sc) (Geo.ambExponents_coordinate sc)

end Glue

end CatalanCore.Elliptic.EPA
