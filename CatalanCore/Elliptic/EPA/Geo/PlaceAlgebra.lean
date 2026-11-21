module

public import CatalanCore.Elliptic.EPA.Geo.Contact
public import CatalanCore.Elliptic.EPA.Vanishing
public import OAI.NumberTheory.PiExponent.Geometry.CurveCenters
public import OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch
public import OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter
public import OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing

/-!
# Place-level algebra for the exceptional degree (row E09.10c)

Algebraic ingredients of `Geo/ExceptionalDegree.lean` that need only built OAI modules:

* `centered_of_closedPoint_eq`: analogue of OAI `JetCenterIdentification.centered_of_closedPoint_eq`
  (not vendored) for the ambient chart: if the closed point of `Spec (ring p)` maps to the centre
  point `(0, 0, c)`, then `p` is centred at `(0, 0, c)`.
* `aeval_relation_eq_zero_iff`: `f(z) = 0 ↔ t² = F(u)`.
* `centreIdealAff_map_eq`: along a map into a ring where the other centre ideals become `⊤`, the
  product `J = ∏_j I_{c_j}` has image `I_{c_k}`.
* `centreIdealPt_map_generic_eq_top`, `centreIdealAff_map_generic_eq_top`: at a generic point
  (some coordinate transcendental over `ℂ`) the centre ideal becomes `⊤`.

(OpenAI/Apache-2.0 template: `Jets/JetCenterIdentification.lean`, `Ampleness/ExceptionalCurveDegree`
`map_powerIdeal_eq_top_of_transcendental`.)
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

namespace Geo

open CatalanCore.Elliptic
open AlgebraicGeometry CategoryTheory TopologicalSpace
open OAI.PiExponent
open CurveValuationCenter CurveCenters PlaceValuationRing

variable {m K : ℕ} {W : Weights m} {σ : ℚ} {ch : OriginChart}

theorem ellCentre_eq_cenPt (c₀ : Fin m → ℂ) : ellCentre c₀ = cenPt c₀ := rfl

theorem aeval_relation_eq_zero_iff {B : Type*} [CommRing B] [Algebra ℂ B] (z : Fin (m + 2) → B) :
    MvPolynomial.aeval z (relation (m := m) ch) = 0 ↔ IsEllBranch ch z := by
  have hu : MvPolynomial.aeval z (uV : AmbRing m) = z 0 := by simp [uV]
  have ht : MvPolynomial.aeval z (tV : AmbRing m) = z 1 := by simp [tV]
  unfold relation IsEllBranch
  rw [map_sub, map_pow, ← Polynomial.aeval_algHom_apply, hu, ht, sub_eq_zero]

/-! ### Identification of centres -/

/-- Analogue of OAI `JetCenterIdentification.centered_of_closedPoint_eq` for the ambient chart. -/
theorem centered_of_closedPoint_eq {E : Type} [Field E] [Algebra ℂ E] (p : NormalizedPlace ℂ E)
    (z : Fin (m + 2) → E) (c₀ : Fin m → ℂ)
    {X : Scheme} (j : ambSpace m ⟶ X) [IsOpenImmersion j]
    (q : Spec (CommRingCat.of (ring p)) ⟶ X)
    (hgeneric : Spec.map (CommRingCat.ofHom (algebraMap (ring p) E)) ≫ q =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (hclosed : q (IsLocalRing.closedPoint (ring p)) = j (cenPrime c₀)) :
    Centered z (ellCentre c₀) p := by
  have hr : Set.range q ⊆ Set.range j := by
    rintro _ ⟨y, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint y).map q.continuous).mem_open
      j.isOpenEmbedding.isOpen_range (hclosed ▸ Set.mem_range_self (cenPrime c₀))
  let g := IsOpenImmersion.lift j q hr
  have hg : g ≫ j = q := IsOpenImmersion.lift_fac j q hr
  let φ : AmbRing m →+* ring p := (Spec.preimage g).hom
  have hgφ : Spec.map (CommRingCat.ofHom φ) = g := Spec.map_preimage g
  have hcomp : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap (ring p) E) =
      CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, hgφ]
    apply (cancel_mono j).mp
    rw [Category.assoc, hg]
    exact hgeneric
  have hgc : g (IsLocalRing.closedPoint (ring p)) = cenPrime c₀ := by
    apply j.isOpenEmbedding.injective
    change (g ≫ j) (IsLocalRing.closedPoint (ring p)) = _
    rw [hg, hclosed]
  have hcomap : PrimeSpectrum.comap φ (IsLocalRing.closedPoint (ring p)) = cenPrime c₀ := by
    change (Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint (ring p)) = _
    rw [hgφ, hgc]
  intro i
  let P : AmbRing m := MvPolynomial.X i - MvPolynomial.C (cenPt c₀ i)
  have hmem : φ P ∈ IsLocalRing.maximalIdeal (ring p) := by
    change P ∈ (PrimeSpectrum.comap φ (IsLocalRing.closedPoint (ring p))).asIdeal
    rw [hcomap]
    change P ∈ WeightedBezout.pointIdeal (cenPt c₀)
    rw [WeightedBezout.mem_pointIdeal]
    simp [P]
  have hpos := p.valuation.toValuation.mem_maximalIdeal_iff.mp hmem
  have heval := congrArg
    (fun f : CommRingCat.of (AmbRing m) ⟶ CommRingCat.of E => f P) hcomp
  change algebraMap (ring p) E (φ P) = MvPolynomial.aeval z P at heval
  change 0 < p.valuation (algebraMap (ring p) E (φ P)) at hpos
  rw [heval] at hpos
  simpa [P, ellCentre_eq_cenPt] using hpos

section Local

variable (sc : EpaScale W σ) (s : OriginSeries ch) (c : Fin K → Fin m → ℂ)

theorem centreIdealAff_map_eq {V : Type} [CommRing V] (φ : AmbRing m →+* V) (k : Fin K)
    (hother : ∀ j, j ≠ k → (centreIdealPt sc s (c j)).map φ = ⊤) :
    (centreIdealAff sc s c).map φ = (centreIdealPt sc s (c k)).map φ := by
  unfold centreIdealAff
  have h := map_prod (Ideal.mapHom φ) (fun j => centreIdealPt sc s (c j)) Finset.univ
  simp only [Ideal.mapHom_apply] at h
  rw [h, Finset.prod_eq_single k]
  · intro j _ hj
    rw [hother j hj, Ideal.one_eq_top]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- At a generic point (some coordinate transcendental), `I_{c₀} · E = E`. -/
theorem centreIdealPt_map_generic_eq_top {E : Type} [Field E] [Algebra ℂ E] (c₀ : Fin m → ℂ)
    (z : Fin (m + 2) → E) (hz : ∃ i, Transcendental ℂ (z i)) :
    (centreIdealPt sc s c₀).map (MvPolynomial.aeval z : AmbRing m →ₐ[ℂ] E).toRingHom = ⊤ := by
  by_contra hne
  have hzero : ∀ g ∈ centreGens sc s c₀, MvPolynomial.aeval z g = 0 := by
    intro g hg
    by_contra h0
    apply hne
    apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (Ideal.subset_span hg))
    exact isUnit_iff_ne_zero.mpr h0
  have hz1 : z 1 = 0 := by
    have h := hzero (genElt sc s c₀ 0) (genElt_mem sc s c₀ 0)
    have h1 : MvPolynomial.aeval z (genElt sc s c₀ 0) = (z 1) ^ sc.a := by
      show MvPolynomial.aeval z (tV ^ sc.a) = _
      simp [tV]
    rw [h1] at h
    exact (pow_eq_zero_iff sc.a_pos.ne').mp h
  have hz0 : z 0 = 0 := by
    have h := hzero (uV ^ sc.a) (Or.inl (by simp))
    have h1 : MvPolynomial.aeval z (uV ^ sc.a : AmbRing m) = (z 0) ^ sc.a := by simp [uV]
    rw [h1] at h
    exact (pow_eq_zero_iff sc.a_pos.ne').mp h
  have htr : MvPolynomial.aeval z (truncL s sc.T₀) = 0 := by
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp (truncL_mem_span_tV (m := m) s sc.T₀)
    have ht : MvPolynomial.aeval z (tV : AmbRing m) = z 1 := by simp [tV]
    rw [hr, map_mul, ht, hz1, zero_mul]
  have hall : ∀ i, z i = algebraMap ℂ E (ellCentre c₀ i) := by
    refine forall_amb ?_ ?_ ?_
    · rw [ellCentre_zero, map_zero, hz0]
    · rw [ellCentre_one, map_zero, hz1]
    · intro i
      have h := hzero (genElt sc s c₀ i.succ) (genElt_mem sc s c₀ i.succ)
      have h1 : MvPolynomial.aeval z (genElt sc s c₀ i.succ) =
          (z i.succ.succ - algebraMap ℂ E (c₀ i) - MvPolynomial.aeval z (truncL s sc.T₀)) ^
            sc.b i := by
        show MvPolynomial.aeval z ((zV i - MvPolynomial.C (c₀ i) - truncL s sc.T₀) ^ sc.b i) = _
        simp [zV]
      rw [h1, htr, sub_zero] at h
      have h2 := (pow_eq_zero_iff (sc.b_pos i).ne').mp h
      rw [ellCentre_succ_succ]
      exact sub_eq_zero.mp h2
  obtain ⟨i, hi⟩ := hz
  exact hi (hall i ▸ isAlgebraic_algebraMap (ellCentre c₀ i))

theorem centreIdealAff_map_generic_eq_top {E : Type} [Field E] [Algebra ℂ E]
    (z : Fin (m + 2) → E) (hz : ∃ i, Transcendental ℂ (z i)) :
    (centreIdealAff sc s c).map (MvPolynomial.aeval z : AmbRing m →ₐ[ℂ] E).toRingHom = ⊤ := by
  unfold centreIdealAff
  have h := map_prod (Ideal.mapHom (MvPolynomial.aeval z : AmbRing m →ₐ[ℂ] E).toRingHom)
    (fun j => centreIdealPt sc s (c j)) Finset.univ
  simp only [Ideal.mapHom_apply] at h
  rw [h]
  rw [Finset.prod_eq_one]
  · exact Ideal.one_eq_top
  · intro j _
    rw [centreIdealPt_map_generic_eq_top sc s (c j) z hz, Ideal.one_eq_top]


end Local

end Geo

end CatalanCore.Elliptic.EPA
