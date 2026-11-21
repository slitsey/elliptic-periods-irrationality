module

public import CatalanCore.Elliptic.EPA.Geo.Blowup
public import CatalanCore.Elliptic.EPA.Geo.Contact
public import CatalanCore.Elliptic.EPA.Geo.PlaceAlgebra
public import CatalanCore.Elliptic.EPA.Vanishing
public import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree
public import OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter
public import OAI.NumberTheory.PiExponent.Geometry.CurveContactSum
public import OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch
public import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel

/-!
# The exceptional degree along a curve (row E09.10c)

Labels refer to the proof design (§2 P3, §5 E09.10c, §A3, §A4) and to the OpenAI/Apache-2.0
file `Ampleness/ExceptionalCurveDegree.lean` (`centerMorphism_eq_centeredLift`,
`compactIdeal_comap_ne_bot_of_generic`, `compactIdeal_degree_eq_neg_contact_sum`), whose
log-specific tail is replaced here by the elliptic computation of `Geo/Contact.lean`.

Let `E` be a function field over `ℂ`, `f ∈ E` transcendental with `E` finite over `ℂ(f)`,
`g : parameterCurve f hf ⟶ Y` (`Y` the blow-up of `Geo/Blowup`) with generic point over the chart:
`generic ≫ g ≫ π = Spec(aeval z) ≫ ambChart` for `z = (u, t, Z) : Fin (m+2) → E`.

* `centerMorphism_eq_centeredLift` (row E09.10c′, §A3): the centre morphism of a place centred at
  `a` is `Spec (aeval (lift p z a)) ≫ j`.
* `centered_of_closedPoint_eq`: the analogue of OAI `JetCenterIdentification` (not vendored):
  a place whose centre point maps to `(0,0,c)` is centred at `(0,0,c)`.
* `ellLength p`: the length `ℓ_p` of `O_p / (I · O_p)` (`localIdeal` of the centre ideal).
* `ellLength_of_centred` (CM l.3563-3589, over `X`): `ℓ_p = D · μ_p`.
* `ellLength_ne_zero_imp`, `ellLength_le_coordinateOrder` (off `X`): `ℓ_p ≠ 0` only at centred
  places, where `ℓ_p ≤ ord_p f(z)`.
* `ell_exceptional_degree_over_X`: `deg 𝒥 = −D Σ_p μ_p` when `f(z) = 0`.
* `ell_exceptional_degree_off_X`: `−deg 𝒥 ≤ 8 w₀ d_C` when `f(z) ≠ 0` (design P3(i), §A4).
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

namespace Geo

open CatalanCore.Elliptic
open AlgebraicGeometry CategoryTheory TopologicalSpace
open OAI.PiExponent
open OAI.PiExponentSeshadri
open OAI.PiExponentSeshadri.Geometry
open CurveNormalizationModel CurveValuationCenter CurvePlaceCenter CurveCenters PlaceValuationRing

variable {m K : ℕ} {W : Weights m} {σ : ℚ} {ch : OriginChart}

/-- Row E09.10c′ (§A3): the centre morphism of a place centred at `a` is the morphism induced by
the lift of `z` to the valuation ring (OAI `centerMorphism_eq_centeredLift`, generic proof). -/
theorem centerMorphism_eq_centeredLift {E : Type} [Field E] [Algebra ℂ E] (f : E)
    (hf : Transcendental ℂ f) [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]
    {X : Scheme} [X.IsSeparated] (j : ambSpace m ⟶ X)
    (g : parameterCurve f hf ⟶ X) (z : Fin (m + 2) → E)
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (p : NormalizedPlace ℂ E) (a : Fin (m + 2) → ℂ) (hc : Centered z a p) :
    centerMorphism f hf p ≫ g =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.aeval (PlaceCenteredBranch.lift p z a hc)).toRingHom) ≫ j := by
  apply centerMorphism_comp_eq_of_generic f hf p g
  rw [hgeneric, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro P
  exact PlaceCenteredBranch.lift_aeval p z a hc P

/-! ### The local ideal of the centre ideal -/

section Local

variable (sc : EpaScale W σ) (s : OriginSeries ch) (c : Fin K → Fin m → ℂ)

theorem localIdeal_centreIdeal {V : Type} [CommRing V] (φ : AmbRing m →+* V) :
    ExceptionalCurveDegree.localIdeal (centreIdeal sc s c)
        (Spec.map (CommRingCat.ofHom φ) ≫ ambChart sc) = (centreIdealAff sc s c).map φ := by
  unfold ExceptionalCurveDegree.localIdeal
  rw [Scheme.IdealSheafData.comap_comp, centreIdeal_restrict]
  exact ExceptionalCurveDegree.localIdeal_specIdeal _ φ

/-- `𝓘` pulls back to a nonzero ideal along a curve with a transcendental coordinate (OAI
`compactIdeal_comap_ne_bot_of_generic`). -/
theorem centreIdeal_comap_ne_bot {E : Type} [Field E] [Algebra ℂ E] (f : E)
    (hf : Transcendental ℂ f) [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]
    (g' : parameterCurve f hf ⟶ ambX sc) (z : Fin (m + 2) → E) (hz : ∃ i, Transcendental ℂ (z i))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g' =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ ambChart sc) :
    (centreIdeal sc s c).comap g' ≠ ⊥ := by
  have htop : ExceptionalCurveDegree.localIdeal (centreIdeal sc s c)
      (parameterCurveGenericPoint f hf ≫ g') = ⊤ := by
    rw [hgeneric, localIdeal_centreIdeal, centreIdealAff_map_generic_eq_top]
    exact hz
  intro hzero
  have hb : ExceptionalCurveDegree.localIdeal (centreIdeal sc s c)
      (parameterCurveGenericPoint f hf ≫ g') = ⊥ := by
    simp only [ExceptionalCurveDegree.localIdeal, Scheme.IdealSheafData.comap_comp, hzero,
      Scheme.IdealSheafData.comap_bot]
    exact Ideal.map_bot
  exact bot_ne_top (hb.symm.trans htop)

end Local

/-! ### Lengths at the places of a curve -/

section Places

variable (sc : EpaScale W σ) (s : OriginSeries ch) (c : Fin K → Fin m → ℂ)
variable {E : Type} [Field E] [Algebra ℂ E] (f : E) (hf : Transcendental ℂ f)
  [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]
variable (g : parameterCurve f hf ⟶ blowup sc s c) (z : Fin (m + 2) → E)

/-- The length `ℓ_p = length (O_p / 𝓘 O_p)` at the place `p`. -/
noncomputable def ellLength (p : NormalizedPlace ℂ E) : ℕ :=
  (Module.length (ring p) ((ring p) ⧸ ExceptionalCurveDegree.localIdeal (centreIdeal sc s c)
    (centerMorphism f hf p ≫ g ≫ blowupProj sc s c))).toNat

variable {f hf g z}

/-- The hypothesis tying `g` to the coordinates `z` (generic point over the chart). -/
def GenericOver (g : parameterCurve f hf ⟶ blowup sc s c) (z : Fin (m + 2) → E) : Prop :=
  parameterCurveGenericPoint f hf ≫ g ≫ blowupProj sc s c =
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ ambChart sc

theorem localIdeal_at_place (hgen : GenericOver sc s c g z) (hcinj : Function.Injective c)
    (p : NormalizedPlace ℂ E) (k : Fin K) (hc : Centered z (ellCentre (c k)) p)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))] :
    ExceptionalCurveDegree.localIdeal (centreIdeal sc s c)
        (centerMorphism f hf p ≫ g ≫ blowupProj sc s c) =
      (centreIdealPt sc s (c k)).map
        (MvPolynomial.aeval (PlaceCenteredBranch.lift p z (ellCentre (c k)) hc) :
          AmbRing m →ₐ[ℂ] ring p).toRingHom := by
  have hq := centerMorphism_eq_centeredLift f hf (ambChart sc) (g ≫ blowupProj sc s c) z hgen
    p (ellCentre (c k)) hc
  rw [hq, localIdeal_centreIdeal]
  apply centreIdealAff_map_eq
  intro j hj
  exact centreIdealPt_map_eq_top sc s (isCentredAt_lift p z (c k) hc) (fun h => hj (hcinj h))

/-- CM l.3563-3589 (over `X`): `ℓ_p = D · μ_p` at a place centred at `c_k`. -/
theorem ellLength_of_centred (hgen : GenericOver sc s c g z) (hcinj : Function.Injective c)
    (hrel : IsEllBranch ch z) (hz : ∃ i, Transcendental ℂ (z i))
    (p : NormalizedPlace ℂ E) (k : Fin K) (hc : Centered z (ellCentre (c k)) p)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))] :
    (ellLength sc s c f hf g p : ℚ) =
      sc.D * ellContact s (c k) (PlaceCenteredBranch.lift p z (ellCentre (c k)) hc) (jetWt W) := by
  unfold ellLength
  rw [localIdeal_at_place sc s c hgen hcinj p k hc]
  exact centreIdealPt_length sc s (c k) (isEllBranch_lift p z (ellCentre (c k)) hc hrel)
    (isCentredAt_lift p z (c k) hc) (lift_nonconstant_ell p z (c k) hc hz)

/-- `ℓ_p ≠ 0` only at centred places (the centre avoids the support of `𝓘` elsewhere). -/
theorem ellLength_ne_zero_imp (hgen : GenericOver sc s c g z)
    (p : NormalizedPlace ℂ E) (hp : ellLength sc s c f hf g p ≠ 0) :
    ∃ k, Centered z (ellCentre (c k)) p := by
  by_contra hcon
  apply hp
  have havoid : (centerMorphism f hf p ≫ g ≫ blowupProj sc s c)
      (IsLocalRing.closedPoint (ring p)) ∉ (centreIdeal sc s c).support := by
    intro hmem
    change _ ∈ ((centreIdeal sc s c).support : Set (ambX sc)) at hmem
    rw [centreIdeal_support] at hmem
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hmem
    obtain ⟨a, ha⟩ := hk
    have hap : ambPoint (c k) a = cenPrime (c k) := by
      have h := Set.mem_range_self (f := ambPoint (c k)) a
      rw [range_ambPoint] at h
      exact h
    have hclosed : (centerMorphism f hf p ≫ g ≫ blowupProj sc s c)
        (IsLocalRing.closedPoint (ring p)) = ambChart sc (cenPrime (c k)) :=
      ha.symm.trans (congrArg (ambChart sc) hap)
    have hfield : Spec.map (CommRingCat.ofHom (algebraMap (ring p) E)) ≫
        (centerMorphism f hf p ≫ g ≫ blowupProj sc s c) =
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ ambChart sc := by
      rw [← Category.assoc, centerMorphism_generic]
      exact hgen
    exact hcon ⟨k, centered_of_closedPoint_eq p z (c k) (ambChart sc) _ hfield hclosed⟩
  unfold ellLength
  rw [ExceptionalCurveDegree.localIdeal_eq_top_of_not_mem _ _ havoid]
  simp

/-- Off `X`: at a place with `ℓ_p ≠ 0`, `ℓ_p ≤ ord_p f(z)` (`f ∈ I_c`; design P3(i), §A4). -/
theorem ellLength_le_coordinateOrder (hgen : GenericOver sc s c g z) (hcinj : Function.Injective c)
    (hres : ∀ p : NormalizedPlace ℂ E, Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hne : MvPolynomial.aeval z (relation (m := m) ch) ≠ 0)
    (p : NormalizedPlace ℂ E) (hp : ellLength sc s c f hf g p ≠ 0) :
    ((ellLength sc s c f hf g p : ℕ) : ℤ) ≤
      WeightedPolynomialPole.coordinateOrder p.valuation (MvPolynomial.aeval z (relation ch)) := by
  obtain ⟨k, hc⟩ := ellLength_ne_zero_imp sc s c hgen p hp
  letI := hres p
  have hx : MvPolynomial.aeval (PlaceCenteredBranch.lift p z (ellCentre (c k)) hc)
      (relation (m := m) ch) ∈
        (centreIdealPt sc s (c k)).map
          (MvPolynomial.aeval (PlaceCenteredBranch.lift p z (ellCentre (c k)) hc) :
            AmbRing m →ₐ[ℂ] ring p).toRingHom :=
    Ideal.mem_map_of_mem _ (relation_mem_centreIdealPt sc s (c k))
  have hx0 : MvPolynomial.aeval (PlaceCenteredBranch.lift p z (ellCentre (c k)) hc)
      (relation (m := m) ch) ≠ 0 := by
    intro h0
    apply hne
    rw [← PlaceCenteredBranch.lift_aeval p z (ellCentre (c k)) hc, h0, map_zero]
  have h1 := length_toNat_le_addVal hx hx0
  have h2 := PlaceCenteredBranch.coordinateOrder_aeval_eq_length p z (ellCentre (c k)) hc
    (relation ch) hne
  rw [CurveLocalOrder.length_quotient_span_eq_addVal hx0] at h2
  unfold ellLength
  rw [localIdeal_at_place sc s c hgen hcinj p k hc, h2]
  exact_mod_cast h1

/-- The degree `deg 𝒥 = χ(𝒥|_C) − χ(𝒪_C)` of the exceptional bundle on the normalised curve. -/
noncomputable def exceptionalDegree (g : parameterCurve f hf ⟶ blowup sc s c) : ℤ :=
  eulerCharacteristic (parameterCurveStructureMap f hf) 1 ((J sc s c).pullback g).sheaf -
    eulerCharacteristic (parameterCurveStructureMap f hf) 1 (structureSheaf (parameterCurve f hf))

theorem exceptionalDegree_eq_neg_sum (hgen : GenericOver sc s c g z)
    (hz : ∃ i, Transcendental ℂ (z i)) :
    ∃ hg : (centreIdeal sc s c).comap (g ≫ blowupProj sc s c) ≠ ⊥,
      exceptionalDegree sc s c g =
        -(ExceptionalCurveDegree.idealDivisor f hf (centreIdeal sc s c) (blowupProj sc s c)
          (J sc s c) (exceptionalInclusion sc s c) (exceptional_presents sc s c) g hg).sum
            (fun _ n => (n : ℤ)) := by
  have hg : (centreIdeal sc s c).comap (g ≫ blowupProj sc s c) ≠ ⊥ :=
    centreIdeal_comap_ne_bot sc s c f hf (g ≫ blowupProj sc s c) z hz hgen
  exact ⟨hg, ExceptionalCurveDegree.degree_eq_neg_idealDivisor_sum f hf (centreIdeal sc s c)
    (blowupProj sc s c) (J sc s c) (exceptionalInclusion sc s c) (exceptional_presents sc s c)
    g hg⟩

/-- Over `X = {f = 0}`: `deg 𝒥 = −D Σ_p μ_p` (CM l.3563-3589; replaces OAI
`compactIdeal_degree_eq_neg_contact_sum`). -/
theorem ell_exceptional_degree_over_X (hgen : GenericOver sc s c g z)
    (hcinj : Function.Injective c)
    (hres : ∀ p : NormalizedPlace ℂ E, Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ q : E, Transcendental ℂ q → FiniteDimensional (IntermediateField.adjoin ℂ {q}) E)
    (hz : ∃ i, Transcendental ℂ (z i)) (hrel : IsEllBranch ch z) :
    ((exceptionalDegree sc s c g : ℤ) : ℚ) =
      -(sc.D : ℚ) * ∑ p ∈ ellPlaces hfinite z c hz,
        ellPlaceContact hres hfinite s z c hz (jetWt W) p := by
  classical
  obtain ⟨hg, hd⟩ := exceptionalDegree_eq_neg_sum sc s c hgen hz
  let Dv := ExceptionalCurveDegree.idealDivisor f hf (centreIdeal sc s c) (blowupProj sc s c)
    (J sc s c) (exceptionalInclusion sc s c) (exceptional_presents sc s c) g hg
  let P := ellPlaces hfinite z c hz
  have hDv : ∀ p, Dv p = ellLength sc s c f hf g p := fun p =>
    ExceptionalCurveDegree.idealDivisor_apply f hf (centreIdeal sc s c) (blowupProj sc s c)
      (J sc s c) (exceptionalInclusion sc s c) (exceptional_presents sc s c) g hg p
  have hzero : ∀ p, p ∉ P → Dv p = 0 := by
    intro p hp
    rw [hDv]
    by_contra hne
    obtain ⟨k, hk⟩ := ellLength_ne_zero_imp sc s c hgen p hne
    exact hp ((mem_ellPlaces hfinite z c hz p).mpr ⟨k, hk⟩)
  have hsupport : Dv.support ⊆ P := by
    intro p hp
    by_contra h
    exact (Finsupp.mem_support_iff.mp hp) (hzero p h)
  have hvalue : ∀ p ∈ P, (Dv p : ℚ) =
      sc.D * ellPlaceContact hres hfinite s z c hz (jetWt W) p := by
    intro p hp
    letI := hres p
    have hc := ellCentered hfinite z c hz p hp
    have h := ellLength_of_centred sc s c hgen hcinj hrel hz p
      (ellCenter hfinite z c hz p hp) hc
    have h2 : ellPlaceContact hres hfinite s z c hz (jetWt W) p =
        ellContact s (c (ellCenter hfinite z c hz p hp))
          (PlaceCenteredBranch.lift p z (ellCentre (c (ellCenter hfinite z c hz p hp))) hc)
          (jetWt W) := ellPlaceContact_of_mem hres hfinite s z c hz (jetWt W) p hp
    rw [h2, hDv]
    exact h
  have hsum : Dv.sum (fun _ n => (n : ℚ)) =
      sc.D * ∑ p ∈ P, ellPlaceContact hres hfinite s z c hz (jetWt W) p := by
    rw [Dv.sum_of_support_subset hsupport (fun _ n => (n : ℚ)) (by simp)]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p hp => hvalue p hp)
  have hdq : ((exceptionalDegree sc s c g : ℤ) : ℚ) = -Dv.sum (fun _ n => (n : ℚ)) := by
    simpa only [Int.cast_neg, Finsupp.sum, Int.cast_sum, Int.cast_natCast] using
      congrArg (fun a : ℤ => (a : ℚ)) hd
  rw [hsum] at hdq
  simpa only [neg_mul] using hdq

/-- Off `X` (`f(z) ≠ 0`): `−deg 𝒥 ≤ 8 w₀ · d_C`, `d_C` the weighted pole degree of `z`
(design P3(i) via `polynomial_contact_sum_le`, §A4). -/
theorem ell_exceptional_degree_off_X (hgen : GenericOver sc s c g z)
    (hcinj : Function.Injective c)
    (hres : ∀ p : NormalizedPlace ℂ E, Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ q : E, Transcendental ℂ q → FiniteDimensional (IntermediateField.adjoin ℂ {q}) E)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hne : MvPolynomial.aeval z (relation (m := m) ch) ≠ 0) :
    -((exceptionalDegree sc s c g : ℤ) : ℝ) ≤
      8 * (W.w₀ : ℝ) * CurveContactSum.weightedDegree hfinite z (srcWt W) := by
  classical
  obtain ⟨hg, hd⟩ := exceptionalDegree_eq_neg_sum sc s c hgen hz
  let Dv := ExceptionalCurveDegree.idealDivisor f hf (centreIdeal sc s c) (blowupProj sc s c)
    (J sc s c) (exceptionalInclusion sc s c) (exceptional_presents sc s c) g hg
  have hDv : ∀ p, Dv p = ellLength sc s c f hf g p := fun p =>
    ExceptionalCurveDegree.idealDivisor_apply f hf (centreIdeal sc s c) (blowupProj sc s c)
      (J sc s c) (exceptionalInclusion sc s c) (exceptional_presents sc s c) g hg p
  have hw0 : (0 : ℝ) < W.w₀ := by exact_mod_cast W.w₀_pos
  have hle := CurveContactSum.polynomial_contact_sum_le hfinite z (srcWt W) (srcWt_pos W)
    (8 * (W.w₀ : ℝ)) 1 (by linarith) (relation ch) (relation_srcDeg_le W ch) hne Dv.support
    (fun p => (Dv p : ℝ)) (by
      intro p hp
      have hp' : ellLength sc s c f hf g p ≠ 0 := by
        rw [← hDv]; exact (Finsupp.mem_support_iff.mp hp)
      have h := ellLength_le_coordinateOrder sc s c hgen hcinj hres hne p hp'
      rw [one_mul, hDv]
      exact_mod_cast h)
  have hdr : ((exceptionalDegree sc s c g : ℤ) : ℝ) = -∑ p ∈ Dv.support, (Dv p : ℝ) := by
    simpa only [Int.cast_neg, Finsupp.sum, Int.cast_sum, Int.cast_natCast] using
      congrArg (fun a : ℤ => (a : ℝ)) hd
  rw [hdr, neg_neg]
  simpa using hle

end Places

end Geo

end CatalanCore.Elliptic.EPA
