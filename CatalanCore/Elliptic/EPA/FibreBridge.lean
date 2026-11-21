module

public import CatalanCore.Elliptic.EPA.Vanishing
public import CatalanCore.Elliptic.EPA.Numerics
public import OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily
public import OAI.NumberTheory.PiExponent.Geometry.CurveFieldRigidity
public import OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch
public import OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact
public import OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Ideal.Height

/-!
# The fibre bridge (row E09.9, part 1)

Labels refer to the proof design §5 E09.9 and to CM (arXiv 2610.31112) §11-§12
(arXiv 2610.31112 l.2756-3014, 3246-3290).

When the curve lies in the origin fibre `u = t = 0` (E09.8), the elliptic data `(u, t, Z)` is the
point `ellPad x = (0, 0, x)` with `x = (Z₁, …, Z_m)`, and the elliptic contact data is exactly the
ordinary-fibre data of OAI `CurveContactFamily`: the places centred at `(0, 0, c_j)` are the places
centred at `(1, c_j)` of `fibre x = (1, x)`, the contact `μ_p` is the ordinary contact of `x` at
`c_j` for the weights `v_{i+1}`, and the weighted degree of `(0, 0, x)` for `srcWt` is the weighted
degree of `fibre x` for `radWt` (constants have no poles). This file proves these identifications
and the numerical hypotheses of the OAI ordinary-fibre theorems
`CurveInequality.excess_implies_fibre_coordinate_constant` and
`CurveInequality.no_fibre_excess_of_constant_coordinate` (used in `CurveInequality.lean`):

* `An_eq_comparisonConstant`: `A_m(σ)` is the OAI `comparisonConstant` (design coordinator note).
* `coordinateKernel_height_le`: `ht(ker (ℂ[Z] → E)) ≤ m`.
* `ellPad`, `exists_ellPad`, `centered_ellPad`, `ellPlaces_ellPad`: places.
* `ellPlaceContact_ellPad`: contact; `weightedDegree_ellPad_srcWt`: degree.
* `fibre_vol`, `fibre_separated`, `fibre_ratio`: the hypotheses `hvol`, `hseparated`, `hratio`.

OAI sources (openai/math fd4aeeb2, Apache License 2.0, Copyright OpenAI): `Geometry/CurveInequality`,
`Geometry/CurveContactFamily`, `LocalAlgebra/FibreContact` (the zero-coordinate lemmas are used as
they are).
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

open CatalanCore.Elliptic OAI.PiExponent CurveValuationCenter CurveCenters PlaceValuationRing

variable {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ} {ch : OriginChart}

/-! ### The comparison constant -/

/-- `A_m(σ)` (E09.0) is OAI `PersistentWeightComparison.comparisonConstant m σ`. -/
theorem An_eq_comparisonConstant (m : ℕ) (σ : ℚ) :
    ((An m σ : ℚ) : ℝ) = PersistentWeightComparison.comparisonConstant m (σ : ℝ) := by
  unfold An PersistentWeightComparison.comparisonConstant
  push_cast <;> ring

theorem An_le_C4 (W : Weights m) {σ : ℚ} (hσ : 0 < σ) : An m σ ≤ C4 W σ := by
  have h := An_pos (m + 1) (eps0_pos W hσ)
  have h2 : (0 : ℚ) < 4 * 2 ^ (m + 3) * An (m + 1) (eps0 W σ) := mul_pos (by positivity) h
  unfold C4
  linarith

/-! ### The height of the coordinate kernel -/

/-- The kernel of `ℂ[Z₁, …, Z_m] → E` has height `≤ m = dim ℂ[Z]`. -/
theorem coordinateKernel_height_le (x : Fin m → E) :
    (CurveFieldRigidity.coordinateKernel x).height ≤ (m : ℕ∞) := by
  haveI := CurveFieldRigidity.coordinateKernel_isPrime x
  have h2 : ((CurveFieldRigidity.coordinateKernel x).height : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin m) ℂ) :=
    Ideal.height_le_ringKrullDim_of_isPrime
  have h3 : ringKrullDim (MvPolynomial (Fin m) ℂ) = ((m : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    simp
  rw [h3] at h2
  exact WithBot.coe_le_coe.mp (h2.trans (le_of_eq (by first | rfl | simp | norm_cast)))

/-! ### The padded point `(0, 0, x)` -/

/-- `(0, 0, x)`: the point of the origin fibre of the ambient space with fibre coordinates `x`. -/
def ellPad {α : Type*} [Zero α] (x : Fin m → α) : Fin (m + 2) → α :=
  Fin.cases (motive := fun _ => α) 0 (Fin.cases (motive := fun _ => α) 0 x)

theorem ellCentre_eq_ellPad (c : Fin m → ℂ) : ellCentre c = ellPad c := rfl

@[simp] theorem ellPad_zero {α : Type*} [Zero α] (x : Fin m → α) : ellPad x 0 = 0 := rfl

theorem ellPad_one {α : Type*} [Zero α] (x : Fin m → α) : ellPad x 1 = 0 := by
  rw [one_eq_succ_zero]; rfl

@[simp] theorem ellPad_succ_succ {α : Type*} [Zero α] (x : Fin m → α) (i : Fin m) :
    ellPad x i.succ.succ = x i := rfl

/-- A point of the origin fibre `u = t = 0` is a padded point. -/
theorem exists_ellPad (z : Fin (m + 2) → E) (h0 : z 0 = 0) (h1 : z 1 = 0) :
    ∃ x : Fin m → E, z = ellPad x := by
  refine ⟨fun i => z i.succ.succ, ?_⟩
  funext j
  revert j
  refine forall_amb ?_ ?_ ?_
  · rw [ellPad_zero]; exact h0
  · rw [ellPad_one]; exact h1
  · intro i; rfl

theorem exists_transcendental_of_ellPad {x : Fin m → E}
    (hz : ∃ i, Transcendental ℂ (ellPad x i)) : ∃ i, Transcendental ℂ (x i) := by
  obtain ⟨i, hi⟩ := hz
  induction i using Fin.cases with
  | zero =>
    have h : ellPad x 0 = 0 := rfl
    rw [h] at hi
    exact (hi isAlgebraic_zero).elim
  | succ j =>
    induction j using Fin.cases with
    | zero =>
      have h : ellPad x (Fin.succ 0) = 0 := rfl
      rw [h] at hi
      exact (hi isAlgebraic_zero).elim
    | succ i => exact ⟨i, hi⟩

theorem transcendental_fibre {x : Fin m → E} (hx : ∃ i, Transcendental ℂ (x i)) :
    ∃ i, Transcendental ℂ (CurveContactFamily.fibre x i) := by
  obtain ⟨i, hi⟩ := hx
  exact ⟨i.succ, hi⟩

/-! ### Centred places -/

theorem centered_ellPad {x : Fin m → E} {c : Fin m → ℂ} {p : NormalizedPlace ℂ E}
    (h : Centered x c p) : Centered (ellPad x) (ellCentre c) p := by
  intro i
  revert i
  refine forall_amb ?_ ?_ ?_
  · have h0 : ellPad x 0 - algebraMap ℂ E (ellCentre c 0) = 0 := by
      rw [ellPad_zero, ellCentre_zero, map_zero, sub_zero]
    rw [h0, AddValuation.map_zero]
    first | exact WithTop.coe_lt_top (0 : ℤ) | simp
  · have h1 : ellPad x 1 - algebraMap ℂ E (ellCentre c 1) = 0 := by
      rw [ellPad_one, ellCentre_one, map_zero, sub_zero]
    rw [h1, AddValuation.map_zero]
    first | exact WithTop.coe_lt_top (0 : ℤ) | simp
  · intro i
    exact h i

theorem centered_of_ellPad {x : Fin m → E} {c : Fin m → ℂ} {p : NormalizedPlace ℂ E}
    (h : Centered (ellPad x) (ellCentre c) p) : Centered x c p :=
  fun i => h i.succ.succ

theorem centered_fibre {x : Fin m → E} {c : Fin m → ℂ} {p : NormalizedPlace ℂ E}
    (h : Centered x c p) :
    Centered (CurveContactFamily.fibre x) (CurveContactFamily.fullCenter c) p := by
  intro i
  induction i using Fin.cases with
  | zero =>
    have h0 : CurveContactFamily.fibre x 0 -
        algebraMap ℂ E (CurveContactFamily.fullCenter c 0) = 0 := by
      rw [CurveContactFamily.fibre_zero, CurveContactFamily.fullCenter_zero, map_one, sub_self]
    rw [h0, AddValuation.map_zero]
    first | exact WithTop.coe_lt_top (0 : ℤ) | simp
  | succ i => exact h i

theorem centered_of_fibre {x : Fin m → E} {c : Fin m → ℂ} {p : NormalizedPlace ℂ E}
    (h : Centered (CurveContactFamily.fibre x) (CurveContactFamily.fullCenter c) p) :
    Centered x c p :=
  fun i => h i.succ

/-- The elliptic centred places of `(0, 0, x)` are the OAI centred places of `fibre x`. -/
theorem ellPlaces_ellPad
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin m → E) (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (ellPad x i))
    (hz' : ∃ i, Transcendental ℂ (CurveContactFamily.fibre x i)) :
    ellPlaces hfinite (ellPad x) c hz =
      CurveContactFamily.places hfinite (CurveContactFamily.fibre x) c hz' := by
  ext p
  rw [mem_ellPlaces, CurveContactFamily.mem_places]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, centered_fibre (centered_of_ellPad hj)⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, centered_ellPad (centered_of_fibre hj)⟩

/-! ### The contact -/

section Contact

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra ℂ A]
  [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

/-- If `t = 0` the elliptic branch coordinates are `(0, Z_i − c_i)`: `L(0) = 0`. -/
theorem ellExpCoords_eq_cases (s : OriginSeries ch) (c : Fin m → ℂ) (a : Fin (m + 2) → A)
    (h1 : a 1 = 0) :
    ellExpCoords s c a = Fin.cases (motive := fun _ => PowerSeries ℂ) 0
      (OrdinaryDVRBranchJet.coordinates c (fun i => a i.succ.succ)) := by
  funext i
  induction i using Fin.cases with
  | zero =>
    show ellExpCoords s c a 0 = 0
    rw [ellExpCoords_zero, h1, map_zero]
  | succ i =>
    show ellExpCoords s c a i.succ =
      DVRBranch.expansion ℂ A (a i.succ.succ) - PowerSeries.C (c i)
    rw [ellExpCoords_succ, h1, map_zero,
      PowerSeries.subst_zero_of_constantCoeff_zero (constantCoeff_Ls s), sub_zero]

/-- The elliptic contact of a branch with `t = 0` is the ordinary contact of `(Z_i)` for the
weights `v_{i+1}`. -/
theorem ellContact_eq_ordinary (s : OriginSeries ch) (c : Fin m → ℂ) (a : Fin (m + 2) → A)
    (h1 : a 1 = 0) (v : Fin (m + 1) → ℚ) (hnc : ∃ i, a i.succ.succ ≠ algebraMap ℂ A (c i)) :
    ellContact s c a v =
      OrdinaryDVRBranchJet.contact (fun i => v i.succ) c (fun i => a i.succ.succ) hnc := by
  have hne := OrdinaryDVRBranchJet.coordinates_nonzero c (fun i => a i.succ.succ) hnc
  have hfull' : ∃ i, (Fin.cases (motive := fun _ => PowerSeries ℂ) 0
      (OrdinaryDVRBranchJet.coordinates c (fun i => a i.succ.succ)) :
        Fin (m + 1) → PowerSeries ℂ) i ≠ 0 := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i.succ, hi⟩
  have hfull : ∃ i, ellExpCoords s c a i ≠ 0 := by
    rw [ellExpCoords_eq_cases s c a h1]; exact hfull'
  rw [ellContact_eq_contact v hfull]
  have hcongr : ∀ {b d : Fin (m + 1) → PowerSeries ℂ} (he : b = d) (hb : ∃ i, b i ≠ 0)
      (hd : ∃ i, d i ≠ 0), BranchContact.contact v b hb = BranchContact.contact v d hd := by
    intro b d he hb hd
    subst he
    rfl
  exact (hcongr (ellExpCoords_eq_cases s c a h1) hfull hfull').trans
    (FibreContact.contact_zero_cons v _ hne hfull')

end Contact

theorem ellContact_lift_eq_ordinaryContact (s : OriginSeries ch) (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]
    (x : Fin m → E) (c : Fin m → ℂ) (hc : Centered (ellPad x) (ellCentre c) p)
    (hnc : ∃ i, x i ≠ algebraMap ℂ E (c i)) (v : Fin (m + 1) → ℚ) :
    ellContact s c (PlaceCenteredBranch.lift p (ellPad x) (ellCentre c) hc) v =
      PlaceCenteredBranch.ordinaryContact p x c (centered_of_ellPad hc) hnc
        (fun i => v i.succ) := by
  have h1 : PlaceCenteredBranch.lift p (ellPad x) (ellCentre c) hc 1 = 0 := by
    apply Subtype.ext
    rw [PlaceCenteredBranch.lift_coe, ellPad_one]
    try rfl
  have hnc' := PlaceCenteredBranch.lift_nonconstant p x c (centered_of_ellPad hc) hnc
  exact ellContact_eq_ordinary s c _ h1 v hnc'

theorem ordinaryContact_congr (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))] {n : ℕ} (z : Fin n → E)
    {c c' : Fin n → ℂ} (h : c = c') (hc : Centered z c p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (c i)) (hc' : Centered z c' p)
    (hnc' : ∃ i, z i ≠ algebraMap ℂ E (c' i)) (v : Fin n → ℚ) :
    PlaceCenteredBranch.ordinaryContact p z c hc hnc v =
      PlaceCenteredBranch.ordinaryContact p z c' hc' hnc' v := by
  subst h
  rfl

/-- The elliptic contact at a centred place of `(0, 0, x)` is the OAI contact of `fibre x`. -/
theorem ellPlaceContact_ellPad
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (s : OriginSeries ch) (x : Fin m → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (ellPad x i))
    (hz' : ∃ i, Transcendental ℂ (CurveContactFamily.fibre x i))
    (v : Fin (m + 1) → ℚ) (p : NormalizedPlace ℂ E)
    (hp : p ∈ ellPlaces hfinite (ellPad x) c hz) :
    ellPlaceContact hres hfinite s (ellPad x) c hz v p =
      CurveContactFamily.contact hres hfinite (CurveContactFamily.fibre x) c hz' v p := by
  letI := hres p
  have hp' : p ∈ CurveContactFamily.places hfinite (CurveContactFamily.fibre x) c hz' := by
    rwa [← ellPlaces_ellPad hfinite x c hz hz']
  rw [ellPlaceContact_of_mem hres hfinite s (ellPad x) c hz v p hp,
    CurveContactFamily.contact_one hres hfinite x c hz' v p hp']
  have hx := exists_transcendental_of_ellPad hz
  have hc1 := ellCentered hfinite (ellPad x) c hz p hp
  have hc1' := centered_of_ellPad hc1
  have hc2 : Centered x
      (c (CurveContactFamily.center hfinite (CurveContactFamily.fibre x) c hz' p hp')) p :=
    fun i => CurveContactFamily.centered hfinite (CurveContactFamily.fibre x) c hz' p hp' i.succ
  have hcc := hc1'.center_eq hc2
  have key := ellContact_lift_eq_ordinaryContact s p x
    (c (ellCenter hfinite (ellPad x) c hz p hp)) hc1
    (Centered.exists_nonzero_difference x _ hx) v
  refine key.trans ?_
  exact ordinaryContact_congr p x hcc _ _ _ _ _

/-! ### The weighted degree -/

theorem coordinatePole_ellPad (val : AddValuation E (WithTop ℤ)) (w : Fin (m + 2) → ℚ)
    (x : Fin m → E) :
    WeightedPolynomialPole.coordinatePole val (ellPad x) w =
      WeightedPolynomialPole.coordinatePole val x (fun i => w i.succ.succ) := by
  have hz0 : WeightedPolynomialPole.coordinateOrder val (0 : E) = 0 := by
    simp [WeightedPolynomialPole.coordinateOrder]
  have he : (fun i : Fin (m + 2) =>
      (WeightedPolynomialPole.coordinateOrder val (ellPad x i) : ℚ)) =
      ellPad (fun i : Fin m => (WeightedPolynomialPole.coordinateOrder val (x i) : ℚ)) := by
    funext i
    revert i
    refine forall_amb ?_ ?_ ?_
    · simp [ellPad_zero, hz0]
    · simp [ellPad_one, hz0]
    · intro i; rfl
  unfold WeightedPolynomialPole.coordinatePole
  rw [he]
  exact (FibreContact.weightedPole_zero_cons w _).trans
    (FibreContact.weightedPole_zero_cons (fun i => w i.succ) _)

theorem weightedDegree_ellPad
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (w : Fin (m + 2) → ℚ) (x : Fin m → E) :
    CurveContactSum.weightedDegree hfinite (ellPad x) w =
      CurveContactSum.weightedDegree hfinite x (fun i => w i.succ.succ) := by
  have he : CurveContactSum.weightedPoleDivisor hfinite (ellPad x) w =
      CurveContactSum.weightedPoleDivisor hfinite x (fun i => w i.succ.succ) := by
    ext p
    exact coordinatePole_ellPad p.valuation w x
  unfold CurveContactSum.weightedDegree
  rw [he]

/-- The source weighted degree of `(0, 0, x)` is the OAI weighted degree of `fibre x` for the radius
weights `(w₀, w₁, …, w_m)`. -/
theorem weightedDegree_ellPad_srcWt
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (W : Weights m) (x : Fin m → E) :
    CurveContactSum.weightedDegree hfinite (ellPad x) (srcWt W) =
      CurveContactSum.weightedDegree hfinite (CurveContactFamily.fibre x) (radWt W) := by
  exact (weightedDegree_ellPad hfinite (srcWt W) x).trans
    (FibreContact.weightedDegree_one hfinite (radWt W) x).symm

/-! ### The numerical hypotheses of the OAI ordinary-fibre theorems -/

theorem fb_radWt_pos (W : Weights m) (j : Fin (m + 1)) : 0 < radWt W j := by
  induction j using Fin.cases with
  | zero => exact W.w₀_pos
  | succ i => exact W.w_pos i

theorem fb_jetWt_pos (W : Weights m) (j : Fin (m + 1)) : 0 < jetWt W j := by
  induction j using Fin.cases with
  | zero => exact W.v₀_pos
  | succ i => exact div_pos (W.w_pos i) W.θ_pos

/-- `hvol` of OAI `excess_implies_fibre_coordinate_constant`, from `EpaSigma.h₂`. -/
theorem fibre_vol (W : Weights m) {σ : ℚ} (hσ : EpaSigma m K W σ) :
    (K : ℝ) * (1 + 3 * (σ : ℝ)) ^ m * (∏ i : Fin m, ((radWt W i.succ : ℚ) : ℝ)) /
      (∏ i : Fin m, ((jetWt W i.succ : ℚ) : ℝ)) < 1 := by
  have hθ : (0 : ℝ) < (W.θ : ℝ) := by exact_mod_cast W.θ_pos
  have hP : 0 < ∏ i : Fin m, (W.w i : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast W.w_pos i
  have hjet : ∀ i : Fin m, ((jetWt W i.succ : ℚ) : ℝ) = (W.w i : ℝ) / (W.θ : ℝ) := fun i => by
    rw [jetWt_succ, Rat.cast_div]
  have hv : ∏ i : Fin m, ((jetWt W i.succ : ℚ) : ℝ) = (∏ i : Fin m, (W.w i : ℝ)) / (W.θ : ℝ) ^ m := by
    simp only [hjet]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hrad : ∏ i : Fin m, ((radWt W i.succ : ℚ) : ℝ) = ∏ i : Fin m, (W.w i : ℝ) := by
    simp only [radWt_succ]
  have h2 : (1 + 3 * (σ : ℝ)) ^ m * ((K : ℝ) * (W.θ : ℝ) ^ m) < 1 := by
    exact_mod_cast hσ.h₂
  have hθm : (W.θ : ℝ) ^ m ≠ 0 := pow_ne_zero m hθ.ne'
  have hPne : (∏ i : Fin m, (W.w i : ℝ)) ≠ 0 := hP.ne'
  have heq : (K : ℝ) * (1 + 3 * (σ : ℝ)) ^ m * (∏ i : Fin m, (W.w i : ℝ)) /
      ((∏ i : Fin m, (W.w i : ℝ)) / (W.θ : ℝ) ^ m) =
      (1 + 3 * (σ : ℝ)) ^ m * ((K : ℝ) * (W.θ : ℝ) ^ m) := by
    rw [div_div_eq_mul_div, div_eq_iff hPne]
    ring
  rw [hv, hrad, heq]
  exact h2

/-- `hseparated` of OAI `excess_implies_fibre_coordinate_constant`, from `explicit_separation`. -/
theorem fibre_separated (W : Weights m) {σ : ℚ} (hσ : 0 < σ) (hthr : EpaThresholds W σ) :
    ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B → (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      PersistentWeightComparison.comparisonConstant m (σ : ℝ) * (∏ j ∈ B, ((jetWt W j : ℚ) : ℝ)) <
        ∏ j ∈ A, ((radWt W j : ℚ) : ℝ) := by
  intro A B _ i hi hiA hiB habove
  have h := explicit_separation_real W hthr A B i hi hiA hiB habove
  rw [← An_eq_comparisonConstant]
  have hAn : ((An m σ : ℚ) : ℝ) ≤ (C4 W σ : ℝ) := by exact_mod_cast An_le_C4 W hσ
  have hB : 0 ≤ ∏ j ∈ B, ((jetWt W j : ℚ) : ℝ) :=
    Finset.prod_nonneg fun j _ => by exact_mod_cast (fb_jetWt_pos W j).le
  calc ((An m σ : ℚ) : ℝ) * ∏ j ∈ B, ((jetWt W j : ℚ) : ℝ)
      ≤ (C4 W σ : ℝ) * ∏ j ∈ B, ((jetWt W j : ℚ) : ℝ) := mul_le_mul_of_nonneg_right hAn hB
    _ < _ := h

/-- `hratio` of OAI `no_fibre_excess_of_constant_coordinate`, from `EpaSigma.h₃`. -/
theorem fibre_ratio (W : Weights m) {σ : ℚ} (hσ : EpaSigma m K W σ) :
    ∀ i : Fin m, (1 + (σ : ℝ)) * ((radWt W i.succ : ℚ) : ℝ) < ((jetWt W i.succ : ℚ) : ℝ) := by
  intro i
  have hθ : (0 : ℝ) < (W.θ : ℝ) := by exact_mod_cast W.θ_pos
  have hw : (0 : ℝ) < (W.w i : ℝ) := by exact_mod_cast W.w_pos i
  have h3 : (1 + (σ : ℝ)) * (W.θ : ℝ) < 1 := by exact_mod_cast hσ.h₃
  have hjet : ((jetWt W i.succ : ℚ) : ℝ) = (W.w i : ℝ) / (W.θ : ℝ) := by
    rw [jetWt_succ, Rat.cast_div]
  rw [hjet, radWt_succ, lt_div_iff₀ hθ]
  nlinarith [mul_lt_mul_of_pos_left h3 hw]

end CatalanCore.Elliptic.EPA
