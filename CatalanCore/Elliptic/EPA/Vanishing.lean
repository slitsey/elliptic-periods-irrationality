module

public import CatalanCore.Elliptic.EPA.Branch
public import CatalanCore.Elliptic.EPA.Numerics
public import OAI.NumberTheory.PiExponent.Geometry.CurveCenters
public import OAI.NumberTheory.PiExponent.Geometry.CurveContactSum
public import OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch

/-!
# Excess contact supplies terminal vanishing (row E09.7, part 2)

Labels refer to the proof design §5 E09.7 and CM (arXiv 2610.31112) §9, Theorem
`thm:contact-terminal` (l.2330) and its use in §10 (l.2689-2712, the quartic margin).

Let `E` be a function field over `ℂ` with the finiteness hypothesis `hfinite` of OAI
`CurveContactSum`, `z = (u, t, Z) : Fin (m+2) → E` with `t² = F(u)` and a nonconstant coordinate,
and centres `c : Fin K → Fin m → ℂ`; the centred places are those of OAI `CurveCenters` for the
centre array `ellCentres c j = (0, 0, c_j)`.

* `ellPlaces`, `ellCenter`, `ellCentered`: the centred places and a choice of centre per place.
* `ellPlaceContact`: the contact `μ_p` of `Branch.lean` at the place `p` (the generic
  `PlaceCenteredBranch.lift` of OAI to the valuation ring `ring p`); `0` off the centred places.
* `ellPlaceContact_pos`, `ellPlaceContact_nonneg`.
* `ell_word_order_lower`: at a centred place, `μ_p (H − c(W)) ≤ ord_p (D_W P(z))` (CM l.2281 for
  `p`), for `Φ_{c_j}(P) ∈ j_H` at every centre.
* `ell_words_vanish_of_excess`: CM Theorem `contact-terminal`: if `P` has source cutoff `N`,
  `Φ_{c_j}(P) ∈ j_R` for all `j`, `0 ≤ B`, and
  `(N + (2w₀/v₀) B) d_C < (R − B) Σ_p μ_p`, then `D_W P(z) = 0` for every word with `c(W) ≤ B`.
* `ell_words_vanish`: the specialisation of CM l.2689-2712 (`R = (1+3σ)N`, `B = ε₀ N`,
  excess `d_C < (1+σ) Σ_p μ_p`), using the margin `scalar_margin` of `Numerics.lean`.

The proof is that of OAI `CurveDerivativeVanishing.logarithmic_words_vanish`
(openai/math fd4aeeb2, Apache License 2.0, Copyright OpenAI): the generic
`CurveContactSum.polynomial_eq_zero_of_excess_contact` (zeros versus poles on the curve), the local
bound `ell_word_order_lower`, and the degree bound `srcDeg_frameWord` of `Frame.lean`.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

open CatalanCore.Elliptic OAI.PiExponent OAI.PiExponent.JetGeometry
  CurveValuationCenter CurveCenters PlaceValuationRing

variable {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ} {ch : OriginChart}

theorem jetWt_pos (W : Weights m) (i : Fin (m + 1)) : 0 < jetWt W i := by
  induction i using Fin.cases with
  | zero => exact W.v₀_pos
  | succ i => exact div_pos (W.w_pos i) W.θ_pos

/-! ### Centred places -/

/-- The places of `E` centred at some `(0, 0, c_j)` (OAI `centerPlaces` for `ellCentres c`). -/
noncomputable def ellPlaces
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m + 2) → E) (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i)) :
    Finset (NormalizedPlace ℂ E) :=
  centerPlaces z (ellCentres c) hz hfinite

theorem mem_ellPlaces
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m + 2) → E) (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i))
    (p : NormalizedPlace ℂ E) :
    p ∈ ellPlaces hfinite z c hz ↔ ∃ j : Fin K, Centered z (ellCentre (c j)) p :=
  mem_centerPlaces z (ellCentres c) hz hfinite p

/-- A centre index of a centred place (a choice; by `Centered.center_eq` it is unique up to equal
centres). -/
noncomputable def ellCenter
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m + 2) → E) (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i))
    (p : NormalizedPlace ℂ E) (hp : p ∈ ellPlaces hfinite z c hz) : Fin K :=
  Classical.choose ((mem_ellPlaces hfinite z c hz p).mp hp)

theorem ellCentered
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m + 2) → E) (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i))
    (p : NormalizedPlace ℂ E) (hp : p ∈ ellPlaces hfinite z c hz) :
    Centered z (ellCentre (c (ellCenter hfinite z c hz p hp))) p :=
  Classical.choose_spec ((mem_ellPlaces hfinite z c hz p).mp hp)

/-- The elliptic contact `μ_p` at a place `p` (CM l.2262-2268): `ellContact` of the lift of `z` to
the valuation ring of `p` at the centre of `p`; `0` if `p` is not centred. -/
noncomputable def ellPlaceContact
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (s : OriginSeries ch) (z : Fin (m + 2) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (v : Fin (m + 1) → ℚ) (p : NormalizedPlace ℂ E) : ℚ := by
  classical
  letI := hres p
  exact if hp : p ∈ ellPlaces hfinite z c hz then
    ellContact s (c (ellCenter hfinite z c hz p hp))
      (PlaceCenteredBranch.lift p z (ellCentre (c (ellCenter hfinite z c hz p hp)))
        (ellCentered hfinite z c hz p hp)) v
  else 0

theorem ellPlaceContact_of_mem
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (s : OriginSeries ch) (z : Fin (m + 2) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (v : Fin (m + 1) → ℚ) (p : NormalizedPlace ℂ E)
    (hp : p ∈ ellPlaces hfinite z c hz) :
    letI := hres p
    ellPlaceContact hres hfinite s z c hz v p =
      ellContact s (c (ellCenter hfinite z c hz p hp))
        (PlaceCenteredBranch.lift p z (ellCentre (c (ellCenter hfinite z c hz p hp)))
          (ellCentered hfinite z c hz p hp)) v := by
  classical
  unfold ellPlaceContact
  simp only [dite_eq_left hp]

theorem ellPlaceContact_of_not_mem
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (s : OriginSeries ch) (z : Fin (m + 2) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (v : Fin (m + 1) → ℚ) (p : NormalizedPlace ℂ E)
    (hp : p ∉ ellPlaces hfinite z c hz) :
    ellPlaceContact hres hfinite s z c hz v p = 0 := by
  classical
  unfold ellPlaceContact
  simp only [dite_eq_right hp]

/-! ### Lifting the branch to the valuation ring of a place -/

theorem isEllBranch_lift (p : NormalizedPlace ℂ E) (z : Fin (m + 2) → E) (c' : Fin (m + 2) → ℂ)
    (hc : Centered z c' p) (hrel : IsEllBranch ch z) :
    IsEllBranch ch (PlaceCenteredBranch.lift p z c' hc) := by
  unfold IsEllBranch
  apply IsFractionRing.injective (ring p) E
  rw [map_pow, ← Polynomial.aeval_algebraMap_apply]
  exact hrel

theorem isCentredAt_lift (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]
    (z : Fin (m + 2) → E) (c : Fin m → ℂ) (hc : Centered z (ellCentre c) p) :
    IsCentredAt c (PlaceCenteredBranch.lift p z (ellCentre c) hc) :=
  fun i => PlaceCenteredBranch.lift_residue p z (ellCentre c) hc i

theorem lift_nonconstant_ell (p : NormalizedPlace ℂ E)
    (z : Fin (m + 2) → E) (c : Fin m → ℂ) (hc : Centered z (ellCentre c) p)
    (hz : ∃ i, Transcendental ℂ (z i)) :
    ∃ i, PlaceCenteredBranch.lift p z (ellCentre c) hc i ≠
      algebraMap ℂ (ring p) (ellCentre c i) :=
  PlaceCenteredBranch.lift_nonconstant p z (ellCentre c) hc
    (Centered.exists_nonzero_difference z (ellCentre c) hz)

theorem ellPlaceContact_pos
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (s : OriginSeries ch) (z : Fin (m + 2) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (hrel : IsEllBranch ch z)
    {v : Fin (m + 1) → ℚ} (hv : ∀ i, 0 < v i) (p : NormalizedPlace ℂ E)
    (hp : p ∈ ellPlaces hfinite z c hz) :
    0 < ellPlaceContact hres hfinite s z c hz v p := by
  letI := hres p
  rw [ellPlaceContact_of_mem hres hfinite s z c hz v p hp]
  exact ellContact_pos hv (isEllBranch_lift p z _ _ hrel)
    (isCentredAt_lift p z _ (ellCentered hfinite z c hz p hp))
    (lift_nonconstant_ell p z _ (ellCentered hfinite z c hz p hp) hz)

theorem ellPlaceContact_nonneg
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (s : OriginSeries ch) (z : Fin (m + 2) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (hrel : IsEllBranch ch z)
    {v : Fin (m + 1) → ℚ} (hv : ∀ i, 0 < v i) (p : NormalizedPlace ℂ E) :
    0 ≤ ellPlaceContact hres hfinite s z c hz v p := by
  by_cases hp : p ∈ ellPlaces hfinite z c hz
  · exact (ellPlaceContact_pos hres hfinite s z c hz hrel hv p hp).le
  · rw [ellPlaceContact_of_not_mem hres hfinite s z c hz v p hp]

/-! ### The local order bound at a centred place (CM l.2281) -/

/-- At a centred place `p`: if `Φ_{c_j}(P) ∈ j_H` for every centre `j`, then
`μ_p (H − c(W)) ≤ ord_p (D_W P (z))`. -/
theorem ell_word_order_lower
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (s : OriginSeries ch) (z : Fin (m + 2) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (hrel : IsEllBranch ch z)
    {v : Fin (m + 1) → ℚ} (hv : ∀ i, 0 < v i) (H : ℚ) {F : AmbRing m}
    (hF : ∀ j, ellJet s (c j) F ∈ rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m + 1)))
    (hne : MvPolynomial.aeval z (frameWord ch word F) ≠ 0) (p : NormalizedPlace ℂ E)
    (hp : p ∈ ellPlaces hfinite z c hz) :
    ellPlaceContact hres hfinite s z c hz v p * (H - (word.map v).sum) ≤
      (WeightedPolynomialPole.coordinateOrder p.valuation
        (MvPolynomial.aeval z (frameWord ch word F)) : ℚ) := by
  letI := hres p
  have hc := ellCentered hfinite z c hz p hp
  have hn : MvPolynomial.aeval (PlaceCenteredBranch.lift p z _ hc) (frameWord ch word F) ≠ 0 := by
    intro h0
    apply hne
    rw [← PlaceCenteredBranch.lift_aeval p z _ hc, h0, map_zero]
  have hb := ell_word_colength_lower (s := s) hv H (isEllBranch_lift p z _ hc hrel)
    (isCentredAt_lift p z _ hc) (lift_nonconstant_ell p z _ hc hz)
    (hF (ellCenter hfinite z c hz p hp)) word hn
  rw [PlaceCenteredBranch.coordinateOrder_aeval_eq_length p z _ hc _ hne,
    ellPlaceContact_of_mem hres hfinite s z c hz v p hp]
  simpa only [Int.cast_natCast] using hb

/-! ### Terminal vanishing (CM Theorem `contact-terminal`) -/

/-- CM Theorem `thm:contact-terminal` (l.2330), in the generality of the paper: `P` of source
cutoff `N ≥ 0` with `Φ_{c_j}(P) ∈ j_R` at every centre; `0 ≤ B`; and
`(N + (2w₀/v₀) B) d_C < (R − B) Σ_p μ_p`. Then `D_W P(z) = 0` for every word with `c(W) ≤ B`. -/
theorem ell_words_vanish_of_excess (W : Weights m)
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (s : OriginSeries ch) (z : Fin (m + 2) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (hrel : IsEllBranch ch z)
    {N : ℝ} (hN : 0 ≤ N) {R B : ℚ} (hB : 0 ≤ B) {F : AmbRing m} (hF : SrcDeg W N F)
    (hjet : ∀ j, ellJet s (c j) F ∈
      rationalWeightedIdeal (jetWt W) (fun i => (jetWt_pos W i).le) R)
    (hexcess : (N + ((2 * W.w₀ / W.v₀ * B : ℚ) : ℝ)) *
        CurveContactSum.weightedDegree hfinite z (srcWt W) <
      ((R : ℝ) - (B : ℝ)) *
        ∑ p ∈ ellPlaces hfinite z c hz,
          (ellPlaceContact hres hfinite s z c hz (jetWt W) p : ℝ)) :
    ∀ word : List (Fin (m + 1)), (word.map (jetWt W)).sum ≤ B →
      MvPolynomial.aeval z (frameWord ch word F) = 0 := by
  intro word hword
  have hlam : 0 ≤ 2 * W.w₀ / W.v₀ := div_nonneg (mul_nonneg two_pos.le W.w₀_pos.le) W.v₀_pos.le
  have hcost : (word.map (srcCost W)).sum ≤ 2 * W.w₀ / W.v₀ * B :=
    (srcCost_sum_le W word).trans (mul_le_mul_of_nonneg_left hword hlam)
  have hNB : 0 ≤ N + ((2 * W.w₀ / W.v₀ * B : ℚ) : ℝ) := by
    have : (0 : ℝ) ≤ ((2 * W.w₀ / W.v₀ * B : ℚ) : ℝ) := by
      exact_mod_cast mul_nonneg hlam hB
    linarith
  have hdegree : ∀ d ∈ (frameWord ch word F).support,
      Finsupp.weight (fun i => ((srcWt W i : ℚ) : ℝ)) d ≤
        N + ((2 * W.w₀ / W.v₀ * B : ℚ) : ℝ) := by
    have h1 := srcDeg_frameWord (ch := ch) hF word
    have h2 : (((word.map (srcCost W)).sum : ℚ) : ℝ) ≤ ((2 * W.w₀ / W.v₀ * B : ℚ) : ℝ) := by
      exact_mod_cast hcost
    have h3 : SrcDeg W (N + ((2 * W.w₀ / W.v₀ * B : ℚ) : ℝ)) (frameWord ch word F) :=
      h1.mono (by linarith)
    exact h3
  apply CurveContactSum.polynomial_eq_zero_of_excess_contact hfinite z (srcWt W)
    (srcWt_pos W) (N + ((2 * W.w₀ / W.v₀ * B : ℚ) : ℝ)) ((R : ℝ) - (B : ℝ)) hNB
    (frameWord ch word F) hdegree (ellPlaces hfinite z c hz)
    (fun p => (ellPlaceContact hres hfinite s z c hz (jetWt W) p : ℝ))
  · intro hne p hp
    have hlocal := ell_word_order_lower hres hfinite s z c hz hrel (fun i => jetWt_pos W i) R hjet
      word hne p hp
    have hμ := ellPlaceContact_nonneg hres hfinite s z c hz hrel (fun i => jetWt_pos W i) p
    have hle : ellPlaceContact hres hfinite s z c hz (jetWt W) p * (R - B) ≤
        (WeightedPolynomialPole.coordinateOrder p.valuation
          (MvPolynomial.aeval z (frameWord ch word F)) : ℚ) :=
      (mul_le_mul_of_nonneg_left (by linarith) hμ).trans hlocal
    have hr : (ellPlaceContact hres hfinite s z c hz (jetWt W) p : ℝ) * ((R : ℝ) - (B : ℝ)) ≤
        (WeightedPolynomialPole.coordinateOrder p.valuation
          (MvPolynomial.aeval z (frameWord ch word F)) : ℝ) := by
      exact_mod_cast hle
    rw [mul_comm]
    exact hr
  · exact hexcess

/-- The terminal vanishing of CM l.2689-2712: with `R = (1+3σ)N`, `B = ε₀ N` and the excess
`d_C < (1+σ) Σ_p μ_p`, every word of cost `≤ ε₀ N` kills `P(z)`. -/
theorem ell_words_vanish (W : Weights m)
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (s : OriginSeries ch) (z : Fin (m + 2) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (hrel : IsEllBranch ch z)
    {σ : ℚ} (hσ : 0 < σ) {N : ℕ} (hN : 0 < N) {F : AmbRing m} (hF : SrcDeg W (N : ℝ) F)
    (hjet : ∀ j, ellJet s (c j) F ∈
      rationalWeightedIdeal (jetWt W) (fun i => (jetWt_pos W i).le) ((1 + 3 * σ) * N))
    (hexcess : CurveContactSum.weightedDegree hfinite z (srcWt W) <
      (1 + (σ : ℝ)) * ∑ p ∈ ellPlaces hfinite z c hz,
        (ellPlaceContact hres hfinite s z c hz (jetWt W) p : ℝ)) :
    ∀ word : List (Fin (m + 1)), (word.map (jetWt W)).sum ≤ eps0 W σ * N →
      MvPolynomial.aeval z (frameWord ch word F) = 0 := by
  have hm := scalar_margin W hσ
  have hε0 : 0 < eps0 W σ := hm.1
  have hg0 : 0 < gConst W σ := by
    have : 0 < 2 * W.w₀ / W.v₀ * eps0 W σ :=
      mul_pos (div_pos (mul_pos two_pos W.w₀_pos) W.v₀_pos) hε0
    unfold gConst
    linarith
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hB : 0 ≤ eps0 W σ * N := (mul_pos hε0 hNq).le
  have hkey : gConst W σ * (1 + σ) ≤ (1 + 3 * σ) - eps0 W σ := by
    have := hm.2.2.2.2; linarith
  have hgN : (N : ℚ) + 2 * W.w₀ / W.v₀ * (eps0 W σ * N) = gConst W σ * N := by
    unfold gConst; ring
  set S : ℝ := ∑ p ∈ ellPlaces hfinite z c hz,
    (ellPlaceContact hres hfinite s z c hz (jetWt W) p : ℝ) with hS
  have hS0 : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro p hp
    exact Rat.cast_nonneg.mpr
      (ellPlaceContact_nonneg hres hfinite s z c hz hrel (fun i => jetWt_pos W i) p)
  apply ell_words_vanish_of_excess W hres hfinite s z c hz hrel (N := (N : ℝ)) (Nat.cast_nonneg N)
    (R := (1 + 3 * σ) * N) (B := eps0 W σ * N) hB hF hjet
  have hgR : (0 : ℝ) < ((gConst W σ : ℚ) : ℝ) := by exact_mod_cast hg0
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hkeyR : ((gConst W σ : ℚ) : ℝ) * (1 + (σ : ℝ)) ≤
      (1 + 3 * (σ : ℝ)) - ((eps0 W σ : ℚ) : ℝ) := by exact_mod_cast hkey
  have hgNR : (N : ℝ) + ((2 * W.w₀ / W.v₀ * (eps0 W σ * N) : ℚ) : ℝ) =
      ((gConst W σ : ℚ) : ℝ) * N := by exact_mod_cast hgN
  rw [hgNR]
  have hRB : (((1 + 3 * σ) * N : ℚ) : ℝ) - ((eps0 W σ * N : ℚ) : ℝ) =
      ((1 + 3 * (σ : ℝ)) - ((eps0 W σ : ℚ) : ℝ)) * N := by push_cast; ring
  rw [hRB]
  calc ((gConst W σ : ℚ) : ℝ) * N * CurveContactSum.weightedDegree hfinite z (srcWt W)
      < ((gConst W σ : ℚ) : ℝ) * N * ((1 + (σ : ℝ)) * S) :=
        mul_lt_mul_of_pos_left hexcess (mul_pos hgR hNR)
    _ = (((gConst W σ : ℚ) : ℝ) * (1 + (σ : ℝ))) * (N * S) := by ring
    _ ≤ ((1 + 3 * (σ : ℝ)) - ((eps0 W σ : ℚ) : ℝ)) * (N * S) :=
        mul_le_mul_of_nonneg_right hkeyR (mul_nonneg hNR.le hS0)
    _ = ((1 + 3 * (σ : ℝ)) - ((eps0 W σ : ℚ) : ℝ)) * N * S := by ring

end CatalanCore.Elliptic.EPA
