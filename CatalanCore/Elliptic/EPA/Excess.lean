module

public import CatalanCore.Elliptic.EPA.Params
public import CatalanCore.Elliptic.EPA.Numerics
public import CatalanCore.Elliptic.EPA.Persistence
public import CatalanCore.Elliptic.EPA.Auxiliary
public import CatalanCore.Elliptic.EPA.Vanishing
public import CatalanCore.Elliptic.EPA.Local.Quartic
public import CatalanCore.Elliptic.EPA.Rigid.Quartic
public import CatalanCore.Elliptic.EPA.Rigid.Exclusion
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Ideal.Height

/-!
# Excess contact forces the curve into the origin fibre (row E09.8)

Labels refer to `D2-DESIGN-2026-11-20.md` §5 E09.8 and to CM (arXiv 2610.31112) Proposition
`origin-excess-fiber` (`cm-2610.31112-nolean.tex` l.3190, proof l.3199-3244). Template: OAI
`Geometry/CurveInequality.excess_implies_zeroth_eq_one` (openai/math fd4aeeb2, Apache License 2.0,
Copyright OpenAI).

Setting: `E` a function field over `ℂ` with the finiteness hypothesis `hfinite` of OAI
`CurveContactSum`, `z = (u, t, Z) : Fin (m+2) → E` with `t² = F(u)`, a transcendental coordinate,
centres `c : Fin K → Fin m → ℂ`, and `μ_p = ellPlaceContact … p` at the places centred at some
`(0, 0, c_j)`.

* `kernel_height_le`: the kernel `𝔭` of `R = ℂ[u, t, Z] → E`, `X ↦ z`, has height `≤ m + 1` (a
  transcendental coordinate makes `R/𝔭` not a field, so `𝔭` lies strictly below a maximal ideal and
  `dim R = m + 2`).
* `excess_implies_origin_fibre`: if `d_C < (1+σ) Σ_p μ_p` then `u = t = 0` in `E`.

Proof (CM l.3199-3243). Choose `N ≥ N₀` (E09.6 with `ρ = 1 + 3σ`), `N ≥ 8 w₀`, and the rectangle
budget `δ = ε₀ N/(m+3) > (m+1) max κ_j`. The auxiliary `P ∉ (f)` has `Φ_{c_j}(P) ∈ j_{(1+3σ)N}`;
terminal vanishing (E09.7) kills every word of jet cost `≤ ε₀ N = (m+3) δ` on `z`, so the words
lie in `𝔭`. Persistence (E09.3) gives a prime `Q ≤ 𝔭`, strictly above `(f)`, minimal over `I_{rδ}`,
with `D_ν(I_{rδ}) ⊆ Q` for `c(ν) ≤ δ`. The persistent comparison (E09.4c, constant `C₄`) and
`explicit_separation` (E09.0) exclude every forbidden pair of normal bases, so the constant
projection theorem (E09.5d; the critical cases `J̄ = 0`, `t̄ = 0` are inside it) gives constants
`c₀, c₁` with `u − c₀, t − c₁ ∈ Q ⊆ 𝔭`, i.e. `u = c₀`, `t = c₁` in `E`. At a centred place the
residue of `u`, `t` is `0`, so `c₀ = c₁ = 0`. A centred place exists because the excess forces
`Σ_p μ_p > 0` (`d_C ≥ 0`).

Deviations from the design statement (each at least as strong): the hypotheses `hbase`, `hgen`,
`htrdeg` of the design are not needed and are omitted (the height bound uses only a transcendental
coordinate; `EpaSigma` carries the volume inequality `h₁`); the contact is `ellPlaceContact`
(E09.7, total) and the word-cost cutoff is `eps0 W σ · N` (E09.7 deviation), `hpers` of E09.4c takes
the rational word cost cast to `ℝ`.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

open CatalanCore.Elliptic OAI.PiExponent OAI.PiExponent.JetGeometry
  CurveValuationCenter CurveCenters PlaceValuationRing

variable {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ} {ch : OriginChart}

/-! ### The height of the coordinate kernel -/

/-- The kernel of `ℂ[u, t, Z] → E`, `X ↦ z`, has height `≤ m + 1` when some coordinate of `z` is
transcendental. -/
theorem kernel_height_le (z : Fin (m + 2) → E) (hz : ∃ i, Transcendental ℂ (z i)) :
    (RingHom.ker (MvPolynomial.aeval (R := ℂ) z).toRingHom : Ideal (AmbRing m)).height ≤
      ((m + 1 : ℕ) : ℕ∞) := by
  set 𝔭 : Ideal (AmbRing m) := RingHom.ker (MvPolynomial.aeval (R := ℂ) z).toRingHom with h𝔭
  haveI : 𝔭.IsPrime := RingHom.ker_isPrime _
  have hnm : ¬ 𝔭.IsMaximal := by
    intro hmax
    letI : Field (AmbRing m ⧸ 𝔭) := Ideal.Quotient.field 𝔭
    haveI : Module.Finite ℂ (AmbRing m ⧸ 𝔭) :=
      finite_of_finite_type_of_isJacobsonRing ℂ (AmbRing m ⧸ 𝔭)
    haveI : Algebra.IsAlgebraic ℂ (AmbRing m ⧸ 𝔭) := Algebra.IsAlgebraic.of_finite ℂ _
    obtain ⟨i, hi⟩ := hz
    let f : (AmbRing m ⧸ 𝔭) →ₐ[ℂ] E :=
      Ideal.Quotient.liftₐ 𝔭 (MvPolynomial.aeval z) (fun a ha => ha)
    have hfi : f (Ideal.Quotient.mk 𝔭 (MvPolynomial.X i)) = z i := by
      exact MvPolynomial.aeval_X z i
    have halg : IsAlgebraic ℂ (f (Ideal.Quotient.mk 𝔭 (MvPolynomial.X i))) :=
      (Algebra.IsAlgebraic.isAlgebraic _).algHom f
    rw [hfi] at halg
    exact hi halg
  obtain ⟨M, hM, h𝔭M⟩ := Ideal.exists_le_maximal 𝔭 (Ideal.IsPrime.ne_top ‹𝔭.IsPrime›)
  have hlt : 𝔭 < M := lt_of_le_of_ne h𝔭M (fun h => hnm (h ▸ hM))
  haveI := hM.isPrime
  have h1 : 𝔭.height + 1 ≤ M.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h2 : (M.height : WithBot ℕ∞) ≤ ringKrullDim (AmbRing m) :=
    Ideal.height_le_ringKrullDim_of_isPrime
  have h3 : ringKrullDim (AmbRing m) = ((m + 2 : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    simp
  rw [h3] at h2
  have h4 : M.height ≤ ((m + 2 : ℕ) : ℕ∞) :=
    WithBot.coe_le_coe.mp (h2.trans (le_of_eq (by first | rfl | simp | norm_cast)))
  have h5 : 𝔭.height + 1 ≤ ((m + 1 : ℕ) : ℕ∞) + 1 := by
    refine h1.trans (h4.trans (le_of_eq ?_))
    push_cast
    ring
  exact (ENat.add_le_add_iff_right (by simp)).mp h5

/-! ### The proposition -/

/-- **Row E09.8** (CM Prop `origin-excess-fiber`, l.3190). Under the parameter conditions
`EpaSigma`, `EpaThresholds`, if the weighted degree of the coordinates is below `(1+σ)` times the
total contact then `u = t = 0`. -/
theorem excess_implies_origin_fibre (W : Weights m)
    {σ : ℚ} (hσ : EpaSigma m K W σ) (hthr : EpaThresholds W σ)
    (s : OriginSeries ch)
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m + 2) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (hrel : IsEllBranch ch z)
    (hexcess : CurveContactSum.weightedDegree hfinite z (srcWt W) <
      (1 + (σ : ℝ)) * ∑ p ∈ ellPlaces hfinite z c hz,
        (ellPlaceContact hres hfinite s z c hz (jetWt W) p : ℝ)) :
    z 0 = 0 ∧ z 1 = 0 := by
  classical
  have hσ0 : 0 < σ := hσ.pos
  have hε : 0 < eps0 W σ := eps0_pos W hσ0
  have hεR : (0 : ℝ) < (eps0 W σ : ℝ) := by exact_mod_cast hε
  have hm3 : (0 : ℝ) < (m : ℝ) + 3 := by positivity
  have hm3q : (0 : ℚ) < (m : ℚ) + 3 := by positivity
  have hw0R : (0 : ℝ) < (W.w₀ : ℝ) := by exact_mod_cast W.w₀_pos
  -- a centred place exists
  have hne : (ellPlaces hfinite z c hz).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty, mul_zero] at hexcess
    exact (not_lt_of_ge (CurveContactSum.weightedDegree_nonneg hfinite z (srcWt W))) hexcess
  -- the auxiliary polynomial
  have hvol : (K : ℚ) * (W.w₀ / W.v₀) * W.θ ^ m * (1 + 3 * σ) ^ (m + 1) < 1 := by
    rw [mul_comm]; exact hσ.h₁
  obtain ⟨N₀, hN₀⟩ := ell_auxiliary (K := K) s W (ρ := 1 + 3 * σ) (by linarith) hvol
  -- the choice of N
  have hSum : 0 ≤ ∑ j, ((jetWt W j : ℚ) : ℝ) :=
    Finset.sum_nonneg (fun j _ => by exact_mod_cast (jetWt_pos W j).le)
  obtain ⟨N', hN'⟩ := exists_nat_gt
    (((m : ℝ) + 1) * ((m : ℝ) + 3) * (∑ j, ((jetWt W j : ℚ) : ℝ)) / (eps0 W σ : ℝ) +
      8 * (W.w₀ : ℝ))
  set N : ℕ := N₀ + N' + 1 with hNdef
  have hN0 : N₀ ≤ N := by omega
  have hNpos : 0 < N := by omega
  have hNgt : ((m : ℝ) + 1) * ((m : ℝ) + 3) * (∑ j, ((jetWt W j : ℚ) : ℝ)) / (eps0 W σ : ℝ) +
      8 * (W.w₀ : ℝ) < (N : ℝ) := by
    have : (N' : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : N' ≤ N)
    linarith
  have hfirst : 0 ≤ ((m : ℝ) + 1) * ((m : ℝ) + 3) * (∑ j, ((jetWt W j : ℚ) : ℝ)) /
      (eps0 W σ : ℝ) :=
    div_nonneg (mul_nonneg (by positivity) hSum) hεR.le
  have hN8 : 8 * (W.w₀ : ℝ) ≤ (N : ℝ) := by linarith
  have hNR : (0 : ℝ) < (N : ℝ) := by linarith
  have hX' : ((m : ℝ) + 1) * ((m : ℝ) + 3) * (∑ j, ((jetWt W j : ℚ) : ℝ)) <
      (N : ℝ) * (eps0 W σ : ℝ) := by
    have : ((m : ℝ) + 1) * ((m : ℝ) + 3) * (∑ j, ((jetWt W j : ℚ) : ℝ)) / (eps0 W σ : ℝ) <
        (N : ℝ) := by linarith
    exact (div_lt_iff₀ hεR).mp this
  -- the rectangle budget δ
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℚ, δ = eps0 W σ * N / ((m : ℚ) + 3) := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by
    rw [hδdef]
    exact div_nonneg (mul_nonneg hε.le (Nat.cast_nonneg _)) hm3q.le
  have hδR : (δ : ℝ) = (eps0 W σ : ℝ) * (N : ℝ) / ((m : ℝ) + 3) := by
    rw [hδdef]; push_cast; ring
  have hmδ : ((m : ℚ) + 3) * δ = eps0 W σ * N := by
    rw [hδdef]; field_simp
  have hrect : Local.EllUniformRectangles W ((eps0 W σ : ℝ) * (N : ℝ) / ((m : ℝ) + 3)) := by
    apply Local.ellUniformRectangles_of_lt
    intro j
    rw [lt_div_iff₀ hm3]
    have hj : ((jetWt W j : ℚ) : ℝ) ≤ ∑ j, ((jetWt W j : ℚ) : ℝ) :=
      Finset.single_le_sum (f := fun j => ((jetWt W j : ℚ) : ℝ))
        (fun j _ => by exact_mod_cast (jetWt_pos W j).le) (Finset.mem_univ j)
    calc ((m : ℝ) + 1) * ((jetWt W j : ℚ) : ℝ) * ((m : ℝ) + 3)
        = ((m : ℝ) + 1) * ((m : ℝ) + 3) * ((jetWt W j : ℚ) : ℝ) := by ring
      _ ≤ ((m : ℝ) + 1) * ((m : ℝ) + 3) * (∑ j, ((jetWt W j : ℚ) : ℝ)) := by gcongr
      _ < (N : ℝ) * (eps0 W σ : ℝ) := hX'
      _ = (eps0 W σ : ℝ) * (N : ℝ) := by ring
  -- the auxiliary polynomial at level N
  obtain ⟨P, -, hPf, hPdeg, -, hPjet⟩ := hN₀ N hN0 c
  -- terminal vanishing (E09.7)
  have hwords := ell_words_vanish W hres hfinite s z c hz hrel hσ0 hNpos hPdeg hPjet hexcess
  -- the kernel prime
  set 𝔭 : Ideal (AmbRing m) := RingHom.ker (MvPolynomial.aeval (R := ℂ) z).toRingHom with h𝔭
  haveI h𝔭p : 𝔭.IsPrime := RingHom.ker_isPrime _
  haveI hfp : (Ideal.span {relation ch} : Ideal (AmbRing m)).IsPrime := relation_isPrime ch
  have hrelz : MvPolynomial.aeval z (relation ch : AmbRing m) = 0 := by
    have h := hrel
    unfold IsEllBranch at h
    unfold relation uV tV
    rw [map_sub, map_pow, ← Polynomial.aeval_algHom_apply]
    simp only [MvPolynomial.aeval_X]
    exact sub_eq_zero.mpr h
  have hf : (Ideal.span {relation ch} : Ideal (AmbRing m)) ≤ 𝔭 :=
    Ideal.span_le.mpr (by
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact RingHom.mem_ker.mpr hrelz)
  have hht : 𝔭.height ≤ ((m + 1 : ℕ) : ℕ∞) := kernel_height_le z hz
  have hvan : ∀ word : List (Fin (m + 1)), (word.map (jetWt W)).sum ≤ ((m : ℚ) + 3) * δ →
      frameWord ch word P ∈ 𝔭 := by
    intro word hw
    rw [hmδ] at hw
    exact RingHom.mem_ker.mpr (hwords word hw)
  -- persistence (E09.3)
  obtain ⟨r, hr, Q, hQ1, -, hQ𝔭, hQlt, -, -, hQpers⟩ :=
    persistent_prime (v := jetWt W) (fun i => (jetWt_pos W i).le) δ hδ0 hPf 𝔭 hf hht hvan
  haveI hQp : Q.IsPrime := hQ1.1.1
  -- the comparison and the exclusion (E09.4c, E09.0)
  have hrδ : (r : ℚ) * δ ≤ eps0 W σ * N := by
    have hr' : (r : ℚ) ≤ (m : ℚ) + 3 := by exact_mod_cast hr.le
    calc (r : ℚ) * δ ≤ ((m : ℚ) + 3) * δ := mul_le_mul_of_nonneg_right hr' hδ0
      _ = eps0 W σ * N := hmδ
  have hs : (((r : ℚ) * δ : ℚ) : ℝ) ≤ (eps0 W σ : ℝ) * (N : ℝ) := by
    exact_mod_cast hrδ
  have hpers : ∀ g ∈ derivIdeal ch P (jetWt W) ((r : ℚ) * δ), ∀ word : List (Fin (m + 1)),
      ((((word.map (jetWt W)).sum : ℚ)) : ℝ) ≤ (eps0 W σ : ℝ) * (N : ℝ) / ((m : ℝ) + 3) →
        frameWord ch word g ∈ Q := by
    intro g hg word hw
    rw [← hδR] at hw
    exact hQpers g hg word (by exact_mod_cast hw)
  have hexcl : ∀ hJ : resJ ch Q ≠ 0, ∀ S T : Finset (Fin (m + 1)),
      IsIntrinsicCoordinateNormalBasis ch Q S → IsFrameNormalBasis ch Q hJ T →
      ∀ i, i ≠ 0 → i ∈ S → i ∉ T → (∀ j, i < j → (j ∈ S ↔ j ∈ T)) → False := by
    intro hJ S T hS hT i hi hiS hiT hab
    have h1 := Local.ell_persistent_comparison W ch hσ0 P (N : ℝ) hPdeg hN8 hrect
      ((r : ℚ) * δ) hs Q hJ hQ1 hpers S T hS hT
    have h2 := explicit_separation_real W hthr S T i hi hiS hiT hab
    linarith
  -- constant projection (E09.5d)
  obtain ⟨c₀, c₁, h0, h1⟩ := ell_projection_constant_of_exclusion ch Q hQlt hexcl
  have hz0 : z 0 = algebraMap ℂ E c₀ := by
    have h : MvPolynomial.aeval z (uV - MvPolynomial.C c₀ : AmbRing m) = 0 :=
      RingHom.mem_ker.mp (hQ𝔭 h0)
    simp only [uV, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C] at h
    exact sub_eq_zero.mp h
  have hz1 : z 1 = algebraMap ℂ E c₁ := by
    have h : MvPolynomial.aeval z (tV - MvPolynomial.C c₁ : AmbRing m) = 0 :=
      RingHom.mem_ker.mp (hQ𝔭 h1)
    simp only [tV, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C] at h
    exact sub_eq_zero.mp h
  -- evaluation at a centred place
  obtain ⟨p, hp⟩ := hne
  have hcen := ellCentered hfinite z c hz p hp
  have hc0 : c₀ = 0 := by
    have := hcen.constant_coordinate 0 c₀ hz0
    simpa using this
  have hc1 : c₁ = 0 := by
    have := hcen.constant_coordinate 1 c₁ hz1
    rwa [ellCentre_one] at this
  refine ⟨?_, ?_⟩
  · rw [hz0, hc0, map_zero]
  · rw [hz1, hc1, map_zero]

end CatalanCore.Elliptic.EPA
