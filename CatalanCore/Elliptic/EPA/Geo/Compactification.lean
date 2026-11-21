module

public import CatalanCore.Elliptic.EPA.Ambient
public import OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral
public import OAI.NumberTheory.PiExponent.Ampleness.WeightedProjectiveAmple
public import OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting
public import OAI.NumberTheory.PiExponent.Polynomials.SimplexRationalWeights
public import OAI.NumberTheory.PiExponent.Geometry.CurveMonomialMap
public import OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout

/-!
# The ambient compactification of `thm:epa` (row E09.10a)

Labels refer to `D2-DESIGN-2026-11-20.md` (§0.1, §2 P3 and P7, §5 E09.10a, §A6) and to the
OpenAI/Apache-2.0 library file `Ampleness/AdmissibleBlowupGeometry.lean` (template, lines 15--60).

The ambient design: we compactify `𝔸^{m+2} = Spec ℂ[u, t, Z₁, …, Z_m]` by the monomial
embedding `Proj (imageGrade a)` for `a` the monomials of source weight at most `D`
(`monomials (srcWt W) D`), exactly the shape of the OAI compactification of
`𝔸^{m+1}`; the relation `f = t² − F(u)` goes into the centre ideal (`CentreIdeal.lean`).

* `EpaScale W σ`: the scale `D` (a common multiple of the denominators of the source weights and
  of the jet weights, with `D ≥ 8 w₀ (1+σ)`, design P3(i)), the exponents `a = D/v₀`,
  `b_i = D/v_i`, the cutoff `T₀`. `exists_epaScale`: it exists (design P7).
* `ambX sc`: the compactification; `ambProj`, `ambChart` (open immersion of `Spec ℂ[u,t,Z]`),
  `hyp` (`𝒪(1)`) and `hyp_ample`.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

namespace Geo

open CatalanCore.Elliptic
open AlgebraicGeometry CategoryTheory TopologicalSpace
open OAI.PiExponent
open OAI.PiExponentSeshadri.Geometry

variable {m : ℕ}

/-! ### Weight scales (copy of OAI `Approximation/WeightedGeometryScale.lean`, Apache-2.0)

`WeightedGeometryScale` is imported only by the `Admissible*` geometry, so it is not in the vendored
closure; the five lemmas used here are copied (same statements and proofs), under this namespace. -/

theorem exists_power_scale {n : ℕ} (w : Fin n → ℚ) (hw : ∀ i, 0 < w i) :
    ∃ R : ℕ, 0 < R ∧ ∃ e : Fin n → ℕ,
      (∀ i, 0 < e i) ∧ ∀ i, w i * (e i : ℚ) = R := by
  obtain ⟨R,hR,e,he,heq⟩ := positive_rational_weights_common_denominator
    (fun i => (w i)⁻¹) (fun i => inv_pos.mpr (hw i))
  refine ⟨R,hR,e,he,fun i => ?_⟩
  have hi : (w i)⁻¹ = (e i : ℚ) / (R : ℚ) := by
    apply Rat.cast_injective (α := ℝ)
    simpa only [Rat.cast_inv, Rat.cast_div, Rat.cast_natCast] using heq i
  have hR' : (R : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
  have hwi : w i ≠ 0 := (hw i).ne'
  have hi' := (eq_div_iff hR').mp hi
  rw [← hi']
  field_simp

/-- The monomials of weight `≤ R`. -/
noncomputable def monomials {n : ℕ} (w : Fin n → ℚ) (R : ℚ) : Finset (Fin n →₀ ℕ) :=
  (realWeightedSimplex (fun i => (w i : ℝ)) (R : ℝ)).image Finsupp.equivFunOnFinite.symm

@[simp] theorem mem_monomials {n : ℕ} (w : Fin n → ℚ) (hw : ∀ i, 0 < w i)
    (R : ℚ) (a : Fin n →₀ ℕ) :
    a ∈ monomials w R ↔ (∑ i, w i * (a i : ℚ)) ≤ R := by
  classical
  rw [monomials, Finset.mem_image]
  constructor
  · rintro ⟨b,hb,rfl⟩
    have h := (mem_realWeightedSimplex (fun i => by exact_mod_cast hw i)).mp hb
    exact_mod_cast h
  · intro ha
    refine ⟨fun i => a i,?_,Finsupp.equivFunOnFinite_symm_coe a⟩
    apply (mem_realWeightedSimplex (fun i => by exact_mod_cast hw i)).mpr
    exact_mod_cast ha

theorem zero_mem_monomials {n : ℕ} (w : Fin n → ℚ) (hw : ∀ i, 0 < w i)
    (R : ℚ) (hR : 0 ≤ R) : (0 : Fin n →₀ ℕ) ∈ monomials w R := by
  rw [mem_monomials w hw]
  simpa using hR

theorem pure_mem_monomials {n : ℕ} (w : Fin n → ℚ) (hw : ∀ i, 0 < w i)
    (R : ℚ) (e : Fin n → ℕ) (he : ∀ i, w i * (e i : ℚ) = R) (i : Fin n) :
    Finsupp.single i (e i) ∈ monomials w R := by
  classical
  rw [mem_monomials w hw]
  simpa [Finsupp.single_apply] using (he i).le

theorem coordinate_mem_monomials {n : ℕ} (w : Fin n → ℚ) (hw : ∀ i, 0 < w i)
    (R : ℚ) (e : Fin n → ℕ) (hepos : ∀ i, 0 < e i)
    (he : ∀ i, w i * (e i : ℚ) = R) (i : Fin n) :
    Finsupp.single i 1 ∈ monomials w R := by
  classical
  rw [mem_monomials w hw]
  have hi : (1 : ℚ) ≤ e i := by exact_mod_cast hepos i
  have h := mul_le_mul_of_nonneg_left hi (hw i).le
  simpa [Finsupp.single_apply, he] using h

theorem exists_log_cutoff {m : ℕ} (v : Fin (m+1) → ℚ) (hv0 : 0 < v 0) :
    ∃ T : Fin m → ℕ, ∀ i, v i.succ < (T i : ℚ) * v 0 := by
  have h (i : Fin m) : ∃ T : ℕ, v i.succ < (T : ℚ) * v 0 := by
    obtain ⟨T,hT⟩ := exists_nat_gt (v i.succ / v 0)
    exact ⟨T,(div_lt_iff₀ hv0).mp hT⟩
  exact Classical.axiom_of_choice h

/-- `jetWt` is positive. -/
theorem jetWt_pos (W : Weights m) (j : Fin (m + 1)) : 0 < jetWt W j := by
  induction j using Fin.cases with
  | zero => exact W.v₀_pos
  | succ i => exact div_pos (W.w_pos i) W.θ_pos

/-- The scale of the geometry (design E09.10a, P3(i), P7). All fields are chosen before the
centres: `D` depends on the weights and `σ` only. -/
structure EpaScale (W : Weights m) (σ : ℚ) where
  D : ℕ
  D_pos : 0 < D
  /-- `D / srcWt` -/
  src_e : Fin (m + 2) → ℕ
  src_pos : ∀ i, 0 < src_e i
  src_eq : ∀ i, srcWt W i * (src_e i : ℚ) = D
  /-- `a = D / v₀` -/
  a : ℕ
  a_pos : 0 < a
  /-- `b_i = D / v_i = D θ / w_i` -/
  b : Fin m → ℕ
  b_pos : ∀ i, 0 < b i
  a_eq : W.v₀ * (a : ℚ) = D
  b_eq : ∀ i, (W.w i / W.θ) * (b i : ℚ) = D
  T₀ : ℕ
  T₀_gt : ∀ i, W.w i / W.θ < (T₀ : ℚ) * W.v₀
  D_ge : 8 * W.w₀ * (1 + σ) ≤ (D : ℚ)

/-- The scale exists (design P7): common multiples of the denominators of the weights, enlarged
until `D ≥ 8 w₀ (1+σ)`. -/
theorem exists_epaScale (W : Weights m) (σ : ℚ) : Nonempty (EpaScale W σ) := by
  obtain ⟨R₁, hR₁, e, he, heq⟩ :=
    exists_power_scale (srcWt W) (srcWt_pos W)
  obtain ⟨R₂, hR₂, t, ht, htq⟩ :=
    exists_power_scale (jetWt W) (jetWt_pos W)
  obtain ⟨T, hT⟩ := exists_log_cutoff (jetWt W) (jetWt_pos W 0)
  obtain ⟨N, hN⟩ := exists_nat_ge (8 * W.w₀ * (1 + σ))
  have hk₁ : 0 < R₂ * (N + 1) := Nat.mul_pos hR₂ (Nat.succ_pos N)
  have hk₂ : 0 < R₁ * (N + 1) := Nat.mul_pos hR₁ (Nat.succ_pos N)
  have hDpos : 0 < R₁ * R₂ * (N + 1) := Nat.mul_pos (Nat.mul_pos hR₁ hR₂) (Nat.succ_pos N)
  refine ⟨⟨R₁ * R₂ * (N + 1), hDpos, fun i => e i * (R₂ * (N + 1)),
    fun i => Nat.mul_pos (he i) hk₁, ?_, t 0 * (R₁ * (N + 1)), Nat.mul_pos (ht 0) hk₂,
    fun i => t i.succ * (R₁ * (N + 1)), fun i => Nat.mul_pos (ht i.succ) hk₂, ?_, ?_,
    Finset.univ.sup T, ?_, ?_⟩⟩
  · intro i
    have h := heq i
    push_cast
    linear_combination ((R₂ : ℚ) * ((N : ℚ) + 1)) * h
  · have h := htq 0
    simp only [jetWt_zero] at h
    push_cast
    linear_combination ((R₁ : ℚ) * ((N : ℚ) + 1)) * h
  · intro i
    have h := htq i.succ
    simp only [jetWt_succ] at h
    push_cast
    linear_combination ((R₁ : ℚ) * ((N : ℚ) + 1)) * h
  · intro i
    have h1 := hT i
    simp only [jetWt_succ, jetWt_zero] at h1
    have h2 : ((T i : ℕ) : ℚ) ≤ ((Finset.univ.sup T : ℕ) : ℚ) := by
      exact_mod_cast Finset.le_sup (Finset.mem_univ i)
    exact h1.trans_le (mul_le_mul_of_nonneg_right h2 W.v₀_pos.le)
  · have h1 : N + 1 ≤ R₁ * R₂ * (N + 1) := Nat.le_mul_of_pos_left _ (Nat.mul_pos hR₁ hR₂)
    have h2 : (N : ℚ) ≤ ((R₁ * R₂ * (N + 1) : ℕ) : ℚ) := by
      exact_mod_cast (Nat.le_succ N).trans h1
    exact hN.trans h2

variable {W : Weights m} {σ : ℚ}

/-! ### The compactification -/

/-- The index set of the monomial embedding: the monomials of source weight `≤ D`. -/
abbrev Idx (sc : EpaScale W σ) : Type :=
  ↥(monomials (srcWt W) (sc.D : ℚ))

/-- The exponent family `a : Idx → (Fin (m+2) →₀ ℕ)`. -/
def ambExponents (sc : EpaScale W σ) : Idx sc → Fin (m + 2) →₀ ℕ := Subtype.val

/-- The constant monomial `1`. -/
def constantIndex (sc : EpaScale W σ) : Idx sc :=
  ⟨0, zero_mem_monomials (srcWt W) (srcWt_pos W) _
    (by exact_mod_cast sc.D_pos.le)⟩

/-- The coordinate monomials `x_i`. -/
noncomputable def coordinateIndex (sc : EpaScale W σ) (i : Fin (m + 2)) : Idx sc :=
  ⟨Finsupp.single i 1, coordinate_mem_monomials (srcWt W) (srcWt_pos W) _
    sc.src_e sc.src_pos sc.src_eq i⟩

/-- The pure powers `x_i^{D/w_i}`, of weight exactly `D`. -/
noncomputable def pureIndex (sc : EpaScale W σ) (i : Fin (m + 2)) : Idx sc :=
  ⟨Finsupp.single i (sc.src_e i), pure_mem_monomials (srcWt W)
    (srcWt_pos W) _ sc.src_e sc.src_eq i⟩

@[simp] theorem ambExponents_constant (sc : EpaScale W σ) : ambExponents sc (constantIndex sc) = 0 :=
  rfl

@[simp] theorem ambExponents_coordinate (sc : EpaScale W σ) (i : Fin (m + 2)) :
    ambExponents sc (coordinateIndex sc i) = Finsupp.single i 1 := rfl

@[simp] theorem ambExponents_pure (sc : EpaScale W σ) (i : Fin (m + 2)) :
    ambExponents sc (pureIndex sc i) = Finsupp.single i (sc.src_e i) := rfl

/-- Every exponent of the family has source weight `≤ D`. -/
theorem ambExponents_weight_le (sc : EpaScale W σ) (j : Idx sc) :
    (∑ i, srcWt W i * (ambExponents sc j i : ℚ)) ≤ sc.D :=
  (mem_monomials (srcWt W) (srcWt_pos W) _ j.val).mp j.property

instance idx_finite (sc : EpaScale W σ) : Finite (Idx sc) := inferInstance

instance idx_nonempty (sc : EpaScale W σ) : Nonempty (Idx sc) := ⟨constantIndex sc⟩

/-- The compactification `P` of `𝔸^{m+2}`: `Proj` of the monomial algebra of source weight `≤ D`. -/
noncomputable abbrev ambX (sc : EpaScale W σ) : Scheme :=
  Proj (WeightedCompactification.imageGrade (R := ℂ) (ambExponents sc))

/-- The affine ambient space `Spec ℂ[u, t, Z]`. -/
noncomputable abbrev ambSpace (m : ℕ) : Scheme := Spec (CommRingCat.of (AmbRing m))

/-- The base `Spec ℂ`. -/
noncomputable abbrev baseC : Scheme := Spec (CommRingCat.of ℂ)

/-- The structure map `Spec ℂ[u,t,Z] → Spec ℂ`. -/
noncomputable def ambStructureMap (m : ℕ) : ambSpace m ⟶ baseC :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ (AmbRing m)))

/-- The structure map of `P`. -/
noncomputable def ambProj (sc : EpaScale W σ) : ambX sc ⟶ baseC :=
  WeightedCompactification.projection (ambExponents sc)

instance ambProj_proper (sc : EpaScale W σ) : IsProper (ambProj sc) := by
  dsimp [ambProj]
  infer_instance

/-- The open immersion `𝔸^{m+2} → P`. -/
noncomputable def ambChart (sc : EpaScale W σ) : ambSpace m ⟶ ambX sc :=
  WeightedCompactification.affineChartMap (R := ℂ) (ambExponents sc) (constantIndex sc)
    (ambExponents_constant sc) (coordinateIndex sc) (ambExponents_coordinate sc)

instance ambChart_isOpenImmersion (sc : EpaScale W σ) : IsOpenImmersion (ambChart sc) := by
  dsimp [ambChart]
  infer_instance

/-- The origin `0 ∈ 𝔸^{m+2}` as a prime of `ℂ[u,t,Z]` (used for nonemptiness only). -/
noncomputable def ambOrigin (m : ℕ) : ambSpace m :=
  ⟨OAI.PiExponent.WeightedBezout.pointIdeal (0 : Fin (m + 2) → ℂ), inferInstance⟩

instance ambX_nonempty (sc : EpaScale W σ) : Nonempty (ambX sc) := ⟨ambChart sc (ambOrigin m)⟩

instance ambX_isIntegral (sc : EpaScale W σ) : IsIntegral (ambX sc) := by infer_instance

instance ambX_isLocallyNoetherian (sc : EpaScale W σ) : IsLocallyNoetherian (ambX sc) :=
  LocallyOfFiniteType.isLocallyNoetherian (ambProj sc)

instance ambX_compact (sc : EpaScale W σ) : CompactSpace (ambX sc) :=
  QuasiCompact.compactSpace_of_compactSpace (ambProj sc)

instance ambX_isNoetherian (sc : EpaScale W σ) : IsNoetherian (ambX sc) := {}

instance ambChart_quasiCompact (sc : EpaScale W σ) : QuasiCompact (ambChart sc) := by
  infer_instance

/-- The chart lies over `Spec ℂ`. -/
theorem ambChart_over (sc : EpaScale W σ) : ambChart sc ≫ ambProj sc = ambStructureMap m :=
  CurveMonomialMap.affineChartMap_projection (ambExponents sc) (constantIndex sc)
    (ambExponents_constant sc) (coordinateIndex sc) (ambExponents_coordinate sc)

/-- The hyperplane bundle `𝒪(1)` of the monomial embedding. -/
noncomputable def hyp (sc : EpaScale W σ) : LineBundle (ambX sc) :=
  WeightedCompactification.lineBundle (ambExponents sc)

theorem hyp_ample (sc : EpaScale W σ) : (hyp sc).IsAmple :=
  WeightedCompactification.lineBundle_ample (ambExponents sc)

end Geo

end CatalanCore.Elliptic.EPA
