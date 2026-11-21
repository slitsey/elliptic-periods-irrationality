module

public import CatalanCore.Elliptic.EPA.Frame
public import OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent
public import OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.StdBasis

/-!
# The tangent graph and the adjunction of `u` (row E09.5a)

Labels refer to `D2-DESIGN-2026-11-20.md` §5 E09.5a and to CM §7 (l.1265–1295, l.1767–1790).

Let `Q` be a prime of `R = AmbRing m = ℂ[u, t, Z]` with `f = relation ch ∈ Q`, let `K = Frac(R/Q)`
be its literal residue field (`Q.ResidueField`), `J̄ = F′(ū)` and `t̄` the residues of
`F′(u)` and `t`. The polynomial tangent space `T_Q ⊂ K^{m+2}` (coordinates `(u, t, Z₁, …, Z_m)`,
`OAI.PiExponent.polynomialTangent`) satisfies `J̄ v_u = 2 t̄ v_t` (differentiating `f`), so for
`J̄ ≠ 0` it is the image of the **graph map**

  `G (v₀, v₁, …, v_m) = (2 t̄ v₀ / J̄, v₀, v₁, …, v_m)`.

* `graphMap J tbar`: the linear map `G` (`J`, `tbar` free field elements).
* `intrinsicTangent ch Q = G⁻¹(T_Q) ⊂ K^{m+1}` (the intrinsic tangent in the `(t, Z)` coordinates;
  the hypothesis `J̄ ≠ 0` is not needed to define it, only to relate it to `T_Q`).
* `tangent_le_graph`, `map_graphMap_intrinsicTangent`: `T_Q = G (intrinsicTangent ch Q)`.
* `IsIntrinsicCoordinateNormalBasis ch Q S`: `S ⊂ Fin (m+1)` is a coordinate normal basis of the
  intrinsic quotient `N = K^{m+1}/V`, `V = intrinsicTangent ch Q`.
* `normalBasis_adjoin_u`: `S` is an intrinsic coordinate normal basis iff `{u} ∪ S` (shifted by
  `Fin.succ`) is an ambient coordinate normal basis of `K^{m+2}/T_Q`.
* `IsFrameNormalBasis ch Q hJ T`: `T` is a normal basis of `N` for the frame vectors
  `b₀ = (−J̄, 1, …, 1)`, `b_i = e_i` (OAI `NormalBasisRigidity.frameBasis` with `y = −J̄`).
* `graphMap_frameBasis`: `G b_j` is the residue coefficient vector of the frame derivation
  `frameDeriv ch j` (CM l.1286–1292): the two frames agree.

The shape follows OAI `Jets/NormalFrameBasis.lean` and `Jets/PolynomialTangentDifferential.lean`
(openai/math fd4aeeb2, Apache License 2.0, Copyright OpenAI), used as imports.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

open CatalanCore.Elliptic
open OAI.PiExponent
open OAI.PiExponent.NormalBasisRigidity

/-! ### Generic linear algebra: adjoining a kernel vector to a normal basis -/

section LinearAlgebra

variable {K N N' : Type*} [Field K] [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N']

/-- Let `f : N → N'` be onto with kernel `K · v₀`, `v₀ ≠ 0`, and `f (v (j+1)) = v' j`. Then
`{v₀} ∪ {v (j+1) : j ∈ S}` is a normal basis of `N` iff `S` is a normal basis of `N'` for `v'`. -/
theorem isNormalBasis_insert_zero_succ_iff {n : ℕ} (f : N →ₗ[K] N')
    (hf : Function.Surjective f) (v : Fin (n + 1) → N) (v' : Fin n → N')
    (h0 : v 0 ≠ 0) (hf0 : f (v 0) = 0) (hker : ∀ x, f x = 0 → ∃ c : K, x = c • v 0)
    (hs : ∀ j, f (v j.succ) = v' j) (S : Finset (Fin n)) :
    IsNormalBasis (K := K) v (insert 0 (S.map (Fin.succEmb _))) ↔ IsNormalBasis (K := K) v' S := by
  classical
  have h0S : (0 : Fin (n + 1)) ∉ S.map (Fin.succEmb _) := by
    simp [Finset.mem_map]
  have hsum : ∀ g : Fin (n + 1) → K, ∑ a ∈ insert 0 (S.map (Fin.succEmb _)), g a • v a
      = g 0 • v 0 + ∑ j ∈ S, g j.succ • v j.succ := by
    intro g
    rw [Finset.sum_insert h0S, Finset.sum_map]
    rfl
  constructor
  · rintro ⟨hind, hspan⟩
    refine ⟨?_, ?_⟩
    · rw [linearIndepOn_finset_iff] at hind ⊢
      intro g hg j hj
      obtain ⟨c, hc⟩ := hker (∑ j ∈ S, g j • v j.succ) (by
        rw [map_sum]; simpa [map_smul, hs] using hg)
      have := hind (Fin.cons (-c) g) (by
        rw [hsum]
        simp [hc]) j.succ (by simp [hj])
      simpa using this
    · apply top_unique
      have h1 : (⊤ : Submodule K N') = Submodule.map f
          (Submodule.span K (v '' ↑(insert 0 (S.map (Fin.succEmb _))))) := by
        rw [hspan, Submodule.map_top, LinearMap.range_eq_top.mpr hf]
      rw [h1, Submodule.map_span]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      rcases Finset.mem_insert.mp ha with rfl | ha
      · simp [hf0]
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp ha
        have : f (v (Fin.succEmb _ j)) = v' j := hs j
        rw [SetLike.mem_coe, this]
        exact Submodule.subset_span ⟨j, hj, rfl⟩
  · rintro ⟨hind, hspan⟩
    refine ⟨?_, ?_⟩
    · rw [linearIndepOn_finset_iff] at hind ⊢
      intro g hg a ha
      rw [hsum] at hg
      have hg' : ∑ j ∈ S, g j.succ • v' j = 0 := by
        have := congrArg f hg
        rw [map_add, map_smul, hf0, smul_zero, zero_add, map_sum, map_zero] at this
        simpa [map_smul, hs] using this
      have hS := hind (fun j => g j.succ) hg'
      have hg0 : g 0 = 0 := by
        have : g 0 • v 0 = 0 := by
          have h2 : ∑ j ∈ S, g j.succ • v j.succ = 0 :=
            Finset.sum_eq_zero fun j hj => by rw [hS j hj, zero_smul]
          rwa [h2, add_zero] at hg
        exact (smul_eq_zero.mp this).resolve_right h0
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hg0
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp ha
        exact hS j hj
    · rw [eq_top_iff]
      intro x _
      set P := Submodule.span K (v '' ↑(insert 0 (S.map (Fin.succEmb _)))) with hP
      have hv0 : v 0 ∈ P := Submodule.subset_span ⟨0, by simp, rfl⟩
      have hvs : ∀ j ∈ S, v j.succ ∈ P := fun j hj =>
        Submodule.subset_span ⟨j.succ, by simp [Finset.mem_map, hj], rfl⟩
      have hfx : f x ∈ P.map f := by
        have : f x ∈ Submodule.span K (v' '' ↑S) := by rw [hspan]; trivial
        refine Submodule.span_le.mpr ?_ this
        rintro _ ⟨j, hj, rfl⟩
        exact ⟨v j.succ, hvs j hj, hs j⟩
      obtain ⟨p, hp, hpx⟩ := hfx
      obtain ⟨c, hc⟩ := hker (x - p) (by rw [map_sub, ← hpx, sub_self])
      have : x = p + c • v 0 := by rw [← hc]; abel
      rw [this]
      exact P.add_mem hp (P.smul_mem c hv0)

end LinearAlgebra

/-! ### The graph map -/

section Graph

variable {m : ℕ} {K : Type*} [Field K]

/-- `v ↦ (2 t̄ v₀ / J, v₀, v₁, …, v_m)`: the coordinates are `(u, t, Z₁, …, Z_m)` (CM l.1779). -/
def graphMap (J tbar : K) : (Fin (m + 1) → K) →ₗ[K] (Fin (m + 2) → K) where
  toFun v := Fin.cons (2 * tbar * v 0 / J) v
  map_add' v w := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Pi.add_apply]; ring
    · simp
  map_smul' c v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
    · simp

@[simp] theorem graphMap_apply_zero (J tbar : K) (v : Fin (m + 1) → K) :
    graphMap J tbar v 0 = 2 * tbar * v 0 / J := rfl

@[simp] theorem graphMap_apply_succ (J tbar : K) (v : Fin (m + 1) → K) (j : Fin (m + 1)) :
    graphMap J tbar v j.succ = v j := rfl

/-- Drop the `u` coordinate. -/
def dropU : (Fin (m + 2) → K) →ₗ[K] (Fin (m + 1) → K) := LinearMap.funLeft K K Fin.succ

@[simp] theorem dropU_apply (x : Fin (m + 2) → K) (j : Fin (m + 1)) : dropU x j = x j.succ := rfl

@[simp] theorem dropU_graphMap (J tbar : K) (v : Fin (m + 1) → K) :
    dropU (graphMap J tbar v) = v := rfl

theorem graphMap_injective (J tbar : K) : Function.Injective (graphMap (m := m) J tbar) :=
  fun v w h => by rw [← dropU_graphMap J tbar v, h, dropU_graphMap]

/-- The image of the graph map: `J x_u = 2 t̄ x_t`. -/
theorem mem_range_graphMap_iff {J : K} (hJ : J ≠ 0) (tbar : K) (x : Fin (m + 2) → K) :
    x ∈ LinearMap.range (graphMap J tbar) ↔ J * x 0 = 2 * tbar * x 1 := by
  constructor
  · rintro ⟨w, rfl⟩
    have h1 : (1 : Fin (m + 2)) = Fin.succ (0 : Fin (m + 1)) := one_eq_succ_zero
    rw [h1, graphMap_apply_succ, graphMap_apply_zero]
    field_simp
  · intro h
    refine ⟨dropU x, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have h1 : (1 : Fin (m + 2)) = Fin.succ (0 : Fin (m + 1)) := one_eq_succ_zero
      rw [graphMap_apply_zero, dropU_apply, ← h1]
      field_simp
      linear_combination -h
    · rfl

end Graph

/-! ### The residue field data of a prime -/

section Prime

variable {m : ℕ} (ch : OriginChart) (Q : Ideal (AmbRing m)) [Q.IsPrime]

/-- `J̄ = F′(ū)`, the image of `F′(u)` in the residue field `Frac(R/Q)`. -/
noncomputable def resJ : Q.ResidueField :=
  primeResidueMap Q (Polynomial.aeval (uV : AmbRing m) (Polynomial.derivative (Fc ch)))

/-- `t̄`, the image of `t` in the residue field. -/
noncomputable def resT : Q.ResidueField := primeResidueMap Q (tV : AmbRing m)

/-- A vector is in the polynomial tangent space iff it annihilates the evaluated gradient of
every element of `Q`. -/
theorem mem_polynomialTangent_iff (v : Fin (m + 2) → Q.ResidueField) :
    v ∈ polynomialTangent (primeResidueMap Q) Q ↔
      ∀ p ∈ Q, ∑ i, primeResidueMap Q (MvPolynomial.pderiv i p) * v i = 0 := by
  unfold polynomialTangent
  rw [LinearMap.mem_ker]
  constructor
  · intro h p hp
    exact congrFun h ⟨p, hp⟩
  · intro h
    funext p
    exact h p.1 p.2

/-- Differentiating `f = t² − F(u) ∈ Q`: every tangent vector satisfies `J̄ v_u = 2 t̄ v_t`
(CM l.1783). -/
theorem tangent_relation (hf : relation ch ∈ Q) {v : Fin (m + 2) → Q.ResidueField}
    (hv : v ∈ polynomialTangent (primeResidueMap Q) Q) :
    resJ ch Q * v 0 = 2 * resT Q * v 1 := by
  have h := (mem_polynomialTangent_iff Q v).mp hv _ hf
  have key : ∀ i : Fin (m + 2), primeResidueMap Q (MvPolynomial.pderiv i (relation ch)) * v i =
      (if i = 1 then 2 * resT Q * v i else 0) - (if i = 0 then resJ ch Q * v i else 0) := by
    intro i
    rw [pderiv_relation]
    by_cases h1 : i = 1
    · have h0 : i ≠ 0 := by rw [h1]; exact zero_ne_one_amb.symm
      have h2 : primeResidueMap Q (2 : AmbRing m) = 2 := map_ofNat _ 2
      simp [h1, h0, resT, resJ, map_sub, map_mul, h2]
    · by_cases h0 : i = 0
      · simp [h1, h0, resT, resJ, map_sub, map_mul]
      · simp [h1, h0]
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_sub_distrib] at h
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  linear_combination -h

/-- `T_Q ⊆ G(K^{m+1})` (CM l.1783: the ambient tangent is the graph). -/
theorem tangent_le_graph (hJ : resJ ch Q ≠ 0) (hf : relation ch ∈ Q) :
    polynomialTangent (primeResidueMap Q) Q ≤
      LinearMap.range (graphMap (resJ ch Q) (resT Q)) := fun _ hv =>
  (mem_range_graphMap_iff hJ _ _).mpr (tangent_relation ch Q hf hv)

/-- The intrinsic tangent `V = G⁻¹(T_Q) ⊂ K^{m+1}` in the `(t, Z)` coordinates (CM l.1779). -/
noncomputable def intrinsicTangent : Submodule Q.ResidueField (Fin (m + 1) → Q.ResidueField) :=
  (polynomialTangent (primeResidueMap Q) Q).comap (graphMap (resJ ch Q) (resT Q))

theorem mem_intrinsicTangent_iff (w : Fin (m + 1) → Q.ResidueField) :
    w ∈ intrinsicTangent ch Q ↔
      graphMap (resJ ch Q) (resT Q) w ∈ polynomialTangent (primeResidueMap Q) Q := Iff.rfl

/-- `T_Q = G(V)` (CM l.1783). -/
theorem map_graphMap_intrinsicTangent (hJ : resJ ch Q ≠ 0) (hf : relation ch ∈ Q) :
    (intrinsicTangent ch Q).map (graphMap (resJ ch Q) (resT Q)) =
      polynomialTangent (primeResidueMap Q) Q := by
  unfold intrinsicTangent
  rw [Submodule.map_comap_eq, inf_eq_right.mpr (tangent_le_graph ch Q hJ hf)]

/-- The intrinsic quotient `N = K^{m+1}/V` and the images of the coordinate vectors: a set `S` is
an intrinsic coordinate normal basis when these images indexed by `S` form a basis of `N`. -/
def IsIntrinsicCoordinateNormalBasis (S : Finset (Fin (m + 1))) : Prop :=
  IsNormalBasis (K := Q.ResidueField)
    (fun i : Fin (m + 1) =>
      (intrinsicTangent ch Q).mkQ (Pi.basisFun Q.ResidueField (Fin (m + 1)) i)) S

/-- Normal bases of `N` for the frame vectors `b₀ = (−J̄, 1, …, 1)`, `b_i = e_i`. -/
def IsFrameNormalBasis (hJ : resJ ch Q ≠ 0) (T : Finset (Fin (m + 1))) : Prop :=
  IsNormalBasis (K := Q.ResidueField)
    (fun j : Fin (m + 1) => (intrinsicTangent ch Q).mkQ
      (frameBasis m (-(resJ ch Q)) (neg_ne_zero.mpr hJ) j)) T

/-- Adjoining `u` (CM l.1286–1292): `S` is an intrinsic coordinate normal basis iff `{u} ∪ S` is an
ambient coordinate normal basis of `K^{m+2}/T_Q`. -/
theorem normalBasis_adjoin_u (hJ : resJ ch Q ≠ 0) (hf : relation ch ∈ Q)
    (S : Finset (Fin (m + 1))) :
    IsIntrinsicCoordinateNormalBasis ch Q S ↔
      IsNormalBasis (K := Q.ResidueField)
        (fun i : Fin (m + 2) => (polynomialTangent (primeResidueMap Q) Q).mkQ
          (Pi.basisFun Q.ResidueField (Fin (m + 2)) i))
        (insert 0 (S.map (Fin.succEmb _))) := by
  classical
  set T := polynomialTangent (primeResidueMap Q) Q with hT
  set V := intrinsicTangent ch Q with hV
  set G := graphMap (m := m) (resJ ch Q) (resT Q) with hG
  have hTV : T ≤ V.comap dropU := by
    intro x hx
    obtain ⟨w, rfl⟩ := tangent_le_graph ch Q hJ hf hx
    rw [Submodule.mem_comap, dropU_graphMap]
    exact hx
  have hmem : ∀ x, x ∈ T → dropU x ∈ V := fun x hx => hTV hx
  refine Iff.symm ?_
  unfold IsIntrinsicCoordinateNormalBasis
  refine isNormalBasis_insert_zero_succ_iff (T.mapQ V dropU hTV) ?_ _ _ ?_ ?_ ?_ ?_ S
  · -- surjective
    intro y
    obtain ⟨w, rfl⟩ := V.mkQ_surjective y
    exact ⟨T.mkQ (G w), by simp [Submodule.mapQ_apply]; rfl⟩
  · -- the vector `u` is nonzero modulo `T`
    simp only [Pi.basisFun_apply, ne_eq, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    intro h
    obtain ⟨w, hw⟩ := tangent_le_graph ch Q hJ hf h
    have := (mem_range_graphMap_iff hJ (resT Q) (Pi.single (0 : Fin (m + 2)) 1)).mp ⟨w, hw⟩
    simp [one_ne_zero.symm, zero_ne_one_amb.symm] at this
    exact hJ (by simpa using this)
  · -- `u` dies
    simp only [Pi.basisFun_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
    have : dropU (Pi.single (0 : Fin (m + 2)) (1 : Q.ResidueField)) = 0 := by
      funext j
      simp [Pi.single_apply, Fin.succ_ne_zero]
    rw [this]
    simp
  · -- the kernel is spanned by `u`
    intro x hx
    obtain ⟨y, rfl⟩ := T.mkQ_surjective x
    simp only [Submodule.mapQ_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    refine ⟨y 0 - 2 * resT Q * y 1 / resJ ch Q, ?_⟩
    have h1 : y - G (dropU y) = (y 0 - 2 * resT Q * y 1 / resJ ch Q) •
        Pi.single (0 : Fin (m + 2)) (1 : Q.ResidueField) := by
      have h1 : (1 : Fin (m + 2)) = Fin.succ (0 : Fin (m + 1)) := one_eq_succ_zero
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Pi.sub_apply, hG, graphMap_apply_zero, dropU_apply, Pi.smul_apply,
          Pi.single_eq_same, smul_eq_mul, mul_one]
        rw [← h1]
      · simp [hG, Pi.single_apply, Fin.succ_ne_zero]
    have h3 : T.mkQ (G (dropU y)) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx
    have h2 : (T.mkQ y : _ ⧸ T) = T.mkQ (y - G (dropU y)) := by
      rw [map_sub, h3, sub_zero]
    rw [h2, h1, map_smul]
    simp [Pi.basisFun_apply]
  · -- the other vectors
    intro j
    simp only [Pi.basisFun_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
    congr 1
    funext k
    simp [Pi.single_apply, Fin.succ_inj]

/-- The two frames agree (CM l.1286–1292): `G (b_j)` is the residue coefficient vector of the frame
derivation `D_j` (`D₀ = −2t ∂_u − F′(u) ∂_t + Σ ∂_{Z_i}`, `D_i = ∂_{Z_i}`). -/
theorem graphMap_frameBasis (hJ : resJ ch Q ≠ 0) (j : Fin (m + 1)) :
    graphMap (resJ ch Q) (resT Q)
        (frameBasis m (-(resJ ch Q)) (neg_ne_zero.mpr hJ) j) =
      fun i : Fin (m + 2) => primeResidueMap Q (frameDeriv ch j (MvPolynomial.X i)) := by
  have hJdef : primeResidueMap Q
      (Polynomial.aeval (uV : AmbRing m) (Polynomial.derivative (Fc ch))) = resJ ch Q := rfl
  have hTdef : primeResidueMap Q (tV : AmbRing m) = resT Q := rfl
  have n1 : (1 : Fin (m + 2)) ≠ 0 := zero_ne_one_amb.symm
  have n2 : (0 : Fin (m + 2)) ≠ 1 := zero_ne_one_amb
  have n3 : ∀ i : Fin m, (i.succ.succ : Fin (m + 2)) ≠ 0 := fun i => Fin.succ_ne_zero _
  have n4 : ∀ i : Fin m, (0 : Fin (m + 2)) ≠ i.succ.succ := zero_ne_succ_succ
  have n5 : ∀ i : Fin m, (1 : Fin (m + 2)) ≠ i.succ.succ := one_ne_succ_succ
  have n6 : ∀ i : Fin m, (i.succ.succ : Fin (m + 2)) ≠ 1 := fun i => (one_ne_succ_succ i).symm
  have hA : algebraMap ℂ Q.ResidueField 2 = 2 := map_ofNat _ 2
  induction j using Fin.cases with
  | zero =>
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [graphMap_apply_zero, frameBasis_zero_zero, frameDeriv_zero_apply]
      simp [hJdef, hTdef, MvPolynomial.pderiv_X, Pi.single_apply, n1, n2, n3, n4, hA]
      field_simp
    · refine Fin.cases ?_ (fun k => ?_) i
      · have hz : ∀ k : Fin m, MvPolynomial.pderiv k.succ.succ
            (MvPolynomial.X (Fin.succ (0 : Fin (m + 1))) : AmbRing m) = 0 := fun k => by
          rw [MvPolynomial.pderiv_X]
          simp [Pi.single_apply, n6 k, ← one_eq_succ_zero]
        simp only [graphMap_apply_succ, frameBasis_zero_zero, frameDeriv_zero_apply, hz,
          Finset.sum_const_zero]
        simp [hJdef, hTdef, MvPolynomial.pderiv_X, Pi.single_apply, n1, n2, n3, n4, hA]
      · simp only [graphMap_apply_succ, frameBasis_zero_succ, frameDeriv_zero_apply]
        simp [hJdef, hTdef, MvPolynomial.pderiv_X, Pi.single_apply, n1, n2, n3, n4, n5, n6, hA,
          Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  | succ j =>
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [Pi.single_apply, n3, n4]
    · refine Fin.cases ?_ (fun k => ?_) i
      · simp only [graphMap_apply_succ, frameBasis_succ, frameDeriv_succ]
        simp [MvPolynomial.pderiv_X, Pi.single_apply, Fin.succ_ne_zero, n5, n6]
      · simp only [graphMap_apply_succ, frameBasis_succ, frameDeriv_succ]
        simp [MvPolynomial.pderiv_X, Pi.single_apply, Fin.succ_inj]

end Prime

end CatalanCore.Elliptic.EPA
