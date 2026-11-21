module

public import CatalanCore.Elliptic.EPA.Local.FixedBezoutPrime
public import CatalanCore.Elliptic.EPA.Local.Rectangular
public import CatalanCore.Elliptic.EPA.Rigid.Graph
public import CatalanCore.Elliptic.EPA.Rigid.Quartic
public import CatalanCore.Elliptic.EPA.Persistence
public import CatalanCore.Elliptic.EPA.Numerics
public import OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts
public import OAI.NumberTheory.PiExponent.Jets.TransverseWeightedMultiplicity
public import OAI.NumberTheory.PiExponent.Approximation.RectangularVolume

/-!
# Quartic matched lengths and the persistent comparison (row E09.4c)

Labels refer to `D2-DESIGN-2026-11-20.md` §5 E09.4c and to CM `cm-2610.31112-nolean.tex`
l.1380–1450 (the upper bound with the factor `4`, the corrected growth constants, the comparison
constant `C₄`) and input (A) l.3034–3055.

Setting: `R = AmbRing m = ℂ[u, t, Z₁, …, Z_m]`, `f = relation ch = t² − F(u)`, `P ∈ R` with source
degree `≤ N`, `N ≥ 8 w₀`, `ε = ε₀ = eps0 W σ`, `s ≤ ε N`, `I_s = derivIdeal ch P (jetWt W) s`, and
`Q` a prime minimal over `I_s` with `F′(ū) ≠ 0` in `Frac(R/Q)` (`resJ ch Q ≠ 0`). The hypothesis
`hpers` is the persistence conclusion of `persistent_prime` (E09.3): every frame word of jet cost at
most `δ = ε N / (m + 3)` maps `I_s` into `Q`.

* `EllUniformRectangles W δ`: all the rectangle cutoffs `⌈δ / (k κ_{B j})⌉`, `1 ≤ k ≤ m + 1`, are at
  least `2` (OAI `PersistentWeightComparison.UniformRectangles`, with budget `δ`).
* `EllNormalProductComparison W ch Q hJ C`: for every coordinate normal basis `S` (E09.5a
  `IsIntrinsicCoordinateNormalBasis`) and every frame normal basis `T` (E09.5a `IsFrameNormalBasis`)
  `∏_{i∈S} r_i ≤ C ∏_{j∈T} κ_j`.
* `ell_persistent_comparison`: the comparison holds with `C = C₄` (`C4 W σ`).

Proof (CM l.1380–1450). `S`, `T` have the same cardinality `k` (normal bases of the same quotient).
For `k = 0` the claim is `1 ≤ C₄`. For `k ≥ 1`: put `A = {u} ∪ S`. By E09.5a `A` is an ambient
coordinate normal basis; the fixed equation `f` survives the slice (its `u⁴` term cannot cancel,
`qrt_relation_slice_ne_zero`), so the fixed-hypersurface bound `prime_length_fixed_equation_le`
(E09.4a, with `ρ = srcWt`, `d₀ = 8 w₀`, `M = g N`; all generators of `I_s` have source degree `≤ g N`
by E09.1) gives `ℓ_Q(I_s) ≤ 8 w₀ (g N)^k / ∏_A ρ ≤ 4 (g N)^k / ∏_S r` (`ρ_{succ i} ≥ r_i`, `ρ_u = 2 w₀`;
this is CM's factor `4` bound, which is weaker than the case split of CM l.1401–1409 only when `0 ∈ S`).
The Taylor lower bound `prime_rectangular_length_lower` (E09.4b) for the frame `frameDeriv ch`
(whose graph lifts are the frame normal vectors, `graphMap_frameBasis`, E09.5a) with the ceiling
rectangles gives `ℓ_Q(I_s) ≥ δ^k / (k^k ∏_T κ)`. Same prime, same ideal, same field. The scalar
`4 g^k k^k ((m+3)/ε)^k ≤ C₄` is `coeff_bound` (E09.0).

The proof of the lower and upper bounds is that of OAI `PersistentWeightComparison`
(`logarithmic_normal_comparison`, openai/math fd4aeeb2, Apache License 2.0, Copyright OpenAI), with
the two bounds replaced by E09.4a and E09.4b.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA.Local

noncomputable section

open scoped BigOperators
open CatalanCore.Elliptic CatalanCore.Elliptic.EPA
open OAI OAI.PiExponent OAI.PiExponent.NormalBasisRigidity OAI.PiExponent.NormalBasisProducts
open OAI.PiExponent.TransverseWeightedMultiplicity OAI.PiExponent.CoordinateSliceComparison
open OAI.PiExponent.CoordinateFiniteSlice OAI.PiExponent.WeightedSliceDegree

variable {m : ℕ}

/-! ### Elementary facts on the weights and constants -/

theorem qrt_radWt_pos (W : Weights m) (j : Fin (m + 1)) : 0 < radWt W j := by
  induction j using Fin.cases with
  | zero => rw [radWt_zero]; exact W.w₀_pos
  | succ i => rw [radWt_succ]; exact W.w_pos i

theorem qrt_jetWt_pos (W : Weights m) (j : Fin (m + 1)) : 0 < jetWt W j := by
  induction j using Fin.cases with
  | zero => rw [jetWt_zero]; exact W.v₀_pos
  | succ i => rw [jetWt_succ]; exact div_pos (W.w_pos i) W.θ_pos

/-- The ambient source weight of `Z_i`/`t` dominates the intrinsic radius weight. -/
theorem qrt_radWt_le_srcWt (W : Weights m) (j : Fin (m + 1)) : radWt W j ≤ srcWt W j.succ := by
  induction j using Fin.cases with
  | zero =>
    have h : srcWt W (Fin.succ (0 : Fin (m + 1))) = 4 * W.w₀ := rfl
    rw [h, radWt_zero]
    have := W.w₀_pos
    linarith
  | succ i =>
    exact le_of_eq (by rw [radWt_succ, srcWt_succ_succ])

theorem qrt_one_le_gConst (W : Weights m) {σ : ℚ} (hσ : 0 < σ) : 1 ≤ gConst W σ := by
  have h1 := W.w₀_pos
  have h2 := W.v₀_pos
  have h3 := eps0_pos W hσ
  unfold gConst
  have : 0 ≤ 2 * W.w₀ / W.v₀ * eps0 W σ := by positivity
  linarith

theorem qrt_one_le_An (n : ℕ) {s : ℚ} (hs : 0 < s) : 1 ≤ An n s := by
  have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  have h1 : (1 : ℚ) ≤ ((n : ℚ) + 2) ^ (n + 2) := one_le_pow₀ (by linarith)
  have hq : (0 : ℚ) ≤ ((n : ℚ) + 2) / s := by positivity
  have h2 : (1 : ℚ) ≤ (1 + ((n : ℚ) + 2) / s) ^ (n + 2) := one_le_pow₀ (by linarith)
  have h3 := mul_le_mul h1 h2 zero_le_one (by linarith)
  unfold An
  nlinarith [h3]

theorem qrt_one_le_C4 (W : Weights m) {σ : ℚ} (hσ : 0 < σ) : 1 ≤ C4 W σ := by
  have h1 := qrt_one_le_An m hσ
  have h2 := An_pos (m + 1) (eps0_pos W hσ)
  unfold C4
  have : 0 ≤ 4 * (2 : ℚ) ^ (m + 3) * An (m + 1) (eps0 W σ) :=
    mul_nonneg (by positivity) h2.le
  linarith

/-- `SrcDeg` in the form of the fixed-hypersurface bound (`∑ d_i ρ_i ≤ N`, `ρ = srcWt`). -/
theorem qrt_srcDeg_sum {W : Weights m} {N : ℝ} {P : AmbRing m} (h : SrcDeg W N P) :
    ∀ d ∈ P.support, (∑ i ∈ d.support, (d i : ℝ) * ((srcWt W i : ℚ) : ℝ)) ≤ N := by
  intro d hd
  have := h d hd
  simpa only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, srcRho] using this

theorem qrt_cast_jet_sum (W : Weights m) (word : List (Fin (m + 1))) :
    ((((word.map (jetWt W)).sum : ℚ)) : ℝ) =
      (word.map (fun j : Fin (m + 1) => ((jetWt W j : ℚ) : ℝ))).sum := by
  induction word with
  | nil => simp
  | cons a w ih => simp [List.sum_cons, ih]

/-! ### Uniform rectangles -/

/-- All the ceiling-rectangle cutoffs for the budget `δ` are at least `2`
(OAI `PersistentWeightComparison.UniformRectangles`). -/
def EllUniformRectangles (W : Weights m) (δ : ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → k ≤ m + 1 → ∀ B : Fin k → Fin (m + 1), ∀ i,
    2 ≤ rectangularCutoff (fun j => ((jetWt W (B j) : ℚ) : ℝ)) δ i

/-- A sufficient condition: `(m+1) κ_j < δ` for all `j`. -/
theorem ellUniformRectangles_of_lt (W : Weights m) {δ : ℝ}
    (h : ∀ j : Fin (m + 1), ((m : ℝ) + 1) * ((jetWt W j : ℚ) : ℝ) < δ) :
    EllUniformRectangles W δ := by
  intro k hk hkm B i
  apply two_le_rectangularCutoff hk (fun j => ((jetWt W (B j) : ℚ) : ℝ))
    (fun j => by exact_mod_cast qrt_jetWt_pos W (B j)) i
  have hkR : (k : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hkm
  have hpos : (0 : ℝ) < ((jetWt W (B i) : ℚ) : ℝ) := by exact_mod_cast qrt_jetWt_pos W (B i)
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hkR hpos.le) (h (B i))

/-! ### The comparison statement -/

/-- For all coordinate normal bases `S` and frame normal bases `T` of the intrinsic quotient,
`∏_{i∈S} r_i ≤ C ∏_{j∈T} κ_j`. -/
def EllNormalProductComparison (W : Weights m) (ch : OriginChart) (Q : Ideal (AmbRing m))
    [Q.IsPrime] (hJ : resJ ch Q ≠ 0) (C : ℝ) : Prop :=
  ∀ S T : Finset (Fin (m + 1)), IsIntrinsicCoordinateNormalBasis ch Q S →
    IsFrameNormalBasis ch Q hJ T →
    ∏ i ∈ S, ((radWt W i : ℚ) : ℝ) ≤ C * ∏ j ∈ T, ((jetWt W j : ℚ) : ℝ)

/-! ### Generators of the derivative ideal -/

/-- The generating set `{f} ∪ {D_ν P : c(ν) ≤ s}` of `derivIdeal`. -/
def qrtGenSet (ch : OriginChart) (P : AmbRing m) (v : Fin (m + 1) → ℚ) (s : ℚ) :
    Set (AmbRing m) :=
  {relation ch} ∪ {g | ∃ word : List (Fin (m + 1)), (word.map v).sum ≤ s ∧
    g = frameWord ch word P}

theorem derivIdeal_eq_span_gen (ch : OriginChart) (P : AmbRing m) (v : Fin (m + 1) → ℚ) (s : ℚ) :
    derivIdeal ch P v s = Ideal.span (qrtGenSet ch P v s) := by
  unfold derivIdeal qrtGenSet
  rw [Ideal.span_union]

/-- The generators as a family indexed by a type. -/
abbrev qrtGen (ch : OriginChart) (P : AmbRing m) (v : Fin (m + 1) → ℚ) (s : ℚ) :
    qrtGenSet ch P v s → AmbRing m := Subtype.val

theorem span_qrtGen (ch : OriginChart) (P : AmbRing m) (v : Fin (m + 1) → ℚ) (s : ℚ) :
    Ideal.span (Set.range (qrtGen ch P v s)) = derivIdeal ch P v s := by
  rw [derivIdeal_eq_span_gen]
  congr 1
  exact Subtype.range_coe

/-! ### The fixed equation survives the slice -/

section Slice

variable {E : Type*} [Field E] [Algebra ℂ E]

theorem qrt_slice_X_of_mem (A : Finset (Fin (m + 2))) (b : Fin (m + 2) → E) (i : Fin (m + 2))
    (hi : i ∈ A) :
    enumeratedSliceMap (C := ℂ) A b (MvPolynomial.X i : AmbRing m) =
      MvPolynomial.X (A.equivFin ⟨i, hi⟩) := by
  change MvPolynomial.rename A.equivFin (sliceMap (C := ℂ) A b (MvPolynomial.X i)) = _
  rw [sliceMap_X_mem (C := ℂ) A b i hi, MvPolynomial.rename_X]

theorem qrt_slice_X_of_notMem (A : Finset (Fin (m + 2))) (b : Fin (m + 2) → E) (i : Fin (m + 2))
    (hi : i ∉ A) :
    enumeratedSliceMap (C := ℂ) A b (MvPolynomial.X i : AmbRing m) = MvPolynomial.C (b i) := by
  change MvPolynomial.rename A.equivFin (sliceMap (C := ℂ) A b (MvPolynomial.X i)) = _
  rw [sliceMap_X_notMem (C := ℂ) A b i hi, MvPolynomial.rename_C]

/-- CM l.1391–1394: if `u ∈ A`, the slice of `f = t² − F(u)` is nonzero (the term `−f(a) u⁴`
cannot cancel: the sliced `t` is a constant or a variable different from `u`). Proof by evaluation:
at `u ↦ x` and the other free coordinates `↦ 0` the slice is `c² − F(x)`, which cannot vanish for
all `x` since `deg F = 4`. -/
theorem qrt_relation_slice_ne_zero (ch : OriginChart) (A : Finset (Fin (m + 2)))
    (h0 : (0 : Fin (m + 2)) ∈ A) (b : Fin (m + 2) → E) :
    enumeratedSliceMap (C := ℂ) A b (relation ch) ≠ 0 := by
  classical
  intro hz
  have h10 : (1 : Fin (m + 2)) ≠ 0 := zero_ne_one_amb.symm
  let c : E := if (1 : Fin (m + 2)) ∈ A then 0 else b 1
  have key : ∀ x : E, c ^ 2 = Polynomial.eval x ((Fc ch).map (algebraMap ℂ E)) := by
    intro x
    let pt : Fin A.card → E := fun j => if (A.equivFin.symm j).val = 0 then x else 0
    let e : Fin (m + 2) → E := fun i => if i = 0 then x else if i ∈ A then 0 else b i
    have hcomp : ((MvPolynomial.aeval pt).restrictScalars ℂ).comp
        (enumeratedSliceMap (C := ℂ) A b) = MvPolynomial.aeval e := by
      apply MvPolynomial.algHom_ext
      intro i
      by_cases hi : i ∈ A
      · rw [AlgHom.comp_apply, qrt_slice_X_of_mem A b i hi]
        simp [pt, e, hi]
      · have hi0 : i ≠ 0 := fun h => hi (by rw [h]; exact h0)
        rw [AlgHom.comp_apply, qrt_slice_X_of_notMem A b i hi]
        simp [e, hi, hi0]
    have h1 := DFunLike.congr_fun hcomp (relation ch)
    rw [AlgHom.comp_apply, hz, map_zero] at h1
    have he0 : e 0 = x := by simp [e]
    have he1 : e 1 = c := by simp [e, c, h10]
    have h2 : MvPolynomial.aeval e (relation ch) = e 1 ^ 2 - Polynomial.aeval (e 0) (Fc ch) := by
      have := Polynomial.aeval_algHom_apply (MvPolynomial.aeval e) (uV : AmbRing m) (Fc ch)
      unfold relation
      rw [map_sub, map_pow, ← this]
      simp [tV, uV]
    have h3 : Polynomial.aeval x (Fc ch) = Polynomial.eval x ((Fc ch).map (algebraMap ℂ E)) := by
      rw [Polynomial.aeval_def, Polynomial.eval_map]
    rw [h2, he1, he0, h3] at h1
    linear_combination (-1 : E) * h1
  have hinf : Infinite E := Infinite.of_injective (algebraMap ℂ E) (algebraMap ℂ E).injective
  let g : Polynomial E := (Fc ch).map (algebraMap ℂ E) - Polynomial.C (c ^ 2)
  have hg : g = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have : {x : E | g.IsRoot x} = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      show g.IsRoot x
      simp only [g, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C]
      rw [← key x, sub_self]
    rw [this]
    exact Set.infinite_univ
  have hc4 := congrArg (fun p => Polynomial.coeff p 4) hg
  have h4 : (Fc ch).coeff 4 ≠ 0 := by
    rw [coeff_four_Fc]
    exact fa_ne_complex ch
  simp only [g, Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_C] at hc4
  simp [h4] at hc4

end Slice

/-! ### Frame vectors and the graph: independence transfers to the ambient quotient -/

section Transfer

variable (ch : OriginChart) (Q : Ideal (AmbRing m)) [Q.IsPrime]

/-- Linear independence of vectors modulo the intrinsic tangent space `V` implies linear
independence of their graph lifts modulo the ambient tangent space `T_Q` (the map `dropU` is a
left inverse of the graph). -/
theorem qrt_linearIndependent_ambient (hJ : resJ ch Q ≠ 0) (hf : relation ch ∈ Q) {k : ℕ}
    (w : Fin k → (Fin (m + 1) → Q.ResidueField))
    (hw : LinearIndependent Q.ResidueField fun j => (intrinsicTangent ch Q).mkQ (w j)) :
    LinearIndependent Q.ResidueField fun j =>
      (polynomialTangent (primeResidueMap Q) Q).mkQ (graphMap (resJ ch Q) (resT Q) (w j)) := by
  have hTV : polynomialTangent (primeResidueMap Q) Q ≤
      (intrinsicTangent ch Q).comap (dropU (m := m)) := by
    intro x hx
    obtain ⟨v, rfl⟩ := tangent_le_graph ch Q hJ hf hx
    rw [Submodule.mem_comap, dropU_graphMap]
    exact hx
  refine LinearIndependent.of_comp
    ((polynomialTangent (primeResidueMap Q) Q).mapQ (intrinsicTangent ch Q) dropU hTV) ?_
  have hfun : ((polynomialTangent (primeResidueMap Q) Q).mapQ (intrinsicTangent ch Q) dropU hTV) ∘
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (graphMap (resJ ch Q) (resT Q) (w j))) =
      fun j => (intrinsicTangent ch Q).mkQ (w j) := by
    funext j
    have h : ((polynomialTangent (primeResidueMap Q) Q).mapQ (intrinsicTangent ch Q) dropU hTV)
        ((polynomialTangent (primeResidueMap Q) Q).mkQ
          (graphMap (resJ ch Q) (resT Q) (w j))) =
        (intrinsicTangent ch Q).mkQ (dropU (graphMap (resJ ch Q) (resT Q) (w j))) := rfl
    simp only [Function.comp_apply, h, dropU_graphMap]
  rw [hfun]
  exact hw

end Transfer

/-! ### The persistent comparison -/

/-- **E09.4c** (CM l.1380–1450, input (A) l.3034–3055; OAI form
`PersistentWeightComparison.logarithmic_persistent_comparison`).

Let `P` have source degree `≤ N`, `N ≥ 8 w₀`, `s ≤ ε₀ N`, and let `Q` be a prime minimal over
`I_s = (f) + (D_ν P : c(ν) ≤ s)` with `F′(ū) ≠ 0` in `Frac(R/Q)`. If all frame words of jet cost at
most `δ = ε₀ N / (m+3)` map `I_s` into `Q` and the rectangle cutoffs for `δ` are at least `2`, then
`∏_{i∈S} r_i ≤ C₄ ∏_{j∈T} κ_j` for all coordinate normal bases `S` and frame normal bases `T`. -/
theorem ell_persistent_comparison (W : Weights m) (ch : OriginChart) {σ : ℚ} (hσ : 0 < σ)
    (P : AmbRing m) (N : ℝ) (hP : SrcDeg W N P) (hN : 8 * (W.w₀ : ℝ) ≤ N)
    (hrect : EllUniformRectangles W ((eps0 W σ : ℝ) * N / ((m : ℝ) + 3)))
    (s : ℚ) (hs : (s : ℝ) ≤ (eps0 W σ : ℝ) * N)
    (Q : Ideal (AmbRing m)) [Q.IsPrime] (hJ : resJ ch Q ≠ 0)
    (hmin : Q ∈ (derivIdeal ch P (jetWt W) s).minimalPrimes)
    (hpers : ∀ g ∈ derivIdeal ch P (jetWt W) s, ∀ word : List (Fin (m + 1)),
      ((((word.map (jetWt W)).sum : ℚ)) : ℝ) ≤ (eps0 W σ : ℝ) * N / ((m : ℝ) + 3) →
        frameWord ch word g ∈ Q) :
    EllNormalProductComparison W ch Q hJ (C4 W σ : ℝ) := by
  classical
  unfold EllNormalProductComparison
  intro S T hS hT
  have hw0 : (0 : ℝ) < (W.w₀ : ℝ) := by exact_mod_cast W.w₀_pos
  have hNpos : 0 < N := by linarith
  have hεpos : (0 : ℝ) < (eps0 W σ : ℝ) := by exact_mod_cast eps0_pos W hσ
  have hm3 : (0 : ℝ) < (m : ℝ) + 3 := by positivity
  have hδpos : 0 < (eps0 W σ : ℝ) * N / ((m : ℝ) + 3) := div_pos (mul_pos hεpos hNpos) hm3
  generalize hδ : (eps0 W σ : ℝ) * N / ((m : ℝ) + 3) = δ at hrect hpers hδpos
  have hfQ : relation ch ∈ Q := hmin.1.2 (relation_mem_derivIdeal s)
  have hS' : IsNormalBasis (K := Q.ResidueField)
      (fun i : Fin (m + 1) =>
        (intrinsicTangent ch Q).mkQ (Pi.basisFun Q.ResidueField (Fin (m + 1)) i)) S := hS
  have hT' : IsNormalBasis (K := Q.ResidueField)
      (fun j : Fin (m + 1) => (intrinsicTangent ch Q).mkQ
        (frameBasis m (-(resJ ch Q)) (neg_ne_zero.mpr hJ) j)) T := hT
  have hcard : S.card = T.card := hS'.card_eq.trans hT'.card_eq.symm
  by_cases hk0 : S.card = 0
  · -- `k = 0`: the claim is `1 ≤ C₄`
    have hS0 : S = ∅ := Finset.card_eq_zero.mp hk0
    have hT0 : T = ∅ := Finset.card_eq_zero.mp (hcard.symm.trans hk0)
    subst hS0
    subst hT0
    rw [Finset.prod_empty, Finset.prod_empty, mul_one]
    exact_mod_cast qrt_one_le_C4 W hσ
  have hkpos : 0 < S.card := Nat.pos_of_ne_zero hk0
  have hkle : S.card ≤ m + 1 := by simpa using Finset.card_le_univ S
  -- the ambient normal basis `A = {u} ∪ S`
  have hA : IsNormalBasis (K := Q.ResidueField)
      (fun i : Fin (m + 2) => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (Pi.basisFun Q.ResidueField (Fin (m + 2)) i))
      (insert 0 (S.map (Fin.succEmb _))) :=
    (normalBasis_adjoin_u ch Q hJ hfQ S).mp hS
  have h0notin : (0 : Fin (m + 2)) ∉ S.map (Fin.succEmb (m + 1)) := by
    simp [Finset.mem_map]
  have h0A : (0 : Fin (m + 2)) ∈ insert 0 (S.map (Fin.succEmb (m + 1))) :=
    Finset.mem_insert_self _ _
  have hAcard : (insert (0 : Fin (m + 2)) (S.map (Fin.succEmb (m + 1)))).card = S.card + 1 := by
    rw [Finset.card_insert_of_notMem h0notin, Finset.card_map]
  -- generators of `I_s` have source degree `≤ g N`
  have hε := eps0_pos W hσ
  have hg1 : (1 : ℝ) ≤ ((gConst W σ : ℚ) : ℝ) := by exact_mod_cast qrt_one_le_gConst W hσ
  have hgdef : ((gConst W σ : ℚ) : ℝ) =
      1 + ((2 * W.w₀ / W.v₀ : ℚ) : ℝ) * (eps0 W σ : ℝ) := by
    unfold gConst
    push_cast
    try ring
  have hc0 : (0 : ℚ) ≤ 2 * W.w₀ / W.v₀ := by
    have := W.w₀_pos
    have := W.v₀_pos
    positivity
  have hcR : (0 : ℝ) ≤ ((2 * W.w₀ / W.v₀ : ℚ) : ℝ) := by exact_mod_cast hc0
  have hgen : ∀ j : qrtGenSet ch P (jetWt W) s,
      SrcDeg W (((gConst W σ : ℚ) : ℝ) * N) j.1 := by
    intro j
    obtain ⟨g, hg⟩ := j
    show SrcDeg W (((gConst W σ : ℚ) : ℝ) * N) g
    simp only [qrtGenSet, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hg
    rcases hg with rfl | ⟨word, hword, rfl⟩
    · refine (relation_srcDeg_le W ch).mono ?_
      nlinarith [mul_nonneg (sub_nonneg.mpr hg1) hNpos.le]
    · have h1 := srcDeg_frameWord (ch := ch) hP word
      refine h1.mono ?_
      have hc := srcCost_sum_le W word
      have hq : ((word.map (srcCost W)).sum : ℚ) ≤ 2 * W.w₀ / W.v₀ * s :=
        hc.trans (mul_le_mul_of_nonneg_left hword hc0)
      have hr : (((word.map (srcCost W)).sum : ℚ) : ℝ) ≤ ((2 * W.w₀ / W.v₀ : ℚ) : ℝ) * (s : ℝ) := by
        exact_mod_cast hq
      have hr2 : ((2 * W.w₀ / W.v₀ : ℚ) : ℝ) * (s : ℝ) ≤
          ((2 * W.w₀ / W.v₀ : ℚ) : ℝ) * ((eps0 W σ : ℝ) * N) :=
        mul_le_mul_of_nonneg_left hs hcR
      rw [hgdef]
      nlinarith [hr, hr2]
  -- upper bound (E09.4a)
  have hQ : Q ∈ (Ideal.span (Set.range (qrtGen ch P (jetWt W) s))).minimalPrimes := by
    rw [span_qrtGen]
    exact hmin
  have hrelmem : relation ch ∈ Ideal.span (Set.range (qrtGen ch P (jetWt W) s)) := by
    rw [span_qrtGen]
    exact relation_mem_derivIdeal s
  have hslice := qrt_relation_slice_ne_zero (E := Q.ResidueField) ch
    (insert 0 (S.map (Fin.succEmb (m + 1)))) h0A (residueCoordinates Q)
  have hMnn : (0 : ℝ) ≤ ((gConst W σ : ℚ) : ℝ) * N := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ ((gConst W σ : ℚ) : ℝ)) hNpos.le
    exact this
  obtain ⟨L, hL, hupper⟩ := prime_length_fixed_equation_le Q
    (insert 0 (S.map (Fin.succEmb (m + 1)))) hA (qrtGen ch P (jetWt W) s) hQ (relation ch) hrelmem
    hslice (srcWt W) (srcWt_pos W) (8 * (W.w₀ : ℝ)) (((gConst W σ : ℚ) : ℝ) * N)
    (by linarith) hMnn (by rw [hAcard]; omega)
    (qrt_srcDeg_sum (relation_srcDeg_le W ch))
    (fun j => qrt_srcDeg_sum (hgen j))
  -- `∏_A ρ ≥ 2 w₀ ∏_S r`
  have h2w : (0 : ℝ) < 2 * (W.w₀ : ℝ) := by linarith
  have hRpos : 0 < ∏ i ∈ S, ((radWt W i : ℚ) : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast qrt_radWt_pos W i
  have hprodA : (2 * (W.w₀ : ℝ)) * ∏ i ∈ S, ((radWt W i : ℚ) : ℝ) ≤
      ∏ i ∈ insert (0 : Fin (m + 2)) (S.map (Fin.succEmb (m + 1))), ((srcWt W i : ℚ) : ℝ) := by
    rw [Finset.prod_insert h0notin, Finset.prod_map]
    have h0 : ((srcWt W 0 : ℚ) : ℝ) = 2 * (W.w₀ : ℝ) := by
      simp
    rw [h0]
    refine mul_le_mul_of_nonneg_left ?_ h2w.le
    refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
    · exact_mod_cast (qrt_radWt_pos W i).le
    · show ((radWt W i : ℚ) : ℝ) ≤ ((srcWt W i.succ : ℚ) : ℝ)
      exact_mod_cast qrt_radWt_le_srcWt W i
  have hAk : (insert (0 : Fin (m + 2)) (S.map (Fin.succEmb (m + 1)))).card - 1 = S.card := by
    rw [hAcard]; omega
  rw [hAk] at hupper
  have hPiApos : 0 < ∏ i ∈ insert (0 : Fin (m + 2)) (S.map (Fin.succEmb (m + 1))),
      ((srcWt W i : ℚ) : ℝ) :=
    lt_of_lt_of_le (mul_pos h2w hRpos) hprodA
  have hL1 := (le_div_iff₀ hPiApos).mp hupper
  have hLR : (L : ℝ) * ∏ i ∈ S, ((radWt W i : ℚ) : ℝ) ≤
      4 * (((gConst W σ : ℚ) : ℝ) * N) ^ S.card := by
    have h2 : (L : ℝ) * ((2 * (W.w₀ : ℝ)) * ∏ i ∈ S, ((radWt W i : ℚ) : ℝ)) ≤
        (L : ℝ) * ∏ i ∈ insert (0 : Fin (m + 2)) (S.map (Fin.succEmb (m + 1))),
          ((srcWt W i : ℚ) : ℝ) :=
      mul_le_mul_of_nonneg_left hprodA (Nat.cast_nonneg L)
    have h3 : (2 * (W.w₀ : ℝ)) * ((L : ℝ) * ∏ i ∈ S, ((radWt W i : ℚ) : ℝ)) ≤
        (2 * (W.w₀ : ℝ)) * (4 * (((gConst W σ : ℚ) : ℝ) * N) ^ S.card) := by
      calc (2 * (W.w₀ : ℝ)) * ((L : ℝ) * ∏ i ∈ S, ((radWt W i : ℚ) : ℝ))
          = (L : ℝ) * ((2 * (W.w₀ : ℝ)) * ∏ i ∈ S, ((radWt W i : ℚ) : ℝ)) := by ring
        _ ≤ _ := h2
        _ ≤ _ := hL1
        _ = _ := by ring
    exact le_of_mul_le_mul_left h3 h2w
  -- lower bound (E09.4b)
  have hκ : ∀ j : Fin (m + 1), 0 < ((jetWt W j : ℚ) : ℝ) := fun j => by
    exact_mod_cast qrt_jetWt_pos W j
  obtain ⟨B, hBdef⟩ : ∃ B : Fin S.card → Fin (m + 1), B = enumeration S T hcard := ⟨_, rfl⟩
  have hli := enumeration_linearIndependent S T hcard hT'
  rw [← hBdef] at hli
  have hB : LinearIndependent Q.ResidueField fun j : Fin S.card =>
      (polynomialTangent (primeResidueMap Q) Q).mkQ
        (fun i : Fin (m + 2) => primeResidueMap Q (frameDeriv ch (B j) (MvPolynomial.X i))) := by
    have h := qrt_linearIndependent_ambient ch Q hJ hfQ
      (fun j : Fin S.card => frameBasis m (-(resJ ch Q)) (neg_ne_zero.mpr hJ) (B j)) hli
    have hfun : (fun j : Fin S.card => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (fun i : Fin (m + 2) => primeResidueMap Q (frameDeriv ch (B j) (MvPolynomial.X i)))) =
        fun j : Fin S.card => (polynomialTangent (primeResidueMap Q) Q).mkQ
          (graphMap (resJ ch Q) (resT Q)
            (frameBasis m (-(resJ ch Q)) (neg_ne_zero.mpr hJ) (B j))) := by
      funext j
      rw [graphMap_frameBasis ch Q hJ (B j)]
    rw [hfun]
    exact h
  have hbudget := rectangularCutoff_budget hkpos (fun j => ((jetWt W (B j) : ℚ) : ℝ))
    (fun j => hκ (B j)) δ hδpos
  have hvanish : ∀ p ∈ Ideal.span (Set.range (qrtGen ch P (jetWt W) s)),
      ∀ word : List (Fin (m + 1)),
        (word.map (fun j : Fin (m + 1) => ((jetWt W j : ℚ) : ℝ))).sum ≤ δ →
          derivWord (frameDeriv ch) word p ∈ Q := by
    intro p hp word hw
    rw [span_qrtGen] at hp
    exact hpers p hp word (by rw [qrt_cast_jet_sum]; exact hw)
  have hlower := prime_rectangular_length_lower Q (frameDeriv ch) B hB
    (Ideal.span (Set.range (qrtGen ch P (jetWt W) s)))
    (fun j : Fin (m + 1) => ((jetWt W j : ℚ) : ℝ))
    (rectangularCutoff (fun j => ((jetWt W (B j) : ℚ) : ℝ)) δ) δ
    (fun i => hrect S.card hkpos hkle B i) (fun i => (hκ i).le) hbudget hvanish
  have hlowerN : (∏ i, rectangularCutoff (fun j => ((jetWt W (B j) : ℚ) : ℝ)) δ i : ℕ) ≤ L := by
    have h := hlower
    change _ ≤ primeLength Q (Ideal.span (Set.range (qrtGen ch P (jetWt W) s))) at h
    rw [hL] at h
    exact_mod_cast h
  have hlowerR : (∏ i, (rectangularCutoff (fun j => ((jetWt W (B j) : ℚ) : ℝ)) δ i : ℝ)) ≤
      (L : ℝ) := by
    exact_mod_cast hlowerN
  have hprodB := prod_enumeration S T hcard (fun j => ((jetWt W j : ℚ) : ℝ))
  rw [← hBdef] at hprodB
  set Kp : ℝ := ∏ j ∈ T, ((jetWt W j : ℚ) : ℝ) with hKp
  have hKppos : 0 < Kp := Finset.prod_pos fun j _ => hκ j
  have hprod_lower := rectangularCutoff_product_lower hkpos (fun j => ((jetWt W (B j) : ℚ) : ℝ))
    (fun j => hκ (B j)) hδpos
  have hkR : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hkpos
  have hkKp : 0 < (S.card : ℝ) ^ S.card * Kp := mul_pos (pow_pos hkR _) hKppos
  have hlow : δ ^ S.card ≤ (L : ℝ) * ((S.card : ℝ) ^ S.card * Kp) := by
    have h1 := hprod_lower.trans hlowerR
    have h2 : (∏ i : Fin S.card, ((jetWt W (B i) : ℚ) : ℝ)) = Kp := hprodB
    have hden : 0 < (S.card : ℝ) ^ S.card * ∏ i : Fin S.card, ((jetWt W (B i) : ℚ) : ℝ) :=
      mul_pos (pow_pos hkR _) (Finset.prod_pos fun i _ => hκ (B i))
    have h1' := (div_le_iff₀ hden).mp h1
    rw [h2] at h1'
    exact h1'
  -- combine
  have hεne : (eps0 W σ : ℝ) ≠ 0 := hεpos.ne'
  have hm3ne : ((m : ℝ) + 3) ≠ 0 := hm3.ne'
  have hN_eq : N = δ * (((m : ℝ) + 3) / (eps0 W σ : ℝ)) := by
    rw [← hδ]
    field_simp
  have hgN : (((gConst W σ : ℚ) : ℝ) * N) ^ S.card =
      (((gConst W σ : ℚ) : ℝ) * (((m : ℝ) + 3) / (eps0 W σ : ℝ))) ^ S.card * δ ^ S.card := by
    rw [hN_eq]
    simp only [mul_pow]
    ring
  have hδk : 0 < δ ^ S.card := pow_pos hδpos _
  have hRle : ∏ i ∈ S, ((radWt W i : ℚ) : ℝ) ≤
      4 * (((gConst W σ : ℚ) : ℝ) * (((m : ℝ) + 3) / (eps0 W σ : ℝ))) ^ S.card *
        ((S.card : ℝ) ^ S.card * Kp) := by
    have h1 : δ ^ S.card * ∏ i ∈ S, ((radWt W i : ℚ) : ℝ) ≤
        δ ^ S.card * (4 * (((gConst W σ : ℚ) : ℝ) * (((m : ℝ) + 3) / (eps0 W σ : ℝ))) ^ S.card *
          ((S.card : ℝ) ^ S.card * Kp)) := by
      calc δ ^ S.card * ∏ i ∈ S, ((radWt W i : ℚ) : ℝ)
          ≤ ((L : ℝ) * ((S.card : ℝ) ^ S.card * Kp)) * ∏ i ∈ S, ((radWt W i : ℚ) : ℝ) :=
            mul_le_mul_of_nonneg_right hlow hRpos.le
        _ = ((L : ℝ) * ∏ i ∈ S, ((radWt W i : ℚ) : ℝ)) * ((S.card : ℝ) ^ S.card * Kp) := by ring
        _ ≤ (4 * (((gConst W σ : ℚ) : ℝ) * N) ^ S.card) * ((S.card : ℝ) ^ S.card * Kp) :=
            mul_le_mul_of_nonneg_right hLR hkKp.le
        _ = _ := by rw [hgN]; ring
    exact le_of_mul_le_mul_left h1 hδk
  have hcoef : 4 * ((gConst W σ : ℚ) : ℝ) ^ S.card * (S.card : ℝ) ^ S.card *
      (((m : ℝ) + 3) / (eps0 W σ : ℝ)) ^ S.card ≤ (C4 W σ : ℝ) := by
    exact_mod_cast coeff_bound W S.card ⟨Nat.succ_le_of_lt hkpos, hkle⟩ hσ
  calc ∏ i ∈ S, ((radWt W i : ℚ) : ℝ)
      ≤ 4 * (((gConst W σ : ℚ) : ℝ) * (((m : ℝ) + 3) / (eps0 W σ : ℝ))) ^ S.card *
        ((S.card : ℝ) ^ S.card * Kp) := hRle
    _ = (4 * ((gConst W σ : ℚ) : ℝ) ^ S.card * (S.card : ℝ) ^ S.card *
        (((m : ℝ) + 3) / (eps0 W σ : ℝ)) ^ S.card) * Kp := by
        simp only [mul_pow]
        ring
    _ ≤ (C4 W σ : ℝ) * Kp := mul_le_mul_of_nonneg_right hcoef hKppos.le

end

end CatalanCore.Elliptic.EPA.Local
