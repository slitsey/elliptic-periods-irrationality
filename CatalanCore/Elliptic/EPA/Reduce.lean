module

public import CatalanCore.Elliptic.EPA.Ambient
public import CatalanCore.Elliptic.EPA.Packet
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Reduction modulo `f = t² − F(u)` (row E09.1)

Labels refer to `D2-DESIGN-2026-11-20.md` §2 P2 (CM l.796–799, l.3328, l.1930) and §5 E09.1.

* `exists_reduced`: a polynomial `P` with `SrcDeg W N P` is congruent modulo `f` to a polynomial `P'`
  with `SrcDeg W N P'` and `t`-degree `≤ 1`. (`t² g ↦ F(u) g` does not raise the source degree
  because every monomial of `F(u)` has weight `≤ 8 w₀ = wt(t²)`; design §A4.)
* `reduced_mem_span`: such a `P'` is a `ℂ`-combination of the monomials `u^k t^b Z^α` of the columns
  `(k, b, α)` of `Weights.colSet` (condition (S)).
* `not_mem_span_of_reduced`: a nonzero polynomial of `t`-degree `≤ 1` is not a multiple of `f`
  (`f` has `t`-degree `2` and `ℂ[u,t,Z]` is a domain, CM l.1930).
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

open CatalanCore.Elliptic MvPolynomial

variable {m : ℕ}

theorem tdeg_sum {ι : Type*} (s : Finset ι) (f : ι → AmbRing m)
    (h : ∀ i ∈ s, ∀ d ∈ (f i).support, d 1 ≤ 1) : ∀ d ∈ (∑ i ∈ s, f i).support, d 1 ≤ 1 := by
  classical
  intro d hd
  obtain ⟨i, hi, hdi⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  exact h i hi d hdi

/-- `F(u) · (c u^a t^b …) = Σ_{k ≤ 4} F_k · c u^{a+k} …`. -/
theorem aeval_uV_mul_monomial (ch : OriginChart) (d : Fin (m + 2) →₀ ℕ) (c : ℂ) :
    (Polynomial.aeval (uV : AmbRing m) (Fc ch)) * monomial d c =
      ∑ k ∈ Finset.range 5, monomial (Finsupp.single 0 k + d) ((Fc ch).coeff k * c) := by
  rw [Polynomial.aeval_eq_sum_range' (n := 5) (by have := natDegree_Fc_le ch; omega),
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mul_assoc]
  simp only [uV]
  rw [X_pow_eq_monomial, monomial_mul, smul_monomial, smul_eq_mul, one_mul]

/-- The monomial case of `exists_reduced`, by strong induction on the `t`-exponent. -/
theorem exists_reduced_monomial (W : Weights m) (ch : OriginChart) :
    ∀ (n : ℕ) (d : Fin (m + 2) →₀ ℕ) (c : ℂ), d 1 ≤ n →
      ∃ P' : AmbRing m, monomial d c - P' ∈ (Ideal.span {relation ch} : Ideal (AmbRing m)) ∧
        SrcDeg W (Finsupp.weight (fun j => srcRho W j) d) P' ∧ ∀ e ∈ P'.support, e 1 ≤ 1 := by
  have hw0 : (0 : ℝ) < W.w₀ := by exact_mod_cast W.w₀_pos
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro d c hdn
  by_cases hd1 : d 1 ≤ 1
  · refine ⟨monomial d c, by simp, SrcDeg.monomial d c le_rfl, ?_⟩
    intro e he
    have := support_monomial_subset he
    rw [Finset.mem_singleton] at this
    subst this
    exact hd1
  · push_neg at hd1
    have hle : Finsupp.single (1 : Fin (m + 2)) 2 ≤ d := by
      rw [Finsupp.single_le_iff]; omega
    obtain ⟨d', hd⟩ : ∃ d' : Fin (m + 2) →₀ ℕ, d = Finsupp.single 1 2 + d' :=
      ⟨d - Finsupp.single 1 2, (add_tsub_cancel_of_le hle).symm⟩
    subst hd
    have h1 : ((Finsupp.single (1 : Fin (m + 2)) 2 + d' : Fin (m + 2) →₀ ℕ) 1) = 2 + d' 1 := by simp
    rw [h1] at hdn hd1
    have hmon : monomial (Finsupp.single (1 : Fin (m + 2)) 2 + d') c =
        (tV : AmbRing m) ^ 2 * monomial d' c := by
      rw [tV, X_pow_eq_monomial, monomial_mul, one_mul]
    have hk : ∀ k : ℕ, ∃ P' : AmbRing m,
        monomial (Finsupp.single 0 k + d') ((Fc ch).coeff k * c) - P' ∈
            (Ideal.span {relation ch} : Ideal (AmbRing m)) ∧
          SrcDeg W (Finsupp.weight (fun j => srcRho W j) (Finsupp.single 0 k + d')) P' ∧
          ∀ e ∈ P'.support, e 1 ≤ 1 := fun k =>
      ih (d' 1) (by omega) _ _
        (by simp [Finsupp.single_apply, zero_ne_one_amb])
    choose Pk hPk using hk
    refine ⟨∑ k ∈ Finset.range 5, Pk k, ?_, ?_, ?_⟩
    · have key : monomial (Finsupp.single (1 : Fin (m + 2)) 2 + d') c -
          ∑ k ∈ Finset.range 5, Pk k =
          relation ch * monomial d' c +
            ∑ k ∈ Finset.range 5,
              (monomial (Finsupp.single 0 k + d') ((Fc ch).coeff k * c) - Pk k) := by
        rw [Finset.sum_sub_distrib, ← aeval_uV_mul_monomial, hmon, relation]
        ring
      rw [key]
      exact add_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _)))
        (Ideal.sum_mem _ fun k _ => (hPk k).1)
    · refine SrcDeg.sum _ fun k hk => ((hPk k).2.1).mono ?_
      have hk4 : (k : ℝ) ≤ 4 := by
        exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp only [map_add, Finsupp.weight_single, nsmul_eq_mul, Nat.cast_ofNat]
      rw [srcRho_zero, srcRho_one]
      nlinarith [mul_nonneg (sub_nonneg.mpr hk4) hw0.le]
    · exact tdeg_sum _ _ fun k _ => (hPk k).2.2

/-- Row E09.1, P2: reduction modulo `f` keeps the source degree and brings the `t`-degree to `≤ 1`. -/
theorem exists_reduced {W : Weights m} {ch : OriginChart} {N : ℝ} {P : AmbRing m}
    (hP : SrcDeg W N P) :
    ∃ P' : AmbRing m, P' - P ∈ (Ideal.span {relation ch} : Ideal (AmbRing m)) ∧
      SrcDeg W N P' ∧ ∀ d ∈ P'.support, d 1 ≤ 1 := by
  classical
  have hmono := fun d : Fin (m + 2) →₀ ℕ =>
    exists_reduced_monomial W ch (d 1) d (P.coeff d) le_rfl
  choose Q hQ using hmono
  refine ⟨∑ d ∈ P.support, Q d, ?_, ?_, ?_⟩
  · have h : P - ∑ d ∈ P.support, Q d =
        ∑ d ∈ P.support, (monomial d (P.coeff d) - Q d) := by
      rw [Finset.sum_sub_distrib, ← MvPolynomial.as_sum]
    have hmem : P - ∑ d ∈ P.support, Q d ∈ (Ideal.span {relation ch} : Ideal (AmbRing m)) := by
      rw [h]
      exact Ideal.sum_mem _ fun d _ => (hQ d).1
    have := (Ideal.neg_mem_iff _).mpr hmem
    rwa [neg_sub] at this
  · exact SrcDeg.sum _ fun d hd => ((hQ d).2.1).mono (hP d hd)
  · exact tdeg_sum _ _ fun d _ => (hQ d).2.2

/-! ### Reduced polynomials are combinations of the columns of `colSet` -/

/-- The exponent vector `(k, b, α) ↦ u^k t^b Z^α` of a column index. -/
noncomputable def ambExp (c : ColIdx m) : Fin (m + 2) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    (Fin.cases (motive := fun _ => ℕ) c.1
      (Fin.cases (motive := fun _ => ℕ) c.2.1.val c.2.2))

/-- The monomial `u^k t^b Z^α` of a column index. -/
noncomputable def ambMonomial (c : ColIdx m) : AmbRing m := monomial (ambExp c) 1

/-- Row E09.1: a reduced polynomial of source degree `≤ H` lies in the span of the monomials of
the columns of `Weights.colSet H` (the paper's `ℱ_H`, condition (S)). -/
theorem reduced_mem_span {W : Weights m} {H : ℝ} {P : AmbRing m} (hP : SrcDeg W H P)
    (ht : ∀ d ∈ P.support, d 1 ≤ 1) :
    P ∈ Submodule.span ℂ {Q : AmbRing m | ∃ c ∈ W.colSet H, Q = ambMonomial c} := by
  classical
  rw [MvPolynomial.as_sum P]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hd1 : d 1 < 2 := by have := ht d hd; omega
  let c : ColIdx m := (d 0, ⟨d 1, hd1⟩, fun i => d i.succ.succ)
  have hcd : ambExp c = d := by
    ext j
    induction j using Fin.cases with
    | zero => rfl
    | succ j =>
      induction j using Fin.cases with
      | zero =>
        show (d 1) = d (Fin.succ 0)
        rw [← one_eq_succ_zero]
      | succ i => rfl
  have hw : Finsupp.weight (fun j => srcRho W j) d =
      2 * (W.w₀ : ℝ) * ((d 0 : ℝ) + 2 * (d 1 : ℝ)) +
        ((W.wt (fun i => d i.succ.succ) : ℚ) : ℝ) := by
    rw [Finsupp.weight_eq_sum, Fin.sum_univ_succ, Fin.sum_univ_succ, W.wt_cast]
    simp only [nsmul_eq_mul, srcRho_zero, srcRho_succ_succ, ← one_eq_succ_zero, srcRho_one]
    rw [Finset.sum_congr rfl fun (x : Fin m) _ => mul_comm ((d x.succ.succ : ℕ) : ℝ) (W.w x : ℝ)]
    ring
  have hcol : c ∈ W.colSet H := by
    rw [Weights.mem_colSet_iff]
    have := hP d hd
    rw [hw] at this
    exact this
  have hm : monomial d (P.coeff d) = P.coeff d • ambMonomial c := by
    rw [ambMonomial, hcd, smul_monomial, smul_eq_mul, mul_one]
  rw [hm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, hcol, rfl⟩)

/-! ### `f` is not a zero-divisor obstruction: reduced polynomials are not multiples of `f` -/

theorem coeff_relation_single_one_two (ch : OriginChart) :
    (relation ch : AmbRing m).coeff (Finsupp.single 1 2) = 1 := by
  have hne : ∀ k : ℕ, Finsupp.single (0 : Fin (m + 2)) k ≠ Finsupp.single 1 2 := by
    intro k h
    have := congrArg (fun f : Fin (m + 2) →₀ ℕ => f 1) h
    simp [Finsupp.single_apply, zero_ne_one_amb] at this
  have hz : ∑ k ∈ Finset.range 5,
      ((Fc ch).coeff k • (uV : AmbRing m) ^ k).coeff (Finsupp.single 1 2) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    simp [uV, X_pow_eq_monomial, coeff_monomial, hne k]
  unfold relation
  rw [coeff_sub, Polynomial.aeval_eq_sum_range' (n := 5) (by have := natDegree_Fc_le ch; omega),
    coeff_sum, hz]
  simp [tV, X_pow_eq_monomial, coeff_monomial]

theorem relation_ne_zero (ch : OriginChart) : (relation ch : AmbRing m) ≠ 0 := by
  intro h
  have := coeff_relation_single_one_two (m := m) ch
  rw [h] at this
  simp at this

/-- `relation` has `t`-degree `≥ 2` (it is monic of degree `2` in `t`). -/
theorem two_le_degreeOf_relation (ch : OriginChart) :
    2 ≤ degreeOf (1 : Fin (m + 2)) (relation ch : AmbRing m) := by
  have hmem : (Finsupp.single (1 : Fin (m + 2)) 2) ∈ (relation ch : AmbRing m).support := by
    rw [MvPolynomial.mem_support_iff, coeff_relation_single_one_two]
    exact one_ne_zero
  have := monomial_le_degreeOf (1 : Fin (m + 2)) hmem
  simpa using this

/-- CM l.1930: a nonzero polynomial of `t`-degree `≤ 1` is not a multiple of `f`. -/
theorem not_mem_span_of_reduced {ch : OriginChart} {P : AmbRing m} (hP0 : P ≠ 0)
    (ht : ∀ d ∈ P.support, d 1 ≤ 1) :
    P ∉ (Ideal.span {relation ch} : Ideal (AmbRing m)) := by
  intro h
  obtain ⟨Q, hQ⟩ := Ideal.mem_span_singleton.mp h
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    exact hP0 (by simpa using hQ)
  have hdeg : degreeOf (1 : Fin (m + 2)) (relation ch * Q) =
      degreeOf 1 (relation ch) + degreeOf 1 Q := degreeOf_mul_eq (relation_ne_zero ch) hQ0
  have h1 : degreeOf (1 : Fin (m + 2)) P ≤ 1 := degreeOf_le_iff.mpr ht
  rw [hQ, hdeg] at h1
  have := two_le_degreeOf_relation (m := m) ch
  omega

end CatalanCore.Elliptic.EPA
