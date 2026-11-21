module

public import CatalanCore.Elliptic.EPA.Rigid.Graph
public import CatalanCore.Elliptic.EPA.Rigid.Quartic
public import CatalanCore.Elliptic.EPA.NoPrimitive.Rigidity
public import OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential
public import OAI.NumberTheory.PiExponent.Jets.DifferentialConstant
public import OAI.NumberTheory.PiExponent.Polynomials.PolynomialNormalNonzero
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Proper tangent and normal exclusion imply constant projection (row E09.5d)

Labels refer to `D2-DESIGN-2026-11-20.md` §5 E09.5d and to CM l.1749-1880
(`cor:origin-critical-locus`, `prop:origin-proper-tangent`,
`thm:origin-normal-exclusion-projection`).

Let `Q ⊂ R = ℂ[u,t,Z]` be a prime with `(f) ⊊ Q`, `f = relation ch`, with literal residue field
`K = Q.ResidueField`.

* `critical_constant` (CM l.1749): if `J̄ = F'(ū) = 0` or `t̄ = 0`, then `ū` and `t̄` are constants
  (ideal-theoretically: `u - c₀, t - c₁ ∈ Q`). Proof: `F'(u) ∈ Q` (resp. `F(u) = t² - f ∈ Q`) is a
  nonzero polynomial equation in `u`, which splits over `ℂ`, so `u - r ∈ Q` for a root `r` since `Q`
  is prime; then `t² - F(r) = (t - c)(t + c) ∈ Q`.
* `intrinsicTangent_ne_top` (CM l.1791-1810, `prop:origin-proper-tangent`): `V ≠ K^{m+1}`. If
  `V = ⊤`, the contraction `Q ∩ ℂ[t,Z]` is a proper partial-derivative-stable ideal, hence `0`
  (OAI `ideal_eq_bot_of_pderiv_stable`), contradicting `contract_ne_bot` (E09.5b).
* `ell_projection_constant` (CM l.1849): with `J̄ ≠ 0` and the normal-basis exclusion hypothesis, the
  OAI dichotomy `normal_basis_differential_dichotomy` (scalar `y = -J̄`) applied to the intrinsic
  vectors of `ℂ`-derivations of `K` gives either `dt̄ = 0` (then `t̄` constant by OAI
  `constant_of_differential_eq_zero`, and `ū` by `t̄² = F(ū)`) or `dz̄ᵢ = -J̄⁻¹ dt̄`, where
  `isAlgebraic_of_quartic_differential` (E09.5c) makes `ū, t̄` constants.
* `ell_projection_constant_of_exclusion`: the combination used by E09.8 (case split on `J̄ = 0`).

Template: OAI `Approximation/GenericNormalRigidity.constant_zeroth_coordinate_of_generic_normal_separation`
(openai/math fd4aeeb2, Apache License 2.0, Copyright OpenAI), used as imports.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

open CatalanCore.Elliptic
open OAI.PiExponent
open OAI.PiExponent.NormalBasisRigidity

variable {m : ℕ}

/-! ### Residues and membership in `Q` -/

section Residue

variable (Q : Ideal (AmbRing m)) [Q.IsPrime]

theorem primeResidueMap_eq_zero_iff (p : AmbRing m) : primeResidueMap Q p = 0 ↔ p ∈ Q :=
  Ideal.algebraMap_residueField_eq_zero (I := Q) (x := p)

/-- If `φ p = algebraMap c` in the residue field then `p - c ∈ Q`. -/
theorem sub_C_mem_of_residue_eq (p : AmbRing m) (c : ℂ)
    (h : algebraMap ℂ Q.ResidueField c = primeResidueMap Q p) : p - MvPolynomial.C c ∈ Q := by
  apply (primeResidueMap_eq_zero_iff Q _).mp
  rw [map_sub, MvPolynomial.algHom_C, h, sub_self]

end Residue

/-! ### Roots of nonzero polynomial equations -/

section Roots

variable (Q : Ideal (AmbRing m)) [Q.IsPrime]

theorem sub_dvd_aeval_sub (p : Polynomial ℂ) (a b : AmbRing m) :
    a - b ∣ Polynomial.aeval a p - Polynomial.aeval b p := by
  have := Polynomial.sub_dvd_eval_sub a b (p.map (algebraMap ℂ (AmbRing m)))
  rw [Polynomial.eval_map_algebraMap, Polynomial.eval_map_algebraMap] at this
  exact this

/-- A nonzero polynomial equation `p(u) ∈ Q` forces `u - r ∈ Q` for a root `r` of `p`. -/
theorem exists_root_mem_of_aeval_mem (p : Polynomial ℂ) (hp : p ≠ 0)
    (h : Polynomial.aeval (uV : AmbRing m) p ∈ Q) : ∃ r : ℂ, uV - MvPolynomial.C r ∈ Q := by
  suffices H : ∀ n : ℕ, ∀ p : Polynomial ℂ, p.natDegree = n → p ≠ 0 →
      Polynomial.aeval (uV : AmbRing m) p ∈ Q → ∃ r : ℂ, uV - MvPolynomial.C r ∈ Q from
    H _ p rfl hp h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p hn hp h
    by_cases hdeg : p.natDegree = 0
    · exfalso
      have hpC : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
      have hc0 : p.coeff 0 ≠ 0 := by
        intro h0
        apply hp
        rw [hpC, h0, map_zero]
      have hmem : (MvPolynomial.C (p.coeff 0) : AmbRing m) ∈ Q := by
        rw [hpC] at h
        simpa [MvPolynomial.algebraMap_eq] using h
      have hunit : IsUnit (MvPolynomial.C (p.coeff 0) : AmbRing m) :=
        (isUnit_iff_ne_zero.mpr hc0).map (MvPolynomial.C : ℂ →+* AmbRing m)
      exact (inferInstance : Q.IsPrime).ne_top (Q.eq_top_of_isUnit_mem hmem hunit)
    · have hdegpos : 0 < p.degree :=
        Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)
      obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p hdegpos.ne'
      obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hr
      have hq0 : q ≠ 0 := by
        rintro rfl
        apply hp
        rw [hq, mul_zero]
      have hnat : q.natDegree < n := by
        have h1 := Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hq0
        rw [← hq, Polynomial.natDegree_X_sub_C] at h1
        omega
      have h1 : Polynomial.aeval (uV : AmbRing m) (Polynomial.X - Polynomial.C r) =
          uV - MvPolynomial.C r := by
        simp [MvPolynomial.algebraMap_eq]
      rw [hq, map_mul, h1] at h
      rcases (inferInstance : Q.IsPrime).mem_or_mem h with h2 | h2
      · exact ⟨r, h2⟩
      · exact ih q.natDegree hnat q rfl hq0 h2

variable (ch : OriginChart)

theorem Fc_ne_zero : Fc ch ≠ 0 := by
  intro h0
  have := Fc_natDegree ch
  rw [h0] at this
  simp at this

theorem derivative_Fc_ne_zero : Polynomial.derivative (Fc ch) ≠ 0 := by
  intro h0
  have := Polynomial.derivative_eq_zero.mp h0
  rw [Fc_natDegree] at this
  omega

/-- `u ≡ r` forces `t² ≡ F(r)`, so `t` is constant mod `Q`. -/
theorem exists_t_const_of_u (hf : relation ch ∈ Q) (r : ℂ) (hu : uV - MvPolynomial.C r ∈ Q) :
    ∃ c : ℂ, tV - MvPolynomial.C c ∈ Q := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (Polynomial.eval r (Fc ch))
    (show 0 < 2 by norm_num)
  obtain ⟨g, hg⟩ := sub_dvd_aeval_sub (m := m) (Fc ch) (uV : AmbRing m) (MvPolynomial.C r)
  have h2 : Polynomial.aeval (algebraMap ℂ (AmbRing m) r) (Fc ch) =
      algebraMap ℂ (AmbRing m) (Polynomial.eval r (Fc ch)) := by
    rw [Polynomial.aeval_def]
    exact Polynomial.eval₂_at_apply (algebraMap ℂ (AmbRing m)) r
  simp only [MvPolynomial.algebraMap_eq] at h2
  have hm : Polynomial.aeval (uV : AmbRing m) (Fc ch) -
      MvPolynomial.C (Polynomial.eval r (Fc ch)) ∈ Q := by
    rw [← h2, hg]
    exact Q.mul_mem_right _ hu
  have key : (tV - MvPolynomial.C c) * (tV + MvPolynomial.C c) =
      relation ch + (Polynomial.aeval (uV : AmbRing m) (Fc ch) -
        MvPolynomial.C (Polynomial.eval r (Fc ch))) := by
    rw [← hc, map_pow]
    unfold relation
    ring
  have hmul : (tV - MvPolynomial.C c) * (tV + MvPolynomial.C c) ∈ Q := by
    rw [key]
    exact Q.add_mem hf hm
  rcases (inferInstance : Q.IsPrime).mem_or_mem hmul with h | h
  · exact ⟨c, h⟩
  · refine ⟨-c, ?_⟩
    rw [map_neg, sub_neg_eq_add]
    exact h

/-- `t ≡ c` forces `F(u) ≡ c²`, so `u` is constant mod `Q`. -/
theorem exists_u_const_of_t (hf : relation ch ∈ Q) (c : ℂ) (ht : tV - MvPolynomial.C c ∈ Q) :
    ∃ r : ℂ, uV - MvPolynomial.C r ∈ Q := by
  apply exists_root_mem_of_aeval_mem Q (Fc ch - Polynomial.C (c ^ 2))
  · intro h0
    have := congrArg Polynomial.natDegree h0
    rw [Polynomial.natDegree_sub_C, Fc_natDegree] at this
    simp at this
  · have key : Polynomial.aeval (uV : AmbRing m) (Fc ch - Polynomial.C (c ^ 2)) =
        (tV - MvPolynomial.C c) * (tV + MvPolynomial.C c) - relation ch := by
      simp only [map_sub, Polynomial.aeval_C, MvPolynomial.algebraMap_eq, map_pow]
      unfold relation
      ring
    rw [key]
    exact Q.sub_mem (Q.mul_mem_right _ ht) hf

/-- **`critical_constant`** (CM l.1749): `J̄ = 0` or `t̄ = 0` makes the projection `(ū, t̄)` constant. -/
theorem critical_constant (hf : relation ch ∈ Q) (h : resJ ch Q = 0 ∨ resT Q = 0) :
    ∃ c₀ c₁ : ℂ, uV - MvPolynomial.C c₀ ∈ Q ∧ tV - MvPolynomial.C c₁ ∈ Q := by
  obtain ⟨r, hr⟩ : ∃ r : ℂ, uV - MvPolynomial.C r ∈ Q := by
    rcases h with hJ | ht
    · have hmem : Polynomial.aeval (uV : AmbRing m) (Polynomial.derivative (Fc ch)) ∈ Q :=
        (primeResidueMap_eq_zero_iff Q _).mp hJ
      exact exists_root_mem_of_aeval_mem Q _ (derivative_Fc_ne_zero ch) hmem
    · have htQ : (tV : AmbRing m) ∈ Q := (primeResidueMap_eq_zero_iff Q _).mp ht
      have hmem : Polynomial.aeval (uV : AmbRing m) (Fc ch) ∈ Q := by
        have e : Polynomial.aeval (uV : AmbRing m) (Fc ch) = tV ^ 2 - relation ch := by
          unfold relation; ring
        rw [e]
        exact Q.sub_mem (Q.pow_mem_of_mem htQ 2 (by norm_num)) hf
      exact exists_root_mem_of_aeval_mem Q _ (Fc_ne_zero ch) hmem
  obtain ⟨c, hc⟩ := exists_t_const_of_u Q ch hf r hr
  exact ⟨r, c, hr, hc⟩

end Roots

/-! ### The intrinsic tangent is proper -/

section Proper

variable (ch : OriginChart) (Q : Ideal (AmbRing m)) [Q.IsPrime]

theorem pderiv_zero_rename (p : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPolynomial.pderiv (0 : Fin (m + 2))
      (MvPolynomial.rename (Fin.succ : Fin (m + 1) → Fin (m + 2)) p : AmbRing m) = 0 := by
  classical
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hv
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp (MvPolynomial.vars_rename Fin.succ p hv)
  exact Fin.succ_ne_zero a ha

theorem pderiv_succ_rename (p : MvPolynomial (Fin (m + 1)) ℂ) (j : Fin (m + 1)) :
    MvPolynomial.pderiv j.succ
      (MvPolynomial.rename (Fin.succ : Fin (m + 1) → Fin (m + 2)) p : AmbRing m) =
    MvPolynomial.rename (Fin.succ : Fin (m + 1) → Fin (m + 2)) (MvPolynomial.pderiv j p) :=
  MvPolynomial.pderiv_rename (Fin.succ_injective _) j p

/-- **Proper intrinsic tangent** (CM l.1799, `prop:origin-proper-tangent`): for a prime strictly
above `(f)`, `V ≠ K^{m+1}`. -/
theorem intrinsicTangent_ne_top (hf : Ideal.span {relation ch} < Q) :
    intrinsicTangent ch Q ≠ ⊤ := by
  classical
  intro htop
  have hbot : Q.comap (MvPolynomial.rename (Fin.succ : Fin (m + 1) → Fin (m + 2)) :
      MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] AmbRing m) = ⊥ := by
    apply ideal_eq_bot_of_pderiv_stable
    · exact (inferInstance : (Q.comap (MvPolynomial.rename
        (Fin.succ : Fin (m + 1) → Fin (m + 2)) :
        MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] AmbRing m)).IsPrime).ne_top
    · intro p hp i
      have hp' : (MvPolynomial.rename (Fin.succ : Fin (m + 1) → Fin (m + 2)) p : AmbRing m) ∈ Q :=
        Ideal.mem_comap.mp hp
      have hmem : (Pi.single i (1 : Q.ResidueField) : Fin (m + 1) → Q.ResidueField) ∈
          intrinsicTangent ch Q := by
        rw [htop]; trivial
      have hT := (mem_polynomialTangent_iff Q _).mp ((mem_intrinsicTangent_iff ch Q _).mp hmem)
        _ hp'
      have hsum : ∑ j : Fin (m + 1),
          primeResidueMap Q (MvPolynomial.pderiv j.succ
            (MvPolynomial.rename (Fin.succ : Fin (m + 1) → Fin (m + 2)) p : AmbRing m)) *
          graphMap (resJ ch Q) (resT Q) (Pi.single i (1 : Q.ResidueField)) j.succ =
          primeResidueMap Q (MvPolynomial.rename (Fin.succ : Fin (m + 1) → Fin (m + 2))
            (MvPolynomial.pderiv i p)) := by
        rw [Finset.sum_eq_single i]
        · rw [pderiv_succ_rename, graphMap_apply_succ, Pi.single_eq_same, mul_one]
        · intro j _ hji
          rw [graphMap_apply_succ, Pi.single_eq_of_ne hji, mul_zero]
        · intro h
          exact absurd (Finset.mem_univ i) h
      rw [Fin.sum_univ_succ, pderiv_zero_rename, map_zero, zero_mul, zero_add, hsum] at hT
      exact Ideal.mem_comap.mpr ((primeResidueMap_eq_zero_iff Q _).mp hT)
  exact contract_ne_bot ch Q hf hbot

end Proper

/-! ### Constant projection -/

section Projection

/-- Derivation form: if `d x = a * d y` for every `ℂ`-derivation, then `dx = a dy`. -/
theorem D_eq_smul {K : Type*} [Field K] [Algebra ℂ K] (x y a : K)
    (h : ∀ d : Derivation ℂ K K, d x = a * d y) :
    KaehlerDifferential.D ℂ K x = a • KaehlerDifferential.D ℂ K y := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff K _).mp
  intro l
  have h1 := h (l.compDer (KaehlerDifferential.D ℂ K))
  change l (KaehlerDifferential.D ℂ K x) = a * l (KaehlerDifferential.D ℂ K y) at h1
  rw [map_sub, map_smul, smul_eq_mul, h1, sub_self]

variable (ch : OriginChart) (Q : Ideal (AmbRing m)) [Q.IsPrime]

theorem tV_eq_X_succ_zero : (MvPolynomial.X (Fin.succ (0 : Fin (m + 1))) : AmbRing m) = tV := by
  unfold tV
  rw [← one_eq_succ_zero]

/-- The intrinsic vector `(d t̄, d Z̄₁, …, d Z̄_m)` of a `ℂ`-derivation of the residue field lies in
`V` (CM l.1771-1778; needs `J̄ ≠ 0` to read the graph). -/
theorem derivation_mem_intrinsicTangent (hf : relation ch ∈ Q) (hJ : resJ ch Q ≠ 0)
    (d : Derivation ℂ Q.ResidueField Q.ResidueField) :
    (fun j : Fin (m + 1) => d (primeResidueMap Q (MvPolynomial.X j.succ))) ∈
      intrinsicTangent ch Q := by
  have hx := derivation_mem_polynomialTangent (primeResidueMap Q) Q
    (fun p hp => (primeResidueMap_eq_zero_iff Q p).mpr hp) d
  have hr := tangent_relation ch Q hf hx
  have hr' : resJ ch Q * d (primeResidueMap Q (MvPolynomial.X 0)) =
      2 * resT Q * d (primeResidueMap Q (MvPolynomial.X 1)) := hr
  rw [mem_intrinsicTangent_iff]
  have hg : graphMap (resJ ch Q) (resT Q)
      (fun j : Fin (m + 1) => d (primeResidueMap Q (MvPolynomial.X j.succ))) =
      fun i => d (primeResidueMap Q (MvPolynomial.X i)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [graphMap_apply_zero]
      show 2 * resT Q * d (primeResidueMap Q (MvPolynomial.X (Fin.succ (0 : Fin (m + 1))))) /
        resJ ch Q = d (primeResidueMap Q (MvPolynomial.X 0))
      rw [← one_eq_succ_zero, div_eq_iff hJ]
      linear_combination (-1 : Q.ResidueField) * hr'
    · rfl
  rw [hg]
  exact hx

/-- **Constant projection** (CM l.1849, `thm:origin-normal-exclusion-projection`), `J̄ ≠ 0` case:
for a prime `Q` strictly above `(f)` with `J̄ ≠ 0` and normal-basis exclusion for its actual normal
quotient, the projection `(ū, t̄)` is constant. -/
theorem ell_projection_constant (hf : Ideal.span {relation ch} < Q) (hJ : resJ ch Q ≠ 0)
    (hexcl : ∀ S T : Finset (Fin (m + 1)),
      IsIntrinsicCoordinateNormalBasis ch Q S → IsFrameNormalBasis ch Q hJ T →
      ∀ i, i ≠ 0 → i ∈ S → i ∉ T → (∀ j, i < j → (j ∈ S ↔ j ∈ T)) → False) :
    ∃ c₀ c₁ : ℂ, uV - MvPolynomial.C c₀ ∈ Q ∧ tV - MvPolynomial.C c₁ ∈ Q := by
  classical
  have hrel : relation ch ∈ Q := hf.le (Ideal.subset_span rfl)
  have : Algebra.EssFiniteType ℂ Q.ResidueField := .comp ℂ (AmbRing m) Q.ResidueField
  have hq0 : (intrinsicTangent ch Q).mkQ ≠ 0 := by
    intro h0
    apply intrinsicTangent_ne_top ch Q hf
    rw [← Submodule.ker_mkQ (intrinsicTangent ch Q), h0, LinearMap.ker_zero]
  have hd := normal_basis_differential_dichotomy m (-(resJ ch Q)) (neg_ne_zero.mpr hJ)
    (intrinsicTangent ch Q).mkQ (Submodule.mkQ_surjective _) hq0
    (fun A B hA hB => hexcl A B hA hB)
  rcases hd with h0 | ⟨i, hi⟩
  · -- first alternative: `dt̄ = 0`
    have hdt : ∀ d : Derivation ℂ Q.ResidueField Q.ResidueField,
        d (primeResidueMap Q tV) = 0 := by
      intro d
      have h := h0 (fun j : Fin (m + 1) => d (primeResidueMap Q (MvPolynomial.X j.succ)))
        ((Submodule.Quotient.mk_eq_zero _).mpr
          (derivation_mem_intrinsicTangent ch Q hrel hJ d))
      have h' : d (primeResidueMap Q (MvPolynomial.X (Fin.succ (0 : Fin (m + 1))))) = 0 := h
      rwa [tV_eq_X_succ_zero] at h'
    have hD : KaehlerDifferential.D ℂ Q.ResidueField (primeResidueMap Q tV) = 0 := by
      have := D_eq_smul (primeResidueMap Q tV) (primeResidueMap Q tV) 0
        (fun d => by rw [zero_mul]; exact hdt d)
      rwa [zero_smul] at this
    obtain ⟨c, hc⟩ := constant_of_differential_eq_zero (primeResidueMap Q tV) hD
    have ht : tV - MvPolynomial.C c ∈ Q := sub_C_mem_of_residue_eq Q _ c hc
    obtain ⟨r, hr⟩ := exists_u_const_of_t Q ch hrel c ht
    exact ⟨r, c, hr, ht⟩
  · -- second alternative: `dz̄ᵢ = -J̄⁻¹ dt̄`
    have hdz : ∀ d : Derivation ℂ Q.ResidueField Q.ResidueField,
        d (primeResidueMap Q (MvPolynomial.X i.succ.succ)) =
          -(resJ ch Q)⁻¹ * d (primeResidueMap Q tV) := by
      intro d
      have h : d (primeResidueMap Q (MvPolynomial.X i.succ.succ)) =
          d (primeResidueMap Q (MvPolynomial.X (Fin.succ (0 : Fin (m + 1))))) /
            -(resJ ch Q) :=
        hi (fun j : Fin (m + 1) => d (primeResidueMap Q (MvPolynomial.X j.succ)))
          ((Submodule.Quotient.mk_eq_zero _).mpr
            (derivation_mem_intrinsicTangent ch Q hrel hJ d))
      rw [tV_eq_X_succ_zero] at h
      rw [h, div_neg, div_eq_inv_mul, neg_mul]
    have hJe : Polynomial.aeval (primeResidueMap Q uV) (Polynomial.derivative (Fc ch)) =
        resJ ch Q :=
      Polynomial.aeval_algHom_apply (primeResidueMap Q) uV _
    have hz : KaehlerDifferential.D ℂ Q.ResidueField
        (primeResidueMap Q (MvPolynomial.X i.succ.succ)) =
        -(Polynomial.aeval (primeResidueMap Q uV) (Polynomial.derivative (Fc ch)))⁻¹ •
          KaehlerDifferential.D ℂ Q.ResidueField (primeResidueMap Q tV) := by
      rw [hJe]
      exact D_eq_smul _ _ _ hdz
    have hJ' : Polynomial.aeval (primeResidueMap Q uV) (Polynomial.derivative (Fc ch)) ≠ 0 := by
      rw [hJe]; exact hJ
    have ht : (primeResidueMap Q tV) ^ 2 =
        Polynomial.aeval (primeResidueMap Q uV) (Fc ch) := by
      have h0 : primeResidueMap Q (relation ch) = 0 :=
        (primeResidueMap_eq_zero_iff Q _).mpr hrel
      unfold relation at h0
      rw [map_sub, map_pow, ← Polynomial.aeval_algHom_apply (primeResidueMap Q) uV (Fc ch)]
        at h0
      exact sub_eq_zero.mp h0
    obtain ⟨c₀, c₁, h1, h2⟩ := constant_of_quartic_differential (Fc ch) (Fc_squarefree ch)
      (two_le_natDegree_Fc ch) (primeResidueMap Q uV) (primeResidueMap Q tV) _ ht hJ' hz
    exact ⟨c₀, c₁, sub_C_mem_of_residue_eq Q _ c₀ h1, sub_C_mem_of_residue_eq Q _ c₁ h2⟩

/-- The statement used by E09.8: exclusion is only assumed when `J̄ ≠ 0`; the critical case
`J̄ = 0` is `critical_constant`. -/
theorem ell_projection_constant_of_exclusion (hf : Ideal.span {relation ch} < Q)
    (hexcl : ∀ hJ : resJ ch Q ≠ 0, ∀ S T : Finset (Fin (m + 1)),
      IsIntrinsicCoordinateNormalBasis ch Q S → IsFrameNormalBasis ch Q hJ T →
      ∀ i, i ≠ 0 → i ∈ S → i ∉ T → (∀ j, i < j → (j ∈ S ↔ j ∈ T)) → False) :
    ∃ c₀ c₁ : ℂ, uV - MvPolynomial.C c₀ ∈ Q ∧ tV - MvPolynomial.C c₁ ∈ Q := by
  by_cases hJ : resJ ch Q = 0
  · exact critical_constant Q ch (hf.le (Ideal.subset_span rfl)) (Or.inl hJ)
  · exact ell_projection_constant ch Q hf hJ (hexcl hJ)

end Projection

end CatalanCore.Elliptic.EPA
