module

public import CatalanCore.Elliptic.EPA.Geo.CentreIdeal
public import CatalanCore.Elliptic.EPA.Branch
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Contact and local length at a centred place (row E09.10c, algebraic core; ledger item P5)

Labels refer to the proof design (§2 P3, P5; §5 E09.10c) and to the CM paper
(arXiv 2610.31112) l.3563-3589 ("lengths of the centre ideal along a branch").

Let `V` be a discrete valuation ring over `ℂ` (residue field integral over `ℂ`), `z = (u, t, Z) :
Fin (m+2) → V` with `t² = F(u)` (`IsEllBranch`), centred at `(0, 0, c)` (`IsCentredAt`), `ε =
DVRBranch.expansion ℂ V`.  Let `I_c = centreIdealPt sc s c` be the centre ideal of
`Geo/CentreIdeal`, with the *truncation* `L_{<T₀}` of `L`.

* `order_subst_Us` (P5, first half): `ord U(τ) = 2 ord τ`, and `order_eq_of_rel` (any `x` with
  `x(0) = 0` and `τ² = F(x)`).
* `contact_truncCoords` (P5, second half): the contact `min_i ord(b_i)/v_i` of the branch
  coordinates is unchanged when `L` is truncated at `T₀` with `v_i < T₀ v₀`; this is OAI
  `BranchContact.contact_add_high_tail` with the tail `L(τ) − L_{<T₀}(τ)` of order `≥ T₀ ord τ`
  (`truncAt_tail_order`).
* `centreIdealPt_map_eq_span`, `centreIdealPt_length`: for a branch over `X = {f = 0}`,
  `I_c · V = (y)` is principal and `length (V / I_c V) = D · μ`, `μ = ellContact`
  (CM l.3563-3589).
* `centreIdealPt_map_eq_top`: at a place centred at a different centre `c'` the ideal is `V`.
* `length_toNat_le_addVal`: `length (V/I) ≤ ord x` for `0 ≠ x ∈ I` (used with `x = f(z)` off `X`).
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

namespace Geo

open CatalanCore.Elliptic OAI.PiExponent

variable {m : ℕ} {W : Weights m} {σ : ℚ} {ch : OriginChart}

/-! ### The series `L` truncated at `T₀`, and its tail -/

theorem coeff_Ls (s : OriginSeries ch) (k : ℕ) :
    PowerSeries.coeff k (Ls s) = ((PowerSeries.coeff k s.L : ℚ) : ℂ) := by
  simp [Ls, PowerSeries.coeff_map]

/-- `L_{<T₀}(τ) = Σ_{k<T₀} l_k τ^k`. -/
noncomputable def truncAt (s : OriginSeries ch) (T₀ : ℕ) (τ : PowerSeries ℂ) : PowerSeries ℂ :=
  ∑ k ∈ Finset.range T₀, PowerSeries.C (PowerSeries.coeff k (Ls s)) * τ ^ k

theorem coeff_truncSum (f : PowerSeries ℂ) (T₀ n : ℕ) :
    PowerSeries.coeff n
        (∑ k ∈ Finset.range T₀, PowerSeries.C (PowerSeries.coeff k f) * PowerSeries.X ^ k) =
      if n < T₀ then PowerSeries.coeff n f else 0 := by
  rw [map_sum]
  simp only [PowerSeries.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

theorem exists_trunc_decomp (f : PowerSeries ℂ) (T₀ : ℕ) :
    ∃ R : PowerSeries ℂ, f =
      (∑ k ∈ Finset.range T₀, PowerSeries.C (PowerSeries.coeff k f) * PowerSeries.X ^ k) +
        PowerSeries.X ^ T₀ * R := by
  have hd : (PowerSeries.X : PowerSeries ℂ) ^ T₀ ∣
      f - ∑ k ∈ Finset.range T₀, PowerSeries.C (PowerSeries.coeff k f) * PowerSeries.X ^ k := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro n hn
    rw [map_sub, coeff_truncSum, if_pos hn, sub_self]
  obtain ⟨R, hR⟩ := hd
  exact ⟨R, by rw [← hR]; ring⟩

theorem subst_truncSum {τ : PowerSeries ℂ} (hτ : PowerSeries.constantCoeff τ = 0)
    (f : PowerSeries ℂ) (T₀ : ℕ) :
    PowerSeries.subst τ
        (∑ k ∈ Finset.range T₀, PowerSeries.C (PowerSeries.coeff k f) * PowerSeries.X ^ k) =
      ∑ k ∈ Finset.range T₀, PowerSeries.C (PowerSeries.coeff k f) * τ ^ k := by
  have hHS : PowerSeries.HasSubst τ := PowerSeries.HasSubst.of_constantCoeff_zero' hτ
  have hsum := map_sum (PowerSeries.substAlgHom (R := ℂ) hHS)
    (fun k => PowerSeries.C (PowerSeries.coeff k f) * (PowerSeries.X : PowerSeries ℂ) ^ k)
    (Finset.range T₀)
  rw [PowerSeries.coe_substAlgHom hHS] at hsum
  rw [hsum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [PowerSeries.subst_mul hHS, PowerSeries.subst_pow hHS, PowerSeries.subst_X hHS,
    PowerSeries.subst_C]
  rfl

/-- The tail `L(τ) − L_{<T₀}(τ)` has order `≥ T₀ ord τ` (CM l.3570-3584). -/
theorem truncAt_tail_order (s : OriginSeries ch) (T₀ : ℕ) {τ : PowerSeries ℂ}
    (hτ : PowerSeries.constantCoeff τ = 0) :
    T₀ • τ.order ≤ PowerSeries.order (PowerSeries.subst τ (Ls s) - truncAt s T₀ τ) := by
  obtain ⟨R, hR⟩ := exists_trunc_decomp (Ls s) T₀
  have hHS : PowerSeries.HasSubst τ := PowerSeries.HasSubst.of_constantCoeff_zero' hτ
  have h1 : PowerSeries.subst τ (Ls s) =
      truncAt s T₀ τ + τ ^ T₀ * PowerSeries.subst τ R := by
    conv_lhs => rw [hR]
    rw [PowerSeries.subst_add hHS, PowerSeries.subst_mul hHS, PowerSeries.subst_pow hHS,
      PowerSeries.subst_X hHS, subst_truncSum hτ]
    rfl
  rw [h1, add_sub_cancel_left]
  exact (PowerSeries.le_order_pow τ T₀).trans (le_self_add.trans (PowerSeries.le_order_mul _ _))

/-- The branch coordinates with `L` truncated at `T₀`: `(τ, ζ_i − c_i − L_{<T₀}(τ))`. -/
noncomputable def truncCoords (s : OriginSeries ch) (T₀ : ℕ) (c : Fin m → ℂ) (τ : PowerSeries ℂ)
    (ζ : Fin m → PowerSeries ℂ) : Fin (m + 1) → PowerSeries ℂ :=
  Fin.cases (motive := fun _ => PowerSeries ℂ) τ
    (fun i => ζ i - PowerSeries.C (c i) - truncAt s T₀ τ)

/-- The tail `(0, L(τ) − L_{<T₀}(τ), …)` separating `truncCoords` from `ellBranchCoords`. -/
noncomputable def tailCoords (s : OriginSeries ch) (T₀ : ℕ) (τ : PowerSeries ℂ) :
    Fin (m + 1) → PowerSeries ℂ :=
  Fin.cases (motive := fun _ => PowerSeries ℂ) 0
    (fun _ => PowerSeries.subst τ (Ls s) - truncAt s T₀ τ)

/-! ### P5: the order of `U(τ)` -/

/-- If `x(0) = 0` and `τ² = F(x)` then `ord x = 2 ord τ` (`F(x) = x · (unit)`). -/
theorem order_eq_of_rel {x τ : PowerSeries ℂ} (hx0 : PowerSeries.constantCoeff x = 0)
    (hrel : τ ^ 2 = Polynomial.aeval x (Fc ch)) : x.order = 2 • τ.order := by
  rw [aeval_Fc_explicit] at hrel
  have hq : τ ^ 2 = x * (1 + ((3 * ch.a : ℤ) : PowerSeries ℂ) * x +
      ((3 * ch.a ^ 2 + ch.A : ℤ) : PowerSeries ℂ) * x ^ 2 +
      ((ch.a ^ 3 + ch.A * ch.a + ch.B : ℤ) : PowerSeries ℂ) * x ^ 3) := by
    rw [hrel]; ring
  have hqu : IsUnit (1 + ((3 * ch.a : ℤ) : PowerSeries ℂ) * x +
      ((3 * ch.a ^ 2 + ch.A : ℤ) : PowerSeries ℂ) * x ^ 2 +
      ((ch.a ^ 3 + ch.A * ch.a + ch.B : ℤ) : PowerSeries ℂ) * x ^ 3) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp [hx0]
  have h := congrArg PowerSeries.order hq
  rw [PowerSeries.order_mul, PowerSeries.order_zero_of_isUnit hqu, add_zero,
    PowerSeries.order_pow] at h
  exact h.symm

/-- P5 (first half, CM l.3570): `ord U(τ) = 2 ord τ`. -/
theorem order_subst_Us (s : OriginSeries ch) {τ : PowerSeries ℂ}
    (hτ : PowerSeries.constantCoeff τ = 0) :
    PowerSeries.order (PowerSeries.subst τ (Us s)) = 2 • τ.order := by
  have hHS : PowerSeries.HasSubst τ := PowerSeries.HasSubst.of_constantCoeff_zero' hτ
  have hy0 : PowerSeries.constantCoeff (PowerSeries.subst τ (Us s)) = 0 :=
    constantCoeff_subst_of_zero hτ (constantCoeff_Us s)
  have hy : Polynomial.aeval (PowerSeries.subst τ (Us s)) (Fc ch) = τ ^ 2 := by
    have h1 := Polynomial.aeval_algHom_apply (PowerSeries.substAlgHom (R := ℂ) hHS) (Us s) (Fc ch)
    rw [PowerSeries.coe_substAlgHom hHS] at h1
    rw [h1, Us_eq, PowerSeries.subst_pow hHS, PowerSeries.subst_X hHS]
  exact order_eq_of_rel hy0 hy.symm

/-! ### P5: the contact is unchanged by truncating `L` -/

/-- P5 (second half, CM l.3570-3584): if `v_i < T₀ v₀` then truncating `L` at `T₀` does not change
the contact `min_i ord(b_i)/v_i`.  OAI `BranchContact.contact_add_high_tail` with the tail
`L(τ) − L_{<T₀}(τ)`. -/
theorem contact_truncCoords (s : OriginSeries ch) (T₀ : ℕ) (c : Fin m → ℂ)
    (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 < v i) (hT : ∀ i : Fin m, v i.succ < (T₀ : ℚ) * v 0)
    {τ : PowerSeries ℂ} (ζ : Fin m → PowerSeries ℂ) (hτ : PowerSeries.constantCoeff τ = 0)
    (hne : ∃ i, ellBranchCoords s c τ ζ i ≠ 0) :
    ∃ hne' : ∃ i, truncCoords s T₀ c τ ζ i ≠ 0,
      BranchContact.contact v (truncCoords s T₀ c τ ζ) hne' =
        BranchContact.contact v (ellBranchCoords s c τ ζ) hne := by
  have htr : truncCoords s T₀ c τ ζ =
      fun i => ellBranchCoords s c τ ζ i + tailCoords (m := m) s T₀ τ i := by
    funext i
    induction i using Fin.cases with
    | zero => exact (add_zero τ).symm
    | succ j =>
      show ζ j - PowerSeries.C (c j) - truncAt s T₀ τ =
        (ζ j - PowerSeries.C (c j) - PowerSeries.subst τ (Ls s)) +
          (PowerSeries.subst τ (Ls s) - truncAt s T₀ τ)
      ring
  have ht : ∀ i (k : ℕ), (tailCoords (m := m) s T₀ τ i).order = (k : ℕ∞) →
      BranchContact.contact v (ellBranchCoords s c τ ζ) hne * v i < (k : ℚ) := by
    intro i k hk
    induction i using Fin.cases with
    | zero =>
      exfalso
      have h0 : tailCoords (m := m) s T₀ τ 0 = 0 := rfl
      rw [h0, PowerSeries.order_zero] at hk
      exact absurd hk (ENat.top_ne_natCast k)
    | succ j =>
      have hk' : PowerSeries.order (PowerSeries.subst τ (Ls s) - truncAt s T₀ τ) = (k : ℕ∞) := hk
      have hTpos : 0 < T₀ := by
        rcases Nat.eq_zero_or_pos T₀ with h0 | h0
        · exfalso
          have h1 : v j.succ < 0 := by simpa [h0] using hT j
          exact absurd (hv j.succ) (not_lt.mpr h1.le)
        · exact h0
      have hτne : τ ≠ 0 := by
        intro h0
        apply absurd hk'
        rw [h0, PowerSeries.subst_zero_of_constantCoeff_zero (constantCoeff_Ls s)]
        have : truncAt s T₀ (0 : PowerSeries ℂ) = 0 := by
          unfold truncAt
          refine Finset.sum_eq_zero fun n _ => ?_
          rcases n with _ | n
          · have : PowerSeries.coeff 0 (Ls s) = 0 := by
              rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact constantCoeff_Ls s
            simp [this]
          · simp
        rw [this, sub_zero, PowerSeries.order_zero]
        exact ENat.top_ne_natCast k
      have hn1 : 1 ≤ τ.order := PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hτ
      obtain ⟨n, hn⟩ : ∃ n : ℕ, τ.order = (n : ℕ∞) :=
        ⟨τ.order.toNat, (PowerSeries.coe_toNat_order hτne).symm⟩
      have hnpos : 0 < n := by
        rw [hn] at hn1
        exact_mod_cast hn1
      have hle : T₀ • τ.order ≤ (k : ℕ∞) := by
        rw [← hk']; exact truncAt_tail_order s T₀ hτ
      have h3 : T₀ * n ≤ k := by
        rw [hn] at hle
        have : ((T₀ * n : ℕ) : ℕ∞) ≤ (k : ℕ∞) := by simpa [nsmul_eq_mul] using hle
        exact_mod_cast this
      have hc : BranchContact.contact v (ellBranchCoords s c τ ζ) hne ≤ (n : ℚ) / v 0 := by
        have h7 := BranchContact.contact_le v (ellBranchCoords s c τ ζ) hne 0 hτne
        have h8 : (ellBranchCoords s c τ ζ 0).order = (n : ℕ∞) := hn
        rwa [h8, ENat.toNat_natCast] at h7
      have hv0 := hv 0
      have hvj := hv j.succ
      have h4 : (n : ℚ) / v 0 * v j.succ < (T₀ : ℚ) * n := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hv0]
        have h5 := hT j
        have h6 : (0 : ℚ) < n := by exact_mod_cast hnpos
        nlinarith
      calc BranchContact.contact v (ellBranchCoords s c τ ζ) hne * v j.succ
          ≤ (n : ℚ) / v 0 * v j.succ := mul_le_mul_of_nonneg_right hc hvj.le
        _ < (T₀ : ℚ) * n := h4
        _ ≤ (k : ℚ) := by exact_mod_cast h3
  have hne' : ∃ i, truncCoords s T₀ c τ ζ i ≠ 0 := by
    rw [htr]; exact BranchContact.add_not_all_zero v hv _ (tailCoords (m := m) s T₀ τ) hne ht
  refine ⟨hne', ?_⟩
  have key : ∀ (f : Fin (m + 1) → PowerSeries ℂ) (hf : f = fun i => ellBranchCoords s c τ ζ i + tailCoords (m := m) s T₀ τ i)
      (h1 : ∃ i, f i ≠ 0),
      BranchContact.contact v f h1 =
        BranchContact.contact v (fun i => ellBranchCoords s c τ ζ i + tailCoords (m := m) s T₀ τ i)
          (BranchContact.add_not_all_zero v hv _ (tailCoords (m := m) s T₀ τ) hne ht) := by
    intro f hf
    subst hf
    intro h1
    rfl
  rw [key _ htr hne']
  exact BranchContact.contact_add_high_tail v hv _ (tailCoords (m := m) s T₀ τ) hne ht

/-! ### The local length of the centre ideal at a branch -/

section DVR

variable {V : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra ℂ V]
  [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField V)]

/-- `ε t`. -/
noncomputable def tauSeries (z : Fin (m + 2) → V) : PowerSeries ℂ :=
  DVRBranch.expansion ℂ V (z 1)

/-- `(ε Z_i)_i`. -/
noncomputable def zetaSeries (z : Fin (m + 2) → V) : Fin m → PowerSeries ℂ :=
  fun j => DVRBranch.expansion ℂ V (z j.succ.succ)

theorem ellExpCoords_eq (s : OriginSeries ch) (c : Fin m → ℂ) (z : Fin (m + 2) → V) :
    ellExpCoords s c z = ellBranchCoords s c (tauSeries z) (zetaSeries z) := rfl

theorem exp_algebraMap (r : ℂ) : DVRBranch.expansion ℂ V (algebraMap ℂ V r) = PowerSeries.C r := by
  rw [AlgHom.commutes]
  simp [PowerSeries.algebraMap_apply]

theorem expansion_aeval_truncL (s : OriginSeries ch) (T₀ : ℕ) (z : Fin (m + 2) → V) :
    DVRBranch.expansion ℂ V (MvPolynomial.aeval z (truncL s T₀)) =
      truncAt s T₀ (tauSeries z) := by
  unfold truncL truncAt tauSeries
  simp only [map_sum, map_mul, map_pow, MvPolynomial.aeval_C, tV, MvPolynomial.aeval_X,
    exp_algebraMap, coeff_Ls]

/-- The generators of `I_c` indexed by the branch coordinates `b_0 = t`, `b_{i+1} = Z_i − c_i −
L_{<T₀}(t)`: `t^a` and `(Z_i − c_i − L_{<T₀}(t))^{b_i}`. -/
noncomputable def genElt (sc : EpaScale W σ) (s : OriginSeries ch) (c : Fin m → ℂ) :
    Fin (m + 1) → AmbRing m :=
  Fin.cases (motive := fun _ => AmbRing m) (tV ^ sc.a)
    (fun j => (zV j - MvPolynomial.C (c j) - truncL s sc.T₀) ^ sc.b j)

/-- The exponents `a, b_1, …, b_m` of `genElt`. -/
def genExp (sc : EpaScale W σ) : Fin (m + 1) → ℕ :=
  Fin.cases (motive := fun _ => ℕ) sc.a sc.b

theorem genExp_pos (sc : EpaScale W σ) (i : Fin (m + 1)) : 0 < genExp sc i := by
  induction i using Fin.cases with
  | zero => exact sc.a_pos
  | succ j => exact sc.b_pos j

theorem genExp_mul_jetWt (sc : EpaScale W σ) (i : Fin (m + 1)) :
    (genExp sc i : ℚ) * jetWt W i = sc.D := by
  induction i using Fin.cases with
  | zero =>
    show (sc.a : ℚ) * W.v₀ = sc.D
    rw [mul_comm]; exact sc.a_eq
  | succ j =>
    show (sc.b j : ℚ) * (W.w j / W.θ) = sc.D
    rw [mul_comm]; exact sc.b_eq j

theorem genElt_mem (sc : EpaScale W σ) (s : OriginSeries ch) (c : Fin m → ℂ) (i : Fin (m + 1)) :
    genElt sc s c i ∈ centreGens sc s c := by
  induction i using Fin.cases with
  | zero => exact Or.inl (by simp [genElt])
  | succ j => exact Or.inr ⟨j, rfl⟩

theorem expansion_genElt (sc : EpaScale W σ) (s : OriginSeries ch) (c : Fin m → ℂ)
    (z : Fin (m + 2) → V) (i : Fin (m + 1)) :
    DVRBranch.expansion ℂ V (MvPolynomial.aeval z (genElt sc s c i)) =
      truncCoords s sc.T₀ c (tauSeries z) (zetaSeries z) i ^ genExp sc i := by
  induction i using Fin.cases with
  | zero =>
    show DVRBranch.expansion ℂ V (MvPolynomial.aeval z (tV ^ sc.a)) =
      (DVRBranch.expansion ℂ V (z 1)) ^ sc.a
    simp [tV]
  | succ j =>
    show DVRBranch.expansion ℂ V (MvPolynomial.aeval z
        ((zV j - MvPolynomial.C (c j) - truncL s sc.T₀) ^ sc.b j)) =
      (DVRBranch.expansion ℂ V (z j.succ.succ) - PowerSeries.C (c j) -
        truncAt s sc.T₀ (DVRBranch.expansion ℂ V (z 1))) ^ sc.b j
    simp only [map_pow, map_sub, zV, MvPolynomial.aeval_X, MvPolynomial.aeval_C, exp_algebraMap,
      expansion_aeval_truncL, tauSeries]

/-- `addVal` of a generator whose branch coordinate is nonzero. -/
theorem addVal_genElt (sc : EpaScale W σ) (s : OriginSeries ch) (c : Fin m → ℂ)
    (z : Fin (m + 2) → V) (i : Fin (m + 1))
    (hi : truncCoords s sc.T₀ c (tauSeries z) (zetaSeries z) i ≠ 0) :
    IsDiscreteValuationRing.addVal V (MvPolynomial.aeval z (genElt sc s c i)) =
      ((genExp sc i * (truncCoords s sc.T₀ c (tauSeries z) (zetaSeries z) i).order.toNat : ℕ) :
        ℕ∞) := by
  rw [← DVRBranch.expansion_order ℂ V, expansion_genElt, PowerSeries.order_pow,
    ← PowerSeries.coe_toNat_order hi]
  simp [nsmul_eq_mul]

/-- `z₁ = t` divides `z₀ = u` along a branch centred at the origin of `u` (CM l.2270: `ord u =
2 ord t`). -/
theorem dvd_u_of_branch {c : Fin m → ℂ} {z : Fin (m + 2) → V} (hrel : IsEllBranch ch z)
    (hres : IsCentredAt c z) : z 1 ∣ z 0 := by
  have hrel' : z 1 ^ 2 = Polynomial.aeval (z 0) (Fc ch) := hrel
  rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, ← DVRBranch.expansion_order ℂ V,
    ← DVRBranch.expansion_order ℂ V]
  have hx0 : PowerSeries.constantCoeff (DVRBranch.expansion ℂ V (z 0)) = 0 := by
    rw [DVRBranch.expansion_constantCoeff, hres 0, ellCentre_zero]
  have hrelε : (DVRBranch.expansion ℂ V (z 1)) ^ 2 =
      Polynomial.aeval (DVRBranch.expansion ℂ V (z 0)) (Fc ch) := by
    rw [← map_pow (DVRBranch.expansion ℂ V) (z 1) 2, hrel', Polynomial.aeval_algHom_apply]
  have h := order_eq_of_rel hx0 hrelε
  rw [h, two_nsmul]
  exact le_self_add

/-- CM l.3563-3589, structure of `I_c · V` along a branch over `X`: it is principal, generated by
the generator of least order, and its colength is `D · μ` where `μ` is the elliptic contact
(`ellContact`, for the *full* `L`; P5 says that the truncated `L` gives the same `μ`). -/
theorem centreIdealPt_map_eq_span (sc : EpaScale W σ) (s : OriginSeries ch) (c : Fin m → ℂ)
    {z : Fin (m + 2) → V} (hrel : IsEllBranch ch z) (hres : IsCentredAt c z)
    (hnc : ∃ i, z i ≠ algebraMap ℂ V (ellCentre c i)) :
    ∃ y : V, y ≠ 0 ∧
      (centreIdealPt sc s c).map (MvPolynomial.aeval z : AmbRing m →ₐ[ℂ] V).toRingHom =
        Ideal.span {y} ∧
      ((IsDiscreteValuationRing.addVal V y).toNat : ℚ) = sc.D * ellContact s c z (jetWt W) := by
  classical
  have hrel' : z 1 ^ 2 = Polynomial.aeval (z 0) (Fc ch) := hrel
  have hv : ∀ i, 0 < jetWt W i := jetWt_pos W
  have hτ0 : PowerSeries.constantCoeff (tauSeries z) = 0 := by
    unfold tauSeries
    rw [DVRBranch.expansion_constantCoeff, hres 1, ellCentre_one]
  have hT : ∀ i : Fin m, jetWt W i.succ < (sc.T₀ : ℚ) * jetWt W 0 := fun i => by
    simpa using sc.T₀_gt i
  have hne : ∃ i, ellBranchCoords s c (tauSeries z) (zetaSeries z) i ≠ 0 :=
    exists_ne_zero_ellBranchCoords (s := s) hrel hres hnc
  obtain ⟨hne', hcont⟩ := contact_truncCoords s sc.T₀ c (jetWt W) hv hT (zetaSeries z) hτ0 hne
  have hμ : ellContact s c z (jetWt W) =
      BranchContact.contact (jetWt W) (truncCoords s sc.T₀ c (tauSeries z) (zetaSeries z)) hne' := by
    rw [hcont]
    exact ellContact_eq_contact (s := s) (c := c) (z := z) (jetWt W) hne
  obtain ⟨i0, hi0, hcont0⟩ := BranchContact.exists_attains (jetWt W)
    (truncCoords s sc.T₀ c (tauSeries z) (zetaSeries z)) hne'
  have hbound : ∀ i (k : ℕ),
      (truncCoords s sc.T₀ c (tauSeries z) (zetaSeries z) i).order = (k : ℕ∞) →
        ellContact s c z (jetWt W) * jetWt W i ≤ (k : ℚ) := fun i k hk => by
    rw [hμ]
    exact BranchContact.contact_bound _ hv _ hne' i k hk
  -- the generator of least order
  have hvaly := addVal_genElt sc s c z i0 hi0
  have hy0 : MvPolynomial.aeval z (genElt sc s c i0) ≠ 0 := by
    intro h
    rw [h, IsDiscreteValuationRing.addVal_zero] at hvaly
    exact ENat.top_ne_natCast _ hvaly
  have hNq : ((genExp sc i0 *
      (truncCoords s sc.T₀ c (tauSeries z) (zetaSeries z) i0).order.toNat : ℕ) : ℚ) =
        sc.D * ellContact s c z (jetWt W) := by
    rw [hμ, hcont0]
    push_cast
    have h1 := genExp_mul_jetWt (W := W) sc i0
    have h2 := (hv i0).ne'
    rw [← h1]
    field_simp
  -- every generator is divisible by `y`
  have hdvd_gen : ∀ i, MvPolynomial.aeval z (genElt sc s c i0) ∣
      MvPolynomial.aeval z (genElt sc s c i) := by
    intro i
    by_cases hti : truncCoords s sc.T₀ c (tauSeries z) (zetaSeries z) i = 0
    · have h0 : MvPolynomial.aeval z (genElt sc s c i) = 0 := by
        apply DVRBranch.expansion_injective ℂ V
        rw [expansion_genElt, hti, zero_pow (genExp_pos sc i).ne', map_zero]
      rw [h0]
      exact dvd_zero _
    · apply (IsDiscreteValuationRing.addVal_le_iff_dvd).mp
      rw [hvaly, addVal_genElt sc s c z i hti]
      have hki : (truncCoords s sc.T₀ c (tauSeries z) (zetaSeries z) i).order =
          ((truncCoords s sc.T₀ c (tauSeries z) (zetaSeries z) i).order.toNat : ℕ∞) :=
        (PowerSeries.coe_toNat_order hti).symm
      have h1 := hbound i _ hki
      have h2 := genExp_mul_jetWt (W := W) sc i
      have h3 : ((genExp sc i0 *
          (truncCoords s sc.T₀ c (tauSeries z) (zetaSeries z) i0).order.toNat : ℕ) : ℚ) ≤
          ((genExp sc i *
            (truncCoords s sc.T₀ c (tauSeries z) (zetaSeries z) i).order.toNat : ℕ) : ℚ) := by
        rw [hNq]
        push_cast
        rw [← h2]
        have hge : (0 : ℚ) < genExp sc i := by exact_mod_cast genExp_pos sc i
        nlinarith
      have h4 : genExp sc i0 *
          (truncCoords s sc.T₀ c (tauSeries z) (zetaSeries z) i0).order.toNat ≤
          genExp sc i * (truncCoords s sc.T₀ c (tauSeries z) (zetaSeries z) i).order.toNat := by
        exact_mod_cast h3
      exact_mod_cast h4
  have hdvd : ∀ g ∈ centreGens sc s c,
      MvPolynomial.aeval z (genElt sc s c i0) ∣ MvPolynomial.aeval z g := by
    intro g hg
    rcases hg with hg | ⟨j, rfl⟩
    · rcases hg with rfl | rfl | rfl
      · exact hdvd_gen 0
      · have h0 : MvPolynomial.aeval z (uV ^ sc.a : AmbRing m) = (z 0) ^ sc.a := by
          simp [uV]
        have h1 : MvPolynomial.aeval z (genElt sc s c 0) = (z 1) ^ sc.a := by
          show MvPolynomial.aeval z (tV ^ sc.a) = _
          simp [tV]
        rw [h0]
        have h2 := hdvd_gen 0
        rw [h1] at h2
        exact h2.trans (pow_dvd_pow_of_dvd (dvd_u_of_branch hrel hres) sc.a)
      · have h0 : MvPolynomial.aeval z (relation (m := m) ch) = 0 := by
          unfold relation
          rw [map_sub, map_pow, ← Polynomial.aeval_algHom_apply]
          have hu : MvPolynomial.aeval z (uV : AmbRing m) = z 0 := by simp [uV]
          have ht : MvPolynomial.aeval z (tV : AmbRing m) = z 1 := by simp [tV]
          rw [hu, ht, hrel', sub_self]
        rw [h0]
        exact dvd_zero _
    · exact hdvd_gen j.succ
  refine ⟨MvPolynomial.aeval z (genElt sc s c i0), hy0, ?_, ?_⟩
  · apply le_antisymm
    · unfold centreIdealPt
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨g, hg, rfl⟩
      exact Ideal.mem_span_singleton.mpr (hdvd g hg)
    · rw [Ideal.span_singleton_le_iff_mem]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span (genElt_mem sc s c i0))
  · rw [hvaly, ENat.toNat_natCast]
    exact hNq

/-- CM l.3563-3589: `length (V / I_c V) = D · μ` along a branch over `X` centred at `c`. -/
theorem centreIdealPt_length (sc : EpaScale W σ) (s : OriginSeries ch) (c : Fin m → ℂ)
    {z : Fin (m + 2) → V} (hrel : IsEllBranch ch z) (hres : IsCentredAt c z)
    (hnc : ∃ i, z i ≠ algebraMap ℂ V (ellCentre c i)) :
    ((Module.length V (V ⧸ (centreIdealPt sc s c).map
        (MvPolynomial.aeval z : AmbRing m →ₐ[ℂ] V).toRingHom)).toNat : ℚ) =
      sc.D * ellContact s c z (jetWt W) := by
  obtain ⟨y, hy, hI, hlen⟩ := centreIdealPt_map_eq_span sc s c hrel hres hnc
  rw [hI, CurveLocalOrder.length_quotient_span_eq_addVal hy]
  exact hlen

/-- At a place centred at another centre `c' ≠ c`, the ideal `I_c` becomes the unit ideal. -/
theorem centreIdealPt_map_eq_top (sc : EpaScale W σ) (s : OriginSeries ch) {c c' : Fin m → ℂ}
    {z : Fin (m + 2) → V} (hres : IsCentredAt c' z) (hne : c ≠ c') :
    (centreIdealPt sc s c).map (MvPolynomial.aeval z : AmbRing m →ₐ[ℂ] V).toRingHom = ⊤ := by
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ c' i := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  refine Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem _ (zpow_mem_centreIdealPt sc s c i)) ?_
  have hres_t : CurveLocalOrder.residueAugmentation ℂ V
      (MvPolynomial.aeval z (truncL s sc.T₀)) = 0 := by
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp (truncL_mem_span_tV (m := m) s sc.T₀)
    rw [hr, map_mul, map_mul]
    have : MvPolynomial.aeval z (tV : AmbRing m) = z 1 := by simp [tV]
    rw [this, hres 1, ellCentre_one, zero_mul]
  show IsUnit ((MvPolynomial.aeval z) ((zV i - MvPolynomial.C (c i) - truncL s sc.T₀) ^ sc.b i))
  rw [map_pow]
  refine IsUnit.pow _ ?_
  rw [map_sub, map_sub]
  simp only [zV, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  rw [← IsDiscreteValuationRing.addVal_eq_zero_iff, ← DVRBranch.expansion_order ℂ V]
  by_contra hcon
  have h0 : PowerSeries.constantCoeff (DVRBranch.expansion ℂ V
      (z i.succ.succ - algebraMap ℂ V (c i) - MvPolynomial.aeval z (truncL s sc.T₀))) = 0 :=
    PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp hcon
  rw [DVRBranch.expansion_constantCoeff, map_sub, map_sub, hres_t, hres i.succ.succ,
    CurveLocalOrder.residueAugmentation_algebraMap, ellCentre_succ_succ, sub_zero] at h0
  exact hi (sub_eq_zero.mp h0).symm

/-- `length (V/I) ≤ ord x` for `0 ≠ x ∈ I` (the quotient `V/I` is a quotient of `V/(x)`). -/
theorem length_toNat_le_addVal {I : Ideal V} {x : V} (hx : x ∈ I) (hx0 : x ≠ 0) :
    (Module.length V (V ⧸ I)).toNat ≤ (IsDiscreteValuationRing.addVal V x).toNat := by
  obtain ⟨y, hI⟩ : ∃ y, I = Ideal.span {y} :=
    ⟨_, (Submodule.IsPrincipal.span_singleton_generator I).symm⟩
  subst hI
  have hxy : y ∣ x := Ideal.mem_span_singleton.mp hx
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, zero_dvd_iff] at hxy
    exact hx0 hxy
  rw [CurveLocalOrder.length_quotient_span_eq_addVal hy0]
  exact ENat.toNat_le_toNat (IsDiscreteValuationRing.addVal_le_iff_dvd.mpr hxy)
    (fun h => hx0 (IsDiscreteValuationRing.addVal_eq_top_iff.mp h))

end DVR

end Geo

end CatalanCore.Elliptic.EPA
