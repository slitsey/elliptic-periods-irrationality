module

public import CatalanCore.Elliptic.EPA.Jet
public import OAI.NumberTheory.PiExponent.Jets.BranchContact
public import OAI.NumberTheory.PiExponent.Jets.DVRBranch
public import OAI.NumberTheory.PiExponent.Jets.FormalBranchOrderRational
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The elliptic branch layer (row E09.7, part 1: branches, contact, order bound)

Labels refer to the proof design §2 P4, P5 and §5 E09.7, and to the CM paper
(arXiv 2610.31112) §9, l.2200-2400 ("From actual branch contact to a curve prime").

Let `A` be a discrete valuation ring over `ℂ` with `Algebra.IsIntegral ℂ (ResidueField A)` and
`z = (u, t, Z₁, …, Z_m) : Fin (m+2) → A` a branch centred at `(0, 0, c)`, with `t² = F(u)`.
Let `ε = DVRBranch.expansion ℂ A : A →ₐ[ℂ] ℂ⟦s⟧`.

* `ellCentre c = (0, 0, c)`: the centre in the ambient coordinates.
* `ellBranchCoords s c τ ζ = (τ, ζ_i − c_i − L(τ))` (CM l.2257-2262): the *intrinsic* branch
  coordinates `(T, V) = (b₀, …, b_m)`; `u` does not enter (it is `U(τ)`).
* `ellBranch_u` (P4, CM l.2270): `ε u = U(ε t)`. Proof by the explicit divided difference of the
  quartic `F(x) − F(y) = (x − y) q`, `q(0) = 1`.
* `ellBranchPoint`, `subst_ellJet`: substituting `(T, V) = b` into `Φ_c(P)` gives the evaluated
  polynomial `P(ε z)` (CM l.2276-2284).
* `ellContact s v c z`: the contact `μ = min_i ord(b_i)/v_i` (CM l.2262-2268), the generic
  `BranchContact.contact` of OAI applied to the coordinates `b`. It is *total*: it is `0` when all
  `b_i` vanish; `exists_ne_zero_ellBranchCoords` shows that this does not happen for a nonconstant
  branch of the curve `t² = F(u)`, so `ellContact_eq_contact` identifies it with the OAI contact and
  `ellContact_pos` gives `0 < μ`.
* `ell_word_addVal_lower` (CM l.2281, branch substitution lemma): if `Φ_c(P) ∈ j_H` then
  `μ (H − c(W)) ≤ ord_s (D_W P (z))`.
* `ell_word_colength_lower`: the same in the form `length (A/(D_W P(z)))`.

The frame-word machinery `frameWord` and contact propagation `ellJet_frameWord_mem` are those of
`Frame.lean` and `Jet.lean`. Templates (openai/math fd4aeeb2, Apache License 2.0, Copyright
OpenAI): `Jets/DVRBranchJet`, `Jets/FormalBranchEvaluation`, `Jets/FormalBranchContact`.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

open CatalanCore.Elliptic OAI.PiExponent OAI.PiExponent.JetGeometry

variable {m : ℕ} {ch : OriginChart}

/-! ### The centre `(0, 0, c)` and the intrinsic branch coordinates -/

/-- The centre `(0, 0, c)` in the ambient coordinates `(u, t, Z)`. -/
def ellCentre (c : Fin m → ℂ) : Fin (m + 2) → ℂ :=
  Fin.cases (motive := fun _ => ℂ) 0 (Fin.cases (motive := fun _ => ℂ) 0 c)

/-- The centre array `j ↦ (0, 0, c_j)`, the form to which OAI `CurveCenters.Centered` and
`centerPlaces` apply. -/
def ellCentres {K : ℕ} (c : Fin K → Fin m → ℂ) : Fin K → Fin (m + 2) → ℂ :=
  fun j => ellCentre (c j)

@[simp] theorem ellCentre_zero (c : Fin m → ℂ) : ellCentre c 0 = 0 := rfl

theorem ellCentre_one (c : Fin m → ℂ) : ellCentre c 1 = 0 := by
  rw [one_eq_succ_zero]; rfl

@[simp] theorem ellCentre_succ_succ (c : Fin m → ℂ) (i : Fin m) : ellCentre c i.succ.succ = c i :=
  rfl

/-- The branch coordinates `(b₀, …, b_m) = (τ, ζ_i − c_i − L(τ))` of CM l.2257. -/
noncomputable def ellBranchCoords (s : OriginSeries ch) (c : Fin m → ℂ) (τ : PowerSeries ℂ)
    (ζ : Fin m → PowerSeries ℂ) : Fin (m + 1) → PowerSeries ℂ :=
  Fin.cases (motive := fun _ => PowerSeries ℂ) τ
    (fun i => ζ i - PowerSeries.C (c i) - PowerSeries.subst τ (Ls s))

@[simp] theorem ellBranchCoords_zero (s : OriginSeries ch) (c : Fin m → ℂ) (τ : PowerSeries ℂ)
    (ζ : Fin m → PowerSeries ℂ) : ellBranchCoords s c τ ζ 0 = τ := rfl

@[simp] theorem ellBranchCoords_succ (s : OriginSeries ch) (c : Fin m → ℂ) (τ : PowerSeries ℂ)
    (ζ : Fin m → PowerSeries ℂ) (i : Fin m) :
    ellBranchCoords s c τ ζ i.succ = ζ i - PowerSeries.C (c i) - PowerSeries.subst τ (Ls s) :=
  rfl

/-! ### Constant coefficients -/

theorem constantCoeff_Us (s : OriginSeries ch) : PowerSeries.constantCoeff (Us s) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Us, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, s.U_zero, map_zero]

theorem constantCoeff_Ls (s : OriginSeries ch) : PowerSeries.constantCoeff (Ls s) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Ls, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, s.L_zero, map_zero]

theorem constantCoeff_subst_of_zero {τ f : PowerSeries ℂ} (hτ : PowerSeries.constantCoeff τ = 0)
    (hf : PowerSeries.constantCoeff f = 0) : PowerSeries.constantCoeff (PowerSeries.subst τ f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hτ f hf

theorem constantCoeff_ellBranchCoords (s : OriginSeries ch) (c : Fin m → ℂ) {τ : PowerSeries ℂ}
    {ζ : Fin m → PowerSeries ℂ} (hτ : PowerSeries.constantCoeff τ = 0)
    (hζ : ∀ i, PowerSeries.constantCoeff (ζ i) = c i) (i : Fin (m + 1)) :
    PowerSeries.constantCoeff (ellBranchCoords s c τ ζ i) = 0 := by
  induction i using Fin.cases with
  | zero => exact hτ
  | succ i =>
    have hL := constantCoeff_subst_of_zero hτ (constantCoeff_Ls s)
    rw [ellBranchCoords_succ, map_sub, map_sub, hL, hζ i, PowerSeries.constantCoeff_C, sub_self,
      sub_zero]

theorem hasSubst_ellBranchCoords (s : OriginSeries ch) (c : Fin m → ℂ) {τ : PowerSeries ℂ}
    {ζ : Fin m → PowerSeries ℂ} (hτ : PowerSeries.constantCoeff τ = 0)
    (hζ : ∀ i, PowerSeries.constantCoeff (ζ i) = c i) :
    MvPowerSeries.HasSubst (ellBranchCoords s c τ ζ) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
    constantCoeff_ellBranchCoords s c hτ hζ i

/-! ### Substituting the branch into the packet `Φ_c` -/

/-- `liftSeries m f = f.toMvPowerSeries 0` (copy of the proof of OAI
`FormalLogTruncation.liftSeries_eq_toMvPowerSeries`). -/
theorem liftSeries_eq_toMv (m : ℕ) (f : PowerSeries ℂ) :
    liftSeries m f = f.toMvPowerSeries (0 : Fin (m + 1)) := by
  classical
  let e : Unit ↪ Fin (m + 1) := ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b⟩
  ext d
  rw [coeff_liftSeries]
  change (if d.tail = 0 then PowerSeries.coeff (d 0) f else 0) =
    MvPowerSeries.coeff d (MvPowerSeries.rename e f)
  by_cases ht : d.tail = 0
  · rw [if_pos ht]
    have hd : d = Finsupp.single 0 (d 0) := by
      calc
        d = Finsupp.cons (d 0) d.tail := (Finsupp.cons_tail d).symm
        _ = Finsupp.single 0 (d 0) := by rw [ht, Finsupp.cons_zero_eq_single_zero]
    have he : Finsupp.embDomain e (Finsupp.single () (d 0)) = Finsupp.single 0 (d 0) := by
      rw [Finsupp.embDomain_single]
      rfl
    conv_rhs => rw [hd, ← he, MvPowerSeries.coeff_embDomain_rename]
    rfl
  · rw [if_neg ht]
    symm
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨x, hx⟩
    have hx' : x = Finsupp.single () (x ()) := by ext; simp
    rw [hx', Finsupp.mapDomain_single] at hx
    apply ht
    rw [← hx]
    change (Finsupp.single (0 : Fin (m + 1)) (x ())).tail = 0
    ext i
    simp [Finsupp.tail_apply, Finsupp.single_apply, (Fin.succ_ne_zero i).symm]

theorem subst_liftSeries (a : Fin (m + 1) → PowerSeries ℂ) (ha : MvPowerSeries.HasSubst a)
    (f : PowerSeries ℂ) :
    MvPowerSeries.subst a (liftSeries m f) = PowerSeries.subst (a 0) f := by
  rw [liftSeries_eq_toMv, PowerSeries.subst_toMvPowerSeries ha]

/-- The ambient point `(U(b₀), b₀, c_i + b_{i+1} + L(b₀))` obtained from `Φ_c` by substituting
`(T, V) = b`. -/
noncomputable def ellBranchPoint (s : OriginSeries ch) (c : Fin m → ℂ)
    (a : Fin (m + 1) → PowerSeries ℂ) : Fin (m + 2) → PowerSeries ℂ :=
  Fin.cases (motive := fun _ => PowerSeries ℂ) (PowerSeries.subst (a 0) (Us s))
    (Fin.cases (motive := fun _ => PowerSeries ℂ) (a 0)
      (fun i => PowerSeries.C (c i) + a i.succ + PowerSeries.subst (a 0) (Ls s)))

/-- CM l.2276-2284: substituting the branch coordinates into `Φ_c(P)` gives `P(u, t, z)`. -/
theorem subst_ellJet (s : OriginSeries ch) (c : Fin m → ℂ) {a : Fin (m + 1) → PowerSeries ℂ}
    (ha : MvPowerSeries.HasSubst a) (P : AmbRing m) :
    MvPowerSeries.subst a (ellJet s c P) = MvPolynomial.aeval (ellBranchPoint s c a) P := by
  have heq : (MvPowerSeries.substAlgHom ha).comp (ellJet s c) =
      MvPolynomial.aeval (ellBranchPoint s c a) := by
    apply MvPolynomial.algHom_ext
    refine forall_amb ?_ ?_ ?_
    · rw [AlgHom.comp_apply, ellJet_X_zero, MvPowerSeries.substAlgHom_apply, subst_liftSeries a ha,
        MvPolynomial.aeval_X] <;> rfl
    · rw [AlgHom.comp_apply, ellJet_X_one, MvPowerSeries.substAlgHom_X, MvPolynomial.aeval_X,
        one_eq_succ_zero] <;> rfl
    · intro i
      rw [AlgHom.comp_apply, ellJet_X_succ_succ, map_add, map_add, MvPowerSeries.substAlgHom_X,
        MvPowerSeries.substAlgHom_apply, MvPowerSeries.substAlgHom_apply, subst_liftSeries a ha,
        MvPowerSeries.subst_C, MvPolynomial.aeval_X] <;> rfl
  have h := AlgHom.congr_fun heq P
  rwa [AlgHom.comp_apply, MvPowerSeries.substAlgHom_apply] at h

/-! ### P4: the expansion of `u` (CM l.2270) -/

theorem aeval_Fc_explicit {B : Type*} [CommRing B] [Algebra ℂ B] (x : B) (ch : OriginChart) :
    Polynomial.aeval x (Fc ch) =
      x + ((3 * ch.a : ℤ) : B) * x ^ 2 + ((3 * ch.a ^ 2 + ch.A : ℤ) : B) * x ^ 3 +
        ((ch.a ^ 3 + ch.A * ch.a + ch.B : ℤ) : B) * x ^ 4 := by
  have hF : Fc ch = Polynomial.X + Polynomial.C ((3 * ch.a : ℤ) : ℂ) * Polynomial.X ^ 2 +
      Polynomial.C ((3 * ch.a ^ 2 + ch.A : ℤ) : ℂ) * Polynomial.X ^ 3 +
      Polynomial.C ((ch.a ^ 3 + ch.A * ch.a + ch.B : ℤ) : ℂ) * Polynomial.X ^ 4 := by
    simp only [Fc, OriginChart.F, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C]
    simp only [eq_intCast]
  rw [hF]
  simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_intCast]

/-- Uniqueness of the root of `F(x) = F(y)` with zero constant term (`F(0) = 0`, `F′(0) = 1`):
`F(x) − F(y) = (x − y) q` with `q(0) = 1`. -/
theorem quartic_inj (x y : PowerSeries ℂ) (hx : PowerSeries.constantCoeff x = 0)
    (hy : PowerSeries.constantCoeff y = 0)
    (h : Polynomial.aeval x (Fc ch) = Polynomial.aeval y (Fc ch)) : x = y := by
  rw [aeval_Fc_explicit, aeval_Fc_explicit] at h
  set q : PowerSeries ℂ :=
    1 + ((3 * ch.a : ℤ) : PowerSeries ℂ) * (x + y) +
      ((3 * ch.a ^ 2 + ch.A : ℤ) : PowerSeries ℂ) * (x ^ 2 + x * y + y ^ 2) +
      ((ch.a ^ 3 + ch.A * ch.a + ch.B : ℤ) : PowerSeries ℂ) *
        (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) with hq
  have hfac : (x - y) * q = 0 := by
    rw [hq]
    linear_combination h
  have hq0 : q ≠ 0 := by
    intro hz
    have h1 : PowerSeries.constantCoeff q = 1 := by
      rw [hq]
      simp [hx, hy]
    rw [hz, map_zero] at h1
    exact zero_ne_one h1
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right hq0)

/-- Formal uniqueness for `F(u) = t²`, over `ℂ⟦s⟧`. -/
theorem series_u_eq (s : OriginSeries ch) (x τ : PowerSeries ℂ)
    (hx0 : PowerSeries.constantCoeff x = 0)
    (hrel : τ ^ 2 = Polynomial.aeval x (Fc ch)) : x = PowerSeries.subst τ (Us s) := by
  have hτ0 : PowerSeries.constantCoeff τ = 0 := by
    have h2 : (PowerSeries.constantCoeff τ) ^ 2 = 0 := by
      have := congrArg PowerSeries.constantCoeff hrel
      rw [aeval_Fc_explicit] at this
      simpa [hx0] using this
    exact (pow_eq_zero_iff two_ne_zero).mp h2
  have hHS : PowerSeries.HasSubst τ := PowerSeries.HasSubst.of_constantCoeff_zero' hτ0
  have hy0 : PowerSeries.constantCoeff (PowerSeries.subst τ (Us s)) = 0 :=
    constantCoeff_subst_of_zero hτ0 (constantCoeff_Us s)
  have hy : Polynomial.aeval (PowerSeries.subst τ (Us s)) (Fc ch) = τ ^ 2 := by
    have h1 := Polynomial.aeval_algHom_apply (PowerSeries.substAlgHom (R := ℂ) hHS) (Us s) (Fc ch)
    rw [PowerSeries.coe_substAlgHom hHS] at h1
    rw [h1, Us_eq, PowerSeries.subst_pow hHS, PowerSeries.subst_X hHS]
  exact quartic_inj x _ hx0 hy0 (by rw [← hrel, hy])

/-- The branch hypothesis on `z = (u, t, Z)`: the relation `t² = F(u)` (so `relation ch` vanishes). -/
def IsEllBranch (ch : OriginChart) {B : Type*} [CommRing B] [Algebra ℂ B]
    (z : Fin (m + 2) → B) : Prop :=
  z 1 ^ 2 = Polynomial.aeval (z 0) (Fc ch)

section Branch

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra ℂ A]
  [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

/-- P4 (D2-design §2, CM l.2270): `ε u = U(ε t)` for a branch with `t² = F(u)` and `u(p) = 0`. -/
theorem ellBranch_u (s : OriginSeries ch) (u t : A) (hrel : t ^ 2 = Polynomial.aeval u (Fc ch))
    (hu : CurveLocalOrder.residueAugmentation ℂ A u = 0) :
    DVRBranch.expansion ℂ A u = PowerSeries.subst (DVRBranch.expansion ℂ A t) (Us s) := by
  apply series_u_eq s
  · rw [DVRBranch.expansion_constantCoeff, hu]
  · rw [← map_pow (DVRBranch.expansion ℂ A) t 2, hrel, Polynomial.aeval_algHom_apply]

/-- The expansion of the coordinates `(ε t, ε Z_i)`. -/
noncomputable def ellExpCoords (s : OriginSeries ch) (c : Fin m → ℂ) (z : Fin (m + 2) → A) :
    Fin (m + 1) → PowerSeries ℂ :=
  ellBranchCoords s c (DVRBranch.expansion ℂ A (z 1))
    (fun i => DVRBranch.expansion ℂ A (z i.succ.succ))

variable (s : OriginSeries ch) (c : Fin m → ℂ) (z : Fin (m + 2) → A)

theorem ellExpCoords_zero : ellExpCoords s c z 0 = DVRBranch.expansion ℂ A (z 1) := rfl

theorem ellExpCoords_succ (i : Fin m) :
    ellExpCoords s c z i.succ = DVRBranch.expansion ℂ A (z i.succ.succ) - PowerSeries.C (c i) -
      PowerSeries.subst (DVRBranch.expansion ℂ A (z 1)) (Ls s) := rfl

/-- Residue conditions: the branch is centred at `(0, 0, c)`. -/
def IsCentredAt (c : Fin m → ℂ) (z : Fin (m + 2) → A) : Prop :=
  ∀ i, CurveLocalOrder.residueAugmentation ℂ A (z i) = ellCentre c i

variable {s c z}

theorem constantCoeff_exp_of_centred (hres : IsCentredAt c z) (i : Fin (m + 2)) :
    PowerSeries.constantCoeff (DVRBranch.expansion ℂ A (z i)) = ellCentre c i := by
  rw [DVRBranch.expansion_constantCoeff, hres i]

theorem hasSubst_ellExpCoords (hres : IsCentredAt c z) :
    MvPowerSeries.HasSubst (ellExpCoords s c z) :=
  hasSubst_ellBranchCoords s c
    (by rw [constantCoeff_exp_of_centred hres 1, ellCentre_one])
    (fun i => by rw [constantCoeff_exp_of_centred hres i.succ.succ, ellCentre_succ_succ])

theorem constantCoeff_ellExpCoords (hres : IsCentredAt c z) (i : Fin (m + 1)) :
    PowerSeries.constantCoeff (ellExpCoords s c z i) = 0 :=
  constantCoeff_ellBranchCoords s c
    (by rw [constantCoeff_exp_of_centred hres 1, ellCentre_one])
    (fun i => by rw [constantCoeff_exp_of_centred hres i.succ.succ, ellCentre_succ_succ]) i

/-- The substituted branch point is the expansion of `z` (uses P4). -/
theorem ellBranchPoint_expCoords (hrel : IsEllBranch ch z) (hres : IsCentredAt c z) :
    ellBranchPoint s c (ellExpCoords s c z) = fun i => DVRBranch.expansion ℂ A (z i) := by
  funext i
  revert i
  refine forall_amb ?_ ?_ ?_
  · have hu := ellBranch_u s (z 0) (z 1) hrel (by rw [hres 0, ellCentre_zero])
    simp only [ellBranchPoint, ellExpCoords, ellBranchCoords, Fin.cases_zero]
    exact hu.symm
  · rw [one_eq_succ_zero]
    simp only [ellBranchPoint, ellExpCoords, ellBranchCoords, Fin.cases_zero, Fin.cases_succ,
      one_eq_succ_zero]
  · intro i
    simp only [ellBranchPoint, ellExpCoords, ellBranchCoords, Fin.cases_zero, Fin.cases_succ]
    ring

/-- `ε (P(z)) = P(Φ_c-substituted)`: the actual evaluation is the substitution of the branch
coordinates into `Φ_c(P)` (CM l.2276-2284). -/
theorem subst_ellJet_expCoords (hrel : IsEllBranch ch z) (hres : IsCentredAt c z) (P : AmbRing m) :
    MvPowerSeries.subst (ellExpCoords s c z) (ellJet s c P) =
      DVRBranch.expansion ℂ A (MvPolynomial.aeval z P) := by
  rw [subst_ellJet s c (hasSubst_ellExpCoords hres), ellBranchPoint_expCoords hrel hres]
  exact (MvPolynomial.comp_aeval_apply (f := z) (DVRBranch.expansion ℂ A) P).symm

/-! ### The contact `μ` -/

open scoped Classical in
/-- The generic contact `min_i ord(a_i)/v_i` of OAI `BranchContact.contact`, made total by the value
`0` when all `a_i` vanish. -/
noncomputable def contactOrZero {n : ℕ} (v : Fin n → ℚ) (a : Fin n → PowerSeries ℂ) : ℚ :=
  if h : ∃ i, a i ≠ 0 then BranchContact.contact v a h else 0

theorem contactOrZero_eq {n : ℕ} (v : Fin n → ℚ) (a : Fin n → PowerSeries ℂ)
    (h : ∃ i, a i ≠ 0) : contactOrZero v a = BranchContact.contact v a h := by
  unfold contactOrZero
  rw [dif_pos h]

variable (s c z) in
/-- The elliptic contact `μ = min_{0 ≤ i ≤ m} ord_p(b_i)/v_i` of the branch `z` at the centre
`(0, 0, c)`, `b = (t, Z_i − c_i − L(t))` (CM l.2262-2268), for the jet weights `v`. Total: `0` if all
`b_i` vanish (impossible for a nonconstant branch of the curve, `exists_ne_zero_ellBranchCoords`).
Generic in the DVR `A`; E09.10c uses it with `A = ring p`. -/
noncomputable def ellContact (v : Fin (m + 1) → ℚ) : ℚ :=
  contactOrZero v (ellExpCoords s c z)

theorem ellContact_eq_contact (v : Fin (m + 1) → ℚ) (h : ∃ i, ellExpCoords s c z i ≠ 0) :
    ellContact s c z v = BranchContact.contact v (ellExpCoords s c z) h :=
  contactOrZero_eq _ _ h

/-- A nonconstant centred branch of `t² = F(u)` has some nonzero coordinate `b_i`
(CM l.2253-2256). -/
theorem exists_ne_zero_ellBranchCoords (hrel : IsEllBranch ch z) (hres : IsCentredAt c z)
    (hnc : ∃ i, z i ≠ algebraMap ℂ A (ellCentre c i)) :
    ∃ i, ellExpCoords s c z i ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have h0 : DVRBranch.expansion ℂ A (z 1) = 0 := hcon 0
  have hz1 : z 1 = 0 := by
    apply DVRBranch.expansion_injective ℂ A
    rw [h0, map_zero]
  have hz0 : z 0 = 0 := by
    apply DVRBranch.expansion_injective ℂ A
    rw [map_zero, ellBranch_u s (z 0) (z 1) hrel (by rw [hres 0, ellCentre_zero]), h0,
      PowerSeries.subst_zero_of_constantCoeff_zero (constantCoeff_Us s)]
  have hall : ∀ i, z i = algebraMap ℂ A (ellCentre c i) := by
    refine forall_amb ?_ ?_ ?_
    · rw [ellCentre_zero, map_zero, hz0]
    · rw [ellCentre_one, map_zero, hz1]
    · intro i
      have hi := hcon i.succ
      rw [ellExpCoords_succ, h0, PowerSeries.subst_zero_of_constantCoeff_zero
        (constantCoeff_Ls s), sub_zero, sub_eq_zero] at hi
      apply DVRBranch.expansion_injective ℂ A
      rw [hi, ellCentre_succ_succ, AlgHom.commutes] <;> rfl
  obtain ⟨i, hi⟩ := hnc
  exact hi (hall i)

theorem ellContact_pos {v : Fin (m + 1) → ℚ} (hv : ∀ i, 0 < v i) (hrel : IsEllBranch ch z)
    (hres : IsCentredAt c z) (hnc : ∃ i, z i ≠ algebraMap ℂ A (ellCentre c i)) :
    0 < ellContact s c z v := by
  have hne := exists_ne_zero_ellBranchCoords (s := s) hrel hres hnc
  rw [ellContact_eq_contact v hne]
  exact BranchContact.contact_pos v hv _ hne (constantCoeff_ellExpCoords hres)

/-! ### The order bound for frame words (CM l.2281) -/

/-- CM l.2281 (the branch substitution lemma), in valuation form: if `Φ_c(P) ∈ j_H`, then for every
frame word `W` with `D_W P(z) ≠ 0`, `μ (H − c(W)) ≤ ord_p (D_W P (z))`. -/
theorem ell_word_addVal_lower {v : Fin (m + 1) → ℚ} (hv : ∀ i, 0 < v i) (H : ℚ)
    (hrel : IsEllBranch ch z) (hres : IsCentredAt c z)
    (hnc : ∃ i, z i ≠ algebraMap ℂ A (ellCentre c i)) {P : AmbRing m}
    (hP : ellJet s c P ∈ rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m + 1)))
    (hne : MvPolynomial.aeval z (frameWord ch word P) ≠ 0) :
    ellContact s c z v * (H - (word.map v).sum) ≤
      ((IsDiscreteValuationRing.addVal A (MvPolynomial.aeval z (frameWord ch word P))).toNat : ℚ) := by
  have hcne := exists_ne_zero_ellBranchCoords (s := s) hrel hres hnc
  have hμ : 0 ≤ ellContact s c z v := (ellContact_pos hv hrel hres hnc).le
  have hf := ellJet_frameWord_mem s c (fun i => (hv i).le) hP word
  have hcontact : ∀ i (k : ℕ), (ellExpCoords s c z i).order = (k : ℕ∞) →
      ellContact s c z v * v i ≤ (k : ℚ) := by
    intro i k hk
    rw [ellContact_eq_contact v hcne]
    exact BranchContact.contact_bound v hv _ hcne i k hk
  have hord := FormalBranchOrder.rational_powerSeries_order_subst_of_mem_weightedIdeal v
    (fun i => (hv i).le) (ellContact s c z v) (H - (word.map v).sum) hμ _ (ellExpCoords s c z)
    (hasSubst_ellExpCoords hres) hf hcontact
  rw [subst_ellJet_expCoords hrel hres] at hord
  have hne' : DVRBranch.expansion ℂ A (MvPolynomial.aeval z (frameWord ch word P)) ≠ 0 :=
    (map_ne_zero_iff _ (DVRBranch.expansion_injective ℂ A)).mpr hne
  have hn := PowerSeries.order_eq_top.not.mpr hne'
  have hh := ENat.toNat_le_toNat hord hn
  rw [DVRBranch.expansion_order] at hh
  exact Nat.ceil_le.mp (by simpa using hh)

/-- The same bound in colength form: `μ (H − c(W)) ≤ length (A / (D_W P (z)))`. -/
theorem ell_word_colength_lower {v : Fin (m + 1) → ℚ} (hv : ∀ i, 0 < v i) (H : ℚ)
    (hrel : IsEllBranch ch z) (hres : IsCentredAt c z)
    (hnc : ∃ i, z i ≠ algebraMap ℂ A (ellCentre c i)) {P : AmbRing m}
    (hP : ellJet s c P ∈ rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m + 1)))
    (hne : MvPolynomial.aeval z (frameWord ch word P) ≠ 0) :
    ellContact s c z v * (H - (word.map v).sum) ≤
      ((Module.length A (A ⧸ Ideal.span {MvPolynomial.aeval z (frameWord ch word P)})).toNat :
        ℚ) := by
  rw [CurveLocalOrder.length_quotient_span_eq_addVal hne]
  exact ell_word_addVal_lower hv H hrel hres hnc hP word hne

end Branch

end CatalanCore.Elliptic.EPA
