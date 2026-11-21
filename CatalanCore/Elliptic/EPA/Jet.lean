module

public import CatalanCore.Elliptic.EPA.Frame
public import CatalanCore.Elliptic.EPA.Reduce
public import OAI.NumberTheory.PiExponent.Jets.JetGeometry
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Algebra.Polynomial.Derivation

/-!
# The packet map `Φ_c` and contact propagation (row E09.2)

Labels refer to the proof design §5 E09.2 (CM l.657–732, 1992–2030, 2239) and §2 P1.

For a centre `c ∈ ℂ^m` the packet homomorphism sends `P ∈ ℂ[u, t, Z]` to
`Φ_c(P) = P(U(T), T, c + V + L(T)) ∈ ℂ⟦T, V₁, …, V_m⟧ = MvPowerSeries (Fin (m+1)) ℂ`
(variable `0` is `T`, variable `i.succ` is `V_i`).

* `liftSeries`: `ℂ⟦T⟧ → ℂ⟦T, V⟧` (shape of OAI `FormalLogJet.liftSeries`).
* `Us`, `Ls`, `Js`: `U`, `L` and `J = F′(U)` as series over `ℂ`.
* `ellJet s c : AmbRing m →ₐ[ℂ] MvPowerSeries (Fin (m+1)) ℂ` is `Φ_c`.
* `ellJet_relation`: `Φ_c(f) = 0` (from `F(U) = T²`).
* `ellJet_frame_zero`, `ellJet_frame_succ`: the intertwining `Φ_c ∘ D_0 = −J ∂_T ∘ Φ_c`,
  `Φ_c ∘ D_{i+1} = ∂_{V_i} ∘ Φ_c` (CM l.705; uses `J U′ = 2T` and `L′ J = −1`).
* `ellJet_frameWord_mem`: contact propagation: if `Φ_c(P) ∈ j_R` (weighted order `≥ R`) then
  `Φ_c(D_word P) ∈ j_{R − Σ v_word}` (CM l.1992–2030, 2239). Template: OAI
  `FormalLogJet.formalJet_polynomialFrameWord_vanishing` (openai/math fd4aeeb2, Apache License 2.0,
  Copyright OpenAI), with the log series replaced by `L` and `y = 1 + T` by `u = U(T), t = T`.
* `ellJet_coeff_monomial`: the D1 bridge: the coefficient of `T^{r₀} V^{r₁…}` of `Φ_c(u^k t^b Z^α)`
  is the packet entry `packetEntry` of `Packet.lean`.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

open CatalanCore.Elliptic OAI.PiExponent.JetGeometry

variable {m : ℕ}

/-! ### The lift `ℂ⟦T⟧ → ℂ⟦T, V₁, …, V_m⟧` -/

/-- `ℂ⟦T⟧ → ℂ⟦T, V⟧`, the series in the first variable (shape of OAI `FormalLogJet.liftSeries`). -/
noncomputable def liftSeries (m : ℕ) : PowerSeries ℂ →+* MvPowerSeries (Fin (m + 1)) ℂ :=
  (MvPowerSeries.finSuccEquiv ℂ m).symm.toRingHom.comp (PowerSeries.map MvPowerSeries.C)

@[simp] theorem coeff_liftSeries (m : ℕ) (f : PowerSeries ℂ) (d : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff d (liftSeries m f) =
      if d.tail = 0 then PowerSeries.coeff (d 0) f else 0 := by
  have h := MvPowerSeries.coeff_coeff_finSuccEquiv (liftSeries m f) (k := d 0) (x := d.tail)
  rw [Finsupp.cons_tail] at h
  rw [← h]
  simp [liftSeries, PowerSeries.coeff_map, MvPowerSeries.coeff_C]

@[simp] theorem liftSeries_X (m : ℕ) :
    liftSeries m (PowerSeries.X : PowerSeries ℂ) = MvPowerSeries.X 0 := by
  apply (MvPowerSeries.finSuccEquiv ℂ m).injective
  simp [liftSeries]

@[simp] theorem liftSeries_C (m : ℕ) (r : ℂ) :
    liftSeries m (PowerSeries.C r) = MvPowerSeries.C r := by
  apply (MvPowerSeries.finSuccEquiv ℂ m).injective
  simp [liftSeries]

theorem pderiv_zero_liftSeries (m : ℕ) (f : PowerSeries ℂ) :
    MvPowerSeries.pderiv (R := ℂ) (0 : Fin (m + 1)) (liftSeries m f) =
      liftSeries m (PowerSeries.derivative f) := by
  ext d
  rw [MvPowerSeries.coeff_pderiv, coeff_liftSeries, coeff_liftSeries, PowerSeries.coeff_derivative]
  have ht : (d + Finsupp.single (0 : Fin (m + 1)) 1).tail = d.tail := by
    ext i
    simp [Finsupp.tail_apply]
  simp only [ht, Finsupp.add_apply, Finsupp.single_eq_same]
  split_ifs <;> simp_all

theorem pderiv_succ_liftSeries (m : ℕ) (i : Fin m) (f : PowerSeries ℂ) :
    MvPowerSeries.pderiv (R := ℂ) i.succ (liftSeries m f) = 0 := by
  ext d
  rw [MvPowerSeries.coeff_pderiv, coeff_liftSeries, MvPowerSeries.coeff_zero]
  have ht : (d + Finsupp.single i.succ 1).tail ≠ 0 := by
    intro h
    have hi := DFunLike.congr_fun h i
    simp [Finsupp.tail_apply] at hi
  simp [ht]

/-! ### Generic helpers -/

/-- A ring homomorphism commuting with the structure maps commutes with `aeval`. -/
theorem ringHom_aeval {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (g : A →+* B) (hg : ∀ r : R, g (algebraMap R A r) = algebraMap R B r) (x : A)
    (p : Polynomial R) : g (Polynomial.aeval x p) = Polynomial.aeval (g x) p := by
  have h : g.comp (algebraMap R A) = algebraMap R B := RingHom.ext hg
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, h]

theorem aeval_map_int {B : Type*} [CommRing B] [Algebra ℂ B] [Algebra ℤ B] (x : B)
    (p : Polynomial ℤ) :
    Polynomial.aeval x (p.map (Int.castRingHom ℂ)) = Polynomial.aeval x p := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map,
    RingHom.ext_int ((algebraMap ℂ B).comp (Int.castRingHom ℂ)) (algebraMap ℤ B)]

theorem derivation_map_of_X {σ S : Type*} [CommRing S] [Algebra ℂ S]
    (φ : MvPolynomial σ ℂ →ₐ[ℂ] S) (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (δ : Derivation ℂ S S)
    (hX : ∀ i, φ (D (MvPolynomial.X i)) = δ (φ (MvPolynomial.X i)))
    (p : MvPolynomial σ ℂ) : φ (D p) = δ (φ p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hp, hX]

theorem forall_amb {P : Fin (m + 2) → Prop} (h0 : P 0) (h1 : P 1)
    (h2 : ∀ i : Fin m, P i.succ.succ) : ∀ j, P j := by
  intro j
  induction j using Fin.cases with
  | zero => exact h0
  | succ j =>
    induction j using Fin.cases with
    | zero => simpa using h1
    | succ i => exact h2 i

theorem liftSeries_aeval (m : ℕ) (f : PowerSeries ℂ) (p : Polynomial ℂ) :
    liftSeries m (Polynomial.aeval f p) = Polynomial.aeval (liftSeries m f) p :=
  ringHom_aeval (R := ℂ) (liftSeries m) (fun r => by
    simp [PowerSeries.algebraMap_apply, MvPowerSeries.algebraMap_apply]) f p

/-! ### The series `U`, `L`, `J` over `ℂ` -/

variable {ch : OriginChart}

/-- `U(T)` over `ℂ`. -/
noncomputable def Us (s : OriginSeries ch) : PowerSeries ℂ :=
  PowerSeries.map (Rat.castHom ℂ) s.U

/-- `L(T)` over `ℂ`. -/
noncomputable def Ls (s : OriginSeries ch) : PowerSeries ℂ :=
  PowerSeries.map (Rat.castHom ℂ) s.L

/-- `J(T) = F′(U(T))`. -/
noncomputable def Js (s : OriginSeries ch) : PowerSeries ℂ :=
  Polynomial.aeval (Us s) (Polynomial.derivative (Fc ch))

theorem aeval_Fc {B : Type*} [CommRing B] [Algebra ℂ B] [Algebra ℤ B] (x : B) (ch : OriginChart) :
    Polynomial.aeval x (Fc ch) = Polynomial.aeval x ch.F :=
  aeval_map_int x ch.F

theorem aeval_derivative_Fc {B : Type*} [CommRing B] [Algebra ℂ B] [Algebra ℤ B] (x : B)
    (ch : OriginChart) :
    Polynomial.aeval x (Polynomial.derivative (Fc ch)) =
      Polynomial.aeval x (Polynomial.derivative ch.F) := by
  unfold Fc
  rw [Polynomial.derivative_map]
  exact aeval_map_int x _

/-- `F(U(T)) = T²` over `ℂ`. -/
theorem Us_eq (s : OriginSeries ch) :
    Polynomial.aeval (Us s) (Fc ch) = (PowerSeries.X : PowerSeries ℂ) ^ 2 := by
  have h := ringHom_aeval (R := ℤ) (PowerSeries.map (Rat.castHom ℂ)) (fun r => by simp)
    s.U ch.F
  rw [s.U_eq, map_pow, PowerSeries.map_X] at h
  unfold Fc
  rw [aeval_map_int]
  exact h.symm

/-- `J U′ = 2T` (differentiate `F(U) = T²`). -/
theorem Js_mul_deriv_Us (s : OriginSeries ch) :
    Js s * PowerSeries.derivative (Us s) = 2 * PowerSeries.X := by
  have h := Derivation.comp_aeval_eq (PowerSeries.derivative (R := ℂ)) (Fc ch) (a := Us s)
  rw [Us_eq, smul_eq_mul] at h
  rw [Js, ← h]
  simp [PowerSeries.derivative_pow]

theorem derivative_map_series (φ : ℚ →+* ℂ) (f : PowerSeries ℚ) :
    PowerSeries.derivative (PowerSeries.map φ f) =
      PowerSeries.map φ (PowerSeries.derivative f) := by
  ext n
  simp [PowerSeries.coeff_derivative, PowerSeries.coeff_map]

/-- `L′ J = −1`. -/
theorem Ls_deriv_mul_Js (s : OriginSeries ch) :
    PowerSeries.derivative (Ls s) * Js s = -1 := by
  have h : PowerSeries.map (Rat.castHom ℂ)
      (PowerSeries.derivative s.L * Polynomial.aeval s.U (Polynomial.derivative ch.F)) =
      PowerSeries.map (Rat.castHom ℂ) (-1) := by rw [s.L_deriv]
  rw [map_mul, map_neg, map_one,
    ringHom_aeval (R := ℤ) (PowerSeries.map (Rat.castHom ℂ)) (fun r => by simp),
    ← derivative_map_series] at h
  rw [Js, aeval_derivative_Fc]
  exact h

/-! ### The packet homomorphism -/

/-- The images of the generators `u, t, Z_i`: `U(T)`, `T`, `c_i + V_i + L(T)`. -/
noncomputable def ellGen (s : OriginSeries ch) (c : Fin m → ℂ) :
    Fin (m + 2) → MvPowerSeries (Fin (m + 1)) ℂ :=
  Fin.cases (motive := fun _ => MvPowerSeries (Fin (m + 1)) ℂ) (liftSeries m (Us s))
    (Fin.cases (motive := fun _ => MvPowerSeries (Fin (m + 1)) ℂ) (MvPowerSeries.X 0)
      (fun i => MvPowerSeries.C (c i) + MvPowerSeries.X i.succ + liftSeries m (Ls s)))

/-- The packet homomorphism `Φ_c : ℂ[u,t,Z] → ℂ⟦T, V⟧`,
`P ↦ P(U(T), T, c + V + L(T))` (CM l.657–732). -/
noncomputable def ellJet (s : OriginSeries ch) (c : Fin m → ℂ) :
    AmbRing m →ₐ[ℂ] MvPowerSeries (Fin (m + 1)) ℂ :=
  MvPolynomial.aeval (ellGen s c)

variable (s : OriginSeries ch) (c : Fin m → ℂ)

theorem ellJet_X_zero : ellJet s c (MvPolynomial.X 0) = liftSeries m (Us s) := by
  simp only [ellJet, MvPolynomial.aeval_X, ellGen, Fin.cases_zero]

theorem ellJet_X_one : ellJet s c (MvPolynomial.X 1) = MvPowerSeries.X 0 := by
  rw [one_eq_succ_zero (m := m)]
  simp only [ellJet, MvPolynomial.aeval_X, ellGen, Fin.cases_succ, Fin.cases_zero]

theorem ellJet_X_succ_succ (i : Fin m) :
    ellJet s c (MvPolynomial.X i.succ.succ) =
      MvPowerSeries.C (c i) + MvPowerSeries.X i.succ + liftSeries m (Ls s) := by
  simp only [ellJet, MvPolynomial.aeval_X, ellGen, Fin.cases_succ]

theorem ellJet_uV : ellJet s c (uV : AmbRing m) = liftSeries m (Us s) := ellJet_X_zero s c

theorem ellJet_tV : ellJet s c (tV : AmbRing m) = MvPowerSeries.X 0 := ellJet_X_one s c

theorem ellJet_zV (i : Fin m) :
    ellJet s c (zV i : AmbRing m) =
      MvPowerSeries.C (c i) + MvPowerSeries.X i.succ + liftSeries m (Ls s) :=
  ellJet_X_succ_succ s c i

theorem ellJet_aeval_uV (p : Polynomial ℂ) :
    ellJet s c (Polynomial.aeval (uV : AmbRing m) p) =
      liftSeries m (Polynomial.aeval (Us s) p) := by
  rw [← Polynomial.aeval_algHom_apply (ellJet s c), ellJet_uV, liftSeries_aeval]

/-- `Φ_c(f) = 0` for `f = t² − F(u)` (from `F(U(T)) = T²`). -/
theorem ellJet_relation : ellJet s c (relation ch : AmbRing m) = 0 := by
  have h1 := ellJet_aeval_uV s c (Fc ch)
  rw [Us_eq, map_pow, liftSeries_X] at h1
  unfold relation
  rw [map_sub, map_pow, ellJet_tV, h1, sub_self]

/-! ### Frame derivations on the generators -/

theorem frameZero_uV (ch : OriginChart) : frameDeriv ch 0 (uV : AmbRing m) = -2 * tV := by
  have hC : (MvPolynomial.C (-2 : ℂ) : AmbRing m) = -2 := by rw [map_neg, map_ofNat]
  rw [frameDeriv_zero_apply]
  simp [pderiv_uV, pderiv_tV, hC, zero_ne_one_amb.symm] <;> ring

theorem frameZero_tV (ch : OriginChart) :
    frameDeriv ch 0 (tV : AmbRing m) = -Polynomial.aeval (uV : AmbRing m)
      (Polynomial.derivative (Fc ch)) := by
  have h1 : ∀ i : Fin m, (i.succ.succ : Fin (m + 2)) ≠ 1 := fun i => (one_ne_succ_succ i).symm
  rw [frameDeriv_zero_apply]
  simp [pderiv_uV, pderiv_tV, zero_ne_one_amb, h1] <;> ring

theorem frameZero_zV (ch : OriginChart) (j : Fin m) : frameDeriv ch 0 (zV j : AmbRing m) = 1 := by
  have h0 : MvPolynomial.pderiv (0 : Fin (m + 2)) (zV j : AmbRing m) = 0 := by
    unfold zV; exact MvPolynomial.pderiv_X_of_ne (Fin.succ_ne_zero _)
  have h1 : MvPolynomial.pderiv (1 : Fin (m + 2)) (zV j : AmbRing m) = 0 := by
    unfold zV; exact MvPolynomial.pderiv_X_of_ne (one_ne_succ_succ j).symm
  have hsum : ∑ i : Fin m, MvPolynomial.pderiv i.succ.succ (zV j : AmbRing m) = 1 := by
    rw [Finset.sum_eq_single j]
    · unfold zV; exact MvPolynomial.pderiv_X_self _
    · intro i _ hij
      unfold zV
      exact MvPolynomial.pderiv_X_of_ne
        (fun h => hij (Fin.succ_injective _ (Fin.succ_injective _ h)).symm)
    · simp
  rw [frameDeriv_zero_apply, h0, h1, hsum]
  simp

theorem frameSucc_zV (ch : OriginChart) (i j : Fin m) :
    frameDeriv ch i.succ (zV j : AmbRing m) = if i = j then 1 else 0 := by
  rw [frameDeriv_succ]
  unfold zV
  by_cases hij : i = j
  · subst hij; simp [MvPolynomial.pderiv_X_self]
  · rw [if_neg hij]
    exact MvPolynomial.pderiv_X_of_ne
      (fun h => hij (Fin.succ_injective _ (Fin.succ_injective _ h)).symm)

/-! ### The intertwining relations (CM l.705) -/

/-- `Φ_c ∘ D_0 = −J ∂_T ∘ Φ_c`. -/
theorem ellJet_frame_zero (P : AmbRing m) :
    ellJet s c (frameDeriv ch 0 P) =
      -(liftSeries m (Js s)) * MvPowerSeries.pderiv (R := ℂ) 0 (ellJet s c P) := by
  have hu : liftSeries m (Js s) * MvPowerSeries.pderiv (R := ℂ) (0 : Fin (m + 1))
      (liftSeries m (Us s)) = 2 * MvPowerSeries.X 0 := by
    rw [pderiv_zero_liftSeries, ← map_mul (liftSeries m), Js_mul_deriv_Us, map_mul (liftSeries m),
      liftSeries_X, map_ofNat]
  have hL : liftSeries m (Js s) * liftSeries m (PowerSeries.derivative (Ls s)) = -1 := by
    rw [← map_mul (liftSeries m), mul_comm, Ls_deriv_mul_Js, map_neg, map_one]
  have hu' : -(liftSeries m (Js s)) * MvPowerSeries.pderiv (R := ℂ) (0 : Fin (m + 1))
      (liftSeries m (Us s)) = -(2 * MvPowerSeries.X 0) := by
    rw [neg_mul, hu]
  have hX : ∀ j : Fin (m + 2),
      ellJet s c (frameDeriv ch 0 (MvPolynomial.X j)) =
        ((-(liftSeries m (Js s)) : MvPowerSeries (Fin (m + 1)) ℂ) •
          MvPowerSeries.pderiv (R := ℂ) (0 : Fin (m + 1))) (ellJet s c (MvPolynomial.X j)) := by
    refine forall_amb ?_ ?_ ?_
    · show ellJet s c (frameDeriv ch 0 uV) = _
      rw [frameZero_uV, ellJet_X_zero, Derivation.smul_apply, smul_eq_mul, hu',
        map_mul (ellJet s c), ellJet_tV, map_neg (ellJet s c), map_ofNat, neg_mul]
    · show ellJet s c (frameDeriv ch 0 tV) = _
      rw [frameZero_tV, map_neg (ellJet s c), ellJet_aeval_uV, ellJet_X_one,
        Derivation.smul_apply, smul_eq_mul, MvPowerSeries.pderiv_X_self, mul_one]
      all_goals rfl
    · intro i
      show ellJet s c (frameDeriv ch 0 (zV i)) = _
      rw [frameZero_zV, map_one (ellJet s c), ellJet_X_succ_succ, Derivation.smul_apply,
        smul_eq_mul, map_add, map_add, MvPowerSeries.pderiv_C,
        MvPowerSeries.pderiv_X_of_ne (Fin.succ_ne_zero i), pderiv_zero_liftSeries]
      linear_combination hL
  have key := derivation_map_of_X (ellJet s c) (frameDeriv ch 0)
    ((-(liftSeries m (Js s)) : MvPowerSeries (Fin (m + 1)) ℂ) •
      MvPowerSeries.pderiv (R := ℂ) (0 : Fin (m + 1))) hX P
  rw [key, Derivation.smul_apply, smul_eq_mul]

/-- `Φ_c ∘ D_{i+1} = ∂_{V_i} ∘ Φ_c`. -/
theorem ellJet_frame_succ (i : Fin m) (P : AmbRing m) :
    ellJet s c (frameDeriv ch i.succ P) =
      MvPowerSeries.pderiv (R := ℂ) i.succ (ellJet s c P) := by
  have hX : ∀ j : Fin (m + 2),
      ellJet s c (frameDeriv ch i.succ (MvPolynomial.X j)) =
        MvPowerSeries.pderiv (R := ℂ) i.succ (ellJet s c (MvPolynomial.X j)) := by
    refine forall_amb ?_ ?_ ?_
    · show ellJet s c (frameDeriv ch i.succ uV) = _
      rw [frameDeriv_succ, pderiv_uV, if_neg (Fin.succ_ne_zero _), map_zero, ellJet_X_zero,
        pderiv_succ_liftSeries]
    · show ellJet s c (frameDeriv ch i.succ tV) = _
      rw [frameDeriv_succ, pderiv_tV, if_neg (one_ne_succ_succ i).symm, map_zero, ellJet_X_one,
        MvPowerSeries.pderiv_X_of_ne (Fin.succ_ne_zero i).symm]
    · intro k
      show ellJet s c (frameDeriv ch i.succ (zV k)) = _
      rw [frameSucc_zV, ellJet_X_succ_succ, map_add, map_add, MvPowerSeries.pderiv_C,
        pderiv_succ_liftSeries]
      by_cases hik : i = k
      · subst hik
        simp [MvPowerSeries.pderiv_X_self]
      · rw [if_neg hik, map_zero, MvPowerSeries.pderiv_X_of_ne
          (fun h => hik (Fin.succ_injective _ h).symm)]
        simp
  exact derivation_map_of_X (ellJet s c) (frameDeriv ch i.succ)
    (MvPowerSeries.pderiv (R := ℂ) i.succ) hX P

/-! ### Contact propagation (CM l.1992–2030, 2239) -/

theorem pderiv_mem_rationalWeightedIdeal {σ : Type*} (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (f : MvPowerSeries σ ℂ) (hf : f ∈ rationalWeightedIdeal v hv H) (i : σ) :
    MvPowerSeries.pderiv (R := ℂ) i f ∈ rationalWeightedIdeal v hv (H - v i) := by
  rw [mem_rationalWeightedIdeal] at hf ⊢
  intro d hd
  have hw : Finsupp.weight v (d + Finsupp.single i 1) < H := by
    rw [map_add, Finsupp.weight_single, one_nsmul]; linarith
  rw [MvPowerSeries.coeff_pderiv, hf _ hw, zero_mul]

/-- One frame derivation lowers the contact order by its weight. -/
theorem ellJet_frameDeriv_mem {v : Fin (m + 1) → ℚ} (hv : ∀ i, 0 ≤ v i) {R : ℚ} {P : AmbRing m}
    (hP : ellJet s c P ∈ rationalWeightedIdeal v hv R) (j : Fin (m + 1)) :
    ellJet s c (frameDeriv ch j P) ∈ rationalWeightedIdeal v hv (R - v j) := by
  induction j using Fin.cases with
  | zero =>
    rw [ellJet_frame_zero]
    exact Ideal.mul_mem_left _ _ (pderiv_mem_rationalWeightedIdeal v hv R _ hP 0)
  | succ i =>
    rw [ellJet_frame_succ]
    exact pderiv_mem_rationalWeightedIdeal v hv R _ hP i.succ

/-- Contact propagation: a frame word of weight `Σ v` lowers the contact order by `Σ v`. -/
theorem ellJet_frameWord_mem {v : Fin (m + 1) → ℚ} (hv : ∀ i, 0 ≤ v i) {R : ℚ} {P : AmbRing m}
    (hP : ellJet s c P ∈ rationalWeightedIdeal v hv R) (word : List (Fin (m + 1))) :
    ellJet s c (frameWord ch word P) ∈ rationalWeightedIdeal v hv (R - (word.map v).sum) := by
  induction word with
  | nil => simpa using hP
  | cons i w ih =>
    have h := ellJet_frameDeriv_mem s c hv ih i
    have e : R - ((i :: w).map v).sum = R - (w.map v).sum - v i := by
      simp only [List.map_cons, List.sum_cons]; ring
    rw [e, frameWord_cons]
    exact h

/-- Corollary used downstream: `Φ_c(P) ∈ j_R` and a word of weight `≤ R'` give `Φ_c(D_word P) ∈ j_{R - R'}`
weakened to a smaller order. -/
theorem ellJet_frameWord_mem_of_le {v : Fin (m + 1) → ℚ} (hv : ∀ i, 0 ≤ v i) {R R' : ℚ}
    {P : AmbRing m} (hP : ellJet s c P ∈ rationalWeightedIdeal v hv R)
    (word : List (Fin (m + 1))) (hw : R' ≤ R - (word.map v).sum) :
    ellJet s c (frameWord ch word P) ∈ rationalWeightedIdeal v hv R' := by
  have h := ellJet_frameWord_mem s c hv hP word
  rw [mem_rationalWeightedIdeal] at h ⊢
  intro d hd
  exact h d (lt_of_lt_of_le hd hw)

/-! ### The D1 bridge: coefficients of `Φ_c(u^k t^b Z^α)` are `packetEntry` -/

/-- `ℂ⟦T⟧[V] → ℂ⟦T, V⟧`, sending `V_i` to the variable `i.succ` and a series to its lift. -/
noncomputable def polyJet (m : ℕ) :
    MvPolynomial (Fin m) (PowerSeries ℂ) →+* MvPowerSeries (Fin (m + 1)) ℂ :=
  MvPolynomial.eval₂Hom (liftSeries m) (fun i => MvPowerSeries.X i.succ)

@[simp] theorem polyJet_C (a : PowerSeries ℂ) : polyJet m (MvPolynomial.C a) = liftSeries m a := by
  simp [polyJet]

@[simp] theorem polyJet_X (i : Fin m) :
    polyJet m (MvPolynomial.X i) = MvPowerSeries.X i.succ := by
  simp [polyJet]

/-- The coefficient of `polyJet p` at `T^s V^β` is the `T^s`-coefficient of the `V^β`-coefficient
of `p`. -/
theorem coeff_polyJet (p : MvPolynomial (Fin m) (PowerSeries ℂ)) :
    ∀ (n : ℕ) (β : Fin m →₀ ℕ),
      MvPowerSeries.coeff (Finsupp.cons n β) (polyJet m p) = PowerSeries.coeff n (p.coeff β) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    intro n β
    rw [polyJet_C, coeff_liftSeries]
    by_cases h : β = 0
    · simp [h, MvPolynomial.coeff_C]
    · simp [h, Ne.symm h, MvPolynomial.coeff_C]
  | add p q hp hq =>
    intro n β
    simp only [map_add, hp, hq, MvPolynomial.coeff_add]
  | mul_X p i hp =>
    intro n β
    have hmul : polyJet m (p * MvPolynomial.X i) = polyJet m p * MvPowerSeries.X i.succ := by
      rw [map_mul, polyJet_X]
    rw [hmul]
    by_cases hi : Finsupp.single i 1 ≤ β
    · obtain ⟨β', rfl⟩ : ∃ β', β = β' + Finsupp.single i 1 :=
        ⟨β - Finsupp.single i 1, (tsub_add_cancel_of_le hi).symm⟩
      have hc : (Finsupp.cons n (β' + Finsupp.single i 1) : Fin (m + 1) →₀ ℕ) =
          Finsupp.cons n β' + Finsupp.single i.succ 1 := by
        ext t
        refine Fin.cases ?_ (fun t => ?_) t
        · simp
        · simp [Finsupp.single_apply]
      rw [hc, MvPowerSeries.X_def, MvPowerSeries.coeff_add_mul_monomial, mul_one, hp,
        MvPolynomial.coeff_mul_X]
    · have hz : β i = 0 := by
        by_contra h
        exact hi (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h))
      have hn : ¬ Finsupp.single i.succ 1 ≤ (Finsupp.cons n β : Fin (m + 1) →₀ ℕ) := by
        intro h
        have := Finsupp.single_le_iff.mp h
        simp [Finsupp.cons_succ, hz] at this
      have hs : i ∉ β.support := by simp [hz]
      rw [MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial, if_neg hn,
        MvPolynomial.coeff_mul_X', if_neg hs, map_zero]

/-- `Φ_c(u^k t^b Z^α) = U^k T^b ∏ (c_i + V_i + L)^{α_i}`. -/
theorem ellJet_ambMonomial (c : Fin m → ℂ) (cl : ColIdx m) :
    ellJet s c (ambMonomial cl) =
      liftSeries m (Us s) ^ cl.1 * MvPowerSeries.X 0 ^ cl.2.1.val *
        ∏ i : Fin m, (MvPowerSeries.C (c i) + MvPowerSeries.X i.succ + liftSeries m (Ls s)) ^
          cl.2.2 i := by
  unfold ambMonomial ellJet
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype]
  · rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp only [ellGen, ambExp, Fin.cases_zero, Fin.cases_succ,
      Finsupp.coe_equivFunOnFinite_symm, map_one, one_mul, mul_assoc]
  · intro i; simp

theorem ellJet_ambMonomial_eq_polyJet {K : ℕ} (cen : Fin K → Fin m → ℚ) (j : Fin K)
    (cl : ColIdx m) :
    ellJet s (fun i => ((cen j i : ℚ) : ℂ)) (ambMonomial cl) =
      polyJet m (MvPolynomial.map (PowerSeries.map (Rat.castHom ℂ)) (packetPoly s cen j cl)) := by
  have hf : ∀ i : Fin m, polyJet m (MvPolynomial.map (PowerSeries.map (Rat.castHom ℂ))
      (MvPolynomial.X i + MvPolynomial.C (PowerSeries.C (cen j i) + s.L))) =
      MvPowerSeries.C ((cen j i : ℚ) : ℂ) + MvPowerSeries.X i.succ + liftSeries m (Ls s) := by
    intro i
    simp [Ls] <;> ring
  have hh : polyJet m (MvPolynomial.map (PowerSeries.map (Rat.castHom ℂ))
      (MvPolynomial.C (s.U ^ cl.1 * PowerSeries.X ^ cl.2.1.val))) =
      liftSeries m (Us s) ^ cl.1 * MvPowerSeries.X 0 ^ cl.2.1.val := by
    simp [Us]
  rw [ellJet_ambMonomial]
  unfold packetPoly
  simp only [map_mul, map_prod, map_pow, hf, MvPolynomial.map_C, polyJet_C, PowerSeries.map_X,
    liftSeries_X, Us]

/-- The D1 bridge (row E09.2): the coefficient of `T^{r₀} V^{r₁…r_m}` in `Φ_c(u^k t^b Z^α)` for
the centre `c = cen j` is the packet entry `packetEntry s cen j r (k, b, α)`. -/
theorem ellJet_coeff_monomial {K : ℕ} (cen : Fin K → Fin m → ℚ) (j : Fin K)
    (r : Fin (m + 1) → ℕ) (cl : ColIdx m) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm r)
        (ellJet s (fun i => ((cen j i : ℚ) : ℂ)) (ambMonomial cl)) =
      ((packetEntry s cen j r cl : ℚ) : ℂ) := by
  have hr : (Finsupp.equivFunOnFinite.symm r : Fin (m + 1) →₀ ℕ) =
      Finsupp.cons (r 0) (Finsupp.equivFunOnFinite.symm (fun i : Fin m => r i.succ)) := by
    ext t
    refine Fin.cases ?_ (fun t => ?_) t <;>
      simp [Finsupp.cons_zero, Finsupp.cons_succ, Finsupp.coe_equivFunOnFinite_symm]
  rw [ellJet_ambMonomial_eq_polyJet, hr, coeff_polyJet, MvPolynomial.coeff_map,
    packetEntry_eq_coeff, PowerSeries.coeff_map]
  try simp

end CatalanCore.Elliptic.EPA
