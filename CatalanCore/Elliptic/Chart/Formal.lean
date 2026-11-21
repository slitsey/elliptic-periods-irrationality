module

public import CatalanCore.Elliptic.Interfaces
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Polynomial.Tower
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# The formal origin chart (row E05, `prop:chart`)

Paper: `paper/elliptic-periods.tex`, `eq:quartic` and `prop:chart`.

For an `OriginChart c` (`A, B, a` with `4A³ + 27B² ≠ 0` and `f(a) ≠ 0`) let
`F(U) = U + 3a U² + (3a² + A) U³ + f(a) U⁴ ∈ ℤ[U]`. Then

* `OriginChart.exists_unique_U`: there is a unique `U ∈ ℤ[[T]]` with `U(0) = 0`, `F(U(T)) = T²`;
  the same holds over every commutative ring (`OriginChart.eq_Useries`);
* `OriginChart.negInv_dF`: `−1/F′(U(T)) ∈ ℤ[[T]]`;
* `OriginChart.series`: the `OriginSeries c` of the contract (over `ℚ`), with
  `OriginSeries.U_integral`, `OriginSeries.negInv_integral`, `OriginSeries.L_integral`
  (`n [Tⁿ] L ∈ ℤ`) and uniqueness `OriginSeries` is a subsingleton.
* `OriginChart.F_quartic`: `eq:quartic`, `t² = F(u)` from `y² = f(x)`.
* `exists_chart_point`: the choice of `a ∈ {0,1,2,3}` with `f(a) ≠ 0`.

The compositional inverse is Mathlib's `PowerSeries.substInvOfIsUnit`, over an arbitrary
commutative ring, so that `ℤ` and `ℚ` are covered at once.
-/

@[expose] public section

namespace CatalanCore.Elliptic

open PowerSeries

/-- The choice of `a ∈ {0,1,2,3}` with `f(a) ≠ 0` (first lines of §2.1 of the paper): the
monic cubic `X³ + A X + B` cannot vanish at `0, 1, 2` simultaneously. -/
theorem exists_chart_point (A B : ℤ) :
    ∃ a : ℤ, 0 ≤ a ∧ a ≤ 3 ∧ a ^ 3 + A * a + B ≠ 0 := by
  by_contra h
  push Not at h
  have h0 := h 0 le_rfl (by norm_num)
  have h1 := h 1 (by norm_num) (by norm_num)
  have h2 := h 2 (by norm_num) (by norm_num)
  omega

/-- A ring homomorphism commutes with `aeval` of an integer polynomial. -/
theorem ringHom_aeval {A B : Type*} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B]
    (g : A →+* B) (x : A) (p : Polynomial ℤ) :
    g (Polynomial.aeval x p) = Polynomial.aeval (g x) p := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
  congr 1
  exact RingHom.ext_int _ _

namespace OriginChart

variable (c : OriginChart)

/-- A chart for any `A, B` with `4A³ + 27B² ≠ 0`, with `a ∈ {0,1,2,3}`. -/
theorem exists_chart (A B : ℤ) (hd : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) :
    ∃ c : OriginChart, c.A = A ∧ c.B = B ∧ 0 ≤ c.a ∧ c.a ≤ 3 := by
  obtain ⟨a, ha0, ha3, hfa⟩ := exists_chart_point A B
  exact ⟨⟨A, B, a, hd, hfa⟩, rfl, rfl, ha0, ha3⟩

theorem F_coeff_zero : c.F.coeff 0 = 0 := by
  simp only [OriginChart.F, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X]
  simp

theorem F_coeff_one : c.F.coeff 1 = 1 := by
  simp only [OriginChart.F, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X]
  simp

/-- `F′(0) = 1`. -/
theorem derivative_F_coeff_zero : (Polynomial.derivative c.F).coeff 0 = 1 := by
  rw [Polynomial.coeff_derivative, F_coeff_one]; simp

/-- `F(u)` written out, in any field (or commutative ring). -/
theorem aeval_F {S : Type*} [CommRing S] (u : S) :
    Polynomial.aeval u c.F =
      u + 3 * c.a * u ^ 2 + (3 * c.a ^ 2 + c.A) * u ^ 3 + (c.a ^ 3 + c.A * c.a + c.B) * u ^ 4 := by
  simp only [OriginChart.F, map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
  simp

/-- `eq:quartic`: if `y² = x³ + A x + B` and `x ≠ a`, then `t² = F(u)` for
`u = 1/(x − a)`, `t = y/(x − a)²`. -/
theorem F_quartic {K : Type*} [Field K] (x y : K) (hx : x ≠ (c.a : K))
    (hy : y ^ 2 = x ^ 3 + (c.A : K) * x + (c.B : K)) :
    (y / (x - c.a) ^ 2) ^ 2 = Polynomial.aeval (1 / (x - (c.a : K))) c.F := by
  have hx' : x - (c.a : K) ≠ 0 := sub_ne_zero.mpr hx
  rw [aeval_F, div_pow, ← pow_mul, hy]
  field_simp
  ring

section Generic

variable (R : Type*) [CommRing R]

/-- `F` as a power series over `R`. -/
noncomputable def Fser : PowerSeries R :=
  ((c.F.map (algebraMap ℤ R) : Polynomial R) : PowerSeries R)

theorem constantCoeff_Fser : constantCoeff (c.Fser R) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, Fser, Polynomial.coeff_coe, Polynomial.coeff_map,
    F_coeff_zero]
  simp

theorem coeff_one_Fser : coeff 1 (c.Fser R) = 1 := by
  rw [Fser, Polynomial.coeff_coe, Polynomial.coeff_map, F_coeff_one]
  simp

theorem isUnit_coeff_one_Fser : IsUnit (coeff 1 (c.Fser R)) := by
  rw [coeff_one_Fser]; exact isUnit_one

/-- The compositional inverse `G` of `F`, `F(G(S)) = S`, `G(0) = 0`. -/
noncomputable def Gser : PowerSeries R :=
  (c.Fser R).substInvOfIsUnit (c.isUnit_coeff_one_Fser R)

/-- `U(T) = G(T²)`. -/
noncomputable def Useries : PowerSeries R :=
  (c.Gser R).subst (X ^ 2 : PowerSeries R)

theorem constantCoeff_Gser : constantCoeff (c.Gser R) = 0 := by
  simp [Gser]

theorem constantCoeff_Useries : constantCoeff (c.Useries R) = 0 := by
  rw [Useries, constantCoeff_subst_X_pow two_ne_zero]
  simp [constantCoeff_Gser]

variable {R}

theorem subst_Fser {a : PowerSeries R} (ha : HasSubst a) :
    (c.Fser R).subst a = Polynomial.aeval a c.F := by
  rw [Fser, subst_coe ha, Polynomial.aeval_map_algebraMap]

/-- `F(U(T)) = T²` over any commutative ring. -/
theorem aeval_Useries : Polynomial.aeval (c.Useries R) c.F = (X : PowerSeries R) ^ 2 := by
  have hX2 : HasSubst (X ^ 2 : PowerSeries R) := HasSubst.X_pow two_ne_zero
  have hG : HasSubst (c.Gser R) := HasSubst.of_constantCoeff_zero' (c.constantCoeff_Gser R)
  have hU : HasSubst (c.Useries R) :=
    HasSubst.of_constantCoeff_zero' (c.constantCoeff_Useries R)
  have hFG : (c.Fser R).subst (c.Gser R) = X :=
    (c.Fser R).subst_substInvOfIsUnit_right (c.constantCoeff_Fser R) (c.isUnit_coeff_one_Fser R)
  rw [← subst_Fser c hU, Useries, ← subst_comp_subst_apply hG hX2, hFG]
  exact subst_X hX2

/-- Uniqueness: any `W` with `W(0) = 0` and `F(W) = T²` is `U`. -/
theorem eq_Useries {W : PowerSeries R} (h0 : constantCoeff W = 0)
    (hW : Polynomial.aeval W c.F = (X : PowerSeries R) ^ 2) : W = c.Useries R := by
  have hWs : HasSubst W := HasSubst.of_constantCoeff_zero' h0
  have hF : HasSubst (c.Fser R) := HasSubst.of_constantCoeff_zero' (c.constantCoeff_Fser R)
  have h1 : (c.Fser R).subst W = (X : PowerSeries R) ^ 2 := by rw [subst_Fser c hWs, hW]
  have h2 := subst_comp_subst_apply hF hWs (c.Gser R)
  rw [Gser, (c.Fser R).subst_substInvOfIsUnit_left (c.constantCoeff_Fser R)
    (c.isUnit_coeff_one_Fser R), subst_X hWs] at h2
  rw [h2, ← Gser, h1]
  rfl

/-- Existence and uniqueness of `U ∈ R[[T]]` (`prop:chart`, first sentence). -/
theorem exists_unique_U :
    ∃! W : PowerSeries R, constantCoeff W = 0 ∧
      Polynomial.aeval W c.F = (X : PowerSeries R) ^ 2 :=
  ⟨c.Useries R, ⟨c.constantCoeff_Useries R, c.aeval_Useries⟩,
    fun _ hW => c.eq_Useries hW.1 hW.2⟩

variable (R)

/-- `F′(U(T))`. -/
noncomputable def dF : PowerSeries R :=
  Polynomial.aeval (c.Useries R) (Polynomial.derivative c.F)

theorem constantCoeff_dF : constantCoeff (c.dF R) = 1 := by
  have h := ringHom_aeval (constantCoeff : PowerSeries R →+* R) (c.Useries R)
    (Polynomial.derivative c.F)
  rw [c.constantCoeff_Useries R] at h
  have h1 : Polynomial.aeval (0 : R) (Polynomial.derivative c.F) = 1 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_at_zero, derivative_F_coeff_zero]; simp
  rw [h1] at h
  exact h

/-- `−1/F′(U(T))`, an element of `R[[T]]`. -/
noncomputable def negInvDF : PowerSeries R := -invOfUnit (c.dF R) 1

theorem dF_mul_negInvDF : c.dF R * c.negInvDF R = -1 := by
  have := mul_invOfUnit (c.dF R) 1 (by rw [c.constantCoeff_dF R]; simp)
  rw [negInvDF, mul_neg, this]

end Generic

/-! ### Comparison `ℤ → ℚ` -/

/-- Pushing forward along `ℤ → ℚ` commutes with `aeval` of an integer polynomial. -/
theorem aeval_map_intCast (W : PowerSeries ℤ) (p : Polynomial ℤ) :
    Polynomial.aeval (map (Int.castRingHom ℚ) W) p =
      map (Int.castRingHom ℚ) (Polynomial.aeval W p) :=
  (ringHom_aeval (map (Int.castRingHom ℚ)) W p).symm

/-- The integral series `U ∈ ℤ[[T]]` pushed to `ℚ[[T]]` is the rational one. -/
theorem map_Useries_int :
    map (Int.castRingHom ℚ) (c.Useries ℤ) = c.Useries ℚ := by
  apply c.eq_Useries
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      c.constantCoeff_Useries ℤ]
    simp
  · rw [aeval_map_intCast, c.aeval_Useries]
    simp

/-- The rational series `L(T)`: `L(0) = 0`, `L′ = −1/F′(U)`; its coefficients are
`[Tⁿ]L = v_{n−1}/n` where `−1/F′(U) = Σ v_k Tᵏ`. -/
noncomputable def Lrat : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((coeff (n - 1) (c.negInvDF ℤ) : ℤ) : ℚ) / n

theorem derivative_Lrat :
    derivative (c.Lrat) = map (Int.castRingHom ℚ) (c.negInvDF ℤ) := by
  ext n
  rw [coeff_derivative, Lrat, coeff_mk, coeff_map]
  simp only [Nat.add_sub_cancel, eq_intCast]
  have : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  push_cast at this ⊢
  field_simp

theorem constantCoeff_Lrat : constantCoeff c.Lrat = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, Lrat, coeff_mk]
  simp

/-- The series of `prop:chart` as an `OriginSeries`. -/
noncomputable def series : OriginSeries c where
  U := map (Int.castRingHom ℚ) (c.Useries ℤ)
  L := c.Lrat
  U_zero := by
    rw [map_Useries_int]; exact c.constantCoeff_Useries ℚ
  U_eq := by
    rw [aeval_map_intCast, c.aeval_Useries]; simp
  L_zero := c.constantCoeff_Lrat
  L_deriv := by
    rw [derivative_Lrat, aeval_map_intCast]
    have h := congrArg (map (Int.castRingHom ℚ)) (c.dF_mul_negInvDF ℤ)
    rw [map_mul, map_neg, map_one] at h
    rw [dF] at h
    rw [mul_comm, h]

end OriginChart

namespace OriginSeries

variable {c : OriginChart}

/-- `F′(U)` has constant term 1, hence is a nonzero element of `ℚ[[T]]`. -/
theorem aeval_derivative_ne_zero (s : OriginSeries c) :
    Polynomial.aeval s.U (Polynomial.derivative c.F) ≠ 0 := by
  intro h
  have hU : s.U = c.Useries ℚ := c.eq_Useries s.U_zero s.U_eq
  have h1 := c.constantCoeff_dF ℚ
  rw [OriginChart.dF, ← hU, h] at h1
  simp at h1

/-- Uniqueness of the rational series `U`. -/
theorem U_eq_map (s : OriginSeries c) :
    s.U = map (Int.castRingHom ℚ) (c.Useries ℤ) := by
  rw [c.map_Useries_int]; exact c.eq_Useries s.U_zero s.U_eq

/-- `U ∈ ℤ[[T]]`: every coefficient of `U` is an integer. -/
theorem U_integral (s : OriginSeries c) :
    ∃ W : PowerSeries ℤ, s.U = map (Int.castRingHom ℚ) W := ⟨_, s.U_eq_map⟩

theorem coeff_U_integral (s : OriginSeries c) (n : ℕ) :
    ∃ k : ℤ, coeff n s.U = k :=
  ⟨coeff n (c.Useries ℤ), by rw [s.U_eq_map, coeff_map]; simp⟩

/-- Uniqueness of the rational series `L`. -/
theorem L_eq (s : OriginSeries c) : s.L = c.Lrat := by
  have hU := s.U_eq_map
  have h1 : derivative s.L * Polynomial.aeval s.U (Polynomial.derivative c.F) = -1 := s.L_deriv
  have h2 := (c.series).L_deriv
  have hne := s.aeval_derivative_ne_zero
  have h3 : (c.series).U = s.U := hU.symm
  change derivative c.Lrat * Polynomial.aeval (c.series).U (Polynomial.derivative c.F) = -1 at h2
  rw [h3] at h2
  have h4 : derivative s.L = derivative c.Lrat := mul_right_cancel₀ hne (h1.trans h2.symm)
  exact PowerSeries.derivative.ext h4 (by rw [s.L_zero, c.constantCoeff_Lrat])

/-- `OriginSeries c` has exactly one element. -/
theorem eq_series (s : OriginSeries c) : s = c.series := by
  cases s with
  | mk U L hU hUe hL hLd =>
    have hs : U = (c.series).U := by
      rw [OriginChart.series]; exact OriginSeries.U_eq_map ⟨U, L, hU, hUe, hL, hLd⟩
    have hl : L = c.Lrat := OriginSeries.L_eq ⟨U, L, hU, hUe, hL, hLd⟩
    subst hs
    subst hl
    rfl

instance : Subsingleton (OriginSeries c) :=
  ⟨fun s s' => (eq_series s).trans (eq_series s').symm⟩

instance : Nonempty (OriginSeries c) := ⟨c.series⟩

/-- `−1/F′(U) ∈ ℤ[[T]]`: `L′ = −1/F′(U)` has integer coefficients. -/
theorem negInv_integral (s : OriginSeries c) :
    ∃ V : PowerSeries ℤ, derivative s.L = map (Int.castRingHom ℚ) V ∧
      V * Polynomial.aeval (c.Useries ℤ) (Polynomial.derivative c.F) = -1 := by
  refine ⟨c.negInvDF ℤ, ?_, ?_⟩
  · rw [s.L_eq, c.derivative_Lrat]
  · have := c.dF_mul_negInvDF ℤ
    rw [OriginChart.dF] at this
    rw [mul_comm]; exact this

/-- `n [Tⁿ] L ∈ ℤ` for `n ≥ 1`, with `n [Tⁿ] L = [T^{n−1}] (−1/F′(U))`. -/
theorem L_integral (s : OriginSeries c) {n : ℕ} (hn : 1 ≤ n) :
    ∃ k : ℤ, (n : ℚ) * coeff n s.L = k := by
  refine ⟨coeff (n - 1) (c.negInvDF ℤ), ?_⟩
  rw [s.L_eq, OriginChart.Lrat, coeff_mk]
  have : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

end OriginSeries

end CatalanCore.Elliptic
