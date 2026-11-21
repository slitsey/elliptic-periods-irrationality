module

public import CatalanCore.Elliptic.EPA.NoPrimitive.RationalODE
public import CatalanCore.Elliptic.EPA.NoPrimitive.TraceDeriv
public import CatalanCore.Elliptic.EPA.NoPrimitive.DerivExtension
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# `dx / (2y)` has no algebraic primitive on any finite cover (row E09, input of D2)

CM (arXiv 2610.31112) `prop:origin-finite-extension-nonexact`, elementary route (CM l.1643-1700):
trace plus the rational differential equation `2 H r' + H' r = 1`.

## Statements

Let `K` be a field of characteristic zero, `H ∈ K[X]` squarefree of degree `≥ 2`, `F ⊇ K` a field
with `x ∈ F` transcendental over `K`, `F` finite over `K(x)`, and `y ∈ F` with `y² = H(x)`.

* `noPrimitive_finite`: there is no `z ∈ F` with `dz = dx/(2y)`, in the form
  "for every `K`-derivation `D` of `F`, `D x = 2 y D z`".
* `noPrimitive_finite_kaehler`: the same in `Ω[F⁄K]`: `D z ≠ (2y)⁻¹ • D x`
  (`KaehlerDifferential.D K F`).
* `noPrimitive_weierstrass`, `noPrimitive_weierstrass_kaehler`: `H = X³ + A X + B` with
  `4 A³ + 27 B² ≠ 0`, i.e. `F` a finite extension of the function field of
  `y² = x³ + A x + B` (CM's `dx/(2y)`).
* `noPrimitive_finite_neg`: the sign `dz = -dx/(2y)` (apply the theorem to `-z`);
  `noPrimitive_finite_smul`: `dz = c dx/(2y)` for a nonzero constant `c ∈ K`.

Paper proof (CM, `prop:origin-finite-extension-nonexact`, with the pole-order lemma rewritten, see
`RationalODE.lean`).  A `K`-derivation `D` of `F` with `D x = 1` exists (`DerivExtension.lean`;
characteristic zero).  If `D x = 2 y D z` for every `D` then `2 y D z = 1`; with `2 y D y = H'(x)` this gives
`2 H D(y z) = H' y z + H` (`H = H(x) = y²`).  `P = K(x)` is stable under `D`, `F/P` is finite
of degree `n ≥ 1`, and the trace is `P`-linear and commutes with `D` (`TraceDeriv.lean`), so
`M = Tr_{F/P}(y z) ∈ P` satisfies `2 H M' = H' M + n H` in `K(x) ≅ K(X)`.  Then `r = M / (n H)`
solves `2 H r' + H' r = 1`, contradicting `no_rational_solution`.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

open Polynomial Module CatalanCore.Elliptic.EPA.NoPrimitive

section Finite

variable {C E : Type*} [Field C] [CharZero C] [Field E] [Algebra C E]
  [Algebra (RatFunc C) E] [IsScalarTower C (RatFunc C) E]

local notation "𝒞" => algebraMap C[X] (RatFunc C)

/-- The coordinate `X ∈ K(X)` seen in `E`. -/
noncomputable abbrev xE (C E : Type*) [Field C] [Field E] [Algebra C E]
    [Algebra (RatFunc C) E] : E := algebraMap (RatFunc C) E RatFunc.X

theorem aeval_xE (H : C[X]) : aeval (xE C E) H = algebraMap (RatFunc C) E (𝒞 H) := by
  rw [xE, aeval_algebraMap_apply, RatFunc.aeval_X_left_eq_algebraMap]

/-- **No algebraic primitive of `dx/(2y)` on a finite cover** (derivation form): there is no
`z ∈ E` with `D x = 2 t D z` for every `C`-derivation `D` of `E`. -/
theorem no_finite_primitive_deriv [FiniteDimensional (RatFunc C) E]
    {H : C[X]} (hH : Squarefree H) (hdeg : 2 ≤ H.natDegree)
    {y z : E} (hy : y ^ 2 = aeval (xE C E) H) :
    ¬ ∀ D : Derivation C E E, D (xE C E) = 2 * y * D z := by
  intro hall
  classical
  obtain ⟨D, hD⟩ := exists_derivation_extension (K := C) (F := E)
  have hDX : D (xE C E) = 1 := by
    have := hD RatFunc.X
    rw [← RatFunc.algebraMap_X, derivationX_X, map_one] at this
    simpa [xE, RatFunc.algebraMap_X] using this
  have hz : 2 * y * D z = 1 := by rw [← hall D, hDX]
  have hDH : D (aeval (xE C E) H) = aeval (xE C E) (derivative H) := by
    rw [aeval_xE, aeval_xE, hD, derivationX_algebraMap]
  have hDy : 2 * y * D y = aeval (xE C E) (derivative H) := by
    rw [← hDH, ← hy, Derivation.leibniz_pow]
    simp only [smul_eq_mul, Nat.add_one_sub_one, pow_one, nsmul_eq_mul]
    push_cast
    ring
  have hE : 2 * aeval (xE C E) H * D (y * z)
      = aeval (xE C E) (derivative H) * (y * z) + aeval (xE C E) H := by
    rw [Derivation.leibniz, ← hDy, ← hy]
    simp only [smul_eq_mul]
    linear_combination (y ^ 2) * hz
  -- pass to `P = K(X)`
  have hE' : (2 * 𝒞 H) • D (y * z) = 𝒞 (derivative H) • (y * z) + 𝒞 H • (1 : E) := by
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]
    simp only [map_mul, map_ofNat, mul_one]
    rw [← aeval_xE, ← aeval_xE]
    exact hE
  have hTr := congrArg (Algebra.trace (RatFunc C) E) hE'
  have hT1 : Algebra.trace (RatFunc C) E (1 : E) = ((finrank (RatFunc C) E : ℕ) : RatFunc C) := by
    simpa using Algebra.trace_algebraMap (R := RatFunc C) (S := E) (1 : RatFunc C)
  simp only [map_add, map_smul, smul_eq_mul, hT1] at hTr
  have hcomm := trace_derivation_comm (D.toLinearMap.toAddMonoidHom)
    (derivationX C).toAddMonoidHom
    (fun f g => by
      show D (f * g) = D f * g + f * D g
      rw [D.leibniz]
      simp only [smul_eq_mul]
      ring) (fun p => hD p) (y * z)
  simp only [LinearMap.toAddMonoidHom_coe, Derivation.coeFn_coe] at hcomm
  rw [← hcomm] at hTr
  set m : RatFunc C := Algebra.trace (RatFunc C) E (y * z) with hm
  set n : ℕ := finrank (RatFunc C) E with hn
  have hnpos : 0 < n := Module.finrank_pos
  have hn0 : ((n : ℕ) : RatFunc C) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hHc : (𝒞 H : RatFunc C) ≠ 0 := by
    intro h0
    have hH0 : H = 0 := (RatFunc.algebraMap_injective C) (by simpa using h0)
    simp [hH0] at hdeg
  have hrel : 2 * 𝒞 H * derivationX C m = 𝒞 (derivative H) * m + (n : RatFunc C) * 𝒞 H := by
    have : 2 * 𝒞 H * derivationX C m = 𝒞 (derivative H) * m + 𝒞 H * (n : RatFunc C) := hTr
    linear_combination this
  apply no_rational_solution hH hdeg
  refine ⟨m / ((n : RatFunc C) * 𝒞 H), ?_⟩
  set r := m / ((n : RatFunc C) * 𝒞 H) with hr
  have hmr : m = (n : RatFunc C) * 𝒞 H * r := by rw [hr]; field_simp
  have hdm : derivationX C m = (n : RatFunc C) * (𝒞 (derivative H) * r + 𝒞 H * derivationX C r) := by
    rw [hmr, Derivation.leibniz, Derivation.leibniz, derivationX_algebraMap]
    simp only [smul_eq_mul, Derivation.map_natCast]
    ring
  rw [hdm, hmr] at hrel
  have : (n : RatFunc C) * 𝒞 H * (2 * 𝒞 H * derivationX C r + 𝒞 (derivative H) * r - 1) = 0 := by
    linear_combination hrel
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 (mul_ne_zero hn0 hHc)
  · linear_combination h0

/-- `y ≠ 0`: `y² = H(x) ≠ 0` since `x` is transcendental. -/
theorem ne_zero_of_sq {H : C[X]} (hH0 : H ≠ 0) {y : E} (hy : y ^ 2 = aeval (xE C E) H)  : y ≠ 0 := by
  rintro rfl
  have h1 : aeval (xE C E) H = 0 := by rw [← hy]; ring
  rw [aeval_xE, map_eq_zero_iff _ (algebraMap (RatFunc C) E).injective] at h1
  exact hH0 ((RatFunc.algebraMap_injective C) (by simpa using h1))

/-- CM `lem:origin-rational-obstruction` (final type of D2-design §6.2): `2 F r' + F' r ≠ 1` for
`r ∈ K(X)`, `F` squarefree of degree `≥ 2`, `r'` the derivative `d/dX`
(`derivationX`, equal to OAI's `ratFuncDerivative`). -/
theorem no_ratfunc_solution {K : Type*} [Field K] [CharZero K] (F : K[X]) (hF : Squarefree F)
    (hd : 2 ≤ F.natDegree) (r : RatFunc K) :
    2 * algebraMap K[X] (RatFunc K) F * derivationX K r
      + algebraMap K[X] (RatFunc K) (derivative F) * r ≠ 1 :=
  fun h => no_rational_solution hF hd ⟨r, h⟩

/-- **No algebraic primitive of `dx/(2t)` on a finite cover** (CM l.1667), in `Ω[E⁄C]`, where
`E` is a finite extension of `C(X)` and `t² = F(X)`; final type of D2-design §6.2. -/
theorem no_finite_primitive [FiniteDimensional (RatFunc C) E]
    {F : C[X]} (hF : Squarefree F) (hd : 2 ≤ F.natDegree)
    {t : E} (ht : t ^ 2 = aeval (xE C E) F) (z : E) :
    KaehlerDifferential.D C E z ≠ (2 * t)⁻¹ • KaehlerDifferential.D C E (xE C E) := by
  intro h
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap C E).injective
  have hF0 : F ≠ 0 := fun h0 => by simp [h0] at hd
  have ht0 := ne_zero_of_sq hF0 ht
  refine no_finite_primitive_deriv hF hd ht (z := z) fun D => ?_
  have := congrArg D.liftKaehlerDifferential h
  rw [Derivation.liftKaehlerDifferential_comp_D, map_smul,
    Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul] at this
  rw [this, ← mul_assoc, mul_inv_cancel₀ (mul_ne_zero two_ne_zero ht0), one_mul]

/-- `dz = c dx/(2t)` has no solution, for a constant `c ≠ 0` (derivation form). -/
theorem no_finite_primitive_smul [FiniteDimensional (RatFunc C) E]
    {F : C[X]} (hF : Squarefree F) (hd : 2 ≤ F.natDegree)
    {t : E} (ht : t ^ 2 = aeval (xE C E) F) (z : E) {c : C} (hc : c ≠ 0) :
    ¬ ∀ D : Derivation C E E, c • D (xE C E) = 2 * t * D z := by
  intro hall
  refine no_finite_primitive_deriv hF hd ht (z := c⁻¹ • z) fun D => ?_
  have h1 := hall D
  rw [D.map_smul]
  calc D (xE C E) = c⁻¹ • (c • D (xE C E)) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = c⁻¹ • (2 * t * D z) := by rw [h1]
    _ = 2 * t * (c⁻¹ • D z) := by rw [mul_smul_comm]

/-- The sign `dz = -dx/(2t)`. -/
theorem no_finite_primitive_neg [FiniteDimensional (RatFunc C) E]
    {F : C[X]} (hF : Squarefree F) (hd : 2 ≤ F.natDegree)
    {t : E} (ht : t ^ 2 = aeval (xE C E) F) (z : E) :
    ¬ ∀ D : Derivation C E E, D (xE C E) = -(2 * t * D z) := by
  intro hall
  refine no_finite_primitive_smul hF hd ht z (c := -1) (neg_ne_zero.2 one_ne_zero) fun D => ?_
  have := hall D
  simp only [neg_smul, one_smul]
  linear_combination (-1) * this

end Finite

section Weierstrass

variable {K : Type*} [Field K] [CharZero K]

/-- The Weierstrass polynomial `X³ + A X + B` is squarefree when `4A³ + 27B² ≠ 0`. -/
theorem squarefree_weierstrass (A B : K) (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) :
    Squarefree ((X ^ 3 + C A * X + C B : K[X])) := by
  apply Polynomial.Separable.squarefree
  have hu : IsUnit (C (4 * A ^ 3 + 27 * B ^ 2) : K[X]) := isUnit_C.2 hΔ.isUnit
  have hder : derivative (X ^ 3 + C A * X + C B : K[X]) = 3 * X ^ 2 + C A := by
    simp only [derivative_add, derivative_X_pow, derivative_mul, derivative_C, derivative_X]
    rw [show (C ((3 : ℕ) : K) : K[X]) = 3 from by
      rw [show ((3 : ℕ) : K) = (3 : K) by norm_num]; exact map_ofNat C 3]
    norm_num
  have key : (-3 * (6 * C A * X - 9 * C B)) * (X ^ 3 + C A * X + C B : K[X])
      + (4 * C A ^ 2 + X * (6 * C A * X - 9 * C B)) * (3 * X ^ 2 + C A)
      = C (4 * A ^ 3 + 27 * B ^ 2) := by
    simp only [map_add, map_mul, map_pow, map_ofNat]
    ring
  unfold Polynomial.Separable
  rw [hder]
  obtain ⟨u, hu'⟩ := hu
  refine ⟨(↑u⁻¹ : K[X]) * (-3 * (6 * C A * X - 9 * C B)),
    (↑u⁻¹ : K[X]) * (4 * C A ^ 2 + X * (6 * C A * X - 9 * C B)), ?_⟩
  calc _ = (↑u⁻¹ : K[X]) * ((-3 * (6 * C A * X - 9 * C B)) * (X ^ 3 + C A * X + C B : K[X])
      + (4 * C A ^ 2 + X * (6 * C A * X - 9 * C B)) * (3 * X ^ 2 + C A)) := by ring
    _ = 1 := by rw [key, ← hu']; simp

theorem natDegree_weierstrass (A B : K) :
    (X ^ 3 + C A * X + C B : K[X]).natDegree = 3 := by
  compute_degree!

variable {E : Type*} [Field E] [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
  [FiniteDimensional (RatFunc K) E]

/-- **No algebraic primitive of `dx/(2y)` on any finite cover of the elliptic curve
`y² = x³ + A x + B`**, `4A³ + 27B² ≠ 0` (derivation form). -/
theorem no_primitive_weierstrass (A B : K) (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    {y z : E} (hy : y ^ 2 = xE K E ^ 3 + algebraMap K E A * xE K E + algebraMap K E B) :
    ¬ ∀ D : Derivation K E E, D (xE K E) = 2 * y * D z :=
  no_finite_primitive_deriv (squarefree_weierstrass A B hΔ)
    (by rw [natDegree_weierstrass]; norm_num) (by simpa [aeval_def] using hy)

/-- The same in `Ω[E⁄K]`: `dz ≠ dx/(2y)`. -/
theorem no_primitive_weierstrass_kaehler (A B : K) (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    {y : E} (hy : y ^ 2 = xE K E ^ 3 + algebraMap K E A * xE K E + algebraMap K E B) (z : E) :
    KaehlerDifferential.D K E z ≠ (2 * y)⁻¹ • KaehlerDifferential.D K E (xE K E) :=
  no_finite_primitive (squarefree_weierstrass A B hΔ)
    (by rw [natDegree_weierstrass]; norm_num) (by simpa [aeval_def] using hy) z

end Weierstrass

end CatalanCore.Elliptic.EPA
