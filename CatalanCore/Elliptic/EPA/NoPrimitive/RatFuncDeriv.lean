module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.Derivation.Basic

/-!
# The derivative `d/dX` on `K(X)`

For a field `K`, `RatFunc.derivationX K : Derivation K (RatFunc K) (RatFunc K)` is the
`K`-derivation with `d/dX (X) = 1` (not in Mathlib at our pin).  Its value on a quotient of
polynomials `a / b` is `(a' b - a b') / b²`; additivity and the Leibniz rule are checked on
arbitrary (not necessarily reduced) representatives.

This is the first ingredient of `CatalanCore/Elliptic/EPA/NoPrimitive.lean`
(CM `lem:origin-rational-obstruction`, `prop:origin-finite-extension-nonexact`).
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA.NoPrimitive

open Polynomial

variable {K : Type*} [Field K]

local notation "𝒞" => algebraMap K[X] (RatFunc K)

/-- The quotient-rule expression, using the reduced representative `num / denom`. -/
noncomputable def ratDer (f : RatFunc K) : RatFunc K :=
  (𝒞 (derivative f.num) * 𝒞 f.denom - 𝒞 f.num * 𝒞 (derivative f.denom)) / 𝒞 f.denom ^ 2

private lemma c_ne_zero (b : K[X]) (hb : b ≠ 0) : (𝒞 b : RatFunc K) ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).2 hb

/-- `ratDer` computed on an arbitrary representative `a / b` of `f`. -/
theorem ratDer_div (a b : K[X]) (hb : b ≠ 0) :
    ratDer ((𝒞 a : RatFunc K) / 𝒞 b) =
      (𝒞 (derivative a) * 𝒞 b - 𝒞 a * 𝒞 (derivative b)) / 𝒞 b ^ 2 := by
  set f : RatFunc K := (𝒞 a) / 𝒞 b with hf
  have hd : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hnd : (𝒞 f.num : RatFunc K) / 𝒞 f.denom = 𝒞 a / 𝒞 b := by
    rw [RatFunc.num_div_denom]
  rw [div_eq_div_iff (c_ne_zero _ hd) (c_ne_zero _ hb)] at hnd
  have h : f.num * b = a * f.denom :=
    (RatFunc.algebraMap_injective K) (by simpa using hnd)
  have h' := congrArg derivative h
  simp only [derivative_mul] at h'
  have key : (derivative f.num * f.denom - f.num * derivative f.denom) * b ^ 2
      = (derivative a * b - a * derivative b) * f.denom ^ 2 := by
    linear_combination (f.denom * b) * h' - (derivative f.denom * b + derivative b * f.denom) * h
  unfold ratDer
  rw [div_eq_div_iff (pow_ne_zero 2 (c_ne_zero _ hd)) (pow_ne_zero 2 (c_ne_zero _ hb))]
  have := congrArg 𝒞 key
  simp only [map_mul, map_sub, map_pow] at this
  exact this

theorem ratDer_algebraMap (a : K[X]) : ratDer (𝒞 a : RatFunc K) = 𝒞 (derivative a) := by
  have := ratDer_div (K := K) a 1 one_ne_zero
  rw [map_one, div_one] at this
  rw [this]
  simp

theorem ratDer_add (f g : RatFunc K) : ratDer (f + g) = ratDer f + ratDer g := by
  have hf := RatFunc.num_div_denom f
  have hg := RatFunc.num_div_denom g
  have hfd := RatFunc.denom_ne_zero f
  have hgd := RatFunc.denom_ne_zero g
  have e1 : f + g = 𝒞 (f.num * g.denom + g.num * f.denom) / 𝒞 (f.denom * g.denom) := by
    rw [map_add, map_mul, map_mul, map_mul]
    nth_rewrite 1 [← hf]
    nth_rewrite 1 [← hg]
    have := c_ne_zero f.denom hfd
    have := c_ne_zero g.denom hgd
    field_simp
  rw [e1, ratDer_div _ _ (mul_ne_zero hfd hgd)]
  conv_rhs => rw [← hf, ← hg]
  rw [ratDer_div _ _ hfd, ratDer_div _ _ hgd]
  have := c_ne_zero f.denom hfd
  have := c_ne_zero g.denom hgd
  simp only [derivative_mul, map_add, map_mul]
  field_simp
  ring

theorem ratDer_mul (f g : RatFunc K) : ratDer (f * g) = f * ratDer g + g * ratDer f := by
  obtain ⟨a, b, hb, rfl⟩ : ∃ a b : K[X], b ≠ 0 ∧ f = 𝒞 a / 𝒞 b :=
    ⟨f.num, f.denom, RatFunc.denom_ne_zero f, (RatFunc.num_div_denom f).symm⟩
  obtain ⟨c, d, hd, rfl⟩ : ∃ c d : K[X], d ≠ 0 ∧ g = 𝒞 c / 𝒞 d :=
    ⟨g.num, g.denom, RatFunc.denom_ne_zero g, (RatFunc.num_div_denom g).symm⟩
  have hb' := c_ne_zero b hb
  have hd' := c_ne_zero d hd
  have e1 : (𝒞 a : RatFunc K) / 𝒞 b * (𝒞 c / 𝒞 d) = 𝒞 (a * c) / 𝒞 (b * d) := by
    rw [map_mul, map_mul]
    field_simp
  rw [e1, ratDer_div _ _ (mul_ne_zero hb hd), ratDer_div _ _ hb, ratDer_div _ _ hd]
  simp only [derivative_mul, map_add, map_mul]
  field_simp
  ring

theorem ratDer_const (c : K) : ratDer (algebraMap K (RatFunc K) c) = 0 := by
  have h : algebraMap K (RatFunc K) c = 𝒞 (Polynomial.C c) := by
    rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_apply]
    rfl
  rw [h, ratDer_algebraMap]
  simp

/-- The `K`-derivation `d/dX` of `RatFunc K`. -/
noncomputable def derivationX (K : Type*) [Field K] : Derivation K (RatFunc K) (RatFunc K) :=
  Derivation.mk'
    { toFun := ratDer
      map_add' := ratDer_add
      map_smul' := fun c f => by
        have h1 := ratDer_mul (algebraMap K (RatFunc K) c) f
        rw [ratDer_const, mul_zero, add_zero] at h1
        rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def]
        exact h1 }
    (fun f g => by
      simp only [smul_eq_mul, LinearMap.coe_mk, AddHom.coe_mk]
      rw [ratDer_mul])

@[simp] theorem derivationX_apply (f : RatFunc K) : derivationX K f = ratDer f := rfl

@[simp] theorem derivationX_algebraMap (a : K[X]) :
    derivationX K (𝒞 a) = 𝒞 (derivative a) := ratDer_algebraMap a

@[simp] theorem derivationX_X : derivationX K (𝒞 (Polynomial.X : K[X])) = 1 := by
  have := derivationX_algebraMap (K := K) Polynomial.X
  simpa using this

@[simp] theorem derivationX_C (c : K) : derivationX K (algebraMap K (RatFunc K) c) = 0 :=
  ratDer_const c

end CatalanCore.Elliptic.EPA.NoPrimitive
