module

public import CatalanCore.Elliptic.EPA.NoPrimitive.RatFuncDeriv
public import Mathlib.FieldTheory.Differential.Basic

/-!
# Extending `d/dX` to a finite extension of `K(X)`

Let `F` be a field with `Algebra (RatFunc K) F`, `IsScalarTower K (RatFunc K) F` and `F` finite over
`K(X)`, `K` of characteristic zero.  Then there is a `K`-derivation `D` of `F` with
`D (algebraMap f) = algebraMap (d/dX f)` for all rational functions `f`; in particular `D X = 1`.

Paper argument (CM: "characteristic zero gives a unique extension `D` of `d/dU` to the finite
separable extension `F`"): Mathlib's `Differential.differentialFiniteDimensional` extends a
derivation of a characteristic-zero field to any finite extension (through a primitive element and
`AdjoinRoot`); we apply it to the base `K(X)` with `d/dX`.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA.NoPrimitive

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The extension of `d/dX` to a finite extension of `K(X)`. -/
theorem exists_derivation_extension [CharZero K] [Algebra (RatFunc K) F]
    [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F] :
    ∃ D : Derivation K F F,
      ∀ f : RatFunc K, D (algebraMap (RatFunc K) F f) = algebraMap (RatFunc K) F (derivationX K f) := by
  classical
  let _ : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
  let _ : Differential K := ⟨0⟩
  let _ : Differential (RatFunc K) :=
    ⟨{ toFun := fun f => derivationX K f
       map_add' := fun a b => map_add _ a b
       map_smul' := fun n a => by
         simp only [RingHom.id_apply]
         exact map_zsmul (derivationX K).toAddMonoidHom n a
       map_one_eq_zero' := (derivationX K).map_one_eq_zero
       leibniz' := fun a b => by
         show derivationX K (a * b) = a * derivationX K b + b * derivationX K a
         rw [(derivationX K).leibniz]
         simp only [smul_eq_mul] }⟩
  let _ : Differential F := Differential.differentialFiniteDimensional (RatFunc K) F
  have : DifferentialAlgebra (RatFunc K) F := Differential.differentialAlgebraFiniteDimensional
  have hD : ∀ f : RatFunc K, Differential.deriv (R := F) (algebraMap (RatFunc K) F f) =
      algebraMap (RatFunc K) F (derivationX K f) :=
    fun f => DifferentialAlgebra.deriv_algebraMap f
  have hK : ∀ c : K, Differential.deriv (R := F) (algebraMap K F c) = 0 := by
    intro c
    have := hD (algebraMap K (RatFunc K) c)
    rw [← IsScalarTower.algebraMap_apply, derivationX_C, map_zero] at this
    exact this
  let D : Derivation K F F := Derivation.mk'
    { toFun := fun a => Differential.deriv (R := F) a
      map_add' := fun a b => map_add _ a b
      map_smul' := fun c a => by
        simp only [Algebra.smul_def, RingHom.id_apply]
        rw [Derivation.leibniz, hK]
        simp [smul_eq_mul] }
    (fun a b => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
      rw [Derivation.leibniz]
      simp [smul_eq_mul])
  exact ⟨D, hD⟩

end CatalanCore.Elliptic.EPA.NoPrimitive
