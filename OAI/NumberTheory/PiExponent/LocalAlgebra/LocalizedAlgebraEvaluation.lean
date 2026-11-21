module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import Mathlib.Topology.Sheaves.MayerVietoris
public import Mathlib.CategoryTheory.Sites.MayerVietorisSquare
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Tactic

@[expose] public section

namespace OAI

namespace PiExponent.LocalizedAlgebraEvaluation
noncomputable section
variable {P A B : Type*} [CommRing P] [CommRing A] [CommRing B] [Algebra P A]
variable (S : Submonoid P) (T : Submonoid B) (f : A →+* B)
  (hf : ∀ s : S, f (algebraMap P A s.val) ∈ T)

def denominatorMap : S →* T where
  toFun s := ⟨f (algebraMap P A s.val), hf s⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by simp)

@[simp] theorem denominatorMap_val (s : S) :
    (denominatorMap S T f hf s).val = f (algebraMap P A s.val) := rfl

def evaluation : LocalizedModule S A →+ Localization T where
  toFun z := z.liftOn
    (fun p => IsLocalization.mk' (Localization T) (f p.1) (denominatorMap S T f hf p.2))
    (by
      rintro ⟨m,s⟩ ⟨m',s'⟩ ⟨u, hu⟩
      apply (IsLocalization.eq (M := T) (S := Localization T)).mpr
      refine ⟨denominatorMap S T f hf u, ?_⟩
      change f (algebraMap P A u.val) * (f (algebraMap P A s'.val) * f m) =
        f (algebraMap P A u.val) * (f (algebraMap P A s.val) * f m')
      simpa only [Submonoid.smul_def, Algebra.smul_def, map_mul] using congrArg f hu)
  map_zero' := by
    rw [← LocalizedModule.zero_mk (1 : S), LocalizedModule.liftOn_mk,
      map_zero, IsLocalization.mk'_zero]
  map_add' z w := by
    induction z, w using LocalizedModule.induction_on₂ with
    | h m m' s s' =>
      simp only [LocalizedModule.mk_add_mk, LocalizedModule.liftOn_mk,
        Submonoid.smul_def, Algebra.smul_def, map_add, map_mul]
      simpa only [denominatorMap_val, mul_comm] using
        (IsLocalization.mk'_add (M := T) (S := Localization T) (f m) (f m')
          (denominatorMap S T f hf s) (denominatorMap S T f hf s'))

@[simp] theorem evaluation_mk (m : A) (s : S) :
    evaluation S T f hf (LocalizedModule.mk m s) =
      IsLocalization.mk' (Localization T) (f m) (denominatorMap S T f hf s) :=
by
  simp only [evaluation, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LocalizedModule.liftOn_mk]

theorem evaluation_smul (p : P) (z : LocalizedModule S A) :
    evaluation S T f hf (p • z) =
      algebraMap B (Localization T) (f (algebraMap P A p)) * evaluation S T f hf z := by
  induction z using LocalizedModule.induction_on with
  | h m s =>
    rw [LocalizedModule.smul'_mk, evaluation_mk, evaluation_mk]
    simp only [Algebra.smul_def, map_mul]
    exact (IsLocalization.mul_mk'_eq_mk'_of_mul _ _ _).symm

end
end PiExponent.LocalizedAlgebraEvaluation

end OAI
