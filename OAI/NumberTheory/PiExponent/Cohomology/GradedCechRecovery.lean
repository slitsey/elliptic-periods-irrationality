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
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Length
public import Mathlib.AlgebraicGeometry.Morphisms.Integral

@[expose] public section

namespace OAI

namespace PiExponent.GradedCechRecovery

theorem augmentation_surjective_on_closed
    {P M A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ : Type*}
    [AddCommGroup P] [AddCommGroup M]
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
    [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    [AddCommGroup C₀] [AddCommGroup C₁]
    (a₀ : A₀ →+ A₁) (a₁ : A₁ →+ A₂)
    (b₀ : B₀ →+ B₁) (b₁ : B₁ →+ B₂) (c₀ : C₀ →+ C₁)
    (f₀ : A₀ →+ B₀) (f₁ : A₁ →+ B₁) (f₂ : A₂ →+ B₂)
    (g₀ : B₀ →+ C₀) (g₁ : B₁ →+ C₁)
    (εB : P →+ B₀) (εC : M →+ C₀) (g : P →+ M)
    (hg₀ : Function.Surjective g₀)
    (hker : ∀ z : B₁, g₁ z = 0 → ∃ y : A₁, f₁ y = z)
    (hf₂ : Function.Injective f₂)
    (hff₀ : ∀ x, b₀ (f₀ x) = f₁ (a₀ x))
    (hff₁ : ∀ x, b₁ (f₁ x) = f₂ (a₁ x))
    (hgg : ∀ x, g₁ (b₀ x) = c₀ (g₀ x))
    (hzero : ∀ x, g₀ (f₀ x) = 0)
    (hdiff : ∀ x, b₁ (b₀ x) = 0)
    (hε : ∀ x, εC (g x) = g₀ (εB x))
    (hfree : ∀ x : B₀, b₀ x = 0 → ∃ p : P, εB p = x)
    (hkernel : ∀ x : A₁, a₁ x = 0 → ∃ y : A₀, a₀ y = x) :
    ∀ x : C₀, c₀ x = 0 → ∃ m : M, εC m = x := by
  intro x hx
  obtain ⟨b, hb⟩ := hg₀ x
  have hdb : g₁ (b₀ b) = 0 := by rw [hgg, hb, hx]
  obtain ⟨a, ha⟩ := hker (b₀ b) hdb
  have hclosed : a₁ a = 0 := by
    apply hf₂
    rw [map_zero, ← hff₁, ha, hdiff]
  obtain ⟨v, hv⟩ := hkernel a hclosed
  have hcorrected : b₀ (b - f₀ v) = 0 := by
    rw [map_sub, hff₀, hv, ha, sub_self]
  obtain ⟨p, hp⟩ := hfree (b - f₀ v) hcorrected
  refine ⟨g p, ?_⟩
  rw [hε, hp, map_sub, hzero, sub_zero, hb]

theorem unique_recovery_of_injective
    {M C₀ C₁ : Type*} [AddCommGroup M] [AddCommGroup C₀] [AddCommGroup C₁]
    (ε : M →+ C₀) (d : C₀ →+ C₁) (hinj : Function.Injective ε)
    (hrec : ∀ c, d c = 0 → ∃ m, ε m = c) :
    ∀ c, d c = 0 → ∃! m, ε m = c := by
  intro c hc
  obtain ⟨m, hm⟩ := hrec c hc
  exact ⟨m, hm, fun n hn => hinj (hn.trans hm.symm)⟩

theorem eventual_unique_recovery
    {M C₀ C₁ : ℕ → Type*}
    [∀ n, AddCommGroup (M n)] [∀ n, AddCommGroup (C₀ n)] [∀ n, AddCommGroup (C₁ n)]
    (ε : ∀ n, M n →+ C₀ n) (d : ∀ n, C₀ n →+ C₁ n)
    (hinj : ∃ N, ∀ n, N ≤ n → Function.Injective (ε n))
    (hrec : ∃ N, ∀ n, N ≤ n → ∀ c, d n c = 0 → ∃ m, ε n m = c) :
    ∃ N, ∀ n, N ≤ n → ∀ c, d n c = 0 → ∃! m, ε n m = c := by
  obtain ⟨N₁, h₁⟩ := hinj
  obtain ⟨N₂, h₂⟩ := hrec
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  exact unique_recovery_of_injective (ε n) (d n)
    (h₁ n ((le_max_left _ _).trans hn)) (h₂ n ((le_max_right _ _).trans hn))

end PiExponent.GradedCechRecovery

end OAI
