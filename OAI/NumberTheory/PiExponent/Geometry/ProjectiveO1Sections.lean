module

public import OAI.NumberTheory.PiExponent.Geometry.LineBundleGluingSections
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinates
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveRatioCocycle
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
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Length
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.Algebra.Category.Grp.Zero

@[expose] public section

namespace OAI

noncomputable section

namespace PiExponent.ProjectiveO1

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.LineBundleGluing PiExponentSeshadri.Frames

variable {R σ : Type} [CommRing R]

def coordinateCoefficients (k : σ) (V : (projectiveSpace R σ).Opens) :
    sections (coordinateCocycle (R := R) (σ := σ)) V :=
  ⟨fun p => coordinateRatio p.1 k p.2.val p.2.property.2,
   ⟨fun i _ _ _ hi h => coordinateRatio_restrict i k h hi,
    fun i j W _ hi hj => (coordinateRatio_mul i j k W hi hj).symm⟩⟩

def coordinateSection (k : σ) :
    O (projectiveSpace R σ) ⟶ (lineBundle (R := R) (σ := σ)).sheaf :=
  globalSection coordinateCocycle (coordinateCoefficients k ⊤)

theorem coordinateSection_coefficient (i k : σ) (W : (projectiveSpace R σ).Opens)
    (hW : W ≤ coordinateOpen i) :
    W.topIso.hom (coefficient (openFrame coordinateCocycle i W hW)
      (restrictSection W.ι (coordinateSection k))) = coordinateRatio i k W hW := by
  exact globalSection_coefficient coordinateCocycle (coordinateCoefficients k ⊤) i W hW

theorem coordinateSection_coefficient_eq (i k : σ) (W : (projectiveSpace R σ).Opens)
    (hW : W ≤ coordinateOpen i) :
    coefficient (openFrame coordinateCocycle i W hW)
      (restrictSection W.ι (coordinateSection k)) =
        W.topIso.inv (coordinateRatio i k W hW) := by
  apply (ConcreteCategory.bijective_of_isIso W.topIso.hom).1
  rw [coordinateSection_coefficient]
  exact (Iso.inv_hom_id_apply W.topIso (coordinateRatio i k W hW)).symm

theorem coordinateSection_normalized (i : σ) (W : (projectiveSpace R σ).Opens)
    (hW : W ≤ coordinateOpen i) :
    coefficient (openFrame coordinateCocycle i W hW)
      (restrictSection W.ι (coordinateSection i)) = 1 := by
  apply (ConcreteCategory.bijective_of_isIso W.topIso.hom).1
  rw [coordinateSection_coefficient, coordinateRatio_self, map_one]

theorem coordinateOpen_le_isoOpen (i : σ) :
    coordinateOpen (R := R) i ≤ PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection i) := by
  intro x hx
  have h := preimage_isoOpen (coordinateSection (R := R) i) (coordinateOpen i).ι
    (openFrame coordinateCocycle i (coordinateOpen i) le_rfl)
  have hn := coordinateSection_normalized (R := R) i (coordinateOpen i) le_rfl
  have hbasic := congrArg (coordinateOpen (R := R) i).toScheme.basicOpen hn
  have hone := h.trans (hbasic.trans (Scheme.basicOpen_one _))
  have hp : (⟨x,hx⟩ : (coordinateOpen (R := R) i).toScheme) ∈
      (coordinateOpen i).ι ⁻¹ᵁ PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection i) := by
    rw [hone]
    trivial
  exact hp

theorem coordinateSection_cover :
    (⨆ i : σ, PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection (R := R) i)) = ⊤ := by
  apply top_unique
  rw [← show (⨆ i : σ, coordinateOpen (R := R) i) = ⊤ from
    PiExponentSeshadri.Projective.standardChart_cover]
  exact iSup_mono coordinateOpen_le_isoOpen

end PiExponent.ProjectiveO1

end

end OAI
