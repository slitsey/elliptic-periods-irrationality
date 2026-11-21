module

public import CatalanCore.Elliptic.EPA.Geo.CentreIdeal
public import OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral
public import OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupRestriction

/-!
# The blow-up of the compactification along the centre ideal (row E09.10b, part 2)

Labels refer to the proof design (§5 E09.10b) and to the OpenAI/Apache-2.0 file
`Ampleness/AdmissibleBlowupGeometry.lean` lines 100--160 (template: the instance block
`IsProper`, `IsIntegral`, `IsNoetherian` of the blow-up, `A`, `J`, `exceptional_presents`,
`isBlowup`).

* `blowup sc s c`: `Y = Bl_𝓘 P`, `blowupProj : Y → P`, `blowupStructureMap : Y → Spec ℂ`.
* `A = blowupProj^* 𝒪(1)` and `J` the exceptional line bundle, with `exceptionalInclusion`.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

namespace Geo

open CatalanCore.Elliptic
open AlgebraicGeometry CategoryTheory TopologicalSpace
open OAI.PiExponent
open OAI.PiExponentSeshadri
open OAI.PiExponentSeshadri.Geometry

variable {m K : ℕ} {W : Weights m} {σ : ℚ} {ch : OriginChart}
variable (sc : EpaScale W σ) (s : OriginSeries ch) (c : Fin K → Fin m → ℂ)

/-- The blow-up `Y` of `P` along the centre ideal `𝓘`. -/
noncomputable abbrev blowup : Scheme := BlowupGluing.scheme (centreIdeal sc s c)

/-- The blow-up morphism `Y → P`. -/
noncomputable abbrev blowupProj : blowup sc s c ⟶ ambX sc := BlowupGluing.projection (centreIdeal sc s c)

/-- The structure map `Y → Spec ℂ`. -/
noncomputable def blowupStructureMap : blowup sc s c ⟶ baseC := blowupProj sc s c ≫ ambProj sc

instance blowupProj_proper : IsProper (blowupProj sc s c) := by infer_instance

instance blowupStructureMap_proper : IsProper (blowupStructureMap sc s c) := by
  dsimp [blowupStructureMap]
  infer_instance

instance blowup_isIntegral : IsIntegral (blowup sc s c) :=
  BlowupGluing.scheme_isIntegral (centreIdeal sc s c) (centreIdeal_support_ne_top sc s c)

instance blowup_isLocallyNoetherian : IsLocallyNoetherian (blowup sc s c) :=
  LocallyOfFiniteType.isLocallyNoetherian (blowupStructureMap sc s c)

instance blowup_compact : CompactSpace (blowup sc s c) :=
  QuasiCompact.compactSpace_of_compactSpace (blowupStructureMap sc s c)

instance blowup_isNoetherian : IsNoetherian (blowup sc s c) := {}

/-- `A = π^* 𝒪(1)`, the pullback of the hyperplane bundle. -/
noncomputable def A : LineBundle (blowup sc s c) := (hyp sc).pullback (blowupProj sc s c)

/-- The exceptional line bundle `𝒥` of the blow-up. -/
noncomputable abbrev J : LineBundle (blowup sc s c) := BlowupGluing.exceptionalLineBundle (centreIdeal sc s c)

/-- The inclusion `𝒥 → 𝒪_Y`. -/
noncomputable abbrev exceptionalInclusion := BlowupGluing.exceptionalInclusion (centreIdeal sc s c)

theorem exceptional_presents :
    PresentsPullbackIdeal (centreIdeal sc s c) (blowupProj sc s c) (J sc s c)
      (exceptionalInclusion sc s c) :=
  BlowupGluing.exceptional_presents (centreIdeal sc s c)

theorem isBlowup : IsBlowup (centreIdeal sc s c) (blowupProj sc s c) :=
  BlowupGluing.isBlowup (centreIdeal sc s c)

end Geo

end CatalanCore.Elliptic.EPA
