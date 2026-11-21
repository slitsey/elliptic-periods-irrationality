module

public import CatalanCore.Elliptic.EPA.Geo.Margin
public import OAI.NumberTheory.PiExponent.Ampleness.AmpleIso
public import OAI.NumberTheory.PiExponent.Ampleness.NumericalAmplenessTheorem
public import OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupJetSurjectivity
public import OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivityComplete
public import OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation

/-!
# Ampleness of the blow-up bundle and eventual jet surjectivity (row E09.10d, part 2)

Labels refer to `D2-DESIGN-2026-11-20.md` (§5 E09.10d) and to the OpenAI/Apache-2.0 files
`Ampleness/AdmissibleBlowupAmple.lean` (`interpolationBundle_ample`),
`Ampleness/AdmissibleJetAmpleness.lean` (`blowupBundle_ample`) and
`Jets/AdmissibleJetSurjectivity.lean` (`eventual_jetRestriction_surjective`).

* `interpolationBundle_ample`: `A ⊗ 𝒥` is ample (OAI `isAmple_of_uniform_curve_margin` with `H = A^q ⊗ 𝒥`
  and the margin of `Geo/Margin.lean`).
* `blowupBundle_ample`: `𝒥 ⊗ A` (OAI `blowupBundle`) is ample (`moduleTensorComm`).
* `eventual_jet_surjective`: there is `N` with `jetRestriction (centreIdeal sc s c) (hyp sc) n`
  surjective for all `n ≥ N` (OAI `eventual_blowup_jetRestriction_surjective`).  `N` depends on the
  centres; the scale `D` does not.
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
variable {sc : EpaScale W σ} {s : OriginSeries ch} {c : Fin K → Fin m → ℂ}

/-- `A ⊗ 𝒥` is ample on the blow-up. -/
theorem interpolationBundle_ample (hσ : EpaSigma m K W σ) (hthr : EpaThresholds W σ)
    (h1m : 1 ≤ m) (hc : ∀ i, Function.Injective fun j => c j i) :
    ((A sc s c).tensor (J sc s c)).IsAmple := by
  have hσ0 : (0 : ℝ) < σ := by exact_mod_cast hσ.pos
  exact NumericalAmpleness.isAmple_of_uniform_curve_margin (blowupStructureMap sc s c)
    (H sc s c) ((A sc s c).tensor (J sc s c)) (H_ample sc s c)
    (BlowupCurveMargin.marginCoefficient (ampleExponent sc s c) (σ : ℝ))
    (BlowupCurveMargin.marginCoefficient_pos (one_lt_ampleExponent sc s c) hσ0)
    (fun C => uniform_margin hσ hthr h1m hc C)

/-- **Row E09.10d, `blowupBundle_ample`.** -/
theorem blowupBundle_ample (hσ : EpaSigma m K W σ) (hthr : EpaThresholds W σ)
    (h1m : 1 ≤ m) (hc : ∀ i, Function.Injective fun j => c j i) :
    (BlowupJetSurjectivity.blowupBundle (centreIdeal sc s c) (hyp sc)).IsAmple :=
  AmpleIso.isAmple_of_sheaf_iso ((A sc s c).tensor (J sc s c))
    (BlowupJetSurjectivity.blowupBundle (centreIdeal sc s c) (hyp sc))
    (moduleTensorComm (A sc s c).sheaf (J sc s c).sheaf)
    (interpolationBundle_ample hσ hthr h1m hc)

/-- **Row E09.10d, `eventual_jet_surjective`.** -/
theorem eventual_jet_surjective (hσ : EpaSigma m K W σ) (hthr : EpaThresholds W σ)
    (h1m : 1 ≤ m) (hc : ∀ i, Function.Injective fun j => c j i) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      Function.Surjective (BlowupJetSurjectivity.jetRestriction (centreIdeal sc s c) (hyp sc) n) :=
  BlowupJetSurjectivity.eventual_blowup_jetRestriction_surjective (ambProj sc)
    (centreIdeal sc s c) (hyp sc) (blowupBundle_ample hσ hthr h1m hc)

end Geo

end CatalanCore.Elliptic.EPA
