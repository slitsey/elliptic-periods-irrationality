module

public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters
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

@[expose] public section

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

variable {K R S : Type*} [CommRing K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S]
variable (e : R ≃ₐ[K] S) (P : Ideal R) [P.IsPrime]

instance primeResidueImage_isPrime : (P.map e.toRingHom).IsPrime :=
  Ideal.map_isPrime_of_equiv e

def primeResidueRingEquiv : P.ResidueField ≃+* (P.map e.toRingHom).ResidueField :=
  IsLocalRing.ResidueField.mapEquiv
    (PiExponentSiegel.W23.atPrimeEquivOfRingEquiv e.toRingEquiv P)

@[simp] theorem primeResidueRingEquiv_algebraMap (r : R) :
    primeResidueRingEquiv e P (algebraMap R P.ResidueField r) =
      algebraMap S (P.map e.toRingHom).ResidueField (e r) := by
  change IsLocalRing.residue (Localization.AtPrime (P.map e.toRingHom))
      (PiExponentSiegel.W23.atPrimeEquivOfRingEquiv e.toRingEquiv P
        (algebraMap R (Localization.AtPrime P) r)) =
    IsLocalRing.residue (Localization.AtPrime (P.map e.toRingHom))
      (algebraMap S (Localization.AtPrime (P.map e.toRingHom)) (e r))
  exact congrArg (IsLocalRing.residue (Localization.AtPrime (P.map e.toRingHom)))
    (PiExponentSiegel.W23.atPrimeEquivOfRingEquiv_algebraMap e.toRingEquiv P r)

def primeResidueAlgEquiv : P.ResidueField ≃ₐ[K] (P.map e.toRingHom).ResidueField where
  __ := primeResidueRingEquiv e P
  commutes' a := by
    change primeResidueRingEquiv e P (algebraMap K P.ResidueField a) = _
    rw [IsScalarTower.algebraMap_apply K R P.ResidueField,
      primeResidueRingEquiv_algebraMap, e.commutes]
    exact (IsScalarTower.algebraMap_apply K S (P.map e.toRingHom).ResidueField a).symm

@[simp] theorem primeResidueAlgEquiv_algebraMap (r : R) :
    primeResidueAlgEquiv e P (algebraMap R P.ResidueField r) =
      algebraMap S (P.map e.toRingHom).ResidueField (e r) :=
  primeResidueRingEquiv_algebraMap e P r

theorem primeResidueAlgEquiv_transcendenceBasis {ι : Type*} (x : ι → P.ResidueField)
    (hx : IsTranscendenceBasis K x) :
    IsTranscendenceBasis K (fun i => primeResidueAlgEquiv e P (x i)) :=
  (primeResidueAlgEquiv e P).isTranscendenceBasis hx

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
