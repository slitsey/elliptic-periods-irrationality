module

public import CatalanCore.Elliptic.EPA.Glue.IdealToPacket
public import CatalanCore.Elliptic.EPA.Glue.Matrix
public import CatalanCore.Elliptic.EPA.Glue.SectionBound
public import CatalanCore.Elliptic.EPA.Geo.Blowup
public import OAI.NumberTheory.PiExponent.Jets.AffineJetPolynomial
public import OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivity

/-!
# Packets from jet surjectivity (row E09.11, part 4)

Labels refer to the proof design (§5 E09.11, §A1). Templates: OpenAI (Apache-2.0,
openai/math fd4aeeb2) `Jets/AffineJetFramedPackets.surjective_of_jetRestriction`,
`Jets/AdmissibleJetPackets.formalPackets_surjective_of_jetRestriction`,
`Approximation/AdmissibleMatrixInterpolation.packetMap_surjective_of_family`.

* `pow_support_subset_chart`: `((I^n).support) ⊆` the chart, `I` the centre ideal.
* `packets_surjective_of_jet`: if `jetRestriction (centreIdeal sc s c) (hyp sc) n` is surjective, and
  the chart coefficients of the sections of `𝒪(1)^n` have source degree `≤ nD`, then the packets of the
  polynomials of source degree `≤ nD` exhaust all families of packets
  `∏_j ℂ⟦T,V⟧ / j_{nD}`.
* `packetMapC_surjective_of_jet`, `matrix_surjective_of_jet`: the same for `F_H` (`packetMapC`) and for
  the D1 packet matrix (rational centres).
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

namespace Glue

open CatalanCore.Elliptic AlgebraicGeometry CategoryTheory
open OAI.PiExponent OAI.PiExponent.JetGeometry

variable {m K : ℕ} {W : Weights m} {σ : ℚ} {ch : OriginChart}

/-- The support of every power of the centre ideal lies in the chart `𝔸^{m+2}` (for `n = 0` it is
empty). -/
theorem pow_support_subset_chart (sc : Geo.EpaScale W σ) (s : OriginSeries ch)
    (c : Fin K → Fin m → ℂ) (n : ℕ) :
    (((Geo.centreIdeal sc s c) ^ n).support : Set (Geo.ambX sc)) ⊆
      (Geo.ambChart sc).opensRange := by
  cases n with
  | zero =>
    have h : (((Geo.centreIdeal sc s c) ^ 0).support : Set (Geo.ambX sc)) = ∅ := by
      first
        | (simp; done)
        | (change (((⊤ : (Geo.ambX sc).IdealSheafData)).support : Set (Geo.ambX sc)) = ∅
           rw [Scheme.IdealSheafData.support_top]
           simp)
    rw [h]
    exact Set.empty_subset _
  | succ n =>
    rw [Scheme.IdealSheafData.support_pow_succ]
    exact Geo.centreIdeal_support_subset_chart sc s c

/-- **Row E09.11.** Jet surjectivity at `n` and the source-degree bound of the chart coefficients give
surjectivity of the packet map on `{P : ℂ[u,t,Z] // SrcDeg W (nD) P}`. -/
theorem packets_surjective_of_jet (sc : Geo.EpaScale W σ) (s : OriginSeries ch)
    (c : Fin K → Fin m → ℂ) (hc : Function.Injective c) (n : ℕ)
    (hjet : Function.Surjective
      (BlowupJetSurjectivity.jetRestriction (Geo.centreIdeal sc s c) (Geo.hyp sc) n))
    (e : AffineJetCoefficientInterface.Frame (Geo.ambChart sc) (Geo.hyp sc))
    (hsec : ∀ t : AffineJetCoefficientInterface.Sections (Geo.hyp sc) n,
      SrcDeg W ((n * sc.D : ℕ) : ℝ)
        (AffineJetCoefficientInterface.coefficient (Geo.ambChart sc) (Geo.hyp sc) n e t)) :
    Function.Surjective fun P : {P : AmbRing m // SrcDeg W ((n * sc.D : ℕ) : ℝ) P} => fun j =>
      rationalCoefficientPacket (jetWt W) ((n * sc.D : ℕ) : ℚ) (ellJet s (c j) P.val) := by
  intro packets
  have hq := AffineJetPolynomial.polynomialQuotient_surjective_of_jetRestriction
    (Geo.centreIdeal sc s c) (Geo.hyp sc) n (Geo.ambChart sc) e (Geo.centreIdealAff sc s c)
    (Geo.centreIdeal_restrict sc s c) (pow_support_subset_chart sc s c n) hjet
  obtain ⟨t, ht⟩ := quotient_to_packets_surjective sc s c hc n
    (AffineJetCoefficientInterface.coefficient (Geo.ambChart sc) (Geo.hyp sc) n e) hq packets
  exact ⟨⟨_, hsec t⟩, ht⟩

/-- The complex packet map `F_{nD} → ∏_j ℂ^{𝒥_{nD}}` is surjective (design §A1). -/
theorem packetMapC_surjective_of_jet (sc : Geo.EpaScale W σ) (s : OriginSeries ch)
    (c : Fin K → Fin m → ℂ) (hc : Function.Injective c) (n : ℕ)
    (hjet : Function.Surjective
      (BlowupJetSurjectivity.jetRestriction (Geo.centreIdeal sc s c) (Geo.hyp sc) n))
    (e : AffineJetCoefficientInterface.Frame (Geo.ambChart sc) (Geo.hyp sc))
    (hsec : ∀ t : AffineJetCoefficientInterface.Sections (Geo.hyp sc) n,
      SrcDeg W ((n * sc.D : ℕ) : ℝ)
        (AffineJetCoefficientInterface.coefficient (Geo.ambChart sc) (Geo.hyp sc) n e t)) :
    Function.Surjective (packetMapC s W c (n * sc.D)) :=
  packetMapC_surjective_of_packets s c (n * sc.D)
    (packets_surjective_of_jet sc s c hc n hjet e hsec)

/-- **Row E09.11 (D1 matrix).** For rational centres `cen` with distinct complex images, the D1 packet
matrix at `H = nD` is surjective over `ℂ`. -/
theorem matrix_surjective_of_jet (sc : Geo.EpaScale W σ) (s : OriginSeries ch)
    (cen : Fin K → Fin m → ℚ) (hc : Function.Injective fun j i => ((cen j i : ℚ) : ℂ)) (n : ℕ)
    (hjet : Function.Surjective
      (BlowupJetSurjectivity.jetRestriction (Geo.centreIdeal sc s
        (fun j i => ((cen j i : ℚ) : ℂ))) (Geo.hyp sc) n))
    (e : AffineJetCoefficientInterface.Frame (Geo.ambChart sc) (Geo.hyp sc))
    (hsec : ∀ t : AffineJetCoefficientInterface.Sections (Geo.hyp sc) n,
      SrcDeg W ((n * sc.D : ℕ) : ℝ)
        (AffineJetCoefficientInterface.coefficient (Geo.ambChart sc) (Geo.hyp sc) n e t)) :
    Function.Surjective
      ((packetMatrix W s cen ((n * sc.D : ℕ) : ℝ)).map (algebraMap ℚ ℂ)).mulVecLin :=
  matrix_surjective_of_packets s cen (n * sc.D)
    (packets_surjective_of_jet sc s (fun j i => ((cen j i : ℚ) : ℂ)) hc n hjet e hsec)

end Glue

end CatalanCore.Elliptic.EPA
