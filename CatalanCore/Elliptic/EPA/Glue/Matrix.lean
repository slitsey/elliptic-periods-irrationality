module

public import CatalanCore.Elliptic.EPA.Jet
public import CatalanCore.Elliptic.EPA.Reduce
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Reduction, `F_H` and the D1 matrix (row E09.11, part 3)

Labels refer to the proof design §5 E09.11 and §A1. Template: OpenAI (Apache-2.0,
openai/math fd4aeeb2) `Approximation/AdmissibleMatrixInterpolation.lean`
(`actualMatrix_surjective_of_formalPackets`, `packetMap_surjective_of_family`).

* `FH W H`: the paper's `F_H`, the span of the monomials `u^k t^b Z^α` of the columns of
  `Weights.colSet H` (`b ≤ 1`, `2 w₀ (k + 2b) + W(α) ≤ H`, condition (S)).
* `packetMapC s W c H : F_H →ₗ[ℂ] ∏_j ℂ^{𝒥_H}`: the packet map (eq:packet) for complex centres.
* `exists_fh_of_packets`: if the packets of polynomials of source degree `≤ H` exhaust all families of
  packets, so do the packets of `F_H` (reduction modulo `f`, `Φ_c(f) = 0`).
* `packetMapC_surjective_of_packets`, `matrix_surjective_of_packets`: surjectivity of `packetMapC` and of
  the D1 packet matrix (over `ℂ`) for rational centres.

The hypothesis `hpk` is produced by `Glue.Surjective` (from the jet surjectivity) and consumed here.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

namespace Glue

open CatalanCore.Elliptic OAI.PiExponent.JetGeometry

variable {m K : ℕ} {W : Weights m} {ch : OriginChart}

/-- The paper's `F_H`. -/
noncomputable def FH (W : Weights m) (H : ℕ) : Submodule ℂ (AmbRing m) :=
  Submodule.span ℂ {Q : AmbRing m | ∃ c ∈ W.colSet (H : ℝ), Q = ambMonomial c}

/-- The target of the packet map: for each centre `j`, the coefficients of jet weight `< H`. -/
abbrev PacketTarget (W : Weights m) (K H : ℕ) : Type :=
  Fin K → {d : Fin (m + 1) →₀ ℕ // Finsupp.weight (jetWt W) d < (H : ℚ)} → ℂ

/-- The packet map `F_H → ∏_j ℂ^{𝒥_H}` (eq:packet), complex centres. -/
noncomputable def packetMapC (s : OriginSeries ch) (W : Weights m) (c : Fin K → Fin m → ℂ)
    (H : ℕ) : FH W H →ₗ[ℂ] PacketTarget W K H where
  toFun P := fun j d => MvPowerSeries.coeff d.val (ellJet s (c j) P.val)
  map_add' P Q := by
    funext j d
    simp
  map_smul' a P := by
    funext j d
    simp

theorem ellJet_eq_of_sub_mem (s : OriginSeries ch) (c : Fin m → ℂ) {P P' : AmbRing m}
    (h : P' - P ∈ (Ideal.span {relation ch} : Ideal (AmbRing m))) :
    ellJet s c P' = ellJet s c P := by
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp h
  have h0 : ellJet s c (P' - P) = 0 := by
    rw [← hq, map_mul, ellJet_relation, mul_zero]
  rw [map_sub, sub_eq_zero] at h0
  exact h0

/-- Reduction: packets of polynomials of source degree `≤ H` are packets of elements of `F_H`. -/
theorem exists_fh_of_packets (s : OriginSeries ch) (c : Fin K → Fin m → ℂ) (H : ℕ)
    (hpk : Function.Surjective fun P : {P : AmbRing m // SrcDeg W (H : ℝ) P} => fun j =>
      rationalCoefficientPacket (jetWt W) (H : ℚ) (ellJet s (c j) P.val)) :
    ∀ packets : PacketTarget W K H, ∃ P' ∈ FH W H, ∀ j,
      rationalCoefficientPacket (jetWt W) (H : ℚ) (ellJet s (c j) P') = packets j := by
  intro packets
  obtain ⟨⟨P, hP⟩, hPe⟩ := hpk packets
  obtain ⟨P', hrel, hdeg, ht⟩ := exists_reduced (ch := ch) hP
  refine ⟨P', reduced_mem_span hdeg ht, fun j => ?_⟩
  rw [ellJet_eq_of_sub_mem s (c j) hrel]
  exact congrFun hPe j

theorem packetMapC_surjective_of_packets (s : OriginSeries ch) (c : Fin K → Fin m → ℂ) (H : ℕ)
    (hpk : Function.Surjective fun P : {P : AmbRing m // SrcDeg W (H : ℝ) P} => fun j =>
      rationalCoefficientPacket (jetWt W) (H : ℚ) (ellJet s (c j) P.val)) :
    Function.Surjective (packetMapC s W c H) := by
  intro packets
  obtain ⟨P', hmem, hP'⟩ := exists_fh_of_packets s c H hpk packets
  exact ⟨⟨P', hmem⟩, funext fun j => hP' j⟩

/-! ### The D1 matrix -/

theorem weight_cast_eq (W : Weights m) (d : Fin (m + 1) →₀ ℕ) :
    ((Finsupp.weight (jetWt W) d : ℚ) : ℝ) = ∑ i, W.rowWeights i * (d i : ℝ) := by
  simp only [Finsupp.weight_eq_sum, nsmul_eq_mul, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [jetWt_cast, mul_comm]

theorem mem_rowSet_of_weight_lt (W : Weights m) {H : ℕ} (d : Fin (m + 1) →₀ ℕ)
    (hd : Finsupp.weight (jetWt W) d < (H : ℚ)) : (⇑d : Fin (m + 1) → ℕ) ∈ W.rowSet (H : ℝ) := by
  rw [W.mem_rowSet_iff (H : ℝ)]
  rw [← weight_cast_eq W d]
  exact_mod_cast hd

theorem weight_lt_of_mem_rowSet (W : Weights m) {H : ℕ} {a : Fin (m + 1) → ℕ}
    (ha : a ∈ W.rowSet (H : ℝ)) :
    Finsupp.weight (jetWt W) (Finsupp.equivFunOnFinite.symm a) < (H : ℚ) := by
  have h1 := (W.mem_rowSet_iff (H : ℝ) a).mp ha
  have h2 := weight_cast_eq W (Finsupp.equivFunOnFinite.symm a)
  simp only [Finsupp.coe_equivFunOnFinite_symm] at h2
  have h3 : ((Finsupp.weight (jetWt W) (Finsupp.equivFunOnFinite.symm a) : ℚ) : ℝ) <
      ((H : ℚ) : ℝ) := by
    rw [h2]
    simpa using h1
  exact_mod_cast h3

/-- Row E09.11: the D1 packet matrix of rational centres is surjective (over `ℂ`) as soon as the
packets of polynomials of source degree `≤ H` exhaust all families of packets. A target vector is a
family of packets; reduce a polynomial with these packets modulo `f` to an element of `F_H`, a
`ℂ`-combination of the columns; the combination coefficients solve `A x = target`
(`ellJet_coeff_monomial`). -/
theorem matrix_surjective_of_packets (s : OriginSeries ch) (cen : Fin K → Fin m → ℚ) (H : ℕ)
    (hpk : Function.Surjective fun P : {P : AmbRing m // SrcDeg W (H : ℝ) P} => fun j =>
      rationalCoefficientPacket (jetWt W) (H : ℚ)
        (ellJet s (fun i => ((cen j i : ℚ) : ℂ)) P.val)) :
    Function.Surjective ((packetMatrix W s cen (H : ℝ)).map (algebraMap ℚ ℂ)).mulVecLin := by
  classical
  intro v
  let packets : PacketTarget W K H := fun j d =>
    v (j, ⟨(⇑d.val : Fin (m + 1) → ℕ), mem_rowSet_of_weight_lt W d.val d.property⟩)
  obtain ⟨P', hmem, hP'⟩ :=
    exists_fh_of_packets s (fun j i => ((cen j i : ℚ) : ℂ)) H hpk packets
  have hset : {Q : AmbRing m | ∃ c ∈ W.colSet (H : ℝ), Q = ambMonomial c} =
      Set.range (fun col : Col W (H : ℝ) => ambMonomial (m := m) col.1) := by
    ext Q
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
    · rintro ⟨col, rfl⟩
      exact ⟨col.1, col.2, rfl⟩
  have hmem' : P' ∈ LinearMap.range
      (Fintype.linearCombination ℂ (fun col : Col W (H : ℝ) => ambMonomial (m := m) col.1)) := by
    rw [Fintype.range_linearCombination, ← hset]
    exact hmem
  obtain ⟨x, hx⟩ := hmem'
  refine ⟨x, ?_⟩
  funext ρ
  rw [Matrix.mulVecLin_apply]
  show ∑ col, (((packetMatrix W s cen (H : ℝ)).map (algebraMap ℚ ℂ)) ρ col) * x col = v ρ
  have hent : ∀ col : Col W (H : ℝ),
      ((packetMatrix W s cen (H : ℝ)).map (algebraMap ℚ ℂ)) ρ col =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (ρ.2.1 : Fin (m + 1) → ℕ))
          (ellJet s (fun i => ((cen ρ.1 i : ℚ) : ℂ)) (ambMonomial col.1)) := by
    intro col
    rw [ellJet_coeff_monomial, Matrix.map_apply, packetMatrix_apply, eq_ratCast]
  simp_rw [hent]
  have hsum : ∑ col : Col W (H : ℝ),
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (ρ.2.1 : Fin (m + 1) → ℕ))
        (ellJet s (fun i => ((cen ρ.1 i : ℚ) : ℂ)) (ambMonomial col.1)) * x col =
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (ρ.2.1 : Fin (m + 1) → ℕ))
        (ellJet s (fun i => ((cen ρ.1 i : ℚ) : ℂ)) P') := by
    rw [← hx, Fintype.linearCombination_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun col _ => ?_
    rw [map_smul, map_smul, smul_eq_mul, mul_comm]
  rw [hsum]
  have hfinal := congrFun (hP' ρ.1)
    ⟨Finsupp.equivFunOnFinite.symm (ρ.2.1 : Fin (m + 1) → ℕ), weight_lt_of_mem_rowSet W ρ.2.2⟩
  refine hfinal.trans ?_
  exact congrArg v (Prod.ext rfl (Subtype.ext (Finsupp.coe_equivFunOnFinite_symm _)))

end Glue

end CatalanCore.Elliptic.EPA
