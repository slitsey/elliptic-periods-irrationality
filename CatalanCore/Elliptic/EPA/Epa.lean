module

public import CatalanCore.Elliptic.EPA.Packet
public import CatalanCore.Elliptic.EPA.Geo.Ample
public import CatalanCore.Elliptic.EPA.Glue.Surjective

/-!
# The theorem `thm:epa` and the D1 interface (row E09.12)

Labels refer to the proof design (§5 E09.12, §A1). Paper: `thm:epa`
(Chudnovsky--Chudnovsky, Cor. 13.5; paper l.451--470).

* `epa_complex`: the complex-centre form of `thm:epa`: there is `D > 0` (depending on the data, the
  weights and `σ₀` only) such that for every centre array `c : Fin K → Fin m → ℂ` injective in each
  coordinate there is `H₀` with `packetMapC s W c H : F_H → ∏_j ℂ^{𝒥_H}` surjective for all
  `H ≥ H₀`, `D ∣ H`.
* `epa`: the same for rational centres in the form D1 consumes, `PacketSurjective W K s`.

Quantifier order: data, `σ₀`, thresholds, weights, `D` (the scale `sc.D`, depending on `W`, `σ` only),
centres, `H₀ = max N₁ N₂ · D` (`N₁` from the jet surjectivity, `N₂` from the section bound).
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

open CatalanCore.Elliptic

variable {m K : ℕ}

/-- **`thm:epa`, complex centres** (design §A1). -/
theorem epa_complex (hm : 1 ≤ m) (W : Weights m) {ch : OriginChart} (s : OriginSeries ch)
    (σ : ℚ) (hσ : EpaSigma m K W σ) (hthr : EpaThresholds W σ) :
    ∃ D : ℕ, 0 < D ∧ ∀ c : Fin K → Fin m → ℂ, (∀ i : Fin m, Function.Injective fun j => c j i) →
      ∃ H₀ : ℕ, ∀ H : ℕ, H₀ ≤ H → D ∣ H → Function.Surjective (Glue.packetMapC s W c H) := by
  obtain ⟨sc⟩ := Geo.exists_epaScale W σ
  refine ⟨sc.D, sc.D_pos, fun c hc => ?_⟩
  have hc' : Function.Injective c := fun a b h =>
    hc ⟨0, hm⟩ (congrFun h ⟨0, hm⟩)
  obtain ⟨N₁, hN₁⟩ := Geo.eventual_jet_surjective (sc := sc) (s := s) (c := c) hσ hthr hm hc
  obtain ⟨N₂, hN₂⟩ := Glue.eventual_srcDeg sc
  obtain ⟨e⟩ := Glue.ambFrame_nonempty sc
  refine ⟨max N₁ N₂ * sc.D, fun H hH hdvd => ?_⟩
  obtain ⟨n, hn⟩ := hdvd
  have hH' : H = n * sc.D := by rw [hn, Nat.mul_comm]
  subst hH'
  have hle : max N₁ N₂ ≤ n := Nat.le_of_mul_le_mul_right hH sc.D_pos
  exact Glue.packetMapC_surjective_of_jet sc s c hc' n
    (hN₁ n (le_trans (le_max_left _ _) hle)) e
    (fun t => hN₂ n (le_trans (le_max_right _ _) hle) e t)

/-- **`thm:epa`** (row E09.12), in the form consumed by D1 (rational centres):
`PacketSurjective W K s`. -/
theorem epa (hm : 1 ≤ m) (W : Weights m) {ch : OriginChart} (s : OriginSeries ch)
    (σ : ℚ) (hσ : EpaSigma m K W σ) (hthr : EpaThresholds W σ) :
    PacketSurjective W K s := by
  obtain ⟨sc⟩ := Geo.exists_epaScale W σ
  refine ⟨sc.D, sc.D_pos, fun cen hcen => ?_⟩
  have hc : ∀ i : Fin m, Function.Injective fun j => ((cen j i : ℚ) : ℂ) := fun i a b h =>
    hcen i (by simp only at h ⊢; exact_mod_cast h)
  have hc' : Function.Injective fun j i => ((cen j i : ℚ) : ℂ) := fun a b h =>
    hc ⟨0, hm⟩ (congrFun h ⟨0, hm⟩)
  obtain ⟨N₁, hN₁⟩ := Geo.eventual_jet_surjective (sc := sc) (s := s)
    (c := fun j i => ((cen j i : ℚ) : ℂ)) hσ hthr hm hc
  obtain ⟨N₂, hN₂⟩ := Glue.eventual_srcDeg sc
  obtain ⟨e⟩ := Glue.ambFrame_nonempty sc
  refine ⟨max N₁ N₂ * sc.D, fun H hH hdvd => ?_⟩
  obtain ⟨n, hn⟩ := hdvd
  have hH' : H = n * sc.D := by rw [hn, Nat.mul_comm]
  subst hH'
  have hle : max N₁ N₂ ≤ n := Nat.le_of_mul_le_mul_right hH sc.D_pos
  have := Glue.matrix_surjective_of_jet sc s cen hc' n
    (hN₁ n (le_trans (le_max_left _ _) hle)) e
    (fun t => hN₂ n (le_trans (le_max_right _ _) hle) e t)
  exact this

end CatalanCore.Elliptic.EPA
