module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-!
# Rescaling a period pair

Rows E03 and E21 of the T3E ledger (`lem:integral`). Multiplying both periods by a nonzero
complex number `c` multiplies the lattice by `c`, the lattice sums `G n` by `c⁻ⁿ`, hence `g₂` by
`c⁻⁴` and `g₃` by `c⁻⁶`.

The definitions and proofs of `scale`, `lattice_scale`, `latticeScaleEquiv`, `G_scale`, `g₂_scale`,
`g₃_scale` and `G_eq_of_lattice_eq` are adapted from the Tau Ceti project
(`TauCeti/Analysis/Complex/UpperHalfPlane/PeriodPair.lean`, Copyright (c) 2026 The Tau Ceti
contributors, Apache 2.0), which states them for the action `c • L` of `ℂˣ` on `PeriodPair`. Here
`scale c L` is a plain function so that no instance on Mathlib's `PeriodPair` is introduced.
-/

@[expose] public section

noncomputable section

namespace CatalanCore.Elliptic.Lattice

open PeriodPair

/-- Multiplying a period pair by a nonzero complex number: `(ω₁, ω₂) ↦ (c ω₁, c ω₂)`. -/
def scale (c : ℂˣ) (L : PeriodPair) : PeriodPair where
  ω₁ := c * L.ω₁
  ω₂ := c * L.ω₂
  indep := by
    convert L.indep.map' (LinearMap.mulLeft ℝ (c : ℂ))
      (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ c.ne_zero)) using 1
    ext i
    fin_cases i <;> rfl

@[simp] lemma scale_ω₁ (c : ℂˣ) (L : PeriodPair) : (scale c L).ω₁ = c * L.ω₁ := rfl

@[simp] lemma scale_ω₂ (c : ℂˣ) (L : PeriodPair) : (scale c L).ω₂ = c * L.ω₂ := rfl

/-- The lattice of `scale c L` is the image of the lattice of `L` under multiplication by `c`. -/
lemma lattice_scale (c : ℂˣ) (L : PeriodPair) :
    (scale c L).lattice = L.lattice.map (LinearMap.mulLeft ℤ (c : ℂ)) := by
  simp [PeriodPair.lattice, Submodule.map_span]

/-- Multiplication by `c` identifies the lattices of `L` and of `scale c L`. -/
def latticeScaleEquiv (c : ℂˣ) (L : PeriodPair) : L.lattice ≃ₗ[ℤ] (scale c L).lattice :=
  (Submodule.equivMapOfInjective _ (mul_right_injective₀ c.ne_zero) L.lattice).trans
    (LinearEquiv.ofEq _ _ (lattice_scale c L).symm)

@[simp]
lemma coe_latticeScaleEquiv (c : ℂˣ) (L : PeriodPair) (l : L.lattice) :
    (latticeScaleEquiv c L l : ℂ) = c * l := by
  simp only [latticeScaleEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
  exact Submodule.coe_equivMapOfInjective_apply ..

/-- `c x` lies in the lattice of `scale c L` exactly when `x` lies in the lattice of `L`. -/
@[simp]
lemma mul_mem_lattice_scale_iff (c : ℂˣ) (L : PeriodPair) {x : ℂ} :
    (c : ℂ) * x ∈ (scale c L).lattice ↔ x ∈ L.lattice := by
  rw [lattice_scale, Submodule.mem_map]
  exact ⟨fun ⟨y, hy, hyx⟩ ↦ mul_right_injective₀ c.ne_zero hyx ▸ hy, fun h ↦ ⟨x, h, rfl⟩⟩

/-- `z` lies in the lattice of `scale c L` exactly when `c⁻¹ z` lies in the lattice of `L`. -/
lemma mem_lattice_scale_iff (c : ℂˣ) (L : PeriodPair) {z : ℂ} :
    z ∈ (scale c L).lattice ↔ ((c⁻¹ : ℂˣ) : ℂ) * z ∈ L.lattice := by
  rw [← mul_mem_lattice_scale_iff c L, ← mul_assoc]
  simp

/-- The lattice sums `G n` are homogeneous of degree `-n` in the lattice. -/
lemma G_scale (c : ℂˣ) (L : PeriodPair) (n : ℕ) : (scale c L).G n = L.G n / (c : ℂ) ^ n := by
  rw [G, G, ← (latticeScaleEquiv c L).toEquiv.tsum_eq, div_eq_mul_inv, ← tsum_mul_right]
  simp [mul_pow, mul_comm]

lemma g₂_scale (c : ℂˣ) (L : PeriodPair) : (scale c L).g₂ = L.g₂ / (c : ℂ) ^ 4 := by
  rw [g₂, g₂, G_scale, mul_div_assoc]

lemma g₃_scale (c : ℂˣ) (L : PeriodPair) : (scale c L).g₃ = L.g₃ / (c : ℂ) ^ 6 := by
  rw [g₃, g₃, G_scale, mul_div_assoc]

/-- The lattice sums `G n` depend only on the lattice, not on the chosen basis. -/
lemma G_eq_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) : L.G = L'.G := by
  ext n
  rw [G, G, h]

lemma g₂_eq_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) : L.g₂ = L'.g₂ := by
  simp [g₂, G_eq_of_lattice_eq h]

lemma g₃_eq_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) : L.g₃ = L'.g₃ := by
  simp [g₃, G_eq_of_lattice_eq h]

end CatalanCore.Elliptic.Lattice
