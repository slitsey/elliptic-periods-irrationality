module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import CatalanCore.Elliptic.Lattice.Scale

/-!
# The discriminant of a period lattice does not vanish

For every `L : PeriodPair`, `g₂³ - 27 g₃² ≠ 0` (used in row E03). Route: every lattice is
`c • (ℤ τ + ℤ)` with `τ` in the upper half-plane; `g₂(ℤτ+ℤ) = (4π⁴/3) E₄(τ)`,
`g₃(ℤτ+ℤ) = (8π⁶/27) E₆(τ)`; and Mathlib's `Δ = (E₄³ - E₆²)/1728` is nonzero.

Adapted from the Tau Ceti project (`TauCeti/Analysis/SpecialFunctions/Elliptic/Uniformization.lean`
and `.../UpperHalfPlane/PeriodPair.lean`, Copyright (c) 2026 The Tau Ceti contributors,
Apache 2.0), re-proved against Mathlib alone.
-/

@[expose] public section

noncomputable section

namespace CatalanCore.Elliptic.Lattice

open Complex UpperHalfPlane ModularForm PeriodPair
open scoped Real

/-- The period pair `(τ, 1)`, with lattice `ℤ τ + ℤ`. -/
def tauPair (τ : ℍ) : PeriodPair where
  ω₁ := τ
  ω₂ := 1
  indep := by
    refine LinearIndependent.pair_iff.mpr fun s t h ↦ ?_
    have hs : s = 0 := by
      have him := congrArg Complex.im h
      simp only [Complex.real_smul, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, mul_one, Complex.zero_im] at him
      exact (mul_eq_zero.mp him).resolve_right τ.im_pos.ne'
    subst hs
    simpa using h

@[simp] lemma tauPair_ω₁ (τ : ℍ) : (tauPair τ).ω₁ = τ := rfl

@[simp] lemma tauPair_ω₂ (τ : ℍ) : (tauPair τ).ω₂ = 1 := rfl

/-- For `k ≥ 3` the lattice sum `G k` of `ℤ τ + ℤ` is `2 ζ(k) E_k(τ)`. -/
lemma G_tauPair (τ : ℍ) {k : ℕ} (hk : 3 ≤ k) :
    (tauPair τ).G k = 2 * riemannZeta k * E hk τ := by
  have h := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk τ
  rw [PeriodPair.G,
    ← ((finTwoArrowEquiv ℤ).trans (tauPair τ).latticeEquivProd.symm.toEquiv).tsum_eq]
  have hE : E hk τ = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 k τ := rfl
  rw [hE, mul_comm 2, mul_assoc, ← mul_assoc 2, mul_one_div_cancel two_ne_zero, one_mul, ← h]
  refine tsum_congr fun v ↦ ?_
  simp [EisensteinSeries.eisSummand, PeriodPair.latticeEquiv_symm_apply]

/-- `g₂(ℤ τ + ℤ) = (4 π⁴ / 3) E₄(τ)`. -/
lemma g₂_tauPair (τ : ℍ) : (tauPair τ).g₂ = 4 * (π : ℂ) ^ 4 / 3 * E₄ τ := by
  rw [PeriodPair.g₂, G_tauPair τ (by norm_num), Nat.cast_ofNat, riemannZeta_four]
  ring

/-- `g₃(ℤ τ + ℤ) = (8 π⁶ / 27) E₆(τ)`. -/
lemma g₃_tauPair (τ : ℍ) : (tauPair τ).g₃ = 8 * (π : ℂ) ^ 6 / 27 * E₆ τ := by
  have hζ : riemannZeta 6 = (π : ℂ) ^ 6 / 945 := by
    have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
    norm_num [show bernoulli 6 = 1 / 42 by decide +kernel, Nat.factorial] at h
    rw [h]
    ring
  rw [PeriodPair.g₃, G_tauPair τ (by norm_num), Nat.cast_ofNat, hζ]
  ring

/-- `g₂³ - 27 g₃² = (2π)¹² Δ` on `ℤ τ + ℤ`. -/
lemma disc_tauPair (τ : ℍ) :
    (tauPair τ).g₂ ^ 3 - 27 * (tauPair τ).g₃ ^ 2 = (2 * (π : ℂ)) ^ 12 * discriminant τ := by
  rw [g₂_tauPair, g₃_tauPair, discriminant_eq_E₄_cube_sub_E₆_sq]
  ring

lemma ω₁_ne_zero (L : PeriodPair) : L.ω₁ ≠ 0 := by
  simpa using L.indep.ne_zero 0

lemma ω₂_ne_zero (L : PeriodPair) : L.ω₂ ≠ 0 := by
  simpa using L.indep.ne_zero 1

/-- The ratio of the two periods is not real. -/
lemma im_ω₁_div_ω₂_ne_zero (L : PeriodPair) : (L.ω₁ / L.ω₂).im ≠ 0 := by
  intro h
  have hr : ((L.ω₁ / L.ω₂).re : ℂ) = L.ω₁ / L.ω₂ := Complex.ext (by simp) (by simp [h])
  obtain ⟨hs, -⟩ := LinearIndependent.pair_iff.mp L.indep 1 (-(L.ω₁ / L.ω₂).re) (by
    rw [one_smul, Complex.real_smul, Complex.ofReal_neg, hr, neg_mul,
      div_mul_cancel₀ _ (ω₂_ne_zero L), add_neg_cancel])
  exact one_ne_zero hs

/-- Every lattice is `c (ℤ τ + ℤ)` for some `c ≠ 0` and `τ` in the upper half-plane. -/
lemma exists_lattice_eq_scale (L : PeriodPair) :
    ∃ (c : ℂˣ) (τ : ℍ), L.lattice = (scale c (tauPair τ)).lattice := by
  rcases (im_ω₁_div_ω₂_ne_zero L).lt_or_gt with h | h
  · have h' : 0 < (L.ω₂ / L.ω₁).im := by
      rw [← inv_div, Complex.inv_im]
      exact div_pos (neg_pos.mpr h)
        (Complex.normSq_pos.mpr (div_ne_zero (ω₁_ne_zero L) (ω₂_ne_zero L)))
    refine ⟨Units.mk0 L.ω₁ (ω₁_ne_zero L), UpperHalfPlane.mk _ h', ?_⟩
    simp only [PeriodPair.lattice, scale_ω₁, scale_ω₂, tauPair_ω₁, tauPair_ω₂, Units.val_mk0,
      UpperHalfPlane.coe_mk, mul_div_cancel₀ _ (ω₁_ne_zero L), mul_one, Set.pair_comm]
  · refine ⟨Units.mk0 L.ω₂ (ω₂_ne_zero L), UpperHalfPlane.mk _ h, ?_⟩
    simp only [PeriodPair.lattice, scale_ω₁, scale_ω₂, tauPair_ω₁, tauPair_ω₂, Units.val_mk0,
      UpperHalfPlane.coe_mk, mul_div_cancel₀ _ (ω₂_ne_zero L), mul_one]

/-- **The discriminant `g₂³ - 27 g₃²` of a lattice does not vanish.** -/
theorem disc_ne_zero (L : PeriodPair) : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := by
  obtain ⟨c, τ, h⟩ := exists_lattice_eq_scale L
  have h2 : L.g₂ = (tauPair τ).g₂ / (c : ℂ) ^ 4 := by rw [g₂_eq_of_lattice_eq h, g₂_scale]
  have h3 : L.g₃ = (tauPair τ).g₃ / (c : ℂ) ^ 6 := by rw [g₃_eq_of_lattice_eq h, g₃_scale]
  have hc : (c : ℂ) ≠ 0 := c.ne_zero
  have key : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 =
      ((tauPair τ).g₂ ^ 3 - 27 * (tauPair τ).g₃ ^ 2) / (c : ℂ) ^ 12 := by
    rw [h2, h3]
    field_simp
  rw [key, disc_tauPair]
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (mul_ne_zero two_ne_zero
    (by exact_mod_cast Real.pi_ne_zero))) (discriminant_ne_zero τ)) (pow_ne_zero _ hc)

end CatalanCore.Elliptic.Lattice
