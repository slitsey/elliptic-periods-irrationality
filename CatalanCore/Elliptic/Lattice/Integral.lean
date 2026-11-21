module

public import CatalanCore.Elliptic.Lattice.Scale
public import CatalanCore.Elliptic.Lattice.Discriminant

/-!
# The integral model (row E03, `lem:integral`)

For a lattice `L : PeriodPair` with rational `g₂, g₃` there are `d ≥ 1`, a lattice `Λ = d⁻¹ L`
(a `PeriodPair`, `z ∈ Λ ↔ d z ∈ L`) and integers `A, B` with `g₂(Λ) = -4A`, `g₃(Λ) = -4B`,
`4A³ + 27B² ≠ 0`, and the curve relation `y² = x³ + A x + B` for `x = ℘_Λ`, `y = ℘'_Λ / 2` off
the lattice. Also `dx = 2y dz`, that is `dx/(2y) = dz`.
-/

@[expose] public section

noncomputable section

namespace CatalanCore.Elliptic.Lattice

open PeriodPair

/-- `(℘'/2)² = ℘³ - (g₂/4) ℘ - g₃/4` off the lattice, for any `L`. -/
lemma curve_relation (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    (L.derivWeierstrassP z / 2) ^ 2 =
      L.weierstrassP z ^ 3 - L.g₂ / 4 * L.weierstrassP z - L.g₃ / 4 := by
  have h := L.derivWeierstrassP_sq z hz
  linear_combination (1 / 4 : ℂ) * h

/-- `d℘ = ℘' dz`: `℘` has derivative `2 y = ℘'` off the lattice (`dx/(2y) = dz`). -/
lemma hasDerivAt_weierstrassP (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt L.weierstrassP (2 * (L.derivWeierstrassP z / 2)) z := by
  have hd : DifferentiableAt ℂ L.weierstrassP z :=
    L.differentiableOn_weierstrassP.differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hz)
  have h := hd.hasDerivAt
  rw [show deriv L.weierstrassP z = L.derivWeierstrassP z from
    congrFun L.deriv_weierstrassP z] at h
  convert h using 1
  ring

/-- **E03 (`lem:integral`).** Integral model of a lattice with rational `g₂, g₃`. -/
theorem exists_integral_model (L : PeriodPair)
    (hg₂ : ∃ r : ℚ, L.g₂ = r) (hg₃ : ∃ r : ℚ, L.g₃ = r) :
    ∃ (d : ℕ) (A B : ℤ) (Λ : PeriodPair), 1 ≤ d ∧
      (∀ z : ℂ, z ∈ Λ.lattice ↔ (d : ℂ) * z ∈ L.lattice) ∧
      Λ.g₂ = -4 * (A : ℂ) ∧ Λ.g₃ = -4 * (B : ℂ) ∧ 4 * A ^ 3 + 27 * B ^ 2 ≠ 0 ∧
      (∀ z : ℂ, z ∉ Λ.lattice →
        (Λ.derivWeierstrassP z / 2) ^ 2 = Λ.weierstrassP z ^ 3 + A * Λ.weierstrassP z + B) ∧
      (∀ z : ℂ, z ∉ Λ.lattice →
        HasDerivAt Λ.weierstrassP (2 * (Λ.derivWeierstrassP z / 2)) z) := by
  obtain ⟨r₂, hr₂⟩ := hg₂
  obtain ⟨r₃, hr₃⟩ := hg₃
  have hq₂ : (r₂.den : ℂ) ≠ 0 := by exact_mod_cast r₂.den_nz
  have hq₃ : (r₃.den : ℂ) ≠ 0 := by exact_mod_cast r₃.den_nz
  set d : ℕ := 2 * (r₂.den * r₃.den) with hd
  have hdpos : 1 ≤ d := by
    have := Nat.mul_pos r₂.den_pos r₃.den_pos
    omega
  have hdC : (d : ℂ) ≠ 0 := by
    rw [hd]
    push_cast
    exact mul_ne_zero two_ne_zero (mul_ne_zero hq₂ hq₃)
  set c : ℂˣ := Units.mk0 ((d : ℂ)⁻¹) (inv_ne_zero hdC) with hc
  have hcv : (c : ℂ) = (d : ℂ)⁻¹ := rfl
  set Λ : PeriodPair := scale c L with hΛ
  set A : ℤ := -(4 * r₂.num * (r₂.den : ℤ) ^ 3 * (r₃.den : ℤ) ^ 4) with hA
  set B : ℤ := -(16 * r₃.num * (r₂.den : ℤ) ^ 6 * (r₃.den : ℤ) ^ 5) with hB
  have e₂ : L.g₂ = (r₂.num : ℂ) / (r₂.den : ℂ) := by rw [hr₂, Rat.cast_def]
  have e₃ : L.g₃ = (r₃.num : ℂ) / (r₃.den : ℂ) := by rw [hr₃, Rat.cast_def]
  have hg2 : Λ.g₂ = -4 * (A : ℂ) := by
    rw [hΛ, g₂_scale, e₂, hcv, hA, hd]
    push_cast
    field_simp
    ring
  have hg3 : Λ.g₃ = -4 * (B : ℂ) := by
    rw [hΛ, g₃_scale, e₃, hcv, hB, hd]
    push_cast
    field_simp
    ring
  have hlat : ∀ z : ℂ, z ∈ Λ.lattice ↔ (d : ℂ) * z ∈ L.lattice := by
    intro z
    rw [hΛ, mem_lattice_scale_iff]
    have : ((c⁻¹ : ℂˣ) : ℂ) = (d : ℂ) := by
      rw [Units.val_inv_eq_inv_val, hcv, inv_inv]
    rw [this]
  have hne : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0 := by
    intro h
    apply disc_ne_zero Λ
    have h' : ((4 * A ^ 3 + 27 * B ^ 2 : ℤ) : ℂ) = 0 := by exact_mod_cast h
    push_cast at h'
    rw [hg2, hg3]
    linear_combination (-16 : ℂ) * h'
  refine ⟨d, A, B, Λ, hdpos, hlat, hg2, hg3, hne, ?_, fun z hz ↦ hasDerivAt_weierstrassP Λ hz⟩
  intro z hz
  have h := curve_relation Λ hz
  rw [hg2, hg3] at h
  rw [h]
  ring

end CatalanCore.Elliptic.Lattice
