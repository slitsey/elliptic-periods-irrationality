module

public import CatalanCore.Elliptic.Analytic.Transport

@[expose] public section

/-!
# `thm:analytic`: definitions shared by the four parts (rows E14a-d)

Paper: `work/paper-elliptic/elliptic-periods.tex`, §"The analytic upper bound".

* `Gfun M D col ξ ζ = C(α_c, ξ) · g̃_{D,k_c,b_c}(ζ) · ζ^{|α_c| - |ξ|}` (the entire functions `G_{c,ξ}`;
  the exponent is `∑ i, (α_i - ξ_i)`, equal to `|α| - |ξ|` when `ξ ≤ α`, and `C(α, ξ) = 0` otherwise).
* `sCoef cen Ω j β ξ = s(β, ξ, j) = C(ξ, β) ∏_i δ_{ji}^{ξ_i - β_i}`, `δ_{ji} = c_{ji} - jΩ`.
* membership in `𝒯_H` (`mem_tSet_iff`), the box inside `𝒯_H` (`box_subset_tSet`).
* `collisionRemainder_eq_rhoH`: the OAI remainder of C3 is the `ρ_H` of `Interfaces`.
-/

namespace CatalanCore.Elliptic.Analytic

open OAI.PiExponent

noncomputable section

section Defs

variable {Λ : PeriodPair} {Ω : ℝ} {Ω' : ℂ} {a : ℤ}

/-- `G_{c,ξ}(ζ) = C(α_c, ξ) · g̃_{D,k_c,b_c}(ζ) · ζ^{|α_c| - |ξ|}` (`thm:analytic`, expansion in the
displacements). -/
def Gfun (M : Multiplier Λ Ω Ω' a) (D : ℕ) {m : ℕ} (col : ColIdx m) (ξ : Fin m → ℕ) (ζ : ℂ) : ℂ :=
  (∏ i : Fin m, (((col.2.2 i).choose (ξ i) : ℕ) : ℂ)) * gTilde M D col.1 col.2.1.val ζ *
    ζ ^ (∑ i : Fin m, (col.2.2 i - ξ i))

/-- `s(β, ξ, j) = C(ξ, β) ∏_i δ_{ji}^{ξ_i - β_i}` with `δ_{ji} = c_{ji} - jΩ`. -/
def sCoef {m K : ℕ} (cen : Fin K → Fin m → ℚ) (Ω : ℝ) (j : Fin K) (β ξ : Fin m → ℕ) : ℂ :=
  (∏ i : Fin m, (((ξ i).choose (β i) : ℕ) : ℂ)) *
    ∏ i : Fin m, (((cen j i : ℚ) : ℂ) - ((j : ℕ) : ℂ) * (Ω : ℂ)) ^ (ξ i - β i)

theorem gTilde_differentiable (M : Multiplier Λ Ω Ω' a) (D k b : ℕ) :
    Differentiable ℂ (gTilde M D k b) := by
  show Differentiable ℂ (fun z => M.F₀ z ^ (D - k - 2 * b) * M.F₁ z ^ k * M.F₂ z ^ b)
  exact ((M.diff₀.pow _).mul (M.diff₁.pow _)).mul (M.diff₂.pow _)

theorem Gfun_differentiable (M : Multiplier Λ Ω Ω' a) (D : ℕ) {m : ℕ} (col : ColIdx m)
    (ξ : Fin m → ℕ) : Differentiable ℂ (Gfun M D col ξ) := by
  show Differentiable ℂ (fun ζ => (∏ i : Fin m, (((col.2.2 i).choose (ξ i) : ℕ) : ℂ)) *
    gTilde M D col.1 col.2.1.val ζ * ζ ^ (∑ i : Fin m, (col.2.2 i - ξ i)))
  exact ((differentiable_const (∏ i : Fin m, (((col.2.2 i).choose (ξ i) : ℕ) : ℂ))).mul
    (gTilde_differentiable M D col.1 col.2.1.val)).mul (differentiable_id.pow _)

end Defs

end

end CatalanCore.Elliptic.Analytic

namespace CatalanCore.Elliptic

open OAI.PiExponent

noncomputable section

/-! ### The sets `𝒯_H` -/

namespace Weights

variable {m : ℕ} (W : Weights m)

theorem wt_mono {ξ α : Fin m → ℕ} (h : ∀ i, ξ i ≤ α i) :
    ((W.wt ξ : ℚ) : ℝ) ≤ ((W.wt α : ℚ) : ℝ) := by
  rw [W.wt_cast, W.wt_cast]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (by exact_mod_cast h i) (by exact_mod_cast (W.w_pos i).le)

/-- `ξ ∈ 𝒯_X ↔ W(ξ) ≤ X`. -/
theorem mem_tSet_iff (X : ℝ) (ξ : Fin m → ℕ) : ξ ∈ W.tSet X ↔ ((W.wt ξ : ℚ) : ℝ) ≤ X := by
  simp only [tSet, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i => ?_, h⟩
    have hwi : (0 : ℝ) < W.w i := by exact_mod_cast W.w_pos i
    have h1 : (W.w i : ℝ) * (ξ i : ℝ) ≤ ((W.wt ξ : ℚ) : ℝ) := by
      rw [W.wt_cast]
      exact Finset.single_le_sum (f := fun j => (W.w j : ℝ) * (ξ j : ℝ))
        (fun j _ => mul_nonneg (by exact_mod_cast (W.w_pos j).le) (Nat.cast_nonneg _))
        (Finset.mem_univ i)
    have h2 : (ξ i : ℝ) ≤ X / (W.w i : ℝ) := by
      rw [le_div_iff₀ hwi]
      linarith [mul_comm (W.w i : ℝ) (ξ i : ℝ)]
    exact Nat.lt_succ_of_le (Nat.le_floor h2)

theorem zero_mem_tSet {X : ℝ} (hX : 0 ≤ X) : (0 : Fin m → ℕ) ∈ W.tSet X := by
  rw [mem_tSet_iff]
  have : ((W.wt (0 : Fin m → ℕ) : ℚ) : ℝ) = 0 := by
    rw [W.wt_cast]
    simp
  rw [this]
  exact hX

/-- The box `{ξ ≤ α}` lies in `𝒯_H` as soon as `W(α) ≤ H`. -/
theorem box_subset_tSet {H : ℝ} {α : Fin m → ℕ} (hα : ((W.wt α : ℚ) : ℝ) ≤ H) :
    Fintype.piFinset (fun i => Finset.range (α i + 1)) ⊆ W.tSet H := by
  intro ξ hξ
  rw [mem_tSet_iff]
  refine le_trans (W.wt_mono fun i => ?_) hα
  have := (Fintype.mem_piFinset.mp hξ) i
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp this)

/-- `wmin · ∑ ξ_i ≤ W(ξ)`, i.e. `|ξ| ≤ W(ξ)/wmin`. -/
theorem sum_le_wt_div {wmin : ℝ} (hwmin : 0 < wmin) (hwle : ∀ i, wmin ≤ (W.w i : ℝ))
    (ξ : Fin m → ℕ) : ∑ i, (ξ i : ℝ) ≤ ((W.wt ξ : ℚ) : ℝ) / wmin := by
  rw [le_div_iff₀ hwmin, W.wt_cast, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => by
    have := hwle i
    have h0 : (0 : ℝ) ≤ (ξ i : ℝ) := Nat.cast_nonneg _
    nlinarith

end Weights

/-! ### The OAI remainder is `ρ_H` -/

theorem collisionS0_eq : collisionS0 = (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  unfold collisionS0
  rw [Real.sqrt_eq_rpow, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]

theorem collisionRemainder_eq_rhoH (n : ℕ) (H : ℝ) :
    Collision.collisionRemainder n H = rhoH (n : ℝ) H := by
  rw [collisionRemainder_eq]
  unfold rhoH collisionKappa
  rw [collisionS0_eq]

end

end CatalanCore.Elliptic
