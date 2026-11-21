module

public import CatalanCore.Elliptic.Analytic.BoundDefs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section

/-!
# `thm:analytic` (a): the row expansion `eq:tags` (row E14a)

For a column selection `sel`, the determinant of `Ã` expands as

`det Ã_sel = ∑_{g : rows → 𝒯_H} (∏_r s(β_r, g r, j_r)) · det B_g`,
`(B_g)_{r,c} = [z^{s_r}] G_{c, g r}(j_r Ω + z)`.

* `binom_shift`, `row_identity`: the binomial identity
  `C(α,β)(ζ+δ)^{α-β} = ∑_{β ≤ ξ ≤ α} C(ξ,β) δ^{ξ-β} · C(α,ξ) ζ^{α-ξ}` (one variable, then a product).
* `transportEntry_eq_tsum`: each entry of `Ã` is `∑_{ξ ∈ 𝒯_H} s(β,ξ,j) · [z^s] G_{c,ξ}(jΩ + z)`.
* `det_expansion`: multilinearity of the determinant in the rows.
-/

namespace CatalanCore.Elliptic.Analytic

noncomputable section

/-! ### Linearity of the Taylor coefficient -/

theorem taylorCoeff_sum {ι : Type*} (I : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ I, Differentiable ℂ (f i)) (s : ℕ) :
    taylorCoeff s (fun z => ∑ i ∈ I, f i z) = ∑ i ∈ I, taylorCoeff s (f i) := by
  have hd : Differentiable ℂ (fun z => ∑ i ∈ I, f i z) := Differentiable.fun_sum hf
  have h1 : iteratedDeriv s (fun z => ∑ i ∈ I, f i z) 0 = ∑ i ∈ I, iteratedDeriv s (f i) 0 :=
    iteratedDeriv_fun_sum (fun i hi => (hf i hi).contDiff.contDiffAt)
  rw [taylorCoeff_eq_iteratedDeriv hd, h1, Finset.sum_div]
  exact Finset.sum_congr rfl fun i hi => (taylorCoeff_eq_iteratedDeriv (hf i hi) s).symm

/-! ### The binomial identity -/

/-- `C(α,β) (ζ+δ)^{α-β} = ∑_{ξ ≤ α} C(ξ,β) δ^{ξ-β} · C(α,ξ) ζ^{α-ξ}` (zero when `β > α`). -/
theorem binom_shift (α β : ℕ) (ζ δ : ℂ) :
    ((α.choose β : ℕ) : ℂ) * (ζ + δ) ^ (α - β) =
      ∑ ξ ∈ Finset.range (α + 1), ((ξ.choose β : ℕ) : ℂ) * δ ^ (ξ - β) *
        (((α.choose ξ : ℕ) : ℂ) * ζ ^ (α - ξ)) := by
  by_cases hβ : β ≤ α
  · obtain ⟨n, rfl⟩ : ∃ n, α = β + n := ⟨α - β, by omega⟩
    set T : ℕ → ℂ := fun ξ => ((ξ.choose β : ℕ) : ℂ) * δ ^ (ξ - β) *
        ((((β + n).choose ξ : ℕ) : ℂ) * ζ ^ (β + n - ξ)) with hT
    have hr : β + n + 1 = β + (n + 1) := by omega
    rw [hr, Finset.sum_range_add]
    have h0 : ∑ x ∈ Finset.range β, T x = 0 := Finset.sum_eq_zero fun x hx => by
      have hx' : x < β := Finset.mem_range.mp hx
      simp [hT, Nat.choose_eq_zero_of_lt hx']
    have hsub : β + n - β = n := by omega
    rw [h0, zero_add, hsub, add_comm ζ δ, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have e1 : β + l - β = l := by omega
    have e2 : β + n - (β + l) = n - l := by omega
    have key : ((β + n).choose (β + l) : ℂ) * ((β + l).choose β : ℂ) =
        ((β + n).choose β : ℂ) * (n.choose l : ℂ) := by
      have h := Nat.choose_mul (n := β + n) (k := β + l) (s := β) (by omega)
      rw [hsub, e1] at h
      exact_mod_cast h
    simp only [hT, e1, e2]
    linear_combination (-(δ ^ l * ζ ^ (n - l))) * key
  · have hlt : α < β := not_le.mp hβ
    rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, zero_mul]
    symm
    refine Finset.sum_eq_zero fun ξ hξ => ?_
    have hξ' : ξ ≤ α := Nat.lt_succ_iff.mp (Finset.mem_range.mp hξ)
    simp [Nat.choose_eq_zero_of_lt (lt_of_le_of_lt hξ' hlt)]

/-- The product form of `binom_shift`, summed over any `T` containing the box `{ξ ≤ α}`. -/
theorem row_identity {m : ℕ} (α β : Fin m → ℕ) (ζ : ℂ) (δ : Fin m → ℂ) (g : ℂ)
    (T : Finset (Fin m → ℕ)) (hT : Fintype.piFinset (fun i => Finset.range (α i + 1)) ⊆ T) :
    g * (∏ i, (((α i).choose (β i) : ℕ) : ℂ)) * ∏ i, (ζ + δ i) ^ (α i - β i) =
      ∑ ξ ∈ T, ((∏ i, (((ξ i).choose (β i) : ℕ) : ℂ)) * ∏ i, δ i ^ (ξ i - β i)) *
        ((∏ i, (((α i).choose (ξ i) : ℕ) : ℂ)) * g * ζ ^ (∑ i, (α i - ξ i))) := by
  have h1 : (∏ i, (((α i).choose (β i) : ℕ) : ℂ)) * ∏ i, (ζ + δ i) ^ (α i - β i) =
      ∑ ξ ∈ Fintype.piFinset (fun i => Finset.range (α i + 1)),
        ∏ i, (((ξ i).choose (β i) : ℕ) : ℂ) * δ i ^ (ξ i - β i) *
          ((((α i).choose (ξ i) : ℕ) : ℂ) * ζ ^ (α i - ξ i)) := by
    rw [← Finset.prod_mul_distrib]
    rw [Finset.prod_congr rfl (fun i _ => binom_shift (α i) (β i) ζ (δ i))]
    exact Finset.prod_univ_sum (fun i => Finset.range (α i + 1))
      (fun i j => ((j.choose (β i) : ℕ) : ℂ) * δ i ^ (j - β i) *
        ((((α i).choose j : ℕ) : ℂ) * ζ ^ (α i - j)))
  have h2 : ∑ ξ ∈ Fintype.piFinset (fun i => Finset.range (α i + 1)),
        ∏ i, (((ξ i).choose (β i) : ℕ) : ℂ) * δ i ^ (ξ i - β i) *
          ((((α i).choose (ξ i) : ℕ) : ℂ) * ζ ^ (α i - ξ i)) =
      ∑ ξ ∈ T, ∏ i, (((ξ i).choose (β i) : ℕ) : ℂ) * δ i ^ (ξ i - β i) *
          ((((α i).choose (ξ i) : ℕ) : ℂ) * ζ ^ (α i - ξ i)) := by
    refine Finset.sum_subset hT fun ξ _ hξ => ?_
    have hξ' : ¬ ∀ i, ξ i < α i + 1 := fun h =>
      hξ (Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr (h i))
    obtain ⟨i, hi⟩ := not_forall.mp hξ'
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    have : α i < ξ i := by omega
    simp [Nat.choose_eq_zero_of_lt this]
  calc g * (∏ i, (((α i).choose (β i) : ℕ) : ℂ)) * ∏ i, (ζ + δ i) ^ (α i - β i)
      = g * ((∏ i, (((α i).choose (β i) : ℕ) : ℂ)) * ∏ i, (ζ + δ i) ^ (α i - β i)) := by ring
    _ = g * ∑ ξ ∈ T, ∏ i, (((ξ i).choose (β i) : ℕ) : ℂ) * δ i ^ (ξ i - β i) *
          ((((α i).choose (ξ i) : ℕ) : ℂ) * ζ ^ (α i - ξ i)) := by rw [h1, h2]
    _ = _ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ξ _ => ?_
      simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      ring

/-! ### Entries and determinant -/

section Expansion

variable {Λ : PeriodPair} {Ω : ℝ} {Ω' : ℂ} {a : ℤ}

/-- Each entry of `Ã` is a sum over `ξ ∈ 𝒯_H` of the displacement coefficient `s(β,ξ,j)` times a
Taylor coefficient of the entire function `G_{c,ξ}` (`eq:tags`, rows). -/
theorem transportEntry_eq_tsum (M : Multiplier Λ Ω Ω' a) {m K : ℕ} (W : Weights m) (D : ℕ)
    (cen : Fin K → Fin m → ℚ) (H : ℝ) (j : Fin K) (r : Fin (m + 1) → ℕ) {col : ColIdx m}
    (hcol : col ∈ W.colSet H) :
    transportEntry M D cen j r col =
      ∑ ξ ∈ W.tSet H, sCoef cen Ω j (fun i => r i.succ) ξ *
        taylorCoeff (r 0) (fun z => Gfun M D col ξ (((j : ℕ) : ℂ) * (Ω : ℂ) + z)) := by
  have hα : ((W.wt col.2.2 : ℚ) : ℝ) ≤ H := by
    have h := (W.mem_colSet_iff H col).mp hcol
    have hw0 : (0 : ℝ) < W.w₀ := by exact_mod_cast W.w₀_pos
    have h0 : 0 ≤ 2 * (W.w₀ : ℝ) * ((col.1 : ℝ) + 2 * (col.2.1.val : ℝ)) :=
      mul_nonneg (by positivity) (by positivity)
    linarith
  have hfun : (fun z : ℂ => gTilde M D col.1 col.2.1.val (((j : ℕ) : ℂ) * (Ω : ℂ) + z) *
        (∏ i : Fin m, (((col.2.2 i).choose (r i.succ) : ℕ) : ℂ)) *
        ∏ i : Fin m, (((j : ℕ) : ℂ) * (Ω : ℂ) + z +
          (((cen j i : ℚ) : ℂ) - ((j : ℕ) : ℂ) * (Ω : ℂ))) ^ (col.2.2 i - r i.succ)) =
      fun z => ∑ ξ ∈ W.tSet H, sCoef cen Ω j (fun i => r i.succ) ξ *
        Gfun M D col ξ (((j : ℕ) : ℂ) * (Ω : ℂ) + z) := by
    funext z
    exact row_identity col.2.2 (fun i => r i.succ) (((j : ℕ) : ℂ) * (Ω : ℂ) + z)
      (fun i => ((cen j i : ℚ) : ℂ) - ((j : ℕ) : ℂ) * (Ω : ℂ))
      (gTilde M D col.1 col.2.1.val (((j : ℕ) : ℂ) * (Ω : ℂ) + z)) (W.tSet H)
      (W.box_subset_tSet hα)
  have hd : ∀ ξ ∈ W.tSet H, Differentiable ℂ (fun z : ℂ =>
      sCoef cen Ω j (fun i => r i.succ) ξ * Gfun M D col ξ (((j : ℕ) : ℂ) * (Ω : ℂ) + z)) :=
    fun ξ _ => (differentiable_const _).mul
      ((Gfun_differentiable M D col ξ).comp ((differentiable_const _).add differentiable_id))
  have h3 : transportEntry M D cen j r col = taylorCoeff (r 0) (fun z : ℂ =>
      ∑ ξ ∈ W.tSet H, sCoef cen Ω j (fun i => r i.succ) ξ *
        Gfun M D col ξ (((j : ℕ) : ℂ) * (Ω : ℂ) + z)) := congrArg (taylorCoeff (r 0)) hfun
  rw [h3]
  refine (taylorCoeff_sum (W.tSet H) (fun ξ z => sCoef cen Ω j (fun i => r i.succ) ξ *
    Gfun M D col ξ (((j : ℕ) : ℂ) * (Ω : ℂ) + z)) hd (r 0)).trans ?_
  exact Finset.sum_congr rfl fun ξ _ => taylorCoeff_const_mul _ _ _

/-- **E14a, `eq:tags`.** The determinant of `Ã_sel` is the sum over all maps `g` from the rows to
`𝒯_H` of `(∏_r s(β_r, g r, j_r)) · det B_g`, `(B_g)_{r,c} = [z^{s_r}] G_{c, g r}(j_r Ω + z)`. -/
theorem det_expansion (M : Multiplier Λ Ω Ω' a) {m K : ℕ} (W : Weights m) (D : ℕ)
    (cen : Fin K → Fin m → ℚ) (H : ℝ) (sel : Row W K H → Col W H) :
    ((transportMatrix W M D cen H).submatrix id sel).det =
      ∑ g : Row W K H → ↥(W.tSet H),
        (∏ ρ : Row W K H, sCoef cen Ω ρ.1 (fun i => ρ.2.1 i.succ) (g ρ).1) *
          Matrix.det (fun (ρ : Row W K H) (c : Row W K H) =>
            taylorCoeff (ρ.2.1 0) (fun z =>
              Gfun M D (sel c).1 (g ρ).1 (((ρ.1 : ℕ) : ℂ) * (Ω : ℂ) + z))) := by
  let f : MultilinearMap ℂ (fun _ : Row W K H => Row W K H → ℂ) ℂ :=
    (Matrix.detRowAlternating : AlternatingMap ℂ (Row W K H → ℂ) ℂ (Row W K H)).toMultilinearMap
  have hrow : ∀ ρ c : Row W K H, transportEntry M D cen ρ.1 ρ.2.1 (sel c).1 =
      ∑ ξ : ↥(W.tSet H), sCoef cen Ω ρ.1 (fun i => ρ.2.1 i.succ) ξ.1 *
        taylorCoeff (ρ.2.1 0) (fun z => Gfun M D (sel c).1 ξ.1 (((ρ.1 : ℕ) : ℂ) * (Ω : ℂ) + z)) := by
    intro ρ c
    rw [transportEntry_eq_tsum M W D cen H ρ.1 ρ.2.1 (sel c).2]
    exact (Finset.sum_coe_sort (W.tSet H) (fun ξ => sCoef cen Ω ρ.1 (fun i => ρ.2.1 i.succ) ξ *
      taylorCoeff (ρ.2.1 0) (fun z => Gfun M D (sel c).1 ξ (((ρ.1 : ℕ) : ℂ) * (Ω : ℂ) + z)))).symm
  have hmat : (transportMatrix W M D cen H).submatrix id sel =
      fun ρ => ∑ ξ : ↥(W.tSet H), sCoef cen Ω ρ.1 (fun i => ρ.2.1 i.succ) ξ.1 •
        (fun c : Row W K H => taylorCoeff (ρ.2.1 0) (fun z =>
          Gfun M D (sel c).1 ξ.1 (((ρ.1 : ℕ) : ℂ) * (Ω : ℂ) + z))) := by
    ext ρ c
    simp only [Matrix.submatrix_apply, id_eq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hrow ρ c
  have h1 : ((transportMatrix W M D cen H).submatrix id sel).det =
      f (fun ρ => ∑ ξ : ↥(W.tSet H), sCoef cen Ω ρ.1 (fun i => ρ.2.1 i.succ) ξ.1 •
        (fun c : Row W K H => taylorCoeff (ρ.2.1 0) (fun z =>
          Gfun M D (sel c).1 ξ.1 (((ρ.1 : ℕ) : ℂ) * (Ω : ℂ) + z)))) :=
    (congrArg (fun A : Matrix (Row W K H) (Row W K H) ℂ => A.det) hmat).trans rfl
  rw [h1, f.map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [f.map_smul_univ, smul_eq_mul]
  rfl

end Expansion

end

end CatalanCore.Elliptic.Analytic
