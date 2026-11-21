module

public import CatalanCore.Elliptic.Analytic.BoundDefs
public import CatalanCore.Elliptic.Analytic.Growth
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

/-!
# `thm:analytic` (c): the disc bound with `𝒢` and `C_Λ` (row E14c)

With `R = r_* K`, `r_* = 2(Ω+1)`, on `|ζ| ≤ R` every `G_{c,ξ}` is at most `exp(H 𝒢)`,

`𝒢 = (D/H)(log S_* + χ (r_* + Y)² K²) + log(2R)/w_min`.

Proof (paper): `|Im ζ| ≤ R` and `R + Y ≤ (r_* + Y) K` in the growth bound `lem:growth`
(`Multiplier.growthBound`), `C(α,ξ) ≤ 2^{|α|}`, `|ζ|^{|α|-|ξ|} ≤ R^{|α|}` (`R ≥ 1`) and
`|α| ≤ H/w_min` by the column condition (S).
-/

namespace CatalanCore.Elliptic.Analytic

noncomputable section

section Disc

variable {Λ : PeriodPair} {Ω : ℝ} {Ω' : ℂ} {a : ℤ}

/-- `𝒢 = (D/H)(log S_* + χ(r_*+Y)² K²) + log(2 r_* K)/w_min`. -/
def discG (M : Multiplier Λ Ω Ω' a) (H : ℝ) (D K : ℕ) (wmin : ℝ) : ℝ :=
  (D : ℝ) / H * (Real.log M.Sstar + M.chi * (M.rStar + Ω'.im) ^ 2 * (K : ℝ) ^ 2) +
    Real.log (2 * (M.rStar * (K : ℝ))) / wmin

theorem exp_discG (M : Multiplier Λ Ω Ω' a) {H : ℝ} (hH : H ≠ 0) (D K : ℕ) {wmin : ℝ} :
    Real.exp (H * discG M H D K wmin) =
      Real.exp (H * (Real.log (2 * (M.rStar * (K : ℝ))) / wmin)) *
        (Real.exp ((D : ℝ) * Real.log M.Sstar) *
          Real.exp ((D : ℝ) * M.chi * ((M.rStar + Ω'.im) * (K : ℝ)) ^ 2)) := by
  unfold discG
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  have e : H * ((D : ℝ) / H * (Real.log M.Sstar + M.chi * (M.rStar + Ω'.im) ^ 2 * (K : ℝ) ^ 2)) =
      (D : ℝ) * (Real.log M.Sstar + M.chi * (M.rStar + Ω'.im) ^ 2 * (K : ℝ) ^ 2) := by
    field_simp
  rw [mul_add, e]
  ring

theorem norm_Gfun_le (M : Multiplier Λ Ω Ω' a) (hgrow : M.GrowthBound) (hΩ : 0 < Ω)
    (hY : 0 < Ω'.im) {m K : ℕ} (hK : 1 ≤ K) (W : Weights m) {H : ℝ} (hH : 0 < H) (D : ℕ)
    {wmin : ℝ} (hwmin : 0 < wmin) (hwle : ∀ i, wmin ≤ (W.w i : ℝ))
    {col : ColIdx m} (hcol : col ∈ W.colSet H) (hD : col.1 + 2 * col.2.1.val ≤ D)
    (ξ : Fin m → ℕ) {ζ : ℂ} (hζ : ‖ζ‖ ≤ M.rStar * (K : ℝ)) :
    ‖Gfun M D col ξ ζ‖ ≤ Real.exp (H * discG M H D K wmin) := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hrs : M.rStar = 2 * (Ω + 1) := rfl
  have hr2 : 2 ≤ M.rStar := by rw [hrs]; linarith
  have hR1 : 1 ≤ M.rStar * (K : ℝ) := by nlinarith
  have hR0 : 0 < M.rStar * (K : ℝ) := by linarith
  have h2R : 0 < 2 * (M.rStar * (K : ℝ)) := by linarith
  have hχ : 0 ≤ M.chi := by
    unfold Multiplier.chi
    positivity
  have hS1 : 1 ≤ M.Sstar := Multiplier.one_le_Sstar M
  have hSpos : 0 < M.Sstar := by linarith
  -- the column condition
  have hα : ((W.wt col.2.2 : ℚ) : ℝ) ≤ H := by
    have h := (W.mem_colSet_iff H col).mp hcol
    have hw0 : (0 : ℝ) < W.w₀ := by exact_mod_cast W.w₀_pos
    have h0 : 0 ≤ 2 * (W.w₀ : ℝ) * ((col.1 : ℝ) + 2 * (col.2.1.val : ℝ)) :=
      mul_nonneg (by positivity) (by positivity)
    linarith
  obtain ⟨A, hA⟩ : ∃ A : ℕ, A = ∑ i, col.2.2 i := ⟨_, rfl⟩
  have hAle : (A : ℝ) ≤ H / wmin := by
    have h1 := W.sum_le_wt_div hwmin hwle col.2.2
    have h2 : ((W.wt col.2.2 : ℚ) : ℝ) / wmin ≤ H / wmin :=
      div_le_div_of_nonneg_right hα hwmin.le
    have h3 : (A : ℝ) = ∑ i, (col.2.2 i : ℝ) := by rw [hA, Nat.cast_sum]
    rw [h3]
    linarith
  -- the norm of `G`
  have hnorm : ‖Gfun M D col ξ ζ‖ = (∏ i, (((col.2.2 i).choose (ξ i) : ℕ) : ℝ)) *
      ‖gTilde M D col.1 col.2.1.val ζ‖ * ‖ζ‖ ^ (∑ i, (col.2.2 i - ξ i)) := by
    unfold Gfun
    rw [norm_mul, norm_mul, norm_prod, norm_pow]
    simp only [Complex.norm_natCast]
  have hC : ∏ i, (((col.2.2 i).choose (ξ i) : ℕ) : ℝ) ≤ 2 ^ A := by
    calc ∏ i, (((col.2.2 i).choose (ξ i) : ℕ) : ℝ) ≤ ∏ i, (2 : ℝ) ^ (col.2.2 i) :=
          Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i _ => by
            exact_mod_cast Nat.choose_le_two_pow (col.2.2 i) (ξ i)
      _ = 2 ^ A := by rw [hA]; exact Finset.prod_pow_eq_pow_sum _ _ _
  have hYK : (|ζ.im| + Ω'.im) ≤ (M.rStar + Ω'.im) * (K : ℝ) := by
    have h1 : |ζ.im| ≤ ‖ζ‖ := Complex.abs_im_le_norm ζ
    nlinarith
  have hg : ‖gTilde M D col.1 col.2.1.val ζ‖ ≤
      M.Sstar ^ D * Real.exp ((D : ℝ) * M.chi * ((M.rStar + Ω'.im) * (K : ℝ)) ^ 2) := by
    have h1 : ‖gTilde M D col.1 col.2.1.val ζ‖ ≤
        M.Sstar ^ D * Real.exp ((D : ℝ) * M.chi * (|ζ.im| + Ω'.im) ^ 2) := hgrow D _ _ hD ζ
    refine h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
    have h2 : (|ζ.im| + Ω'.im) ^ 2 ≤ ((M.rStar + Ω'.im) * (K : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hYK 2
    have h3 : 0 ≤ (D : ℝ) * M.chi := mul_nonneg (Nat.cast_nonneg _) hχ
    exact mul_le_mul_of_nonneg_left h2 h3
  have hz : ‖ζ‖ ^ (∑ i, (col.2.2 i - ξ i)) ≤ (M.rStar * (K : ℝ)) ^ A := by
    have he : (∑ i, (col.2.2 i - ξ i)) ≤ A := by
      rw [hA]; exact Finset.sum_le_sum fun i _ => Nat.sub_le _ _
    exact (pow_le_pow_left₀ (norm_nonneg ζ) hζ _).trans (pow_le_pow_right₀ hR1 he)
  have hE0 : 0 ≤ M.Sstar ^ D * Real.exp ((D : ℝ) * M.chi * ((M.rStar + Ω'.im) * (K : ℝ)) ^ 2) :=
    by positivity
  -- combine
  have hmain : ‖Gfun M D col ξ ζ‖ ≤ (2 * (M.rStar * (K : ℝ))) ^ A *
      (M.Sstar ^ D * Real.exp ((D : ℝ) * M.chi * ((M.rStar + Ω'.im) * (K : ℝ)) ^ 2)) := by
    rw [hnorm]
    calc _ ≤ (2 ^ A * (M.Sstar ^ D *
          Real.exp ((D : ℝ) * M.chi * ((M.rStar + Ω'.im) * (K : ℝ)) ^ 2))) *
          (M.rStar * (K : ℝ)) ^ A :=
          mul_le_mul (mul_le_mul hC hg (norm_nonneg _) (by positivity)) hz (by positivity)
            (by positivity)
      _ = _ := by ring
  have h2A : (2 * (M.rStar * (K : ℝ))) ^ A ≤
      Real.exp (H * (Real.log (2 * (M.rStar * (K : ℝ))) / wmin)) := by
    have hl : 0 ≤ Real.log (2 * (M.rStar * (K : ℝ))) :=
      Real.log_nonneg (by linarith)
    have hexp : (2 * (M.rStar * (K : ℝ))) ^ A =
        Real.exp ((A : ℝ) * Real.log (2 * (M.rStar * (K : ℝ)))) := by
      rw [Real.exp_nat_mul, Real.exp_log h2R]
    rw [hexp]
    apply Real.exp_le_exp.mpr
    have h4 : (A : ℝ) * Real.log (2 * (M.rStar * (K : ℝ))) ≤
        H / wmin * Real.log (2 * (M.rStar * (K : ℝ))) := mul_le_mul_of_nonneg_right hAle hl
    have e : H * (Real.log (2 * (M.rStar * (K : ℝ))) / wmin) =
        H / wmin * Real.log (2 * (M.rStar * (K : ℝ))) := by ring
    rw [e]
    exact h4
  have hS : M.Sstar ^ D = Real.exp ((D : ℝ) * Real.log M.Sstar) := by
    rw [Real.exp_nat_mul, Real.exp_log hSpos]
  rw [exp_discG M hH.ne' D K]
  refine hmain.trans ?_
  rw [hS]
  exact mul_le_mul_of_nonneg_right h2A (by positivity)

end Disc

end

end CatalanCore.Elliptic.Analytic
