module

public import CatalanCore.Elliptic.Analytic.BoundExpansion
public import CatalanCore.Elliptic.Analytic.BoundDisp
public import CatalanCore.Elliptic.Analytic.BoundDisc

@[expose] public section

/-!
# `thm:analytic` (d): the two-case assembly (row E14d)

Paper: `paper/elliptic-periods.tex`, `thm:analytic`. For `Δ ≠ 0`,

`log|Δ| / (M H) ≤ E_an + e_H + max {-c_H, -ν (a₀ (1-γ) - b̄)}`,
`E_an = C_Λ K²/(2 w₀) + (ν + log(4 r_* K²))/w_min`, `e_H = C_Λ K²/H + ρ_H + log|𝒯_H|/H`.

* `term_bound`: every term of `eq:tags` (a map `g` from the rows to `𝒯_H`) is at most
  `exp (M H (E₀ + 𝒢 + ρ_H + max {…}))`. Two cases on the number of rows with `W(g r) > a₀ H`:
  at least `(1-γ) M` of them (then `∑ W(g r) ≥ a₀(1-γ) M H` and the lemma without its first term is
  used), or fewer (then more than `γ M` rows have `g r` in the set `{W ≤ a₀ H}` of size `≤ N_H`, and
  the occupancy form of the collision lemma gives the factor `exp(-c_H M H)`).
* `det_bound`: sum over the `|𝒯_H|^M` maps `g`.
* `analytic_upper_bound`: with `lem:transport` (`|det Ã| = |Δ| |ψ(0)|^{D J_H K}`, `D = ⌈H/(2w₀)⌉`)
  and `D/H ≤ 1/(2 w₀) + 1/H`; the output type `AnalyticUpperBound` of `Interfaces`.
* `analytic_upper_bound_grid`: the centres `c_{ji} = j p_i/q_i` of the paper with
  `|Ω - p_i/q_i| ≤ q_i^{-ν}`, and `IntegralModel.analytic_upper_bound`.
-/

namespace CatalanCore.Elliptic.Analytic

noncomputable section

section Main

variable {Λ : PeriodPair} {Ω : ℝ} {Ω' : ℂ} {a : ℤ}

/-- `W(β_r)` of the transverse index of a row. -/
def rowWt {m K : ℕ} (W : Weights m) {H : ℝ} (ρ : Row W K H) : ℝ :=
  ((W.wt (fun i => ρ.2.1 i.succ) : ℚ) : ℝ)

/-- `B_g` of `eq:tags`: `(B_g)_{r,c} = [z^{s_r}] G_{c, g r}(j_r Ω + z)`. -/
def Bmat (M : Multiplier Λ Ω Ω' a) (D : ℕ) {m K : ℕ} (W : Weights m) (H : ℝ)
    (sel : Row W K H → Col W H) (g : Row W K H → ↥(W.tSet H)) :
    Matrix (Row W K H) (Row W K H) ℂ :=
  fun ρ c => taylorCoeff (ρ.2.1 0) (fun z =>
    Gfun M D (sel c).1 (g ρ).1 (((ρ.1 : ℕ) : ℂ) * (Ω : ℂ) + z))

/-- The exponent `E₀ + 𝒢 + ρ_H + max {-c_H, -ν (a₀(1-γ) - b̄)}` with `E₀ = (log 2 + C_δ)/w_min`. -/
def Qbound (M : Multiplier Λ Ω Ω' a) {m : ℕ} (W : Weights m) (K D : ℕ) (H ν a₀ γ wmin : ℝ) : ℝ :=
  (Real.log 2 + (ν + Real.log K)) / wmin + discG M H D K wmin + rhoH (W.M K H : ℝ) H +
    max (-(cH W K a₀ γ H)) (-(ν * (a₀ * (1 - γ) - W.bbar K H)))

/-- The product of displacement coefficients: `exp (-ν (∑ W(g r) - ∑ W(β_r)) + M H E₀)`. -/
theorem norm_prod_sCoef_le {m K : ℕ} (W : Weights m) (cen : Fin K → Fin m → ℚ) (Ω : ℝ) {H : ℝ}
    {ν : ℝ} (hν : 0 ≤ ν) (hK : 1 ≤ K)
    (hδ : ∀ (j : Fin K) (i : Fin m), ‖((cen j i : ℚ) : ℂ) - ((j : ℕ) : ℂ) * (Ω : ℂ)‖ ≤
      Real.exp ((ν + Real.log K) - ν * (W.w i : ℝ)))
    {wmin : ℝ} (hwmin : 0 < wmin) (hwle : ∀ i, wmin ≤ (W.w i : ℝ))
    (g : Row W K H → ↥(W.tSet H)) (hle : ∀ (ρ : Row W K H) i, ρ.2.1 i.succ ≤ (g ρ).1 i) :
    ‖∏ ρ : Row W K H, sCoef cen Ω ρ.1 (fun i => ρ.2.1 i.succ) (g ρ).1‖ ≤
      Real.exp (-ν * (∑ ρ : Row W K H, ((W.wt (g ρ).1 : ℚ) : ℝ) - ∑ ρ : Row W K H, rowWt W ρ) +
        (W.M K H : ℝ) * (H * (Real.log 2 + (ν + Real.log K)) / wmin)) := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hCδ : 0 ≤ ν + Real.log K := add_nonneg hν (Real.log_nonneg hKr)
  have hcard : Fintype.card (Row W K H) = W.M K H := W.card_row K H
  have hrowb : ∀ ρ : Row W K H, ‖sCoef cen Ω ρ.1 (fun i => ρ.2.1 i.succ) (g ρ).1‖ ≤
      Real.exp (-ν * (((W.wt (g ρ).1 : ℚ) : ℝ) - rowWt W ρ) +
        H * (Real.log 2 + (ν + Real.log K)) / wmin) := by
    intro ρ
    have hξ : ∑ i, (((g ρ).1 i : ℕ) : ℝ) ≤ H / wmin :=
      (W.sum_le_wt_div hwmin hwle (g ρ).1).trans
        (div_le_div_of_nonneg_right ((W.mem_tSet_iff H _).mp (g ρ).2) hwmin.le)
    have h := norm_sCoef_le cen Ω ρ.1 (hle ρ) (ν := ν) (Cδ := ν + Real.log K) (H := H)
      (wmin := wmin) hCδ (fun i => (W.w i : ℝ)) (fun i => hδ ρ.1 i) hwmin hξ
    have e1 := W.wt_cast (g ρ).1
    have e2 := W.wt_cast (fun i => ρ.2.1 i.succ)
    unfold rowWt
    rw [e1, e2]
    exact h
  rw [norm_prod]
  calc ∏ ρ : Row W K H, ‖sCoef cen Ω ρ.1 (fun i => ρ.2.1 i.succ) (g ρ).1‖
      ≤ ∏ ρ : Row W K H, Real.exp (-ν * (((W.wt (g ρ).1 : ℚ) : ℝ) - rowWt W ρ) +
          H * (Real.log 2 + (ν + Real.log K)) / wmin) :=
        Finset.prod_le_prod₀ (fun ρ _ => norm_nonneg _) fun ρ _ => hrowb ρ
    _ = Real.exp (∑ ρ : Row W K H, (-ν * (((W.wt (g ρ).1 : ℚ) : ℝ) - rowWt W ρ) +
          H * (Real.log 2 + (ν + Real.log K)) / wmin)) := (Real.exp_sum _ _).symm
    _ = _ := by
        congr 1
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, hcard, nsmul_eq_mul] <;> ring

/-- **The per-map bound** (the heart of `thm:analytic`): every term of `eq:tags` is at most
`exp (M H Q)`, `Q = E₀ + 𝒢 + ρ_H + max {-c_H, -ν(a₀(1-γ) - b̄)}`. -/
theorem term_bound (M : Multiplier Λ Ω Ω' a) (hgrow : M.GrowthBound) (hΩ : 0 < Ω)
    (hY : 0 < Ω'.im) {m K : ℕ} (hK : 1 ≤ K) (W : Weights m) (cen : Fin K → Fin m → ℚ)
    {H : ℝ} (hH : 0 < H) (D : ℕ) (hD : ∀ col ∈ W.colSet H, col.1 + 2 * col.2.1.val ≤ D)
    {ν : ℝ} (hν : 0 ≤ ν)
    (hδ : ∀ (j : Fin K) (i : Fin m), ‖((cen j i : ℚ) : ℂ) - ((j : ℕ) : ℂ) * (Ω : ℂ)‖ ≤
      Real.exp ((ν + Real.log K) - ν * (W.w i : ℝ)))
    {wmin : ℝ} (hwmin : 0 < wmin) (hwle : ∀ i, wmin ≤ (W.w i : ℝ))
    {a₀ γ : ℝ} (ha₀ : 0 < a₀) (hγ : 0 ≤ γ) (sel : Row W K H → Col W H)
    (g : Row W K H → ↥(W.tSet H)) :
    ‖(∏ ρ : Row W K H, sCoef cen Ω ρ.1 (fun i => ρ.2.1 i.succ) (g ρ).1) *
        (Bmat M D W H sel g).det‖ ≤
      Real.exp ((W.M K H : ℝ) * H * Qbound M W K D H ν a₀ γ wmin) := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hMn : 0 < W.M K H := Nat.mul_pos hK (W.J_pos hH)
  have hMnr : (0 : ℝ) < (W.M K H : ℝ) := by exact_mod_cast hMn
  have hMne : (W.M K H : ℝ) ≠ 0 := hMnr.ne'
  have hHne : H ≠ 0 := hH.ne'
  have hcard : Fintype.card (Row W K H) = W.M K H := W.card_row K H
  have hcardR : (Fintype.card (Row W K H) : ℝ) = (W.M K H : ℝ) := by rw [hcard]
  have hMH0 : 0 ≤ (W.M K H : ℝ) * H := (mul_pos hMnr hH).le
  have hrs : M.rStar = 2 * (Ω + 1) := rfl
  have hRpos : 0 < M.rStar * (K : ℝ) := mul_pos (by rw [hrs]; linarith) hKpos
  -- hypotheses of the collision lemma
  have hf : ∀ (ξ : ↥(W.tSet H)) (c : Row W K H),
      Differentiable ℂ (fun ζ => Gfun M D (sel c).1 ξ.1 ζ) :=
    fun ξ c => Gfun_differentiable M D (sel c).1 ξ.1
  have hfD : ∀ (ξ : ↥(W.tSet H)) (c : Row W K H) (ζ : ℂ), ‖ζ‖ ≤ M.rStar * (K : ℝ) →
      ‖Gfun M D (sel c).1 ξ.1 ζ‖ ≤ Real.exp (H * discG M H D K wmin) :=
    fun ξ c ζ hζ => norm_Gfun_le M hgrow hΩ hY hK W hH D hwmin hwle (sel c).2
      (hD _ (sel c).2) ξ.1 hζ
  have hw : ∀ ρ : Row W K H, ‖(fun ρ : Row W K H => ((ρ.1 : ℕ) : ℂ) * (Ω : ℂ)) ρ‖ + 1 ≤
      (M.rStar * (K : ℝ)) / 2 := by
    intro ρ
    have hj : ((ρ.1 : ℕ) : ℝ) + 1 ≤ K := by exact_mod_cast Nat.succ_le_of_lt ρ.1.is_lt
    have hn : ‖(((ρ.1 : ℕ) : ℂ) * (Ω : ℂ))‖ = ((ρ.1 : ℕ) : ℝ) * Ω := by
      rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg hΩ.le]
    show ‖(((ρ.1 : ℕ) : ℂ) * (Ω : ℂ))‖ + 1 ≤ (M.rStar * (K : ℝ)) / 2
    rw [hn, hrs]
    nlinarith [mul_nonneg (sub_nonneg.mpr hj) (by linarith : (0 : ℝ) ≤ Ω + 1),
      (Nat.cast_nonneg (ρ.1 : ℕ) : (0 : ℝ) ≤ ((ρ.1 : ℕ) : ℝ))]
  -- the scalar product: zero unless `β_r ≤ g r` for all rows
  by_cases hle : ∀ (ρ : Row W K H) i, ρ.2.1 i.succ ≤ (g ρ).1 i
  swap
  · obtain ⟨ρ, hρ⟩ := not_forall.mp hle
    have h0 : sCoef cen Ω ρ.1 (fun i => ρ.2.1 i.succ) (g ρ).1 = 0 :=
      sCoef_eq_zero_of_not_le cen Ω ρ.1 hρ
    rw [Finset.prod_eq_zero (Finset.mem_univ ρ) h0, zero_mul, norm_zero]
    exact (Real.exp_pos _).le
  have hP := norm_prod_sCoef_le W cen Ω hν hK hδ hwmin hwle g hle
  have hSb : ∑ ρ : Row W K H, rowWt W ρ = (W.M K H : ℝ) * H * W.bbar K H := by
    unfold Weights.bbar rowWt
    field_simp
  have hSgSb : ∑ ρ : Row W K H, rowWt W ρ ≤ ∑ ρ : Row W K H, ((W.wt (g ρ).1 : ℚ) : ℝ) :=
    Finset.sum_le_sum fun ρ _ => W.wt_mono (hle ρ)
  -- the case split
  obtain ⟨nGt, hnGt⟩ : ∃ n : ℕ, n = (Finset.univ.filter fun ρ : Row W K H =>
      a₀ * H < ((W.wt (g ρ).1 : ℚ) : ℝ)).card := ⟨_, rfl⟩
  have hq0 : (Real.log 2 + (ν + Real.log K)) / wmin * ((W.M K H : ℝ) * H) =
      (W.M K H : ℝ) * (H * (Real.log 2 + (ν + Real.log K)) / wmin) := by ring
  unfold Qbound
  by_cases hcase : (1 - γ) * (W.M K H : ℝ) ≤ (nGt : ℝ)
  · -- case 1: many rows with `W(g r) > a₀ H`
    have hdet : ‖(Bmat M D W H sel g).det‖ ≤
        Real.exp ((W.M K H : ℝ) * H * (discG M H D K wmin + rhoH (W.M K H : ℝ) H)) := by
      have h := collision_bound_no_gain g (fun ρ : Row W K H => ρ.2.1 0)
        (fun ρ : Row W K H => ((ρ.1 : ℕ) : ℂ) * (Ω : ℂ))
        (fun (ξ : ↥(W.tSet H)) (c : Row W K H) => Gfun M D (sel c).1 ξ.1) hRpos hH hf hfD hw
      rw [collisionRemainder_eq_rhoH, hcardR] at h
      exact h
    have hSg : (nGt : ℝ) * (a₀ * H) ≤ ∑ ρ : Row W K H, ((W.wt (g ρ).1 : ℚ) : ℝ) := by
      rw [hnGt]
      calc ((Finset.univ.filter fun ρ : Row W K H => a₀ * H < ((W.wt (g ρ).1 : ℚ) : ℝ)).card : ℝ)
            * (a₀ * H)
          = ∑ ρ ∈ Finset.univ.filter (fun ρ : Row W K H => a₀ * H < ((W.wt (g ρ).1 : ℚ) : ℝ)),
              a₀ * H := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ ρ ∈ Finset.univ.filter (fun ρ : Row W K H => a₀ * H < ((W.wt (g ρ).1 : ℚ) : ℝ)),
              ((W.wt (g ρ).1 : ℚ) : ℝ) :=
            Finset.sum_le_sum fun ρ hρ => (Finset.mem_filter.mp hρ).2.le
        _ ≤ ∑ ρ : Row W K H, ((W.wt (g ρ).1 : ℚ) : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun ρ _ _ => W.wt_nonneg _)
    have ha0H : 0 ≤ a₀ * H := (mul_pos ha₀ hH).le
    have hSg2 : (1 - γ) * (W.M K H : ℝ) * (a₀ * H) ≤ (nGt : ℝ) * (a₀ * H) :=
      mul_le_mul_of_nonneg_right hcase ha0H
    have hX : -ν * (∑ ρ : Row W K H, ((W.wt (g ρ).1 : ℚ) : ℝ) - ∑ ρ : Row W K H, rowWt W ρ) ≤
        (W.M K H : ℝ) * H * (-(ν * (a₀ * (1 - γ) - W.bbar K H))) := by
      rw [hSb]
      nlinarith [mul_le_mul_of_nonneg_left (hSg2.trans hSg) hν]
    have hmx : (W.M K H : ℝ) * H * (-(ν * (a₀ * (1 - γ) - W.bbar K H))) ≤
        (W.M K H : ℝ) * H * max (-(cH W K a₀ γ H)) (-(ν * (a₀ * (1 - γ) - W.bbar K H))) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hMH0
    rw [norm_mul]
    calc ‖∏ ρ : Row W K H, sCoef cen Ω ρ.1 (fun i => ρ.2.1 i.succ) (g ρ).1‖ *
          ‖(Bmat M D W H sel g).det‖
        ≤ Real.exp (-ν * (∑ ρ : Row W K H, ((W.wt (g ρ).1 : ℚ) : ℝ) -
            ∑ ρ : Row W K H, rowWt W ρ) +
            (W.M K H : ℝ) * (H * (Real.log 2 + (ν + Real.log K)) / wmin)) *
          Real.exp ((W.M K H : ℝ) * H * (discG M H D K wmin + rhoH (W.M K H : ℝ) H)) :=
          mul_le_mul hP hdet (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp ((-ν * (∑ ρ : Row W K H, ((W.wt (g ρ).1 : ℚ) : ℝ) -
            ∑ ρ : Row W K H, rowWt W ρ) +
            (W.M K H : ℝ) * (H * (Real.log 2 + (ν + Real.log K)) / wmin)) +
          (W.M K H : ℝ) * H * (discG M H D K wmin + rhoH (W.M K H : ℝ) H)) :=
          (Real.exp_add _ _).symm
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          nlinarith [hX, hmx, hq0]
  · -- case 2: fewer than `(1-γ) M` rows have `W(g r) > a₀ H`
    have hcase' : (nGt : ℝ) < (1 - γ) * (W.M K H : ℝ) := not_le.mp hcase
    obtain ⟨S, hSdef⟩ : ∃ S : Finset ↥(W.tSet H), S = Finset.univ.filter
        (fun ξ : ↥(W.tSet H) => ((W.wt ξ.1 : ℚ) : ℝ) ≤ a₀ * H) := ⟨_, rfl⟩
    have hmemS : ∀ ξ : ↥(W.tSet H), ξ ∈ S ↔ ((W.wt ξ.1 : ℚ) : ℝ) ≤ a₀ * H := by
      intro ξ
      rw [hSdef]
      simp
    have ha0H : 0 ≤ a₀ * H := (mul_pos ha₀ hH).le
    have hS0 : 0 < S.card := by
      refine Finset.card_pos.mpr ⟨⟨0, W.zero_mem_tSet hH.le⟩, (hmemS _).mpr ?_⟩
      have h0 : ((W.wt (0 : Fin m → ℕ) : ℚ) : ℝ) = 0 := by
        rw [W.wt_cast]
        simp
      show ((W.wt (0 : Fin m → ℕ) : ℚ) : ℝ) ≤ a₀ * H
      rw [h0]
      exact ha0H
    have hSN : S.card ≤ W.NH a₀ H := by
      show S.card ≤ (W.tSet (a₀ * H)).card
      rw [← Finset.card_map (Function.Embedding.subtype _)]
      apply Finset.card_le_card
      intro x hx
      obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_map.mp hx
      exact (W.mem_tSet_iff _ _).mpr ((hmemS ξ).mp hξ)
    have hfil : (Finset.univ.filter fun ρ : Row W K H => g ρ ∈ S) =
        Finset.univ.filter fun ρ : Row W K H => ¬ (a₀ * H < ((W.wt (g ρ).1 : ℚ) : ℝ)) :=
      Finset.filter_congr fun ρ _ => by rw [hmemS, not_lt]
    have hcnt : nGt + (Finset.univ.filter fun ρ : Row W K H => g ρ ∈ S).card = W.M K H := by
      rw [hfil, hnGt, ← hcard, ← Finset.card_univ]
      exact Finset.card_filter_add_card_filter_not _
    have hcntR : (nGt : ℝ) + ((Finset.univ.filter fun ρ : Row W K H => g ρ ∈ S).card : ℝ) =
        (W.M K H : ℝ) := by exact_mod_cast hcnt
    have hlow : γ * (Fintype.card (Row W K H) : ℝ) ≤
        ((Finset.univ.filter fun ρ : Row W K H => g ρ ∈ S).card : ℝ) := by
      rw [hcardR]
      nlinarith
    have hdet : ‖(Bmat M D W H sel g).det‖ ≤
        Real.exp (-(Real.log 2 / 4) * (γ ^ 2 * (W.M K H : ℝ) ^ 2 / (S.card : ℝ)) +
          (W.M K H : ℝ) * H * (discG M H D K wmin + rhoH (W.M K H : ℝ) H)) := by
      have h := collision_bound_occupancy g (fun ρ : Row W K H => ρ.2.1 0)
        (fun ρ : Row W K H => ((ρ.1 : ℕ) : ℂ) * (Ω : ℂ))
        (fun (ξ : ↥(W.tSet H)) (c : Row W K H) => Gfun M D (sel c).1 ξ.1) hRpos hH hf hfD hw
        S hS0 hγ hlow
      rw [collisionRemainder_eq_rhoH, hcardR] at h
      exact h
    -- `-(log 2/4) γ² M²/|S| ≤ -c_H M H`
    have hSpos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS0
    have hNpos : (0 : ℝ) < (W.NH a₀ H : ℝ) := lt_of_lt_of_le hSpos (by exact_mod_cast hSN)
    have hSNr : (S.card : ℝ) ≤ (W.NH a₀ H : ℝ) := by exact_mod_cast hSN
    have hNne : (W.NH a₀ H : ℝ) ≠ 0 := hNpos.ne'
    have hcH : cH W K a₀ γ H * ((W.M K H : ℝ) * H) =
        (Real.log 2 / 4) * (γ ^ 2 * (W.M K H : ℝ) ^ 2 / (W.NH a₀ H : ℝ)) := by
      unfold cH collisionKappa
      field_simp <;> ring
    have hl4 : 0 ≤ Real.log 2 / 4 := by
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      positivity
    have hdivle : γ ^ 2 * (W.M K H : ℝ) ^ 2 / (W.NH a₀ H : ℝ) ≤
        γ ^ 2 * (W.M K H : ℝ) ^ 2 / (S.card : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hSpos hSNr
    have h5 := mul_le_mul_of_nonneg_left hdivle hl4
    have hmx : -(cH W K a₀ γ H) * ((W.M K H : ℝ) * H) ≤
        (W.M K H : ℝ) * H * max (-(cH W K a₀ γ H)) (-(ν * (a₀ * (1 - γ) - W.bbar K H))) := by
      have := mul_le_mul_of_nonneg_right
        (le_max_left (-(cH W K a₀ γ H)) (-(ν * (a₀ * (1 - γ) - W.bbar K H)))) hMH0
      linarith
    have hν0 : -ν * (∑ ρ : Row W K H, ((W.wt (g ρ).1 : ℚ) : ℝ) - ∑ ρ : Row W K H, rowWt W ρ) ≤ 0 := by
      have := mul_nonneg hν (sub_nonneg.mpr hSgSb)
      linarith
    rw [norm_mul]
    calc ‖∏ ρ : Row W K H, sCoef cen Ω ρ.1 (fun i => ρ.2.1 i.succ) (g ρ).1‖ *
          ‖(Bmat M D W H sel g).det‖
        ≤ Real.exp (-ν * (∑ ρ : Row W K H, ((W.wt (g ρ).1 : ℚ) : ℝ) -
            ∑ ρ : Row W K H, rowWt W ρ) +
            (W.M K H : ℝ) * (H * (Real.log 2 + (ν + Real.log K)) / wmin)) *
          Real.exp (-(Real.log 2 / 4) * (γ ^ 2 * (W.M K H : ℝ) ^ 2 / (S.card : ℝ)) +
          (W.M K H : ℝ) * H * (discG M H D K wmin + rhoH (W.M K H : ℝ) H)) :=
          mul_le_mul hP hdet (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp ((-ν * (∑ ρ : Row W K H, ((W.wt (g ρ).1 : ℚ) : ℝ) -
            ∑ ρ : Row W K H, rowWt W ρ) +
            (W.M K H : ℝ) * (H * (Real.log 2 + (ν + Real.log K)) / wmin)) +
          (-(Real.log 2 / 4) * (γ ^ 2 * (W.M K H : ℝ) ^ 2 / (S.card : ℝ)) +
          (W.M K H : ℝ) * H * (discG M H D K wmin + rhoH (W.M K H : ℝ) H))) :=
          (Real.exp_add _ _).symm
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          nlinarith [hν0, hmx, hq0, h5, hcH]

/-- **Sum over the maps `g`.** `|det Ã_sel| ≤ |𝒯_H|^M · exp (M H Q)`. -/
theorem det_bound (M : Multiplier Λ Ω Ω' a) (hgrow : M.GrowthBound) (hΩ : 0 < Ω)
    (hY : 0 < Ω'.im) {m K : ℕ} (hK : 1 ≤ K) (W : Weights m) (cen : Fin K → Fin m → ℚ)
    {H : ℝ} (hH : 0 < H) (D : ℕ) (hD : ∀ col ∈ W.colSet H, col.1 + 2 * col.2.1.val ≤ D)
    {ν : ℝ} (hν : 0 ≤ ν)
    (hδ : ∀ (j : Fin K) (i : Fin m), ‖((cen j i : ℚ) : ℂ) - ((j : ℕ) : ℂ) * (Ω : ℂ)‖ ≤
      Real.exp ((ν + Real.log K) - ν * (W.w i : ℝ)))
    {wmin : ℝ} (hwmin : 0 < wmin) (hwle : ∀ i, wmin ≤ (W.w i : ℝ))
    {a₀ γ : ℝ} (ha₀ : 0 < a₀) (hγ : 0 ≤ γ) (sel : Row W K H → Col W H) :
    ‖((transportMatrix W M D cen H).submatrix id sel).det‖ ≤
      ((W.tSet H).card : ℝ) ^ (W.M K H) *
        Real.exp ((W.M K H : ℝ) * H * Qbound M W K D H ν a₀ γ wmin) := by
  have hcard : Fintype.card (Row W K H) = W.M K H := W.card_row K H
  rw [det_expansion M W D cen H sel]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ g : Row W K H → ↥(W.tSet H), ‖(∏ ρ : Row W K H,
          sCoef cen Ω ρ.1 (fun i => ρ.2.1 i.succ) (g ρ).1) * (Bmat M D W H sel g).det‖
      ≤ ∑ g : Row W K H → ↥(W.tSet H),
          Real.exp ((W.M K H : ℝ) * H * Qbound M W K D H ν a₀ γ wmin) :=
        Finset.sum_le_sum fun g _ =>
          term_bound M hgrow hΩ hY hK W cen hH D hD hν hδ hwmin hwle ha₀ hγ sel g
    _ = ((W.tSet H).card : ℝ) ^ (W.M K H) *
          Real.exp ((W.M K H : ℝ) * H * Qbound M W K D H ν a₀ γ wmin) := by
        first
          | (rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_coe, hcard,
              nsmul_eq_mul, Nat.cast_pow]; done)
          | (simp [Finset.sum_const, Fintype.card_fun, hcard])

/-! ### The final arithmetic -/

theorem log_le_of_mul_pow_le {Δn F Tc E : ℝ} {e Mnat : ℕ} (hΔ : 0 < Δn) (hF : 0 < F)
    (hT : 0 < Tc) (h : Δn * F ^ e ≤ Tc ^ Mnat * Real.exp E) :
    Real.log Δn ≤ (Mnat : ℝ) * Real.log Tc + E - (e : ℝ) * Real.log F := by
  have h1 := Real.log_le_log (mul_pos hΔ (pow_pos hF e)) h
  rw [Real.log_mul hΔ.ne' (pow_pos hF e).ne', Real.log_pow,
    Real.log_mul (pow_pos hT Mnat).ne' (Real.exp_pos E).ne', Real.log_pow, Real.log_exp] at h1
  linarith

theorem div_step {Mn H Lt Qv Dr Lp : ℝ} (hMn : Mn ≠ 0) (hH : H ≠ 0) :
    (Mn * Lt + Mn * H * Qv + Dr * Mn * Lp) / (Mn * H) = Lt / H + Qv + Dr / H * Lp := by
  field_simp

theorem final_combine {Lt H D X Lp CL K2 w0 E0 Lg ρ mx Lw : ℝ} (hE : E0 + Lg = Lw)
    (f5 : D / H * (X + Lp) ≤ (1 / (2 * w0) + 1 / H) * (CL * K2)) :
    Lt / H + (E0 + (D / H * X + Lg) + ρ + mx) + D / H * Lp ≤
      (CL * K2 / (2 * w0) + Lw) + (CL * K2 / H + ρ + Lt / H) + mx := by
  have e2 : (1 / (2 * w0) + 1 / H) * (CL * K2) = CL * K2 / (2 * w0) + CL * K2 / H := by ring
  have e3 : D / H * (X + Lp) = D / H * X + D / H * Lp := by ring
  linarith

set_option maxHeartbeats 800000 in
/-- **E14, `thm:analytic`.** Assume `Δ ≠ 0` for the minor selected by `sel`. If the centres satisfy
`|c_{ji} - jΩ| ≤ K q_i^{-ν}`, `w_i - 1 < log q_i`, and `0 < w_min ≤ w_i`, then
`log|Δ|/(M H) ≤ E_an + e_H + max {-c_H, -ν (a₀ (1-γ) - b̄)}`. -/
theorem analytic_upper_bound (M : Multiplier Λ Ω Ω' a) (hΩ : 0 < Ω) (hY : 0 < Ω'.im)
    {c : OriginChart} (ser : OriginSeries c) (hg₂ : Λ.g₂ = -4 * (c.A : ℂ))
    (hg₃ : Λ.g₃ = -4 * (c.B : ℂ)) (hca : c.a = a) {m K : ℕ} (hK : 1 ≤ K) (W : Weights m)
    (cen : Fin K → Fin m → ℚ) (q : Fin m → ℕ) {ν : ℝ} (hν : 0 ≤ ν)
    (hδ : ∀ (j : Fin K) (i : Fin m), ‖((cen j i : ℚ) : ℂ) - ((j : ℕ) : ℂ) * (Ω : ℂ)‖ ≤
      (K : ℝ) * (q i : ℝ) ^ (-ν))
    (hq : ∀ i, 0 < q i) (hlog : ∀ i, (W.w i : ℝ) - 1 < Real.log (q i : ℝ))
    {wmin : ℝ} (hwmin : 0 < wmin) (hwle : ∀ i, wmin ≤ (W.w i : ℝ))
    {a₀ γ : ℝ} (ha₀ : 0 < a₀) (hγ : 0 ≤ γ) {H : ℝ} (hH : 0 < H)
    (sel : Row W K H → Col W H) (hΔ : packetDelta W ser cen H sel ≠ 0) :
    AnalyticUpperBound (Real.log |((packetDelta W ser cen H sel : ℚ) : ℝ)|) (W.M K H : ℝ) H
      (W.bbar K H)
      (M.CLam * (K : ℝ) ^ 2 / (2 * (W.w₀ : ℝ)) +
        (ν + Real.log (4 * M.rStar * (K : ℝ) ^ 2)) / wmin)
      (eH W K M.CLam H) (cH W K a₀ γ H) ν a₀ γ := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hw0 : (0 : ℝ) < (W.w₀ : ℝ) := by exact_mod_cast W.w₀_pos
  have hw0ne : (W.w₀ : ℝ) ≠ 0 := hw0.ne'
  have hMn : 0 < W.M K H := Nat.mul_pos hK (W.J_pos hH)
  have hMnr : (0 : ℝ) < (W.M K H : ℝ) := by exact_mod_cast hMn
  have hMne : (W.M K H : ℝ) ≠ 0 := hMnr.ne'
  have hHne : H ≠ 0 := hH.ne'
  have hrs : M.rStar = 2 * (Ω + 1) := rfl
  have hrpos : 0 < M.rStar := by rw [hrs]; linarith
  have hgrow : M.GrowthBound := M.growthBound hΩ hY
  have hD : ∀ col ∈ W.colSet H, col.1 + 2 * col.2.1.val ≤ ⌈H / (2 * (W.w₀ : ℝ))⌉₊ :=
    fun col hc => col_le_ceil W hc
  have hδe : ∀ (j : Fin K) (i : Fin m), ‖((cen j i : ℚ) : ℂ) - ((j : ℕ) : ℂ) * (Ω : ℂ)‖ ≤
      Real.exp ((ν + Real.log K) - ν * (W.w i : ℝ)) := fun j i =>
    (hδ j i).trans (rpow_neg_le_exp (Nat.cast_pos.mpr (hq i)) hν (hlog i) hKpos)
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ, D = ⌈H / (2 * (W.w₀ : ℝ))⌉₊ := ⟨_, rfl⟩
  rw [← hDdef] at hD
  have hdb := det_bound M hgrow hΩ hY hK W cen hH D hD hν hδe hwmin hwle ha₀ hγ sel
  have htr := transport_norm M ser hg₂ hg₃ hca W cen H D hD sel
  have hΔn : 0 < ‖((packetDelta W ser cen H sel : ℚ) : ℂ)‖ := by
    rw [Complex.norm_ratCast]
    exact abs_pos.mpr (by exact_mod_cast hΔ)
  have hF : 0 < ‖M.F₀ 0‖ := norm_pos_iff.mpr M.ne_zero
  have hT : (0 : ℝ) < ((W.tSet H).card : ℝ) := by
    have : 0 < (W.tSet H).card := Finset.card_pos.mpr ⟨0, W.zero_mem_tSet hH.le⟩
    exact_mod_cast this
  rw [htr] at hdb
  have hlogb := log_le_of_mul_pow_le hΔn hF hT hdb
  -- the pieces
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hS1 : 1 ≤ M.Sstar := Multiplier.one_le_Sstar M
  have hlS : 0 ≤ Real.log M.Sstar := Real.log_nonneg hS1
  have hLp : 0 ≤ Real.log (max 1 ‖M.F₀ 0‖⁻¹) := Real.log_nonneg (le_max_left _ _)
  have hneg : -Real.log ‖M.F₀ 0‖ ≤ Real.log (max 1 ‖M.F₀ 0‖⁻¹) := by
    rw [← Real.log_inv]
    exact Real.log_le_log (inv_pos.mpr hF) (le_max_right _ _)
  have hχ : 0 ≤ M.chi := by
    unfold Multiplier.chi
    positivity
  have hDn : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hDle : (D : ℝ) ≤ H / (2 * (W.w₀ : ℝ)) + 1 := by
    rw [hDdef]
    exact (Nat.ceil_lt_add_one (div_nonneg hH.le (by positivity))).le
  have hexp : ((D * W.J H * K : ℕ) : ℝ) = (D : ℝ) * (W.M K H : ℝ) := by
    simp only [Weights.M]
    push_cast
    ring
  rw [hexp] at hlogb
  -- constants
  have hCLam0 : 0 ≤ M.CLam := by
    unfold Multiplier.CLam
    have : 0 ≤ M.chi * (M.rStar + Ω'.im) ^ 2 := by positivity
    linarith
  have hK2 : (1 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
  have f2 : Real.log M.Sstar + M.chi * (M.rStar + Ω'.im) ^ 2 * (K : ℝ) ^ 2 +
      Real.log (max 1 ‖M.F₀ 0‖⁻¹) ≤ M.CLam * (K : ℝ) ^ 2 := by
    unfold Multiplier.CLam
    nlinarith [mul_nonneg (sub_nonneg.mpr hK2) (add_nonneg hlS hLp)]
  have hlog4 : Real.log (4 * M.rStar * (K : ℝ) ^ 2) =
      Real.log 2 + Real.log K + Real.log (2 * (M.rStar * (K : ℝ))) := by
    have h4 : 4 * M.rStar * (K : ℝ) ^ 2 = 2 * (K : ℝ) * (2 * (M.rStar * (K : ℝ))) := by ring
    rw [h4, Real.log_mul (by positivity : (2 * (K : ℝ)) ≠ 0)
      (by positivity : (2 * (M.rStar * (K : ℝ))) ≠ 0),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hKpos.ne']
  have hDH : (D : ℝ) / H ≤ 1 / (2 * (W.w₀ : ℝ)) + 1 / H := by
    have h1 : (D : ℝ) / H ≤ (H / (2 * (W.w₀ : ℝ)) + 1) / H :=
      div_le_div_of_nonneg_right hDle hH.le
    have h2 : (H / (2 * (W.w₀ : ℝ)) + 1) / H = 1 / (2 * (W.w₀ : ℝ)) + 1 / H := by
      field_simp
    rw [h2] at h1
    exact h1
  have f5 : (D : ℝ) / H * (Real.log M.Sstar + M.chi * (M.rStar + Ω'.im) ^ 2 * (K : ℝ) ^ 2 +
      Real.log (max 1 ‖M.F₀ 0‖⁻¹)) ≤ (1 / (2 * (W.w₀ : ℝ)) + 1 / H) * (M.CLam * (K : ℝ) ^ 2) :=
    (mul_le_mul_of_nonneg_left f2 (div_nonneg hDn hH.le)).trans
      (mul_le_mul_of_nonneg_right hDH (mul_nonneg hCLam0 (by positivity)))
  -- the target
  have hlogΔ : Real.log |((packetDelta W ser cen H sel : ℚ) : ℝ)| =
      Real.log ‖((packetDelta W ser cen H sel : ℚ) : ℂ)‖ := by rw [Complex.norm_ratCast]
  show Real.log |((packetDelta W ser cen H sel : ℚ) : ℝ)| / ((W.M K H : ℝ) * H) ≤ _
  rw [hlogΔ]
  -- bound of the log
  have hbound : Real.log ‖((packetDelta W ser cen H sel : ℚ) : ℂ)‖ ≤
      (W.M K H : ℝ) * Real.log ((W.tSet H).card : ℝ) +
        (W.M K H : ℝ) * H * Qbound M W K D H ν a₀ γ wmin +
        (D : ℝ) * (W.M K H : ℝ) * Real.log (max 1 ‖M.F₀ 0‖⁻¹) := by
    have h3 : (D : ℝ) * (W.M K H : ℝ) * (-Real.log ‖M.F₀ 0‖) ≤
        (D : ℝ) * (W.M K H : ℝ) * Real.log (max 1 ‖M.F₀ 0‖⁻¹) :=
      mul_le_mul_of_nonneg_left hneg (mul_nonneg hDn hMnr.le)
    linarith
  have hdiv : Real.log ‖((packetDelta W ser cen H sel : ℚ) : ℂ)‖ / ((W.M K H : ℝ) * H) ≤
      ((W.M K H : ℝ) * Real.log ((W.tSet H).card : ℝ) +
        (W.M K H : ℝ) * H * Qbound M W K D H ν a₀ γ wmin +
        (D : ℝ) * (W.M K H : ℝ) * Real.log (max 1 ‖M.F₀ 0‖⁻¹)) / ((W.M K H : ℝ) * H) :=
    div_le_div_of_nonneg_right hbound (mul_pos hMnr hH).le
  have hsimp := div_step (Mn := (W.M K H : ℝ)) (H := H)
    (Lt := Real.log ((W.tSet H).card : ℝ)) (Qv := Qbound M W K D H ν a₀ γ wmin) (Dr := (D : ℝ))
    (Lp := Real.log (max 1 ‖M.F₀ 0‖⁻¹)) hMne hHne
  refine hdiv.trans (le_of_eq_of_le hsimp ?_)
  unfold Qbound discG eH
  have hE : (Real.log 2 + (ν + Real.log K)) / wmin + Real.log (2 * (M.rStar * (K : ℝ))) / wmin =
      (ν + Real.log (4 * M.rStar * (K : ℝ) ^ 2)) / wmin := by
    rw [hlog4]; ring
  exact final_combine hE f5

/-- **E14 with the grid of the paper.** The centres `c_{ji} = j p_i/q_i`, with
`|Ω - p_i/q_i| ≤ q_i^{-ν}`, `q_i ≥ 1`, `w_i - 1 < log q_i`, `0 < w_min ≤ w_i`. -/
theorem analytic_upper_bound_grid (M : Multiplier Λ Ω Ω' a) (hΩ : 0 < Ω) (hY : 0 < Ω'.im)
    {c : OriginChart} (ser : OriginSeries c) (hg₂ : Λ.g₂ = -4 * (c.A : ℂ))
    (hg₃ : Λ.g₃ = -4 * (c.B : ℂ)) (hca : c.a = a) {m K : ℕ} (hK : 1 ≤ K) (W : Weights m)
    (p : Fin m → ℤ) (q : Fin m → ℕ) {ν : ℝ} (hν : 0 ≤ ν)
    (hclose : ∀ i, |Ω - (p i : ℝ) / (q i : ℝ)| ≤ (q i : ℝ) ^ (-ν))
    (hq : ∀ i, 0 < q i) (hlog : ∀ i, (W.w i : ℝ) - 1 < Real.log (q i : ℝ))
    {wmin : ℝ} (hwmin : 0 < wmin) (hwle : ∀ i, wmin ≤ (W.w i : ℝ))
    {a₀ γ : ℝ} (ha₀ : 0 < a₀) (hγ : 0 ≤ γ) {H : ℝ} (hH : 0 < H)
    (sel : Row W K H → Col W H)
    (hΔ : packetDelta W ser (gridCentres K p q) H sel ≠ 0) :
    AnalyticUpperBound (Real.log |((packetDelta W ser (gridCentres K p q) H sel : ℚ) : ℝ)|)
      (W.M K H : ℝ) H (W.bbar K H)
      (M.CLam * (K : ℝ) ^ 2 / (2 * (W.w₀ : ℝ)) +
        (ν + Real.log (4 * M.rStar * (K : ℝ) ^ 2)) / wmin)
      (eH W K M.CLam H) (cH W K a₀ γ H) ν a₀ γ := by
  refine analytic_upper_bound M hΩ hY ser hg₂ hg₃ hca hK W (gridCentres K p q) q hν ?_ hq hlog
    hwmin hwle ha₀ hγ hH sel hΔ
  intro j i
  have hqi : (0 : ℝ) < (q i : ℝ) := Nat.cast_pos.mpr (hq i)
  have hc : ((gridCentres K p q j i : ℚ) : ℂ) - ((j : ℕ) : ℂ) * (Ω : ℂ) =
      ((((j : ℕ) : ℝ) * ((p i : ℝ) / (q i : ℝ) - Ω) : ℝ) : ℂ) := by
    unfold gridCentres
    push_cast
    ring
  rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
    abs_sub_comm]
  have hjK : ((j : ℕ) : ℝ) ≤ K := by exact_mod_cast (Nat.le_of_lt j.is_lt)
  exact mul_le_mul hjK (hclose i) (abs_nonneg _) (Nat.cast_nonneg _)

end Main

end

end CatalanCore.Elliptic.Analytic

namespace CatalanCore.Elliptic

open CatalanCore.Elliptic.Analytic

/-- **E14 for an integral model** (`thm:analytic`), with the multiplier `ψ̂` of
`IntegralModel.multiplier` and the grid `c_{ji} = j p_i/q_i`. -/
theorem IntegralModel.analytic_upper_bound (Mod : IntegralModel) (ser : OriginSeries Mod.chart)
    {m K : ℕ} (hK : 1 ≤ K) (W : Weights m) (p : Fin m → ℤ) (q : Fin m → ℕ) {ν : ℝ} (hν : 0 ≤ ν)
    (hclose : ∀ i, |Mod.Ω - (p i : ℝ) / (q i : ℝ)| ≤ (q i : ℝ) ^ (-ν))
    (hq : ∀ i, 0 < q i) (hlog : ∀ i, (W.w i : ℝ) - 1 < Real.log (q i : ℝ))
    {wmin : ℝ} (hwmin : 0 < wmin) (hwle : ∀ i, wmin ≤ (W.w i : ℝ))
    {a₀ γ : ℝ} (ha₀ : 0 < a₀) (hγ : 0 ≤ γ) {H : ℝ} (hH : 0 < H)
    (sel : Row W K H → Col W H)
    (hΔ : packetDelta W ser (gridCentres K p q) H sel ≠ 0) :
    AnalyticUpperBound (Real.log |((packetDelta W ser (gridCentres K p q) H sel : ℚ) : ℝ)|)
      (W.M K H : ℝ) H (W.bbar K H)
      (Mod.multiplier.CLam * (K : ℝ) ^ 2 / (2 * (W.w₀ : ℝ)) +
        (ν + Real.log (4 * Mod.multiplier.rStar * (K : ℝ) ^ 2)) / wmin)
      (eH W K Mod.multiplier.CLam H) (cH W K a₀ γ H) ν a₀ γ :=
  Analytic.analytic_upper_bound_grid Mod.multiplier Mod.Ω_pos Mod.Y_pos ser Mod.g₂_eq Mod.g₃_eq rfl
    hK W p q hν hclose hq hlog hwmin hwle ha₀ hγ hH sel hΔ

end CatalanCore.Elliptic
