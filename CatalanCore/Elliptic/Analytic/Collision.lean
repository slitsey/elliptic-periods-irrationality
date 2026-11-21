module

public import OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision
public import OAI.NumberTheory.PiExponent.Analysis.CollisionLimit
public import OAI.NumberTheory.PiExponent.Analysis.CollisionExponential
public import OAI.NumberTheory.PiExponent.Analysis.CollisionOccupancy
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# The collision estimate (paper `lem:collision`, Chudnovsky--Chudnovsky Lemma 16.2)

Rows `r` are indexed by a finite type `ι`, each with a tag `g r : κ`, a Taylor index `s r : ℕ`
and a centre `w r : ℂ`. Columns are indexed by the same type (or by an equivalent one,
`collision_bound_of_equiv`). For entire functions `f ξ c` the matrix entry is the Taylor
coefficient `[z^{s r}] f (g r) c (w r + z)`.

Hypotheses: `‖w r‖ + 1 ≤ R / 2` (the paper's `(K-1)Ω + 1 ≤ R/2` for centres `jΩ`, `j < K`:
`collision_bound_period`) and `‖f ξ c ζ‖ ≤ exp (H 𝒢)` on `‖ζ‖ ≤ R` (the disc hypothesis; only
the circle `‖ζ‖ = R` is used). Conclusion, with `κ = (log 2)/4`, `s₀ = 2^{-1/2}` and
`ρ_H = (log M + κ - log (1 - s₀))/H` (`collisionRemainder M H`), `M = card ι`, `n_ξ = |g⁻¹ ξ|`:
`‖det‖ ≤ exp (-κ ∑_ξ n_ξ² + M H (𝒢 + ρ_H))`.

The vendored OAI modules (Apache-2.0) provide the determinant expansion, the geometric sum and
the combinatorics of collisions. The one change from the OAI row test is that the rows translate
by `z ↦ w + z` on the unit circle instead of `t ↦ center + log (1 + t)` on `|t| = 1/2`, and the
coefficient bound has no `2^ℓ` factor, so the remainder has no `log 2 / v` term.
-/

namespace CatalanCore.Elliptic

open scoped BigOperators
open Complex Finset MeasureTheory Filter
open OAI.PiExponent.AnalyticCollision (normalizedTaylorCoeff norm_normalizedTaylorCoeff_le
  hasSum_normalizedTaylorCoeff)
open OAI.PiExponent

/-! ### The Taylor coefficient functional -/

/-- The `s`-th Taylor coefficient at `0`, as the Cauchy integral on the unit circle. -/
noncomputable def taylorCoeff (s : ℕ) (F : ℂ → ℂ) : ℂ :=
  cauchyPowerSeries F 0 1 s (fun _ => 1)

theorem norm_taylorCoeff_le {F : ℂ → ℂ} {D : ℝ}
    (hD : ∀ z ∈ Metric.sphere (0 : ℂ) 1, ‖F z‖ ≤ D) (s : ℕ) :
    ‖taylorCoeff s F‖ ≤ D := by
  unfold taylorCoeff
  rw [cauchyPowerSeries_apply]
  calc
    _ ≤ (1 : ℝ) * D := by
      apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by norm_num)
      intro z hz
      have hzR : ‖z‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
      simp only [sub_zero, norm_smul, norm_pow, norm_div, norm_one, norm_inv, hzR, div_one,
        inv_one, one_pow, one_mul]
      exact hD z hz
    _ = D := one_mul D

theorem taylorCoeff_const_mul (s : ℕ) (c : ℂ) (F : ℂ → ℂ) :
    taylorCoeff s (fun t => c * F t) = c * taylorCoeff s F := by
  simp only [taylorCoeff, cauchyPowerSeries_apply, smul_eq_mul]
  have heq : (fun z : ℂ => (1 / (z - 0)) ^ s * ((z - 0)⁻¹ * (c * F z))) =
      (fun z : ℂ => c * ((1 / (z - 0)) ^ s * ((z - 0)⁻¹ * F z))) := by
    funext z
    ring
  rw [heq, circleIntegral.integral_const_mul]
  ring

/-- `taylorCoeff s F` is the usual Taylor coefficient `F^{(s)}(0)/s!` of an entire function. -/
theorem taylorCoeff_eq_iteratedDeriv {F : ℂ → ℂ} (hF : Differentiable ℂ F) (s : ℕ) :
    taylorCoeff s F = iteratedDeriv s F 0 / (s.factorial : ℂ) := by
  have h := (hF.diffContOnCl (s := Metric.ball (0 : ℂ) 1)).circleIntegral_one_div_sub_center_pow_smul
    (c := 0) (R := 1) one_pos s
  unfold taylorCoeff
  rw [cauchyPowerSeries_apply]
  have hz : ∀ z : ℂ, (1 / (z - 0)) ^ s • (z - 0)⁻¹ • F z = (1 / (z - 0) ^ (s + 1)) • F z := by
    intro z
    simp only [smul_eq_mul, sub_zero]
    rw [pow_succ, one_div, one_div, mul_inv, inv_pow]
    ring
  simp_rw [hz]
  rw [h, smul_smul]
  have : (s.factorial : ℂ) ≠ 0 := by exact_mod_cast s.factorial_ne_zero
  field_simp [Real.pi_ne_zero, Complex.I_ne_zero]
  simp only [smul_eq_mul]
  field_simp

theorem hasSum_taylorCoeff {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {bound : ℕ → ℝ}
    (hF : ∀ n, Measurable (F n))
    (hbound : ∀ n z, z ∈ Metric.sphere (0 : ℂ) 1 → ‖F n z‖ ≤ bound n)
    (hsum : Summable bound)
    (hpoint : ∀ z ∈ Metric.sphere (0 : ℂ) 1, HasSum (fun n => F n z) (f z))
    (s : ℕ) : HasSum (fun n => taylorCoeff s (F n)) (taylorCoeff s f) := by
  simp only [taylorCoeff, cauchyPowerSeries_apply]
  apply HasSum.const_smul
  change HasSum (fun n => ∫ θ in (0 : ℝ)..2 * Real.pi,
      deriv (circleMap 0 1) θ •
        ((1 / (circleMap 0 1 θ - 0)) ^ s •
          (circleMap 0 1 θ - 0)⁻¹ • F n (circleMap 0 1 θ)))
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      deriv (circleMap 0 1) θ •
        ((1 / (circleMap 0 1 θ - 0)) ^ s •
          (circleMap 0 1 θ - 0)⁻¹ • f (circleMap 0 1 θ)))
  apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => bound n)
  · intro n
    apply Measurable.aestronglyMeasurable
    simp only [deriv_circleMap]
    exact (by fun_prop)
  · intro n
    apply Eventually.of_forall
    intro θ _
    have hb := hbound n (circleMap 0 1 θ) (circleMap_mem_sphere 0 (by norm_num) θ)
    simp only [deriv_circleMap, norm_smul, norm_mul, norm_I, mul_one, sub_zero,
      norm_pow, norm_div, norm_one, norm_inv, norm_circleMap_zero]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1), one_div, inv_one, one_pow, one_mul]
    exact hb
  · exact Eventually.of_forall fun _ _ => hsum
  · exact intervalIntegrable_const
  · apply Eventually.of_forall
    intro θ _
    exact (((hpoint _ (circleMap_mem_sphere 0 (by norm_num) θ)).const_smul _).const_smul _).const_smul _

/-! ### Rows translated by `z ↦ w + z` -/

theorem norm_shift_div_le_half {w z : ℂ} {R : ℝ} (hR : 0 < R) (hw : ‖w‖ + 1 ≤ R / 2)
    (hz : ‖z‖ ≤ 1) : ‖(w + z) / (R : ℂ)‖ ≤ 1 / 2 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  apply (div_le_iff₀ hR).mpr
  have htri := norm_add_le w z
  linarith

theorem norm_taylorCoeff_shift_pow_le {w : ℂ} {R : ℝ} (hR : 0 < R) (hw : ‖w‖ + 1 ≤ R / 2)
    (s d : ℕ) : ‖taylorCoeff s (fun z => ((w + z) / (R : ℂ)) ^ d)‖ ≤ (1 / 2 : ℝ) ^ d := by
  apply norm_taylorCoeff_le
  intro z hz
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_shift_div_le_half hR hw (by simpa only [Metric.mem_sphere, dist_zero_right] using hz.le)) _

theorem hasSum_translated_taylorCoeff {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : NNReal} (hR : 0 < R) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ z ∈ Metric.sphere (0 : ℂ) (R : ℝ), ‖f z‖ ≤ D)
    {w : ℂ} (hw : ‖w‖ + 1 ≤ (R : ℝ) / 2) (s : ℕ) :
    HasSum (fun d => taylorCoeff s (fun z => ((w + z) / (R : ℂ)) ^ d) *
      normalizedTaylorCoeff f R d) (taylorCoeff s (fun z => f (w + z))) := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have h := hasSum_taylorCoeff
    (F := fun d z => normalizedTaylorCoeff f R d * ((w + z) / (R : ℂ)) ^ d)
    (f := fun z => f (w + z))
    (bound := fun d => D * (1 / 2 : ℝ) ^ d)
    (by intro d; fun_prop) ?_ ?_ ?_ s
  · convert! h using 1
    funext d
    rw [taylorCoeff_const_mul, mul_comm]
  · intro d z hz
    rw [norm_mul, norm_pow]
    apply mul_le_mul (norm_normalizedTaylorCoeff_le hR hfD d)
    · apply pow_le_pow_left₀ (norm_nonneg _)
        (norm_shift_div_le_half hR' hw (by simpa only [Metric.mem_sphere, dist_zero_right] using hz.le))
    · positivity
    · exact hD
  · exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left D
  · intro z _
    exact hasSum_normalizedTaylorCoeff hf hR _

/-! ### The numerical factor without a `2^ℓ` -/

theorem collision_factor_le_exp_unit (M C : ℕ) {H A S : ℝ} (hH : 0 < H)
    (hC : 2 * (C : ℝ) = S - M) :
    ((M.factorial : ℝ) * (Real.exp (H * A)) ^ M * 1) *
      Collision.collisionRatio ^ C * ((1 - Collision.collisionRatio)⁻¹) ^ M ≤
    Real.exp (-(Real.log 2 / 4) * S + (M : ℝ) * H *
      (A + Collision.collisionRemainder M H)) := by
  have hr : 0 < 1 - Collision.collisionRatio := sub_pos.mpr Collision.collisionRatio_lt_one
  have hrem : (M : ℝ) * H * (A + Collision.collisionRemainder M H) =
      (M : ℝ) * H * A + (M : ℝ) * (Real.log M + Real.log 2 / 4 -
        Real.log (1 - Collision.collisionRatio)) := by
    unfold Collision.collisionRemainder
    field_simp
  rw [hrem]
  calc
    _ ≤ (Real.exp ((M : ℝ) * Real.log M) * (Real.exp (H * A)) ^ M * 1) *
        Collision.collisionRatio ^ C * ((1 - Collision.collisionRatio)⁻¹) ^ M := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (inv_nonneg.mpr hr.le) M)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg Collision.collisionRatio_pos.le C)
      apply mul_le_mul_of_nonneg_right _ zero_le_one
      exact mul_le_mul_of_nonneg_right (Collision.factorial_le_exp_card_log M) (by positivity)
    _ = _ := by
      rw [mul_one, ← Real.exp_nat_mul, Collision.collisionRatio, ← Real.exp_nat_mul]
      have hi : (1 - Real.exp (-Real.log 2 / 2))⁻¹ =
          Real.exp (-Real.log (1 - Collision.collisionRatio)) := by
        rw [Real.exp_neg, Real.exp_log hr]
        rfl
      rw [hi, ← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1
      have hc : (C : ℝ) = (S - M) / 2 := by linarith
      rw [hc]
      unfold Collision.collisionRatio
      ring

/-! ### The collision estimate -/

theorem norm_le_of_mem_sphere' {z : ℂ} {R' : NNReal} {R : ℝ} (hRR : (R' : ℝ) = R)
    (hz : z ∈ Metric.sphere (0 : ℂ) (R' : ℝ)) : ‖z‖ ≤ R := by
  rw [mem_sphere_zero_iff_norm] at hz
  exact hz.le.trans hRR.le

/-- `n_ξ = |g⁻¹ ξ|`: the number of rows with tag `ξ`. -/
def tagCount {ι κ : Type*} [Fintype ι] [DecidableEq κ] (g : ι → κ) (ξ : κ) : ℕ :=
  (Finset.univ.filter fun r => g r = ξ).card

theorem multiplicity_eq_tagCount {ι κ : Type*} [Fintype ι] [DecidableEq κ] (g : ι → κ) (ξ : κ) :
    Collision.multiplicity Finset.univ g ξ = tagCount g ξ := rfl

/-- `lem:collision`. -/
theorem collision_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (g : ι → κ) (s : ι → ℕ) (w : ι → ℂ) (f : κ → ι → ℂ → ℂ)
    {R : ℝ} (hR : 0 < R) {H G : ℝ} (hH : 0 < H)
    (hf : ∀ ξ c, Differentiable ℂ (f ξ c))
    (hfD : ∀ ξ c ζ, ‖ζ‖ ≤ R → ‖f ξ c ζ‖ ≤ Real.exp (H * G))
    (hw : ∀ r, ‖w r‖ + 1 ≤ R / 2) :
    ‖Matrix.det (fun r c => taylorCoeff (s r) (fun z => f (g r) c (w r + z)))‖ ≤
      Real.exp (-(Real.log 2 / 4) * (∑ ξ, (tagCount g ξ : ℝ) ^ 2) +
        (Fintype.card ι : ℝ) * H * (G + Collision.collisionRemainder (Fintype.card ι) H)) := by
  obtain ⟨R', hRR⟩ : ∃ R' : NNReal, (R' : ℝ) = R := ⟨⟨R, hR.le⟩, rfl⟩
  have hR' : 0 < R' := by
    have : (0 : ℝ) < R' := by rw [hRR]; exact hR
    exact_mod_cast this
  have hinf := Collision.infinite_collision_bound g
    (fun i d => taylorCoeff (s i) (fun z => ((w i + z) / (R' : ℂ)) ^ d))
    (fun a d j => normalizedTaylorCoeff (f a j) R' d)
    (Real.exp (H * G)) Collision.collisionRatio (fun _ => 1) (Real.exp_pos _).le
    Collision.collisionRatio_pos.le Collision.collisionRatio_lt_one (fun _ => zero_le_one)
    (fun a d j => norm_normalizedTaylorCoeff_le hR'
      (fun z hz => hfD a j z (norm_le_of_mem_sphere' hRR hz)) d)
    (fun i d => by
      rw [Collision.collisionRatio_mul_self, one_mul]
      exact norm_taylorCoeff_shift_pow_le (by rw [hRR]; exact hR) (by rw [hRR]; exact hw i) _ _)
    (Matrix.of fun r c => taylorCoeff (s r) (fun z => f (g r) c (w r + z)))
    (fun i j => hasSum_translated_taylorCoeff (hf (g i) j) hR' (Real.exp_pos _).le
      (fun z hz => hfD (g i) j z (norm_le_of_mem_sphere' hRR hz)) (by rw [hRR]; exact hw i) (s i))
  have hfin := collision_factor_le_exp_unit (Fintype.card ι)
    (∑ a, (Collision.multiplicity Finset.univ g a).choose 2) (H := H) (A := G)
    (S := ∑ a, (Collision.multiplicity Finset.univ g a : ℝ) ^ 2) hH
    (Collision.twice_collision_count_eq g)
  simp only [Finset.prod_const_one, mul_one] at hinf hfin
  refine (le_of_eq_of_le ?_ (hinf.trans hfin))
  rfl

/-- The same bound for a rectangular index: rows `ρ`, columns `γ`, with a bijection. -/
theorem collision_bound_of_equiv
    {ρ γ κ : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype κ] [DecidableEq κ]
    (e : ρ ≃ γ)
    (g : ρ → κ) (s : ρ → ℕ) (w : ρ → ℂ) (f : κ → γ → ℂ → ℂ)
    {R : ℝ} (hR : 0 < R) {H G : ℝ} (hH : 0 < H)
    (hf : ∀ ξ c, Differentiable ℂ (f ξ c))
    (hfD : ∀ ξ c ζ, ‖ζ‖ ≤ R → ‖f ξ c ζ‖ ≤ Real.exp (H * G))
    (hw : ∀ r, ‖w r‖ + 1 ≤ R / 2) :
    ‖Matrix.det (fun (r : ρ) (c : ρ) => taylorCoeff (s r) (fun z => f (g r) (e c) (w r + z)))‖ ≤
      Real.exp (-(Real.log 2 / 4) * (∑ ξ, (tagCount g ξ : ℝ) ^ 2) +
        (Fintype.card ρ : ℝ) * H * (G + Collision.collisionRemainder (Fintype.card ρ) H)) :=
  collision_bound g s w (fun ξ c => f ξ (e c)) hR hH (fun ξ c => hf ξ (e c))
    (fun ξ c => hfD ξ (e c)) hw

/-- The case of the paper: centres `j Ω` with `j < K`, `(K - 1) Ω + 1 ≤ R / 2`. -/
theorem collision_bound_period
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (g : ι → κ) (s j : ι → ℕ) {K : ℕ} (hj : ∀ r, j r < K) {Ω : ℝ} (hΩ : 0 ≤ Ω)
    (f : κ → ι → ℂ → ℂ)
    {R : ℝ} (hR : 0 < R) (hKR : ((K : ℝ) - 1) * Ω + 1 ≤ R / 2) {H G : ℝ} (hH : 0 < H)
    (hf : ∀ ξ c, Differentiable ℂ (f ξ c))
    (hfD : ∀ ξ c ζ, ‖ζ‖ ≤ R → ‖f ξ c ζ‖ ≤ Real.exp (H * G)) :
    ‖Matrix.det (fun r c => taylorCoeff (s r)
        (fun z => f (g r) c (((j r : ℝ) * Ω : ℝ) + z)))‖ ≤
      Real.exp (-(Real.log 2 / 4) * (∑ ξ, (tagCount g ξ : ℝ) ^ 2) +
        (Fintype.card ι : ℝ) * H * (G + Collision.collisionRemainder (Fintype.card ι) H)) := by
  refine collision_bound g s (fun r => (((j r : ℝ) * Ω : ℝ) : ℂ)) f hR hH hf hfD ?_
  intro r
  have hjK : (j r : ℝ) + 1 ≤ K := by exact_mod_cast hj r
  have hnn : 0 ≤ (j r : ℝ) * Ω := mul_nonneg (Nat.cast_nonneg _) hΩ
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  nlinarith

/-- Case 1 of the paper: the lemma "without its first term". -/
theorem collision_bound_no_gain
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (g : ι → κ) (s : ι → ℕ) (w : ι → ℂ) (f : κ → ι → ℂ → ℂ)
    {R : ℝ} (hR : 0 < R) {H G : ℝ} (hH : 0 < H)
    (hf : ∀ ξ c, Differentiable ℂ (f ξ c))
    (hfD : ∀ ξ c ζ, ‖ζ‖ ≤ R → ‖f ξ c ζ‖ ≤ Real.exp (H * G))
    (hw : ∀ r, ‖w r‖ + 1 ≤ R / 2) :
    ‖Matrix.det (fun r c => taylorCoeff (s r) (fun z => f (g r) c (w r + z)))‖ ≤
      Real.exp ((Fintype.card ι : ℝ) * H * (G + Collision.collisionRemainder (Fintype.card ι) H)) := by
  refine (collision_bound g s w f hR hH hf hfD hw).trans (Real.exp_le_exp.mpr ?_)
  have h2 : 0 ≤ Real.log 2 / 4 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    positivity
  have hs : 0 ≤ ∑ ξ, (tagCount g ξ : ℝ) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith

/-- Case 2 of the paper: if more than `η M` rows have their tag in a set `S`
(`η ≥ 0`, `S` nonempty), then `∑ n_ξ² ≥ η² M² / |S|` and the collision gain follows. -/
theorem collision_bound_occupancy
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (g : ι → κ) (s : ι → ℕ) (w : ι → ℂ) (f : κ → ι → ℂ → ℂ)
    {R : ℝ} (hR : 0 < R) {H G : ℝ} (hH : 0 < H)
    (hf : ∀ ξ c, Differentiable ℂ (f ξ c))
    (hfD : ∀ ξ c ζ, ‖ζ‖ ≤ R → ‖f ξ c ζ‖ ≤ Real.exp (H * G))
    (hw : ∀ r, ‖w r‖ + 1 ≤ R / 2)
    (S : Finset κ) (hS : 0 < S.card) {η : ℝ} (hη : 0 ≤ η)
    (hlow : η * (Fintype.card ι : ℝ) ≤ ((Finset.univ.filter fun r => g r ∈ S).card : ℝ)) :
    ‖Matrix.det (fun r c => taylorCoeff (s r) (fun z => f (g r) c (w r + z)))‖ ≤
      Real.exp (-(Real.log 2 / 4) * (η ^ 2 * (Fintype.card ι : ℝ) ^ 2 / (S.card : ℝ)) +
        (Fintype.card ι : ℝ) * H * (G + Collision.collisionRemainder (Fintype.card ι) H)) := by
  refine (collision_bound g s w f hR hH hf hfD hw).trans (Real.exp_le_exp.mpr ?_)
  have hocc := Collision.nat_occupancy_square_lower_bound S (tagCount g) (M := Fintype.card ι)
    hη (by
      have hsum := Collision.sum_multiplicity_eq_card_filter (Finset.univ : Finset ι) S g
      have : ∑ a ∈ S, (tagCount g a : ℝ) = ((Finset.univ.filter fun r => g r ∈ S).card : ℝ) := by
        exact_mod_cast hsum
      rw [this]
      exact hlow) hS
  have h2 : 0 ≤ Real.log 2 / 4 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    positivity
  nlinarith

/-! ### The constants in the paper's form -/

/-- `s₀ = 2^{-1/2}`. -/
theorem collisionRatio_eq_rpow : Collision.collisionRatio = (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  unfold Collision.collisionRatio
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- `ρ_H = (log M + κ - log (1 - s₀)) / H` with `κ = (log 2)/4` and `s₀ = 2^{-1/2}`. -/
theorem collisionRemainder_eq (M : ℕ) (H : ℝ) :
    Collision.collisionRemainder M H =
      (Real.log M + Real.log 2 / 4 - Real.log (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))) / H := by
  unfold Collision.collisionRemainder
  rw [collisionRatio_eq_rpow]

end CatalanCore.Elliptic
