module

public import CatalanCore.Elliptic.Interfaces
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# E16, E17: the parameter system (paper `lem:abc`, `prop:params`)

Paper: *A bound for the irrationality exponent of real elliptic periods*, Section "The parameters".

For rational `ν > 3` the data `b, h, θ, a₀, γ, F₀, g` of `CatalanCore.Elliptic.Params` satisfy `lem:abc`
(`abc_a`, `abc_b`, `abc_c`).  `exists_paramChoice` produces the rational `c₁, c₂` of the paper
(`ParamChoice ν` of `CatalanCore.Elliptic.Interfaces`), and `prop_params` records, for every such choice and
`K = ⌊c₁^m⌋`, `w₀ = c₂^{-m}`, `v₀ = 4Kθ^m w₀`, the limits (P1)–(P5) as `m → ∞`:

* `c₁^m/2 ≤ K ≤ c₁^m` for every `m` (stronger than the paper, which assumes `c₁^m ≥ 2`);
* (P1) `Kθ^m → 0`; (P2) `K (w₀/v₀) θ^m = 1/4`; (P3) `K²/w₀ → 0`; (P4) `v₀ → ∞`;
* (P5) `c_∞ = κγ²Kθ^m/((m+1) v₀ a₀^m) → ∞`.

Everything is real arithmetic: closed by `field_simp`, `nlinarith`, `linarith` and standard limits.
-/

open Filter Topology

namespace CatalanCore.Elliptic

namespace Params

variable {ν : ℚ}

/-- `ν - 3 = 4 h ν`. -/
theorem h_rel (hν : 3 < ν) : ν - 3 = 4 * h ν * ν := by
  have : ν ≠ 0 := by linarith
  unfold h
  field_simp

theorem h_pos (hν : 3 < ν) : 0 < h ν := by
  unfold h
  exact div_pos (by linarith) (by linarith)

theorem h_lt (hν : 3 < ν) : h ν < 1 / 4 := by
  have h1 := h_rel hν
  by_contra hcon
  have hcon := not_lt.1 hcon
  nlinarith

theorem b_eq (hν : 3 < ν) : b ν = (2 + 2 * h ν) / 3 := by
  have : ν ≠ 0 := by linarith
  unfold b h
  field_simp
  ring

theorem a₀_eq (ν : ℚ) : a₀ ν = 1 - b ν * h ν := rfl

theorem θ_eq (ν : ℚ) : θ ν = 1 - h ν := rfl

theorem γ_eq (hν : 3 < ν) : γ ν = h ν ^ 2 / 3 := by
  have : ν ≠ 0 := by linarith
  unfold γ
  rw [h_rel hν]
  field_simp
  ring

/-- `lem:abc` (a): `2/3 < b < 1 - 1/ν`, `0 < h < 1/4`, hence `0 < θ < a₀ < 1`. -/
theorem abc_a (hν : 3 < ν) :
    2 / 3 < b ν ∧ b ν < 1 - 1 / ν ∧ 0 < h ν ∧ h ν < 1 / 4 ∧ 0 < θ ν ∧ θ ν < a₀ ν ∧ a₀ ν < 1 := by
  have h0 := h_pos hν
  have h1 := h_lt hν
  have hb := b_eq hν
  have hrel := h_rel hν
  have hν0 : ν ≠ 0 := by linarith
  have hinv : 1 / ν = (1 - 4 * h ν) / 3 := by
    rw [div_eq_div_iff hν0 (by norm_num)]
    linarith
  have hb1 : b ν < 1 := by rw [hb]; linarith
  have hb0 : 0 < b ν := by rw [hb]; linarith
  refine ⟨by rw [hb]; linarith, by rw [hinv, hb]; linarith, h0, h1, ?_, ?_, ?_⟩
  · rw [θ_eq]; linarith
  · rw [θ_eq, a₀_eq]; nlinarith [mul_pos h0 (sub_pos.2 hb1)]
  · rw [a₀_eq]; nlinarith [mul_pos hb0 h0]

/-- `lem:abc` (b): `a₀³ < θ²`. -/
theorem abc_b (hν : 3 < ν) : a₀ ν ^ 3 < θ ν ^ 2 := by
  have h0 := h_pos hν
  have h1 := h_lt hν
  have hb := b_eq hν
  have hb1 : b ν < 1 := by rw [hb]; linarith
  have hb0 : 0 < b ν := by rw [hb]; linarith
  have key : (1 - b ν * h ν) ^ 3 - (1 - h ν) ^ 2 = 3 * h ν ^ 2 * (b ν ^ 2 - 1) - b ν ^ 3 * h ν ^ 3 := by
    rw [hb]; ring
  have t1 : 3 * h ν ^ 2 * (b ν ^ 2 - 1) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) (by nlinarith)
  have t2 : 0 < b ν ^ 3 * h ν ^ 3 := by positivity
  rw [a₀_eq, θ_eq]
  linarith

theorem g_eq (hν : 3 < ν) : g ν = ν * h ν ^ 2 * (2 - a₀ ν) / 3 := by
  have hb := b_eq hν
  have hrel := h_rel hν
  have hγ := γ_eq hν
  unfold g
  rw [hγ, θ_eq, a₀_eq, hb]
  linear_combination (h ν / 3) * hrel

/-- `lem:abc` (c): `g ≥ h(ν-3)/12 > 0`. -/
theorem abc_c (hν : 3 < ν) : h ν * (ν - 3) / 12 ≤ g ν ∧ 0 < h ν * (ν - 3) / 12 := by
  have h0 := h_pos hν
  have hrel := h_rel hν
  obtain ⟨-, -, -, -, -, -, ha1⟩ := abc_a hν
  have hb := b_eq hν
  have ha0 : 0 < a₀ ν := by
    obtain ⟨-, -, -, -, h5, h6, -⟩ := abc_a hν
    linarith
  refine ⟨?_, by nlinarith⟩
  rw [g_eq hν]
  have e : h ν * (ν - 3) / 12 = ν * h ν ^ 2 / 3 := by rw [hrel]; ring
  rw [e]
  have : 0 < ν * h ν ^ 2 * (1 - a₀ ν) := by
    have : 0 < ν := by linarith
    positivity
  nlinarith

/-- Existence of the rational choice of `c₁, c₂` (density of `ℚ`), explicitly. -/
theorem exists_paramChoice (hν : 3 < ν) : Nonempty (ParamChoice ν) := by
  obtain ⟨-, -, -, -, hθ0, hθa, ha1⟩ := abc_a hν
  have hb := abc_b hν
  have ha0 : 0 < a₀ ν := by linarith
  set a := a₀ ν with ha
  set θ' := θ ν with hθ
  set t := a / θ' with ht
  have ht1 : 1 < t := by rw [ht, lt_div_iff₀ hθ0]; linarith
  have ht2 : t ^ 2 * a = a ^ 3 / θ' ^ 2 := by rw [ht]; field_simp
  have ht3 : t ^ 2 * a < 1 := by
    rw [ht2, div_lt_one (by positivity)]; exact hb
  have ht4 : 0 < t ^ 2 * a := by positivity
  set δ := 1 - t ^ 2 * a with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ < 1 := by rw [hδ]; linarith
  set ε := δ / (2 * t + 2) with hε
  have hε0 : 0 < ε := by rw [hε]; apply div_pos hδ0; linarith
  have hεδ : ε * (2 * t + 2) = δ := by rw [hε]; field_simp
  have hε1 : ε < 1 := by nlinarith
  have hc1 : (t + ε) ^ 2 * a < 1 := by
    have e : (t + ε) ^ 2 * a = t ^ 2 * a + 2 * t * ε * a + ε ^ 2 * a := by ring
    have h1 : 2 * t * ε * a ≤ 2 * t * ε := by nlinarith [mul_pos (by linarith : (0:ℚ) < t) hε0]
    have h2 : ε ^ 2 * a ≤ ε := by nlinarith [mul_pos hε0 hε0]
    rw [e]
    nlinarith
  set c₁ := t + ε with hc₁
  have hc10 : 0 < c₁ := by rw [hc₁]; linarith
  have hlo : a / θ' < c₁ := by rw [hc₁]; linarith
  have hM1 : a < 1 / c₁ ^ 2 := by rw [lt_div_iff₀ (by positivity)]; nlinarith
  have hM2 : a < c₁ * θ' := by
    have := hlo
    rw [div_lt_iff₀ hθ0] at this
    linarith
  set M := min (1 / c₁ ^ 2) (c₁ * θ') with hM
  have haM : a < M := lt_min hM1 hM2
  set c₂ := (a + M) / 2 with hc₂
  have hc2a : a < c₂ := by rw [hc₂]; linarith
  have hc2M : c₂ < M := by rw [hc₂]; linarith
  have hc2_1 : c₂ < 1 / c₁ ^ 2 := lt_of_lt_of_le hc2M (min_le_left _ _)
  have hc2_2 : c₂ < c₁ * θ' := lt_of_lt_of_le hc2M (min_le_right _ _)
  refine ⟨⟨c₁, c₂, hc10, hlo, ?_, hc2a, ?_, hc2_2⟩⟩
  · exact hc1
  · rw [lt_div_iff₀ (by positivity)] at hc2_1; exact hc2_1

end Params

/-- `r^n/(n+1) → ∞` for `r > 1`. -/
theorem tendsto_pow_div_succ {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n : ℕ => r ^ n / ((n : ℝ) + 1)) atTop atTop := by
  have hr0 : 0 < r := by linarith
  have h0 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / r ^ n) atTop (𝓝 0) := by
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 hr
    have h2 : Tendsto (fun n : ℕ => 1 / r ^ n) atTop (𝓝 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 hr0.le) (inv_lt_one_of_one_lt₀ hr)
      simpa [one_div, inv_pow] using this
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine h3.congr (fun n => ?_)
    rw [pow_one, ← add_div]
  have h3 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / r ^ n) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨h0, Eventually.of_forall (fun n => by
      simp only [Set.mem_Ioi]
      exact div_pos (by positivity) (pow_pos hr0 n))⟩
  have h4 := h3.inv_tendsto_nhdsGT_zero
  refine h4.congr (fun n => ?_)
  simp [Pi.inv_apply, inv_div]

namespace ParamChoice

open Params

variable {ν : ℚ} (P : ParamChoice ν)

theorem a₀_pos (hν : 3 < ν) : 0 < a₀ ν := by
  obtain ⟨-, -, -, -, h5, h6, -⟩ := abc_a hν
  linarith

theorem one_lt_c₁ (hν : 3 < ν) : 1 < P.c₁ := by
  obtain ⟨-, -, -, -, hθ0, hθa, -⟩ := abc_a hν
  have h1 : 1 < Params.a₀ ν / Params.θ ν := by
    rw [lt_div_iff₀ hθ0]; linarith
  linarith [P.c₁_lo]

theorem c₁θ_lt_one (hν : 3 < ν) : P.c₁ * Params.θ ν < 1 := by
  obtain ⟨-, -, -, -, hθ0, hθa, -⟩ := abc_a hν
  have ha0 := a₀_pos hν
  have h1 := P.one_lt_c₁ hν
  have h2 := P.c₁_hi
  have h3 := P.c₁_pos
  nlinarith [mul_pos (mul_pos h3 ha0) (sub_pos.2 h1), mul_pos h3 (sub_pos.2 hθa)]

theorem c₂_pos (hν : 3 < ν) : 0 < P.c₂ := lt_trans (a₀_pos hν) P.c₂_lo

theorem one_le_K (hν : 3 < ν) (m : ℕ) : 1 ≤ P.K m := by
  unfold K
  rw [Nat.one_le_floor_iff]
  exact one_le_pow₀ (P.one_lt_c₁ hν).le

theorem K_le (m : ℕ) : (P.K m : ℚ) ≤ P.c₁ ^ m := by
  have := P.c₁_pos
  unfold K
  exact Nat.floor_le (by positivity)

/-- `c₁^m / 2 ≤ K` for every `m` (the paper assumes `c₁^m ≥ 2`). -/
theorem K_ge (hν : 3 < ν) (m : ℕ) : P.c₁ ^ m / 2 ≤ (P.K m : ℚ) := by
  have h1 : (1 : ℚ) ≤ P.K m := by exact_mod_cast P.one_le_K hν m
  have h2 : P.c₁ ^ m < (P.K m : ℚ) + 1 := by
    unfold K
    exact Nat.lt_floor_add_one _
  linarith

theorem w₀_real (m : ℕ) : ((P.w₀ m : ℚ) : ℝ) = ((P.c₂ : ℝ) ^ m)⁻¹ := by
  unfold w₀
  push_cast
  rfl

theorem v₀_real (m : ℕ) :
    ((P.v₀ m : ℚ) : ℝ) = 4 * (P.K m : ℝ) * ((Params.θ ν : ℚ) : ℝ) ^ m * ((P.c₂ : ℝ) ^ m)⁻¹ := by
  unfold v₀
  rw [Rat.cast_mul, Rat.cast_mul, w₀_real]
  push_cast
  ring

theorem K_le_real (m : ℕ) : (P.K m : ℝ) ≤ (P.c₁ : ℝ) ^ m := by
  have := P.K_le m
  exact_mod_cast this

theorem K_ge_real (hν : 3 < ν) (m : ℕ) : (P.c₁ : ℝ) ^ m / 2 ≤ (P.K m : ℝ) := by
  have := P.K_ge hν m
  exact_mod_cast this

theorem one_le_K_real (hν : 3 < ν) (m : ℕ) : (1 : ℝ) ≤ (P.K m : ℝ) := by
  exact_mod_cast P.one_le_K hν m

theorem θ_real_pos (hν : 3 < ν) : (0 : ℝ) < ((Params.θ ν : ℚ) : ℝ) := by
  exact_mod_cast (abc_a hν).2.2.2.2.1

/-- (P1): `K θ^m → 0`. -/
theorem tendsto_Kθ (hν : 3 < ν) :
    Tendsto (fun m : ℕ => (P.K m : ℝ) * ((Params.θ ν : ℚ) : ℝ) ^ m) atTop (𝓝 0) := by
  have hc := P.c₁_pos
  have hθ0 := θ_real_pos hν
  have hx : (P.c₁ : ℝ) * ((Params.θ ν : ℚ) : ℝ) < 1 := by exact_mod_cast P.c₁θ_lt_one hν
  have hc' : (0 : ℝ) < (P.c₁ : ℝ) := by exact_mod_cast hc
  have hx0 : 0 ≤ (P.c₁ : ℝ) * ((Params.θ ν : ℚ) : ℝ) := by positivity
  refine squeeze_zero (fun m => by positivity) (fun m => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hx0 hx)
  rw [mul_pow]
  gcongr
  exact P.K_le_real m

/-- (P2): `K (w₀/v₀) θ^m = 1/4` for every `m`. -/
theorem K_w₀_div_v₀ (hν : 3 < ν) (m : ℕ) :
    (P.K m : ℝ) * (((P.w₀ m : ℚ) : ℝ) / ((P.v₀ m : ℚ) : ℝ)) * ((Params.θ ν : ℚ) : ℝ) ^ m = 1 / 4 := by
  have hK := P.one_le_K_real hν m
  have hθ0 := θ_real_pos hν
  have hc2 : (0 : ℝ) < (P.c₂ : ℝ) := by exact_mod_cast P.c₂_pos hν
  have hK0 : (P.K m : ℝ) ≠ 0 := by linarith
  have h1 : ((Params.θ ν : ℚ) : ℝ) ^ m ≠ 0 := by positivity
  have h2 : (P.c₂ : ℝ) ^ m ≠ 0 := by positivity
  rw [v₀_real, w₀_real]
  field_simp

/-- (P3): `K²/w₀ → 0`. -/
theorem tendsto_K_sq_div_w₀ (hν : 3 < ν) :
    Tendsto (fun m : ℕ => (P.K m : ℝ) ^ 2 / ((P.w₀ m : ℚ) : ℝ)) atTop (𝓝 0) := by
  have hc' : (0 : ℝ) < (P.c₁ : ℝ) := by exact_mod_cast P.c₁_pos
  have hc2 : (0 : ℝ) < (P.c₂ : ℝ) := by exact_mod_cast P.c₂_pos hν
  have hx : (P.c₁ : ℝ) ^ 2 * (P.c₂ : ℝ) < 1 := by
    have := P.c₂_hi₁
    rw [mul_comm] at this
    exact_mod_cast this
  have hx0 : 0 ≤ (P.c₁ : ℝ) ^ 2 * (P.c₂ : ℝ) := by positivity
  refine squeeze_zero (fun m => by rw [w₀_real]; positivity) (fun m => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hx0 hx)
  rw [w₀_real, div_inv_eq_mul]
  have hK := P.one_le_K_real hν m
  have hle := P.K_le_real m
  calc (P.K m : ℝ) ^ 2 * (P.c₂ : ℝ) ^ m ≤ ((P.c₁ : ℝ) ^ m) ^ 2 * (P.c₂ : ℝ) ^ m := by
        gcongr
    _ = ((P.c₁ : ℝ) ^ 2 * (P.c₂ : ℝ)) ^ m := by ring

/-- (P4): `v₀ → ∞`. -/
theorem tendsto_v₀ (hν : 3 < ν) :
    Tendsto (fun m : ℕ => ((P.v₀ m : ℚ) : ℝ)) atTop atTop := by
  have hc' : (0 : ℝ) < (P.c₁ : ℝ) := by exact_mod_cast P.c₁_pos
  have hc2 : (0 : ℝ) < (P.c₂ : ℝ) := by exact_mod_cast P.c₂_pos hν
  have hθ0 := θ_real_pos hν
  have hr : 1 < (P.c₁ : ℝ) * ((Params.θ ν : ℚ) : ℝ) / (P.c₂ : ℝ) := by
    rw [one_lt_div hc2]
    exact_mod_cast P.c₂_hi₂
  have hT := (tendsto_pow_atTop_atTop_of_one_lt hr).const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  refine tendsto_atTop_mono (fun m => ?_) hT
  rw [v₀_real, div_pow, mul_pow, div_eq_mul_inv]
  have hk := P.K_ge_real hν m
  have e : 4 * (P.K m : ℝ) * ((Params.θ ν : ℚ) : ℝ) ^ m * ((P.c₂ : ℝ) ^ m)⁻¹
      - 2 * ((P.c₁ : ℝ) ^ m * ((Params.θ ν : ℚ) : ℝ) ^ m * ((P.c₂ : ℝ) ^ m)⁻¹)
      = (4 * (P.K m : ℝ) - 2 * (P.c₁ : ℝ) ^ m) * (((Params.θ ν : ℚ) : ℝ) ^ m * ((P.c₂ : ℝ) ^ m)⁻¹) := by
    ring
  have : 0 ≤ (4 * (P.K m : ℝ) - 2 * (P.c₁ : ℝ) ^ m) * (((Params.θ ν : ℚ) : ℝ) ^ m * ((P.c₂ : ℝ) ^ m)⁻¹) :=
    mul_nonneg (by linarith) (by positivity)
  linarith

/-- The error term `E_ar = c₀ F₀ / v₀ → 0` for any constant numerator. -/
theorem tendsto_const_div_v₀ (hν : 3 < ν) (c : ℝ) :
    Tendsto (fun m : ℕ => c / ((P.v₀ m : ℚ) : ℝ)) atTop (𝓝 0) :=
  Tendsto.div_atTop tendsto_const_nhds (P.tendsto_v₀ hν)

/-- (P5): `c_∞ = κ γ² K θ^m / ((m+1) v₀ a₀^m) → ∞`. -/
theorem tendsto_cInfty (hν : 3 < ν) :
    Tendsto (fun m : ℕ => collisionKappa * ((Params.γ ν : ℚ) : ℝ) ^ 2 * (P.K m : ℝ)
        * ((Params.θ ν : ℚ) : ℝ) ^ m
        / (((m : ℝ) + 1) * ((P.v₀ m : ℚ) : ℝ) * ((Params.a₀ ν : ℚ) : ℝ) ^ m)) atTop atTop := by
  have hθ0 := θ_real_pos hν
  have hc2 : (0 : ℝ) < (P.c₂ : ℝ) := by exact_mod_cast P.c₂_pos hν
  have ha0 : (0 : ℝ) < ((Params.a₀ ν : ℚ) : ℝ) := by exact_mod_cast a₀_pos hν
  have hr : 1 < (P.c₂ : ℝ) / ((Params.a₀ ν : ℚ) : ℝ) := by
    rw [one_lt_div ha0]
    exact_mod_cast P.c₂_lo
  have hκ : 0 < collisionKappa := by
    unfold collisionKappa
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  have hγ : (0 : ℝ) < ((Params.γ ν : ℚ) : ℝ) := by
    rw [γ_eq hν]
    have := h_pos hν
    push_cast
    positivity
  have hpos : 0 < collisionKappa * ((Params.γ ν : ℚ) : ℝ) ^ 2 / 4 := by positivity
  have hT := (tendsto_pow_div_succ hr).const_mul_atTop hpos
  refine hT.congr (fun m => ?_)
  have hK := P.one_le_K_real hν m
  have hK0 : (P.K m : ℝ) ≠ 0 := by linarith
  have h1 : ((Params.θ ν : ℚ) : ℝ) ^ m ≠ 0 := by positivity
  have h2 : (P.c₂ : ℝ) ^ m ≠ 0 := by positivity
  have h3 : ((Params.a₀ ν : ℚ) : ℝ) ^ m ≠ 0 := by positivity
  have h4 : ((m : ℝ) + 1) ≠ 0 := by positivity
  rw [v₀_real, div_pow]
  field_simp

/-- `cInfty` of the interface agrees with the closed expression of `tendsto_cInfty`. -/
theorem cInfty_eq {m : ℕ} (W : Weights m) (hθ : W.θ = Params.θ ν) (hv : W.v₀ = P.v₀ m) :
    cInfty W (P.K m) ((Params.a₀ ν : ℚ) : ℝ) ((Params.γ ν : ℚ) : ℝ)
      = collisionKappa * ((Params.γ ν : ℚ) : ℝ) ^ 2 * (P.K m : ℝ) * ((Params.θ ν : ℚ) : ℝ) ^ m
        / (((m : ℝ) + 1) * ((P.v₀ m : ℚ) : ℝ) * ((Params.a₀ ν : ℚ) : ℝ) ^ m) := by
  unfold cInfty
  rw [hθ, hv]

end ParamChoice

/-- `prop:params` (E17), eventual-in-`m` form, for every rational `ν > 3`: there is a rational choice
`c₁, c₂` (`ParamChoice ν`), with `K = ⌊c₁^m⌋` satisfying `c₁^m/2 ≤ K ≤ c₁^m`, such that (P1)–(P5) hold. -/
theorem prop_params {ν : ℚ} (hν : 3 < ν) :
    ∃ P : ParamChoice ν,
      (∀ m : ℕ, P.c₁ ^ m / 2 ≤ (P.K m : ℚ) ∧ (P.K m : ℚ) ≤ P.c₁ ^ m) ∧
      Tendsto (fun m : ℕ => (P.K m : ℝ) * ((Params.θ ν : ℚ) : ℝ) ^ m) atTop (𝓝 0) ∧
      (∀ m : ℕ, (P.K m : ℝ) * (((P.w₀ m : ℚ) : ℝ) / ((P.v₀ m : ℚ) : ℝ))
        * ((Params.θ ν : ℚ) : ℝ) ^ m = 1 / 4) ∧
      Tendsto (fun m : ℕ => (P.K m : ℝ) ^ 2 / ((P.w₀ m : ℚ) : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun m : ℕ => ((P.v₀ m : ℚ) : ℝ)) atTop atTop ∧
      Tendsto (fun m : ℕ => collisionKappa * ((Params.γ ν : ℚ) : ℝ) ^ 2 * (P.K m : ℝ)
        * ((Params.θ ν : ℚ) : ℝ) ^ m
        / (((m : ℝ) + 1) * ((P.v₀ m : ℚ) : ℝ) * ((Params.a₀ ν : ℚ) : ℝ) ^ m)) atTop atTop := by
  obtain ⟨P⟩ := Params.exists_paramChoice hν
  exact ⟨P, fun m => ⟨P.K_ge hν m, P.K_le m⟩, P.tendsto_Kθ hν, P.K_w₀_div_v₀ hν,
    P.tendsto_K_sq_div_w₀ hν, P.tendsto_v₀ hν, P.tendsto_cInfty hν⟩

end CatalanCore.Elliptic
