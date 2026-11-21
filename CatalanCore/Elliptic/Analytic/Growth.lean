module

public import CatalanCore.Elliptic.Analytic.Multiplier

@[expose] public section

/-!
# The growth bound `lem:growth` (row E08, strip form)

For the multiplier package `M : Multiplier Λ Ω Ω' a` with `0 < Ω`, `0 < Y = Im Ω'`:
`Multiplier.growthBound` proves `M.GrowthBound`, i.e. for `k + 2b ≤ D` and all `z`

  `‖F₀ z ^ (D-k-2b) * F₁ z ^ k * F₂ z ^ b‖ ≤ S_*^D * exp (D χ (|Im z| + Y)²)`,

with `χ = 2π/(ΩY)` and `S_*` the (finite) sup of the `F_i` over the fundamental rectangle, `S_* ≥ 1`.

Proof (the theta-multiplier derivation §6): `n = ⌊Im z / Y⌋`, `l = ⌊Re (z - nΩ') / Ω⌋`, `z₁ = z - lΩ - nΩ'` in the
rectangle, translate formula (`translate₀/₁/₂`, with the `n²` transport of `ψ̂`), then the single
inequality `2 n Im z₁ + n² Y = ((Im z)² - (Im z₁)²)/Y ≤ (|Im z| + Y)²/Y`. No theta-series bound is used.
-/

namespace CatalanCore.Elliptic

open Complex

noncomputable section

namespace Multiplier

variable {Λ : PeriodPair} {Ω : ℝ} {Ω' : ℂ} {a : ℤ}

lemma isCompact_rect (Ω Y : ℝ) : IsCompact (rect Ω Y) := by
  have h : rect Ω Y = (Set.Icc 0 Ω) ×ℂ (Set.Icc 0 Y) := by
    ext z
    simp only [rect, Complex.mem_reProdIm, Set.mem_Icc, Set.mem_setOf_eq]
    tauto
  rw [h]
  exact isCompact_Icc.reProdIm isCompact_Icc

/-- On the rectangle every `‖F_i‖` is at most `S_*`. -/
lemma norm_le_Sstar (M : Multiplier Λ Ω Ω' a) {z : ℂ} (hz : z ∈ rect Ω Ω'.im) :
    ‖M.F₀ z‖ ≤ M.Sstar ∧ ‖M.F₁ z‖ ≤ M.Sstar ∧ ‖M.F₂ z‖ ≤ M.Sstar := by
  have hc : Continuous (fun z => max (max ‖M.F₀ z‖ ‖M.F₁ z‖) ‖M.F₂ z‖) :=
    (((M.diff₀.continuous).norm.max (M.diff₁.continuous).norm)).max (M.diff₂.continuous).norm
  have hb : BddAbove ((fun z => max (max ‖M.F₀ z‖ ‖M.F₁ z‖) ‖M.F₂ z‖) '' rect Ω Ω'.im) :=
    ((isCompact_rect Ω Ω'.im).image hc).bddAbove
  have h := le_csSup hb (Set.mem_image_of_mem _ hz)
  have h' : max (max ‖M.F₀ z‖ ‖M.F₁ z‖) ‖M.F₂ z‖ ≤ M.Sstar := h.trans (le_max_right _ _)
  exact ⟨(le_max_left _ _).trans ((le_max_left _ _).trans h'),
    (le_max_right _ _).trans ((le_max_left _ _).trans h'), (le_max_right _ _).trans h'⟩

lemma one_le_Sstar (M : Multiplier Λ Ω Ω' a) : 1 ≤ M.Sstar := le_max_left _ _

/-- The real part of the exponent of the transport factor. -/
lemma norm_transport (hΩ : 0 < Ω) (n : ℤ) (w : ℂ) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I / Ω) * (2 * n * w + n ^ 2 * Ω'))‖ =
      Real.exp (2 * Real.pi / Ω * (2 * n * w.im + n ^ 2 * Ω'.im)) := by
  rw [Complex.norm_exp]
  congr 1
  have h1 : -(2 * (Real.pi : ℂ) * Complex.I / (Ω : ℂ)) * (2 * (n : ℂ) * w + (n : ℂ) ^ 2 * Ω') =
      ((-(2 * Real.pi / Ω) : ℝ) : ℂ) *
        (Complex.I * (((2 * n : ℝ) : ℂ) * w + (((n : ℝ) ^ 2 : ℝ) : ℂ) * Ω')) := by
    push_cast
    ring
  rw [h1, Complex.re_ofReal_mul, Complex.I_mul_re, Complex.add_im, Complex.im_ofReal_mul,
    Complex.im_ofReal_mul]
  ring

/-- The one inequality: `2 n y₁ + n² Y ≤ (|y| + Y)²/Y` when `n Y = y - y₁`. -/
lemma exponent_le {Y y y₁ n : ℝ} (hY : 0 < Y) (hn : n * Y = y - y₁) :
    2 * n * y₁ + n ^ 2 * Y ≤ (|y| + Y) ^ 2 / Y := by
  rw [le_div_iff₀ hY]
  have h : (2 * n * y₁ + n ^ 2 * Y) * Y = 2 * (n * Y) * y₁ + (n * Y) ^ 2 := by ring
  rw [h, hn]
  nlinarith [sq_nonneg y₁, sq_abs y, mul_nonneg (abs_nonneg y) hY.le, sq_nonneg Y]

/-- **`lem:growth` (E08), strip form.** -/
theorem growthBound (M : Multiplier Λ Ω Ω' a) (hΩ : 0 < Ω) (hY : 0 < Ω'.im) :
    M.GrowthBound := by
  intro D k b hkb z
  have hΩc : (Ω : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hΩ.ne'
  -- floor decomposition
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = ⌊z.im / Ω'.im⌋ := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l : ℤ, l = ⌊(z - n * Ω').re / Ω⌋ := ⟨_, rfl⟩
  obtain ⟨z₁, hz₁⟩ : ∃ z₁ : ℂ, z₁ = z - l * Ω - n * Ω' := ⟨_, rfl⟩
  have hz : z = z₁ + l * Ω + n * Ω' := by rw [hz₁]; ring
  have hre : z₁.re = (z - n * Ω').re - l * Ω := by rw [hz₁]; simp <;> ring
  have him : z₁.im = z.im - n * Ω'.im := by rw [hz₁]; simp <;> ring
  have hn1 : (n : ℝ) ≤ z.im / Ω'.im := by rw [hn]; exact Int.floor_le _
  have hn2 : z.im / Ω'.im < n + 1 := by rw [hn]; exact Int.lt_floor_add_one _
  have hl1 : (l : ℝ) ≤ (z - n * Ω').re / Ω := by rw [hl]; exact Int.floor_le _
  have hl2 : (z - n * Ω').re / Ω < l + 1 := by rw [hl]; exact Int.lt_floor_add_one _
  rw [le_div_iff₀ hY] at hn1
  rw [div_lt_iff₀ hY] at hn2
  rw [le_div_iff₀ hΩ] at hl1
  rw [div_lt_iff₀ hΩ] at hl2
  have hmem : z₁ ∈ rect Ω Ω'.im := by
    simp only [rect, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hre]; linarith
    · rw [hre]; linarith
    · rw [him]; linarith
    · rw [him]; nlinarith
  obtain ⟨h0, h1, h2⟩ := M.norm_le_Sstar hmem
  have hS := M.one_le_Sstar
  -- translate
  have t0 := M.translate₀ hΩc l n z₁
  have t1 := M.translate₁ hΩc l n z₁
  have t2 := M.translate₂ hΩc l n z₁
  rw [← hz] at t0 t1 t2
  set E : ℂ := Complex.exp (-(2 * Real.pi * Complex.I / Ω) * (2 * n * z₁ + n ^ 2 * Ω')) with hE
  have hEn : ‖E‖ = Real.exp (2 * Real.pi / Ω * (2 * n * z₁.im + n ^ 2 * Ω'.im)) :=
    norm_transport (Ω' := Ω') hΩ n z₁
  -- exponent bound
  have hnY : (n : ℝ) * Ω'.im = z.im - z₁.im := by rw [him]; ring
  have hexp := exponent_le hY hnY
  have hexp2 : 2 * Real.pi / Ω * (2 * n * z₁.im + n ^ 2 * Ω'.im) ≤
      M.chi * (|z.im| + Ω'.im) ^ 2 := by
    have hpos : 0 ≤ 2 * Real.pi / Ω := by positivity
    calc 2 * Real.pi / Ω * (2 * n * z₁.im + n ^ 2 * Ω'.im)
        ≤ 2 * Real.pi / Ω * ((|z.im| + Ω'.im) ^ 2 / Ω'.im) := mul_le_mul_of_nonneg_left hexp hpos
      _ = M.chi * (|z.im| + Ω'.im) ^ 2 := by
        unfold Multiplier.chi
        ring
  have hEle : ‖E‖ ≤ Real.exp (M.chi * (|z.im| + Ω'.im) ^ 2) := by
    rw [hEn]; exact Real.exp_le_exp.2 hexp2
  -- assemble
  set p := D - k - 2 * b with hp
  have hD : D = p + k + 2 * b := by omega
  have hnorm : ‖M.F₀ z ^ p * M.F₁ z ^ k * M.F₂ z ^ b‖ =
      (‖M.F₀ z₁‖ ^ p * ‖M.F₁ z₁‖ ^ k * ‖M.F₂ z₁‖ ^ b) * ‖E‖ ^ D := by
    rw [t0, t1, t2]
    have : ‖E‖ ^ D = ‖E‖ ^ p * ‖E‖ ^ k * (‖E‖ ^ 2) ^ b := by
      rw [← pow_mul, ← pow_add, ← pow_add, ← hD]
    rw [this]
    simp only [norm_mul, norm_pow, mul_pow]
    ring
  have hP : ‖M.F₀ z₁‖ ^ p * ‖M.F₁ z₁‖ ^ k * ‖M.F₂ z₁‖ ^ b ≤ M.Sstar ^ D := by
    calc ‖M.F₀ z₁‖ ^ p * ‖M.F₁ z₁‖ ^ k * ‖M.F₂ z₁‖ ^ b
        ≤ M.Sstar ^ p * M.Sstar ^ k * M.Sstar ^ b := by gcongr
      _ = M.Sstar ^ (p + k + b) := by rw [← pow_add, ← pow_add]
      _ ≤ M.Sstar ^ D := pow_le_pow_right₀ hS (by omega)
  have hQ : ‖E‖ ^ D ≤ Real.exp (D * M.chi * (|z.im| + Ω'.im) ^ 2) := by
    calc ‖E‖ ^ D ≤ (Real.exp (M.chi * (|z.im| + Ω'.im) ^ 2)) ^ D :=
          pow_le_pow_left₀ (norm_nonneg _) hEle D
      _ = Real.exp (D * M.chi * (|z.im| + Ω'.im) ^ 2) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hnorm]
  exact mul_le_mul hP hQ (by positivity) (pow_nonneg (by linarith) _)

end Multiplier

/-- The growth bound for the multiplier of an integral model. -/
theorem IntegralModel.growthBound (M : IntegralModel) : M.multiplier.GrowthBound :=
  M.multiplier.growthBound M.Ω_pos M.Y_pos

end

end CatalanCore.Elliptic
