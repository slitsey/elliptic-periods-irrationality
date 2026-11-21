module

public import CatalanCore.Elliptic.Interfaces
public import CatalanCore.Elliptic.Chart.Formal
public import CatalanCore.Elliptic.EPA.Packet
public import CatalanCore.Elliptic.EPA.Epa
public import CatalanCore.Elliptic.Arith.Lower
public import CatalanCore.Elliptic.Analytic.BoundMain
public import CatalanCore.Elliptic.Analytic.BoundRecon
public import CatalanCore.Elliptic.Analytic.Multiplier
public import CatalanCore.Elliptic.Params.System
public import CatalanCore.Elliptic.Params.Counting
public import CatalanCore.Elliptic.Lattice.Integral
public import CatalanCore.Elliptic.Lattice.RealPoints
public import CatalanCore.Elliptic.Lattice.Divisor
public import CatalanCore.Measure.TiedNV

/-!
# Assembly (W2): `thm:omega` (E18) and `thm:main` (E01), unconditional

* `EPAStatement`: the nonvanishing theorem `thm:epa` (Chudnovsky--Chudnovsky, Cor. 13.5), stated for
  the packet map of `EPA/Packet.lean` with the quantifier order of the paper (`D_EPA` before the
  centres, `H₀` after), for every weight system satisfying the hypotheses of `thm:epa`
  (`epaA`, `epaEps`, `epaC4`, `epaQ`, `EpaAdmissible`). It is proved as `epaStatement_holds` from
  `EPA.epa` (row E09.12) and used by every theorem below.
* `thm_omega` (E18, `thm:omega`): for `ν > 3` only finitely many `(p, q)`, `q ≥ 1`, have
  `|Ω − p/q| ≤ q^{-ν}`. Proof: the paper's four steps. Parameters `prop_params` (E2); the weights
  `w_i = ⌈log q_i⌉` chosen in turn from the infinite set; `PacketSurjective` ⟹ `Δ_H ≠ 0` (D1);
  `arith_lower_bound` (B3) against `IntegralModel.analytic_upper_bound` (C5), with `e_H → 0`,
  `c_H → c_∞ > 2` (`cor_limits_weights`, E3).
* `real_period_measure_three` (E01, `thm:main` in the lattice form of plan D1): the plain-measure
  form for `L : PeriodPair` with rational `g₂, g₃`, from E18, the integral model (A1, A5) and the
  scaling lemma `plain_measure_smul` (E1).
-/

@[expose] public section

open Filter Topology

namespace CatalanCore.Elliptic

/-! ### The EPA hypothesis (`thm:epa`) -/

/-- `A_n(s) = 2 (n+2)^{n+2} (1 + (n+2)/s)^{n+2}` of `thm:epa`. -/
def epaA (n : ℕ) (s : ℚ) : ℚ :=
  2 * ((n : ℚ) + 2) ^ (n + 2) * (1 + ((n : ℚ) + 2) / s) ^ (n + 2)

/-- `ε₀ = min {σ₀, σ₀ v₀ / (4 (1 + σ₀) w₀)}` of `thm:epa`. -/
def epaEps (σ₀ w₀ v₀ : ℚ) : ℚ := min σ₀ (σ₀ * v₀ / (4 * (1 + σ₀) * w₀))

/-- `C₄ = A_m(σ₀) + 4 · 2^{m+3} A_{m+1}(ε₀)` of `thm:epa`. -/
def epaC4 (m : ℕ) (σ₀ w₀ v₀ : ℚ) : ℚ :=
  epaA m σ₀ + 4 * 2 ^ (m + 3) * epaA (m + 1) (epaEps σ₀ w₀ v₀)

/-- `q_* = θ^m min {1, w₀} / max {1, v₀}` of `thm:epa`. -/
def epaQ (m : ℕ) (w₀ v₀ θ : ℚ) : ℚ := θ ^ m * min 1 w₀ / max 1 v₀

/-- The choice of `σ₀` and the thresholds on `w₁, …, w_m` in `thm:epa` (the three conditions on
`σ₀` and eq:epa-thresholds; the index `i` is `0`-based, `l < i` is `1 ≤ l < i`). -/
def EpaAdmissible {m : ℕ} (K : ℕ) (W : Weights m) (σ₀ : ℚ) : Prop :=
  0 < σ₀ ∧
  (1 + 3 * σ₀) ^ (m + 1) * ((K : ℚ) * (W.w₀ / W.v₀) * W.θ ^ m) < 1 ∧
  (1 + 3 * σ₀) ^ m * ((K : ℚ) * W.θ ^ m) < 1 ∧
  (1 + σ₀) * W.θ < 1 ∧
  ∀ i : Fin m, max 1 (epaC4 m σ₀ W.w₀ W.v₀ / epaQ m W.w₀ W.v₀ W.θ *
      ∏ l ∈ Finset.univ.filter (fun l : Fin m => l < i), W.w l) < W.w i

/-- **`thm:epa`** (CM Cor. 13.5), in the form consumed by the assembly. For every chart
`(A, B, a)`, every `m, K ≥ 1`, every weight system with `θ < 1`, `K w₀ θ^m / v₀ < 1`, `K θ^m < 1`,
every rational `σ₀` and thresholds as in the paper, there is `D_EPA > 0`, independent of the centres,
such that for every centre array injective in each coordinate there is `H₀` such that for all
integers `H ≥ H₀` divisible by `D_EPA` the packet map is surjective (`PacketSurjective`, whose
quantifier order is that of the paper; the centres are rational, as in the application). -/
def EPAStatement : Prop :=
  ∀ (ch : OriginChart) (s : OriginSeries ch) (m K : ℕ), 1 ≤ m → 1 ≤ K → ∀ (W : Weights m),
    (K : ℚ) * (W.w₀ / W.v₀) * W.θ ^ m < 1 → (K : ℚ) * W.θ ^ m < 1 →
    ∀ σ₀ : ℚ, EpaAdmissible K W σ₀ → PacketSurjective W K s

/-- Translation of `EpaAdmissible` to the hypotheses of `EPA.epa`: the first four conjuncts are
`EpaSigma` and the threshold conjunct is `EpaThresholds` (`max_lt_iff`; `epaC4, epaQ` unfold to
`C4, qStar`). -/
theorem epaAdmissible_iff {m : ℕ} (K : ℕ) (W : Weights m) (σ₀ : ℚ) :
    EpaAdmissible K W σ₀ ↔ EPA.EpaSigma m K W σ₀ ∧ EPA.EpaThresholds W σ₀ := by
  have hC : epaC4 m σ₀ W.w₀ W.v₀ = EPA.C4 W σ₀ := rfl
  have hQ : epaQ m W.w₀ W.v₀ W.θ = EPA.qStar W := rfl
  constructor
  · rintro ⟨h0, h1, h2, h3, h4⟩
    refine ⟨⟨h0, h1, h2, h3⟩, fun i => ?_⟩
    have := h4 i
    rw [hC, hQ, max_lt_iff] at this
    exact this
  · rintro ⟨⟨h0, h1, h2, h3⟩, h4⟩
    refine ⟨h0, h1, h2, h3, fun i => ?_⟩
    rw [hC, hQ, max_lt_iff]
    exact h4 i

/-- **`thm:epa` discharged**: the hypothesis `EPAStatement` holds, by `EPA.epa` (row E09.12). -/
theorem epaStatement_holds : EPAStatement := by
  intro ch s m K hm hK W _ _ σ₀ hadm
  obtain ⟨hσ, hthr⟩ := (epaAdmissible_iff K W σ₀).mp hadm
  exact EPA.epa hm W s σ₀ hσ hthr

/-! ### Elementary lemmas -/

/-- The pairs `(p, q)`, `q ≥ 1`, with `|Ω − p/q| ≤ q^{−ν}`. -/
def omegaApprox (Ω ν : ℝ) : Set (ℤ × ℕ) :=
  {x | 1 ≤ x.2 ∧ |Ω - (x.1 : ℝ) / (x.2 : ℝ)| ≤ (x.2 : ℝ) ^ (-ν)}

theorem mem_omegaApprox_iff {Ω ν : ℝ} {x : ℤ × ℕ} :
    x ∈ omegaApprox Ω ν ↔ 1 ≤ x.2 ∧ |Ω - (x.1 : ℝ) / (x.2 : ℝ)| ≤ (x.2 : ℝ) ^ (-ν) := Iff.rfl

/-- `σ₀` exists (the three strict inequalities hold for small `σ₀ > 0`, by continuity). -/
theorem exists_sigma (m : ℕ) {X Y θ : ℚ} (hX : X < 1) (hY : Y < 1) (hθ : θ < 1) :
    ∃ σ : ℚ, 0 < σ ∧ (1 + 3 * σ) ^ (m + 1) * X < 1 ∧ (1 + 3 * σ) ^ m * Y < 1 ∧
      (1 + σ) * θ < 1 := by
  have c1 : ContinuousAt (fun x : ℝ => (1 + 3 * x) ^ (m + 1) * (X : ℝ)) 0 := by fun_prop
  have c2 : ContinuousAt (fun x : ℝ => (1 + 3 * x) ^ m * (Y : ℝ)) 0 := by fun_prop
  have c3 : ContinuousAt (fun x : ℝ => (1 + x) * (θ : ℝ)) 0 := by fun_prop
  have e1 : (fun x : ℝ => (1 + 3 * x) ^ (m + 1) * (X : ℝ)) 0 < 1 := by
    simpa using (by exact_mod_cast hX : (X : ℝ) < 1)
  have e2 : (fun x : ℝ => (1 + 3 * x) ^ m * (Y : ℝ)) 0 < 1 := by
    simpa using (by exact_mod_cast hY : (Y : ℝ) < 1)
  have e3 : (fun x : ℝ => (1 + x) * (θ : ℝ)) 0 < 1 := by
    simpa using (by exact_mod_cast hθ : (θ : ℝ) < 1)
  have key := (Filter.Tendsto.eventually c1 (gt_mem_nhds e1)).and
    ((Filter.Tendsto.eventually c2 (gt_mem_nhds e2)).and
      (Filter.Tendsto.eventually c3 (gt_mem_nhds e3)))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp key
  obtain ⟨σ, hσ0, hσε⟩ := exists_rat_btwn hε
  have hd : dist (σ : ℝ) 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hσ0]
    exact hσε
  obtain ⟨h1, h2, h3⟩ := hball hd
  refine ⟨σ, by exact_mod_cast hσ0, ?_, ?_, ?_⟩
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h3

/-- The set of approximations is unbounded in `q` (away from `p = 0`) when it is infinite. -/
theorem exists_large_pair {Ω ν : ℝ} (hΩ : 0 < Ω) (hν : 1 ≤ ν)
    (hinf : (omegaApprox Ω ν).Infinite) (N : ℕ) :
    ∃ x ∈ omegaApprox Ω ν, x.1 ≠ 0 ∧ N < x.2 := by
  by_contra hcon
  push_neg at hcon
  set N' : ℕ := max N ⌈1 / Ω⌉₊ with hN'
  set B : ℤ := ⌈(Ω + 1) * (N' : ℝ)⌉ with hB
  refine hinf (Set.Finite.subset (Finset.finite_toSet (Finset.Icc (-B) B ×ˢ Finset.Icc 1 N')) ?_)
  intro x hx
  obtain ⟨hx1, hx2⟩ := mem_omegaApprox_iff.mp hx
  have hq1 : (1 : ℝ) ≤ (x.2 : ℝ) := Nat.one_le_cast.mpr hx1
  have hqpos : (0 : ℝ) < (x.2 : ℝ) := by linarith
  have hrp1 : (x.2 : ℝ) ^ (-ν) ≤ (x.2 : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hrp1' : (x.2 : ℝ) ^ (-1 : ℝ) = ((x.2 : ℝ))⁻¹ := Real.rpow_neg_one _
  have hrp2 : (x.2 : ℝ) ^ (-ν) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1 (by linarith)
  have hxN : x.2 ≤ N' := by
    by_cases h0 : x.1 = 0
    · have h1 : Ω ≤ ((x.2 : ℝ))⁻¹ := by
        have := hx2
        rw [h0] at this
        simp only [Int.cast_zero, zero_div, sub_zero, abs_of_pos hΩ] at this
        linarith
      have h2 : (x.2 : ℝ) ≤ 1 / Ω := by
        rw [le_div_iff₀ hΩ]
        have : Ω * (x.2 : ℝ) ≤ 1 := by
          calc Ω * (x.2 : ℝ) ≤ ((x.2 : ℝ))⁻¹ * (x.2 : ℝ) :=
                mul_le_mul_of_nonneg_right h1 hqpos.le
            _ = 1 := inv_mul_cancel₀ hqpos.ne'
        linarith
      have h3 : (x.2 : ℝ) ≤ (⌈1 / Ω⌉₊ : ℝ) := h2.trans (Nat.le_ceil _)
      have h4 : x.2 ≤ ⌈1 / Ω⌉₊ := by exact_mod_cast h3
      exact h4.trans (le_max_right _ _)
    · exact (hcon x hx h0).trans (le_max_left _ _)
  have hpabs : |(x.1 : ℝ)| ≤ (Ω + 1) * (x.2 : ℝ) := by
    have h1 : |(x.1 : ℝ) / (x.2 : ℝ)| ≤ Ω + 1 := by
      have := abs_sub_abs_le_abs_sub ((x.1 : ℝ) / (x.2 : ℝ)) Ω
      rw [abs_sub_comm] at this
      have h5 : |Ω| = Ω := abs_of_pos hΩ
      linarith
    rw [abs_div, abs_of_pos hqpos, div_le_iff₀ hqpos] at h1
    exact h1
  have hpN : (Ω + 1) * (x.2 : ℝ) ≤ (Ω + 1) * (N' : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hxN) (by linarith)
  have hpB : |(x.1 : ℝ)| ≤ (B : ℝ) := hpabs.trans (hpN.trans (Int.le_ceil _))
  have hpB' : |x.1| ≤ B := by exact_mod_cast hpB
  rw [abs_le] at hpB'
  exact Finset.mem_coe.mpr (Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr hpB', Finset.mem_Icc.mpr ⟨hx1, hxN⟩⟩)

/-- For every `T` there is an approximation with `p ≠ 0` and `log q > T`. -/
theorem exists_pair_log_gt {Ω ν : ℝ} (hΩ : 0 < Ω) (hν : 1 ≤ ν)
    (hinf : (omegaApprox Ω ν).Infinite) (T : ℝ) :
    ∃ x ∈ omegaApprox Ω ν, x.1 ≠ 0 ∧ T < Real.log (x.2 : ℝ) := by
  obtain ⟨x, hx, hx0, hxN⟩ := exists_large_pair hΩ hν hinf ⌈Real.exp T⌉₊
  refine ⟨x, hx, hx0, ?_⟩
  have h1 : Real.exp T < (x.2 : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hxN)
  exact (Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos T) h1)).mpr h1

/-- Step 4 of `thm:omega`, the two cases (pure real arithmetic). -/
theorem final_arith {Lg Ear Ean eH cH bb ν a₀ γ θ g δ : ℝ}
    (hlow : -(1 - bb) - Ear ≤ Lg)
    (hup : Lg ≤ Ean + eH + max (-cH) (-(ν * (a₀ * (1 - γ) - bb))))
    (hbb0 : 0 ≤ bb) (hbbθ : bb < θ) (hν : 1 < ν)
    (hg : g = ν * (a₀ * (1 - γ) - θ) - (1 - θ))
    (hE : Ear + Ean < 2 * δ) (hδg : δ ≤ g / 4) (hδ1 : δ ≤ 1 / 4)
    (heH : eH < 2 * δ) (hc : 2 < cH) : False := by
  rcases max_cases (-cH) (-(ν * (a₀ * (1 - γ) - bb))) with ⟨hmx, -⟩ | ⟨hmx, -⟩
  · rw [hmx] at hup
    linarith
  · rw [hmx] at hup
    have h1 := mul_lt_mul_of_pos_left hbbθ (sub_pos.mpr hν)
    nlinarith

/-! ### E18: `thm:omega` for rational `ν` -/

/-- **E18 (`thm:omega`), rational exponent**. -/
theorem thm_omega_rat (Mod : IntegralModel) {ν : ℚ} (hν : 3 < ν) :
    (omegaApprox Mod.Ω (ν : ℝ)).Finite := by
  by_contra hinf
  have hν3 : (3 : ℝ) < (ν : ℝ) := by exact_mod_cast hν
  have hν1 : (1 : ℝ) ≤ (ν : ℝ) := by linarith
  have hν0 : (0 : ℝ) ≤ (ν : ℝ) := by linarith
  have hΩ : 0 < Mod.Ω := Mod.Ω_pos
  obtain ⟨P, -, hP1, hP2, hP3, hP4, hP5⟩ := prop_params hν
  -- positivity and size facts for the parameters
  have hθ0 : (0 : ℚ) < Params.θ ν := (Params.abc_a hν).2.2.2.2.1
  have hθ1 : Params.θ ν < 1 := by
    show 1 - Params.h ν < 1
    linarith [Params.h_pos hν]
  have hθ0r : (0 : ℝ) < ((Params.θ ν : ℚ) : ℝ) := by exact_mod_cast hθ0
  have ha0q : (0 : ℚ) < Params.a₀ ν := lt_trans hθ0 (Params.abc_a hν).2.2.2.2.2.1
  have ha0 : (0 : ℝ) < ((Params.a₀ ν : ℚ) : ℝ) := by exact_mod_cast ha0q
  have hγq : (0 : ℚ) ≤ Params.γ ν := by
    rw [Params.γ_eq hν]
    positivity
  have hγ0 : (0 : ℝ) ≤ ((Params.γ ν : ℚ) : ℝ) := by exact_mod_cast hγq
  have hgq : (0 : ℚ) < Params.g ν :=
    lt_of_lt_of_le (Params.abc_c hν).2 (Params.abc_c hν).1
  have hgr : (0 : ℝ) < ((Params.g ν : ℚ) : ℝ) := by exact_mod_cast hgq
  have hgeq : ((Params.g ν : ℚ) : ℝ) = (ν : ℝ) * (((Params.a₀ ν : ℚ) : ℝ) *
      (1 - ((Params.γ ν : ℚ) : ℝ)) - ((Params.θ ν : ℚ) : ℝ)) - (1 - ((Params.θ ν : ℚ) : ℝ)) := by
    unfold Params.g
    push_cast
    try ring
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (((Params.g ν : ℚ) : ℝ) / 4) (1 / 4) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; exact lt_min (by linarith) (by norm_num)
  have hδg : δ ≤ ((Params.g ν : ℚ) : ℝ) / 4 := by rw [hδ]; exact min_le_left _ _
  have hδ1 : δ ≤ 1 / 4 := by rw [hδ]; exact min_le_right _ _
  -- Step 1: the dimension `m`
  have hE : Tendsto (fun m : ℕ => Arith.lcmConst * (1 / ((Params.θ ν : ℚ) : ℝ)) /
      ((P.v₀ m : ℚ) : ℝ) + Mod.multiplier.CLam * ((P.K m : ℕ) : ℝ) ^ 2 /
        (2 * ((P.w₀ m : ℚ) : ℝ))) atTop (𝓝 0) := by
    have h1 := P.tendsto_const_div_v₀ hν (Arith.lcmConst * (1 / ((Params.θ ν : ℚ) : ℝ)))
    have h2 := hP3.const_mul (Mod.multiplier.CLam / 2)
    have h3 := h1.add h2
    rw [mul_zero, add_zero] at h3
    refine h3.congr (fun m => ?_)
    try dsimp only
    ring
  have hev := (eventually_ge_atTop 1).and
    ((hP1.eventually (gt_mem_nhds one_pos)).and
      ((hP5.eventually_gt_atTop 2).and (hE.eventually (gt_mem_nhds hδpos))))
  obtain ⟨m, hm1, hm2, hm3, hm4⟩ := hev.exists
  have hm2' : ((P.K m : ℕ) : ℝ) * ((Params.θ ν : ℚ) : ℝ) ^ m < 1 := hm2
  have hm4' : Arith.lcmConst * (1 / ((Params.θ ν : ℚ) : ℝ)) / ((P.v₀ m : ℚ) : ℝ) +
      Mod.multiplier.CLam * ((P.K m : ℕ) : ℝ) ^ 2 / (2 * ((P.w₀ m : ℚ) : ℝ)) < δ := hm4
  have hK1 : 1 ≤ P.K m := P.one_le_K hν m
  have hKpos : (0 : ℚ) < (P.K m : ℚ) := Nat.cast_pos.mpr hK1
  have hw0pos : (0 : ℚ) < P.w₀ m := by
    unfold ParamChoice.w₀
    exact inv_pos.mpr (pow_pos (P.c₂_pos hν) m)
  have hv0pos : (0 : ℚ) < P.v₀ m := by
    unfold ParamChoice.v₀
    exact mul_pos (mul_pos (mul_pos (by norm_num) hKpos) (pow_pos hθ0 m)) hw0pos
  -- the quantity `X = K (w₀/v₀) θ^m = 1/4` and `Y = K θ^m`
  have hXeq : (P.K m : ℚ) * (P.w₀ m / P.v₀ m) * Params.θ ν ^ m = 1 / 4 := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    exact hP2 m
  have hYlt : (P.K m : ℚ) * Params.θ ν ^ m < 1 := by exact_mod_cast hm2'
  obtain ⟨σ₀, hσ0, hσ1, hσ2, hσ3⟩ := exists_sigma m (X := (P.K m : ℚ) * (P.w₀ m / P.v₀ m) *
    Params.θ ν ^ m) (Y := (P.K m : ℚ) * Params.θ ν ^ m) (θ := Params.θ ν)
    (by rw [hXeq]; norm_num) hYlt hθ1
  -- Step 2: the threshold `w_*`
  obtain ⟨wmin, hwmin0, hwminδ⟩ : ∃ wmin : ℝ, 0 < wmin ∧
      ((ν : ℝ) + Real.log (4 * Mod.multiplier.rStar * ((P.K m : ℕ) : ℝ) ^ 2)) / wmin < δ := by
    obtain ⟨N0, hN0⟩ : ∃ N0 : ℝ, N0 = (ν : ℝ) +
        Real.log (4 * Mod.multiplier.rStar * ((P.K m : ℕ) : ℝ) ^ 2) := ⟨_, rfl⟩
    rw [← hN0]
    have hpos : 0 < (|N0| + 1) / δ := div_pos (by positivity) hδpos
    refine ⟨(|N0| + 1) / δ, hpos, ?_⟩
    rw [div_lt_iff₀ hpos]
    have h1 : δ * ((|N0| + 1) / δ) = |N0| + 1 := by field_simp
    have h2 := le_abs_self N0
    linarith
  -- Step 2: choice of the pairs, in turn
  obtain ⟨c, hc⟩ : ∃ c : ℚ, c = epaC4 m σ₀ (P.w₀ m) (P.v₀ m) /
      epaQ m (P.w₀ m) (P.v₀ m) (Params.θ ν) := ⟨_, rfl⟩
  obtain ⟨Mq, hMq⟩ : ∃ Mq : ℚ → ℚ, ∀ P : ℚ, Mq P = max 1 (c * P) :=
    ⟨fun P => max 1 (c * P), fun _ => rfl⟩
  obtain ⟨pick, hpick⟩ : ∃ pick : ℝ → ℤ × ℕ, ∀ T : ℝ, pick T ∈ omegaApprox Mod.Ω (ν : ℝ) ∧
      (pick T).1 ≠ 0 ∧ T < Real.log ((pick T).2 : ℝ) := by
    choose f hf using fun T : ℝ => exists_pair_log_gt hΩ hν1 hinf T
    exact ⟨f, hf⟩
  obtain ⟨st, hst0, hstS⟩ : ∃ st : ℕ → ℚ, st 0 = 1 ∧ ∀ n, st (n + 1) = st n *
      ((Params.logWeight (pick (max ((Mq (st n) : ℚ) : ℝ) wmin)).2 : ℕ) : ℚ) :=
    ⟨fun n => Nat.rec (motive := fun _ => ℚ) 1 (fun _ P => P *
      ((Params.logWeight (pick (max ((Mq P : ℚ) : ℝ) wmin)).2 : ℕ) : ℚ)) n, rfl, fun n => rfl⟩
  obtain ⟨xs, hxs⟩ : ∃ xs : ℕ → ℤ × ℕ, ∀ n, xs n = pick (max ((Mq (st n) : ℚ) : ℝ) wmin) :=
    ⟨fun n => pick (max ((Mq (st n) : ℚ) : ℝ) wmin), fun n => rfl⟩
  have hstS' : ∀ n, st (n + 1) = st n * ((Params.logWeight (xs n).2 : ℕ) : ℚ) := by
    intro n
    rw [hstS n, hxs n]
  have hxsS : ∀ n, xs n ∈ omegaApprox Mod.Ω (ν : ℝ) := fun n => by
    rw [hxs n]; exact (hpick _).1
  have hxs0 : ∀ n, (xs n).1 ≠ 0 := fun n => by
    rw [hxs n]; exact (hpick _).2.1
  have hxsT : ∀ n, max ((Mq (st n) : ℚ) : ℝ) wmin < Real.log ((xs n).2 : ℝ) := fun n => by
    rw [hxs n]; exact (hpick _).2.2
  have hq1 : ∀ n, 1 ≤ (xs n).2 := fun n => (mem_omegaApprox_iff.mp (hxsS n)).1
  have hq2 : ∀ n, 2 ≤ (xs n).2 := by
    intro n
    by_contra hlt
    push_neg at hlt
    have h1 : ((xs n).2 : ℝ) ≤ 1 := by
      have : (xs n).2 ≤ 1 := by omega
      exact_mod_cast this
    have h2 : Real.log ((xs n).2 : ℝ) ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h1
    have h3 : (1 : ℝ) ≤ ((Mq (st n) : ℚ) : ℝ) := by
      rw [hMq]
      exact_mod_cast le_max_left _ _
    have h4 := hxsT n
    have h5 : ((Mq (st n) : ℚ) : ℝ) ≤ max ((Mq (st n) : ℚ) : ℝ) wmin := le_max_left _ _
    linarith
  have hprod : ∀ n, ∏ l ∈ Finset.range n, ((Params.logWeight (xs l).2 : ℕ) : ℚ) = st n := by
    intro n
    induction n with
    | zero => simp [hst0]
    | succ n ih => rw [Finset.prod_range_succ, ih, hstS' n]
  -- the weight system
  obtain ⟨W, hW0, hWv, hWθ, hWw⟩ : ∃ W : Weights m, W.w₀ = P.w₀ m ∧ W.v₀ = P.v₀ m ∧
      W.θ = Params.θ ν ∧ ∀ i : Fin m, W.w i = ((Params.logWeight (xs i).2 : ℕ) : ℚ) :=
    ⟨{ w₀ := P.w₀ m, v₀ := P.v₀ m, θ := Params.θ ν,
       w := fun i => ((Params.logWeight (xs i).2 : ℕ) : ℚ),
       w₀_pos := hw0pos, v₀_pos := hv0pos, θ_pos := hθ0, θ_lt_one := hθ1,
       w_pos := fun i => Nat.cast_pos.mpr (Params.logWeight_pos (hq2 i)) },
      rfl, rfl, rfl, fun _ => rfl⟩
  have hWwr : ∀ i : Fin m, ((W.w i : ℚ) : ℝ) = ((Params.logWeight (xs i).2 : ℕ) : ℝ) :=
    fun i => by rw [hWw i, Rat.cast_natCast]
  have hthr : ∀ i : Fin m, max 1 (epaC4 m σ₀ W.w₀ W.v₀ / epaQ m W.w₀ W.v₀ W.θ *
      ∏ l ∈ Finset.univ.filter (fun l : Fin m => l < i), W.w l) < W.w i := by
    intro i
    have himg : (Finset.univ.filter (fun l : Fin m => l < i)).image Fin.val =
        Finset.range i.val := by
      ext n
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
      constructor
      · rintro ⟨l, hl, rfl⟩
        exact hl
      · intro hn
        exact ⟨⟨n, lt_trans hn i.2⟩, hn, rfl⟩
    have himg2 := Finset.prod_image (f := fun n : ℕ => ((Params.logWeight (xs n).2 : ℕ) : ℚ))
      (s := Finset.univ.filter (fun l : Fin m => l < i)) (g := Fin.val) Fin.val_injective.injOn
    rw [himg] at himg2
    have hprodF : ∏ l ∈ Finset.univ.filter (fun l : Fin m => l < i), W.w l = st i := by
      rw [← hprod i, himg2]
      exact Finset.prod_congr rfl (fun l _ => hWw l)
    rw [hprodF, hW0, hWv, hWθ, ← hc, hWw i, ← hMq (st i)]
    have h1 : ((Mq (st i) : ℚ) : ℝ) < ((Params.logWeight (xs i).2 : ℕ) : ℝ) :=
      lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) (hxsT i)) (Params.log_le_logWeight _)
    exact_mod_cast h1
  have hbase1 : (P.K m : ℚ) * (W.w₀ / W.v₀) * W.θ ^ m < 1 := by
    rw [hW0, hWv, hWθ, hXeq]; norm_num
  have hbase2 : (P.K m : ℚ) * W.θ ^ m < 1 := by rw [hWθ]; exact hYlt
  have hadm : EpaAdmissible (P.K m) W σ₀ := by
    refine ⟨hσ0, ?_, ?_, ?_, hthr⟩
    · rw [hW0, hWv, hWθ]; exact hσ1
    · rw [hWθ]; exact hσ2
    · rw [hWθ]; exact hσ3
  -- Step 3: EPA gives the nonzero minor
  have hsurj := epaStatement_holds Mod.chart Mod.chart.series m (P.K m) hm1 hK1 W hbase1 hbase2 σ₀ hadm
  obtain ⟨D, hD, hall⟩ := packetMinor_of_packetSurjective W (P.K m) Mod.chart.series hsurj
  have hinj : ∀ i : Fin m, Function.Injective fun j : Fin (P.K m) =>
      gridCentres (P.K m) (fun i : Fin m => (xs i).1) (fun i : Fin m => (xs i).2) j i := by
    intro i j j' h
    have hq : (((xs i).2 : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp (hq1 i))
    have hp : (((xs i).1 : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (hxs0 i)
    have h' : ((j : ℕ) : ℚ) * (((xs i).1 : ℤ) : ℚ) / (((xs i).2 : ℕ) : ℚ) =
        ((j' : ℕ) : ℚ) * (((xs i).1 : ℤ) : ℚ) / (((xs i).2 : ℕ) : ℚ) := h
    have h1 := (div_left_inj' hq).mp h'
    have h2 : ((j : ℕ) : ℚ) = ((j' : ℕ) : ℚ) := mul_right_cancel₀ hp h1
    exact Fin.ext (by exact_mod_cast h2)
  obtain ⟨H₀, hH₀⟩ := hall (gridCentres (P.K m) (fun i : Fin m => (xs i).1)
    (fun i : Fin m => (xs i).2)) hinj
  -- the integers `H = D (n + H₀ + 1)`
  have hHt : Tendsto (fun n : ℕ => ((D * (n + H₀ + 1) : ℕ) : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    exact Nat.cast_le.mpr (le_trans (by omega : n ≤ n + H₀ + 1)
      (le_mul_of_one_le_left (Nat.zero_le _) hD))
  -- limits of `e_H` and `c_H` (cor:limits)
  have hlim := Params.cor_limits_weights W (fun i : Fin m => Params.logWeight (xs i).2) hWw
    (fun i => Params.logWeight_pos (hq2 i)) Mod.multiplier.CLam hK1 ha0 ((Params.γ ν : ℚ) : ℝ)
  have hcinf : 2 < cInfty W (P.K m) ((Params.a₀ ν : ℚ) : ℝ) ((Params.γ ν : ℚ) : ℝ) := by
    rw [P.cInfty_eq W hWθ hWv]
    exact hm3
  have hev2 := ((hlim.1.comp hHt).eventually (gt_mem_nhds (by linarith : (0 : ℝ) < 2 * δ))).and
    ((hlim.2.comp hHt).eventually (lt_mem_nhds hcinf))
  obtain ⟨n, hn1, hn2⟩ := hev2.exists
  -- Step 4: the two bounds for one large `H`
  have hHpos : (0 : ℝ) < ((D * (n + H₀ + 1) : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.mul_pos hD (Nat.succ_pos _))
  obtain ⟨sel, -, hΔ⟩ := hH₀ (D * (n + H₀ + 1))
    (le_trans (by omega : H₀ ≤ n + H₀ + 1) (le_mul_of_one_le_left (Nat.zero_le _) hD))
    (dvd_mul_right _ _)
  have hF₀ : 1 / ((W.θ : ℚ) : ℝ) ≤ 1 / ((Params.θ ν : ℚ) : ℝ) := le_of_eq (by rw [hWθ])
  have hlow := Arith.arith_lower_bound hK1 W Mod.chart.series (fun i : Fin m => (xs i).1)
    (fun i : Fin m => (xs i).2) (fun i => hq1 i)
    (fun i => by rw [hWwr i]; exact Params.log_le_logWeight _)
    (1 / ((Params.θ ν : ℚ) : ℝ)) hF₀ hHpos sel hΔ
  have hup := Mod.analytic_upper_bound Mod.chart.series hK1 W (fun i : Fin m => (xs i).1)
    (fun i : Fin m => (xs i).2) hν0 (fun i => (mem_omegaApprox_iff.mp (hxsS i)).2)
    (fun i => Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp (hq1 i)))
    (fun i => by rw [hWwr i]; exact Params.logWeight_sub_one_lt _) hwmin0
    (fun i => by
      rw [hWwr i]
      exact (le_max_right _ _).trans ((hxsT i).le.trans (Params.log_le_logWeight _)))
    ha0 hγ0 hHpos sel hΔ
  unfold ArithLowerBound at hlow
  unfold AnalyticUpperBound at hup
  rw [hWv] at hlow
  rw [hW0] at hup
  have hn1' : eH W (P.K m) Mod.multiplier.CLam ((D * (n + H₀ + 1) : ℕ) : ℝ) < 2 * δ := hn1
  have hn2' : 2 < cH W (P.K m) ((Params.a₀ ν : ℚ) : ℝ) ((Params.γ ν : ℚ) : ℝ)
      ((D * (n + H₀ + 1) : ℕ) : ℝ) := hn2
  have hbb0 := W.bbar_nonneg (P.K m) hHpos.le
  have hbbθ := W.bbar_lt_theta hK1 hHpos
  rw [hWθ] at hbbθ
  exact final_arith hlow hup hbb0 hbbθ (by linarith) hgeq (by linarith [hm4', hwminδ]) hδg hδ1
    hn1' hn2'

/-- **E18 (`thm:omega`)**: for every `ν > 3` there
are only finitely many `(p, q)`, `q ≥ 1`, with `|Ω − p/q| ≤ q^{−ν}`. -/
theorem thm_omega (Mod : IntegralModel) (ν : ℝ) (hν : 3 < ν) :
    {x : ℤ × ℕ | 1 ≤ x.2 ∧ |Mod.Ω - (x.1 : ℝ) / (x.2 : ℝ)| ≤ (x.2 : ℝ) ^ (-ν)}.Finite := by
  obtain ⟨ν', h3, hlt⟩ := exists_rat_btwn hν
  have hfin := thm_omega_rat Mod (ν := ν') (by exact_mod_cast h3)
  refine hfin.subset ?_
  intro x hx
  obtain ⟨h1, h2⟩ := hx
  refine mem_omegaApprox_iff.mpr ⟨h1, h2.trans ?_⟩
  exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr h1) (by linarith)

/-! ### E01: `thm:main` in the plain-measure form (plan D1) -/

/-- **E01 (`thm:main`, lattice form, plain measure).** For a lattice
`L` with rational `g₂, g₃` and a nonzero real `ω ∈ L`, and `ε > 0`, for all large `q` and all integers
`p`, `q^{−(3+ε)} < |ω − p/q|`. -/
theorem real_period_measure_three (L : PeriodPair)
    (hg₂ : ∃ r : ℚ, L.g₂ = r) (hg₃ : ∃ r : ℚ, L.g₃ = r)
    (ω : ℝ) (hω : (ω : ℂ) ∈ L.lattice) (h0 : ω ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ, (q : ℝ) ^ (-(3 + ε)) < |ω - p / q| := by
  obtain ⟨d, A, B, Λ, hd, hΛL, hg2, hg3, hdisc, -, -⟩ :=
    CatalanCore.Elliptic.Lattice.exists_integral_model L hg₂ hg₃
  have hdpos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hmem : (((ω / d : ℝ)) : ℂ) ∈ Λ.lattice := by
    rw [hΛL]
    have : (d : ℂ) * (((ω / d : ℝ)) : ℂ) = (ω : ℂ) := by
      push_cast
      field_simp
    rw [this]
    exact hω
  obtain ⟨Ω, Ω', N, hΩ, hY, hN, hωN, hbasis, hreal⟩ :=
    CatalanCore.Elliptic.Lattice.exists_real_basis Λ (ω / d) hmem (div_ne_zero h0 hdpos.ne')
  obtain ⟨a, ha0, ha3, hfa⟩ := exists_chart_point A B
  obtain ⟨zQ, hzQ, hwp⟩ := CatalanCore.Elliptic.Lattice.exists_polar_point Λ (a : ℂ)
  obtain ⟨Mod, hMΩ⟩ : ∃ Mod : IntegralModel, Mod.Ω = Ω :=
    ⟨{ L := L, d := d, d_pos := hd, Λ := Λ, lattice_scale := hΛL, A := A, B := B,
       g₂_eq := hg2, g₃_eq := hg3, disc_ne := hdisc, Ω := Ω, Ω_pos := hΩ, Ω' := Ω',
       Y_pos := hY, lattice_basis := hbasis, real_points := hreal, a := a,
       a_range := ⟨ha0, ha3⟩, fa_ne := hfa, zQ := zQ, zQ_not_mem := hzQ, wp_zQ := hwp }, rfl⟩
  have hS : (omegaApprox Mod.Ω (3 + ε / 2)).Finite :=
    thm_omega Mod (3 + ε / 2) (by linarith)
  have hev : ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ, (q : ℝ) ^ (-(3 + ε / 2)) < |Ω - p / q| := by
    obtain ⟨Q, hQ⟩ := (hS.image Prod.snd).bddAbove
    filter_upwards [Filter.eventually_gt_atTop Q] with q hq p
    by_contra hcon
    push_neg at hcon
    have hmemS : (p, q) ∈ omegaApprox Mod.Ω (3 + ε / 2) :=
      mem_omegaApprox_iff.mpr ⟨by show 1 ≤ q; omega, by rw [hMΩ]; exact hcon⟩
    have h1 : q ≤ Q := hQ ⟨(p, q), hmemS, rfl⟩
    omega
  have hd0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN0 : (N : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hN
  have hr0 : (1 / ((d : ℚ) * (N : ℚ)) : ℚ) ≠ 0 := one_div_ne_zero (mul_ne_zero hd0 hN0)
  have hNr : (N : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hN
  have h1 : ω = (N : ℝ) * Ω * d := by
    rw [div_eq_iff hdpos.ne'] at hωN
    exact hωN
  have hr : (((1 / ((d : ℚ) * (N : ℚ)) : ℚ)) : ℝ) * ω = Ω := by
    push_cast
    rw [h1]
    field_simp
  exact CatalanCore.Measure.plain_measure_smul (r := 1 / ((d : ℚ) * (N : ℚ))) hr0
    (μ' := 3 + ε / 2) (μ := 3 + ε) (by linarith)
    (hev.mono fun q hq p => by rw [hr]; exact hq p)

end CatalanCore.Elliptic
