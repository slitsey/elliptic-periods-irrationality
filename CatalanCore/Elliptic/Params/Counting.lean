module

public import OAI.NumberTheory.PiExponent.Polynomials.SimplexLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Positivity.Basic

@[expose] public section

/-!
# E15, E15a: the counting limits of the interpolation determinant (paper `cor:limits`)

Paper: *A bound for the irrationality exponent of real elliptic periods*, Section "The interpolation
determinant" and Corollary `cor:limits` (Chudnovsky--Chudnovsky, Cor. 16.4).

Data, all fixed except the cutoff `H`:

* `w : Fin m → ℕ` positive integer weights (`w i = ⌈log q_i⌉`, `logWeight`), `W(β) = ∑ w i * β i`;
* `v₀ θ : ℚ` positive, `θ` the contraction ratio of the paper (`0 < θ < 1` is not needed here);
* `K : ℕ` with `1 ≤ K`, `a₀ γ C_Λ : ℝ` with `0 < a₀`.

Counting sets (`H : ℝ`):

* `jetPairs v₀ θ w H = {(s, β) ∈ ℕ × ℕ^m : v₀ s + W(β)/θ < H}`, `J_H = jetCount`, `M = K J_H`;
* `tagSet w H = {ξ ∈ ℕ^m : W(ξ) ≤ H}`, `𝒯_H`, and `N_H = NH w a₀ H = |{ξ : W(ξ) ≤ a₀ H}|`.

Rates:  `c_H = κγ²M/(H N_H)` with `κ = (log 2)/4`, and
`e_H = C_Λ K²/H + ρ_H + log|𝒯_H|/H` with `ρ_H = (log M + κ - log(1 - s₀))/H`, `s₀ = 2^(-1/2)`.

`cor_limits`: `e_H → 0` and `c_H → κγ²Kθ^m/((m+1)v₀a₀^m)`.

Source of the lattice-point asymptotics: `OAI.PiExponent.tendsto_card_realWeightedSimplex_rational`
and `tendsto_card_strictWeightedSimplex_rational` (vendored, Apache-2.0). The weights of the column
count `2w₀(k+2b) + W(α) ≤ H` do not enter `cor:limits` (the columns are an arbitrary choice of `M`
monomials, `eq:S`), so no column counting is formalised here.
-/

namespace CatalanCore.Elliptic.Params

open Filter Topology
open OAI.PiExponent
open scoped BigOperators

/-! ### Weights `w = ⌈log q⌉` -/

/-- The weight `⌈log q⌉` of a denominator `q`. -/
noncomputable def logWeight (q : ℕ) : ℕ := ⌈Real.log (q : ℝ)⌉₊

theorem logWeight_pos {q : ℕ} (hq : 2 ≤ q) : 0 < logWeight q := by
  unfold logWeight
  apply Nat.ceil_pos.mpr
  apply Real.log_pos
  have : 1 < q := by omega
  exact_mod_cast this

theorem log_le_logWeight (q : ℕ) : Real.log (q : ℝ) ≤ (logWeight q : ℝ) :=
  Nat.le_ceil _

theorem logWeight_sub_one_lt (q : ℕ) : (logWeight q : ℝ) - 1 < Real.log (q : ℝ) := by
  have h := Nat.ceil_lt_add_one (Real.log_natCast_nonneg q)
  unfold logWeight
  linarith

/-! ### The sets -/

/-- The weighted degree `W(β) = ∑ w i * β i`. -/
def wdeg {m : ℕ} (w β : Fin m → ℕ) : ℕ := ∑ i, w i * β i

/-- `𝒯_H = {ξ ∈ ℕ^m : W(ξ) ≤ H}`. -/
noncomputable def tagSet {m : ℕ} (w : Fin m → ℕ) (H : ℝ) : Finset (Fin m → ℕ) :=
  realWeightedSimplex (fun i => (w i : ℝ)) H

theorem mem_tagSet {m : ℕ} {w : Fin m → ℕ} (hw : ∀ i, 0 < w i) {H : ℝ} {ξ : Fin m → ℕ} :
    ξ ∈ tagSet w H ↔ (wdeg w ξ : ℝ) ≤ H := by
  unfold tagSet wdeg
  rw [mem_realWeightedSimplex (w := fun i => (w i : ℝ)) (fun i => by exact_mod_cast hw i)]
  simp only [Nat.cast_sum, Nat.cast_mul]

/-- `N_H = |{ξ ∈ ℕ^m : W(ξ) ≤ a₀ H}|`. -/
noncomputable def NH {m : ℕ} (w : Fin m → ℕ) (a₀ H : ℝ) : ℕ := (tagSet w (a₀ * H)).card

/-- The weights `(v₀, w₁/θ, …, w_m/θ)` of the jet simplex. -/
def jetWeight {m : ℕ} (v₀ θ : ℚ) (w : Fin m → ℕ) : Fin (m + 1) → ℚ :=
  (Fin.cons v₀ (fun i : Fin m => (w i : ℚ) / θ) : Fin (m + 1) → ℚ)

/-- `{(s, β) ∈ ℕ^(1+m) : v₀ s + W(β)/θ < H}`, as a simplex in `Fin (m+1) → ℕ`. -/
noncomputable def jetSet {m : ℕ} (v₀ θ : ℚ) (w : Fin m → ℕ) (H : ℝ) :
    Finset (Fin (m + 1) → ℕ) :=
  strictWeightedSimplex (fun i => ((jetWeight v₀ θ w i : ℚ) : ℝ)) H

theorem headTail_injective (m : ℕ) :
    Function.Injective (fun a : Fin (m + 1) → ℕ => (a 0, fun i : Fin m => a i.succ)) := by
  intro a b h
  simp only [Prod.mk.injEq] at h
  funext i
  exact Fin.cases h.1 (fun j => congrFun h.2 j) i

/-- `𝒥_H = {(s, β) ∈ ℕ × ℕ^m : v₀ s + W(β)/θ < H}` (paper §"Weights, rows and columns"). -/
noncomputable def jetPairs {m : ℕ} (v₀ θ : ℚ) (w : Fin m → ℕ) (H : ℝ) :
    Finset (ℕ × (Fin m → ℕ)) :=
  (jetSet v₀ θ w H).map ⟨fun a => (a 0, fun i : Fin m => a i.succ), headTail_injective m⟩

/-- `J_H = |𝒥_H|`. -/
noncomputable def jetCount {m : ℕ} (v₀ θ : ℚ) (w : Fin m → ℕ) (H : ℝ) : ℕ :=
  (jetPairs v₀ θ w H).card

theorem jetCount_eq {m : ℕ} (v₀ θ : ℚ) (w : Fin m → ℕ) (H : ℝ) :
    jetCount v₀ θ w H = (jetSet v₀ θ w H).card := by
  simp [jetCount, jetPairs]

theorem jetWeight_pos {m : ℕ} {v₀ θ : ℚ} {w : Fin m → ℕ} (hv : 0 < v₀) (hθ : 0 < θ)
    (hw : ∀ i, 0 < w i) (i : Fin (m + 1)) : 0 < jetWeight v₀ θ w i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [jetWeight] using hv
  · simp only [jetWeight, Fin.cons_succ]
    exact div_pos (by exact_mod_cast hw j) hθ

theorem jetSum_eq {m : ℕ} (v₀ θ : ℚ) (w : Fin m → ℕ) (a : Fin (m + 1) → ℕ) :
    ∑ i, ((jetWeight v₀ θ w i : ℚ) : ℝ) * (a i : ℝ) =
      (v₀ : ℝ) * (a 0 : ℝ) + (wdeg w (fun i : Fin m => a i.succ) : ℝ) / (θ : ℝ) := by
  rw [Fin.sum_univ_succ]
  simp only [jetWeight, Fin.cons_zero, Fin.cons_succ, wdeg]
  congr 1
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem mem_jetSet {m : ℕ} {v₀ θ : ℚ} {w : Fin m → ℕ} (hv : 0 < v₀) (hθ : 0 < θ)
    (hw : ∀ i, 0 < w i) {H : ℝ} {a : Fin (m + 1) → ℕ} :
    a ∈ jetSet v₀ θ w H ↔
      (v₀ : ℝ) * (a 0 : ℝ) + (wdeg w (fun i : Fin m => a i.succ) : ℝ) / (θ : ℝ) < H := by
  unfold jetSet
  rw [mem_strictWeightedSimplex (w := fun i => ((jetWeight v₀ θ w i : ℚ) : ℝ))
    (fun i => by exact_mod_cast jetWeight_pos hv hθ hw i), jetSum_eq]

theorem mem_jetPairs {m : ℕ} {v₀ θ : ℚ} {w : Fin m → ℕ} (hv : 0 < v₀) (hθ : 0 < θ)
    (hw : ∀ i, 0 < w i) {H : ℝ} {s : ℕ} {β : Fin m → ℕ} :
    (s, β) ∈ jetPairs v₀ θ w H ↔ (v₀ : ℝ) * (s : ℝ) + (wdeg w β : ℝ) / (θ : ℝ) < H := by
  unfold jetPairs
  rw [Finset.mem_map]
  constructor
  · rintro ⟨a, ha, h⟩
    simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at h
    obtain ⟨h0, h1⟩ := h
    have := (mem_jetSet hv hθ hw).mp ha
    rw [h0, h1] at this
    exact this
  · intro h
    refine ⟨Fin.cons s β, (mem_jetSet hv hθ hw).mpr ?_, ?_⟩
    · simpa using h
    · simp

/-! ### The rates -/

/-- `κ = (log 2)/4` of `lem:collision`. -/
noncomputable def kappa : ℝ := Real.log 2 / 4

/-- `s₀ = 2^(-1/2)` of `lem:collision`. -/
noncomputable def s0 : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ))

/-- `ρ_H = (log M + κ - log(1 - s₀))/H`. -/
noncomputable def rhoH (M H : ℝ) : ℝ := (Real.log M + kappa - Real.log (1 - s0)) / H

/-- `c_H = κ γ² M/(H N_H)` with `M = K J_H`. -/
noncomputable def cH {m : ℕ} (K : ℕ) (v₀ θ : ℚ) (w : Fin m → ℕ) (a₀ γ H : ℝ) : ℝ :=
  kappa * γ ^ 2 * ((K * jetCount v₀ θ w H : ℕ) : ℝ) / (H * (NH w a₀ H : ℝ))

/-- `e_H = C_Λ K²/H + ρ_H + log|𝒯_H|/H` with `M = K J_H`. -/
noncomputable def eH {m : ℕ} (CΛ : ℝ) (K : ℕ) (v₀ θ : ℚ) (w : Fin m → ℕ) (H : ℝ) : ℝ :=
  CΛ * (K : ℝ) ^ 2 / H + rhoH ((K * jetCount v₀ θ w H : ℕ) : ℝ) H +
    Real.log ((tagSet w H).card : ℝ) / H

/-- The limit `c_∞ = κγ²Kθ^m/((m+1)v₀a₀^m)`. -/
noncomputable def cInf {m : ℕ} (K : ℕ) (v₀ θ : ℚ) (a₀ γ : ℝ) : ℝ :=
  kappa * γ ^ 2 * (K : ℝ) * (θ : ℝ) ^ m / (((m : ℝ) + 1) * (v₀ : ℝ) * a₀ ^ m)

/-! ### Asymptotics of the two counts -/

theorem tendsto_NH {m : ℕ} {w : Fin m → ℕ} (hw : ∀ i, 0 < w i) {a₀ : ℝ} (ha : 0 < a₀) :
    Tendsto (fun H : ℝ => (NH w a₀ H : ℝ) / H ^ m) atTop
      (𝓝 (a₀ ^ m / ((m.factorial : ℝ) * ∏ i, (w i : ℝ)))) := by
  have hρ : ∀ i, (0 : ℚ) < (w i : ℚ) := fun i => Nat.cast_pos.mpr (hw i)
  have h := ((tendsto_card_realWeightedSimplex_rational (fun i => (w i : ℚ)) hρ).comp
    (Tendsto.const_mul_atTop ha tendsto_id)).mul_const (a₀ ^ m)
  simp only [Rat.cast_natCast] at h
  have he : 1 / ((m.factorial : ℝ) * ∏ i, (w i : ℝ)) * a₀ ^ m =
      a₀ ^ m / ((m.factorial : ℝ) * ∏ i, (w i : ℝ)) := by ring
  rw [he] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  have ha0 : a₀ ≠ 0 := ha.ne'
  have hH0 : H ≠ 0 := hH.ne'
  simp only [Function.comp_apply, NH, tagSet, id, mul_pow]
  field_simp

theorem tendsto_jetCount {m : ℕ} {v₀ θ : ℚ} {w : Fin m → ℕ} (hv : 0 < v₀) (hθ : 0 < θ)
    (hw : ∀ i, 0 < w i) :
    Tendsto (fun H : ℝ => (jetCount v₀ θ w H : ℝ) / H ^ (m + 1)) atTop
      (𝓝 ((θ : ℝ) ^ m / (((m + 1).factorial : ℝ) * (v₀ : ℝ) * ∏ i, (w i : ℝ)))) := by
  have h := tendsto_card_strictWeightedSimplex_rational (jetWeight v₀ θ w)
    (jetWeight_pos hv hθ hw)
  have hv0 : (v₀ : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  have hθ0 : (θ : ℝ) ≠ 0 := by exact_mod_cast hθ.ne'
  have hP : (∏ i, (w i : ℝ)) ≠ 0 :=
    (Finset.prod_pos (fun i _ => by exact_mod_cast hw i)).ne'
  have hF : (((m + 1).factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hp : ∏ i, ((jetWeight v₀ θ w i : ℚ) : ℝ) = (v₀ : ℝ) * (∏ i, (w i : ℝ)) / (θ : ℝ) ^ m := by
    rw [Fin.prod_univ_succ]
    simp only [jetWeight, Fin.cons_zero, Fin.cons_succ]
    push_cast
    rw [Finset.prod_div_distrib]
    simp [mul_div_assoc]
  rw [hp] at h
  have he : 1 / (((m + 1).factorial : ℝ) * ((v₀ : ℝ) * (∏ i, (w i : ℝ)) / (θ : ℝ) ^ m)) =
      (θ : ℝ) ^ m / (((m + 1).factorial : ℝ) * (v₀ : ℝ) * ∏ i, (w i : ℝ)) := by
    field_simp
  rw [he] at h
  refine h.congr' (Eventually.of_forall fun H => ?_)
  beta_reduce
  rw [jetCount_eq]
  rfl

/-! ### `cor:limits` -/

theorem tendsto_cH {m : ℕ} (K : ℕ) {v₀ θ : ℚ} {w : Fin m → ℕ} (hv : 0 < v₀) (hθ : 0 < θ)
    (hw : ∀ i, 0 < w i) {a₀ : ℝ} (ha : 0 < a₀) (γ : ℝ) :
    Tendsto (fun H : ℝ => cH K v₀ θ w a₀ γ H) atTop (𝓝 (cInf (m := m) K v₀ θ a₀ γ)) := by
  have hv0 : (v₀ : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  have hθ0 : (θ : ℝ) ≠ 0 := by exact_mod_cast hθ.ne'
  have ha0 : a₀ ≠ 0 := ha.ne'
  have hP : 0 < ∏ i, (w i : ℝ) := Finset.prod_pos (fun i _ => by exact_mod_cast hw i)
  have hP0 := hP.ne'
  have hF : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hB : a₀ ^ m / ((m.factorial : ℝ) * ∏ i, (w i : ℝ)) ≠ 0 :=
    (div_pos (pow_pos ha m) (mul_pos (by exact_mod_cast Nat.factorial_pos m) hP)).ne'
  have h := ((tendsto_jetCount hv hθ hw).div (tendsto_NH hw ha) hB).const_mul
    (kappa * γ ^ 2 * (K : ℝ))
  have he : kappa * γ ^ 2 * (K : ℝ) *
      ((θ : ℝ) ^ m / (((m + 1).factorial : ℝ) * (v₀ : ℝ) * ∏ i, (w i : ℝ)) /
        (a₀ ^ m / ((m.factorial : ℝ) * ∏ i, (w i : ℝ)))) = cInf (m := m) K v₀ θ a₀ γ := by
    unfold cInf
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  rw [he] at h
  simp only [Pi.div_apply] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  have hH0 : H ≠ 0 := hH.ne'
  unfold cH
  by_cases hn : (NH w a₀ H : ℝ) = 0
  · simp [hn]
  · simp only [Nat.cast_mul, pow_succ]
    field_simp

theorem tendsto_eH {m : ℕ} (CΛ : ℝ) {K : ℕ} (hK : 1 ≤ K) {v₀ θ : ℚ} {w : Fin m → ℕ}
    (hv : 0 < v₀) (hθ : 0 < θ) (hw : ∀ i, 0 < w i) :
    Tendsto (fun H : ℝ => eH CΛ K v₀ θ w H) atTop (𝓝 0) := by
  have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
  have hP : 0 < ∏ i, (w i : ℝ) := Finset.prod_pos (fun i _ => by exact_mod_cast hw i)
  have hL : 0 < (θ : ℝ) ^ m / (((m + 1).factorial : ℝ) * (v₀ : ℝ) * ∏ i, (w i : ℝ)) := by
    have hv' : (0 : ℝ) < v₀ := by exact_mod_cast hv
    have hθ' : (0 : ℝ) < θ := by exact_mod_cast hθ
    have hF : (0 : ℝ) < ((m + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    positivity
  have hJ := tendsto_jetCount hv hθ hw
  -- (1) the constant term
  have h1 : Tendsto (fun H : ℝ => CΛ * (K : ℝ) ^ 2 / H) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := CΛ * (K : ℝ) ^ 2)).div_atTop tendsto_id
  -- (2) rho_H
  have h2' := tendsto_log_add_div_of_normalized_pow hJ hL
    (Real.log (K : ℝ) + kappa - Real.log (1 - s0))
  have h2 : Tendsto (fun H : ℝ => rhoH ((K * jetCount v₀ θ w H : ℕ) : ℝ) H) atTop (𝓝 0) := by
    refine h2'.congr' ?_
    filter_upwards [hJ.eventually (eventually_ne_nhds hL.ne')] with H hH
    have hJne : (jetCount v₀ θ w H : ℝ) ≠ 0 := by
      intro hz
      apply hH
      simp [hz]
    unfold rhoH
    rw [Nat.cast_mul, Real.log_mul hKR hJne]
    ring_nf
  -- (3) log |T_H| / H
  have hρ : ∀ i, (0 : ℚ) < (w i : ℚ) := fun i => Nat.cast_pos.mpr (hw i)
  have h3 : Tendsto (fun H : ℝ => Real.log ((tagSet w H).card : ℝ) / H) atTop (𝓝 0) := by
    have := tendsto_log_card_realWeightedSimplex_div_rational (fun i => (w i : ℚ)) hρ
    simp only [Rat.cast_natCast] at this
    exact this
  have := (h1.add h2).add h3
  simpa only [add_zero, eH] using this

/-- **`cor:limits`** (Chudnovsky--Chudnovsky Cor. 16.4): with all data other than `H` fixed,
`e_H → 0` and `c_H → c_∞ = κγ²Kθ^m/((m+1)v₀a₀^m)`. -/
theorem cor_limits {m : ℕ} (CΛ : ℝ) {K : ℕ} (hK : 1 ≤ K) {v₀ θ : ℚ} {w : Fin m → ℕ}
    (hv : 0 < v₀) (hθ : 0 < θ) (hw : ∀ i, 0 < w i) {a₀ : ℝ} (ha : 0 < a₀) (γ : ℝ) :
    Tendsto (fun H : ℝ => eH CΛ K v₀ θ w H) atTop (𝓝 0) ∧
      Tendsto (fun H : ℝ => cH K v₀ θ w a₀ γ H) atTop (𝓝 (cInf (m := m) K v₀ θ a₀ γ)) :=
  ⟨tendsto_eH CΛ hK hv hθ hw, tendsto_cH K hv hθ hw ha γ⟩

/-- `cor_limits` along the multiples `H = D n` of a fixed positive integer (the assembly takes `H`
divisible by `D_EPA`). -/
theorem cor_limits_mul {m : ℕ} (CΛ : ℝ) {K : ℕ} (hK : 1 ≤ K) {v₀ θ : ℚ} {w : Fin m → ℕ}
    (hv : 0 < v₀) (hθ : 0 < θ) (hw : ∀ i, 0 < w i) {a₀ : ℝ} (ha : 0 < a₀) (γ : ℝ)
    {D : ℕ} (hD : 0 < D) :
    Tendsto (fun n : ℕ => eH CΛ K v₀ θ w ((D * n : ℕ) : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => cH K v₀ θ w a₀ γ ((D * n : ℕ) : ℝ)) atTop
        (𝓝 (cInf (m := m) K v₀ θ a₀ γ)) := by
  have hmul : Tendsto (fun n : ℕ => ((D * n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n hD) tendsto_id)
  obtain ⟨h1, h2⟩ := cor_limits CΛ hK hv hθ hw ha γ
  exact ⟨h1.comp hmul, h2.comp hmul⟩

end CatalanCore.Elliptic.Params
