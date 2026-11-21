module

public import CatalanCore.Elliptic.Interfaces
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The parameter system of `thm:epa` (row E09.0)

Labels refer to `paper/elliptic-periods.tex` (`thm:epa`, eq:epa-base,
eq:epa-thresholds) and to the Chudnovsky--Chudnovsky paper Corollary 13.5 (§12, "All thresholds can
be chosen before the centers").

* `An n s = A_n(s) = 2 (n+2)^{n+2} (1 + (n+2)/s)^{n+2}`.
* `EpaBase`: the volume conditions eq:epa-base.
* `EpaSigma`: the conditions on `σ₀` of `thm:epa`.
* `eps0 = ε₀`, `gConst = g`, `C4 = C₄`, `qStar = q_*`.
* `EpaThresholds`: eq:epa-thresholds, `w_i > max {1, (C₄/q_*) ∏_{l<i} w_l}`.
* `radWt`, `jetWt`: the "radius" weights `(w₀, w₁, …, w_m)` and the jet weights
  `(v₀, w₁/θ, …, w_m/θ)` on `Fin (m+1)` (the intrinsic frame index set: `0` is `t`/`T`,
  `i.succ` is `Z_i`/`V_i`). They are placed here, not in `Ambient.lean`, because the numerical
  separation lemma (`Numerics.lean`) needs them; row E09.1 imports this file.

The numerical lemmas (scalar margin, coefficient bound, explicit separation) are in
`CatalanCore.Elliptic.EPA.Numerics`.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

open CatalanCore.Elliptic

variable {m K : ℕ}

/-- `A_n(s) = 2 (n+2)^{n+2} (1 + (n+2)/s)^{n+2}` (paper, before `thm:epa`). -/
def An (n : ℕ) (s : ℚ) : ℚ :=
  2 * ((n : ℚ) + 2) ^ (n + 2) * (1 + ((n : ℚ) + 2) / s) ^ (n + 2)

/-- eq:epa-base: the volume conditions `K (w₀/v₀) θ^m < 1` and `K θ^m < 1`
(`θ < 1` is a field of `Weights`). -/
structure EpaBase (m K : ℕ) (W : Weights m) : Prop where
  vol₁ : (K : ℚ) * (W.w₀ / W.v₀) * W.θ ^ m < 1
  vol₂ : (K : ℚ) * W.θ ^ m < 1

/-- The conditions on `σ₀` in `thm:epa`. -/
structure EpaSigma (m K : ℕ) (W : Weights m) (σ : ℚ) : Prop where
  pos : 0 < σ
  h₁ : (1 + 3 * σ) ^ (m + 1) * ((K : ℚ) * (W.w₀ / W.v₀) * W.θ ^ m) < 1
  h₂ : (1 + 3 * σ) ^ m * ((K : ℚ) * W.θ ^ m) < 1
  h₃ : (1 + σ) * W.θ < 1

/-- `ε₀ = min {σ₀, σ₀ v₀ / (4 (1+σ₀) w₀)}`. -/
def eps0 (W : Weights m) (σ : ℚ) : ℚ :=
  min σ (σ * W.v₀ / (4 * (1 + σ) * W.w₀))

/-- `g = 1 + (2 w₀/v₀) ε₀` (CM: `g₄`). -/
def gConst (W : Weights m) (σ : ℚ) : ℚ :=
  1 + 2 * W.w₀ / W.v₀ * eps0 W σ

/-- `C₄ = A_m(σ₀) + 4 · 2^{m+3} A_{m+1}(ε₀)`. -/
def C4 (W : Weights m) (σ : ℚ) : ℚ :=
  An m σ + 4 * 2 ^ (m + 3) * An (m + 1) (eps0 W σ)

/-- `q_* = θ^m min(1, w₀) / max(1, v₀)`. -/
def qStar (W : Weights m) : ℚ :=
  W.θ ^ m * min 1 W.w₀ / max 1 W.v₀

/-- eq:epa-thresholds: `1 < w_i` and `(C₄/q_*) ∏_{l<i} w_l < w_i` for `1 ≤ i ≤ m`
(here `i : Fin m` stands for the paper's index `i+1`, so `∏_{l<i}` runs over `Fin m` below `i`). -/
def EpaThresholds (W : Weights m) (σ : ℚ) : Prop :=
  ∀ i : Fin m, 1 < W.w i ∧
    C4 W σ / qStar W * ∏ l ∈ Finset.univ.filter (· < i), W.w l < W.w i

/-- The "radius" weights `(w₀, w₁, …, w_m)` on `Fin (m+1)`. -/
def radWt (W : Weights m) : Fin (m + 1) → ℚ :=
  Fin.cases (motive := fun _ => ℚ) W.w₀ W.w

/-- The jet weights `(v₀, w₁/θ, …, w_m/θ)` on `Fin (m+1)`. -/
def jetWt (W : Weights m) : Fin (m + 1) → ℚ :=
  Fin.cases (motive := fun _ => ℚ) W.v₀ (fun i => W.w i / W.θ)

@[simp] theorem radWt_zero (W : Weights m) : radWt W 0 = W.w₀ := rfl
@[simp] theorem radWt_succ (W : Weights m) (i : Fin m) : radWt W i.succ = W.w i := rfl
@[simp] theorem jetWt_zero (W : Weights m) : jetWt W 0 = W.v₀ := rfl
@[simp] theorem jetWt_succ (W : Weights m) (i : Fin m) : jetWt W i.succ = W.w i / W.θ := rfl

/-- `jetWt` is the rational form of `Weights.rowWeights` of `Interfaces`. -/
theorem jetWt_cast (W : Weights m) (j : Fin (m + 1)) :
    ((jetWt W j : ℚ) : ℝ) = W.rowWeights j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [Weights.rowWeights]
  · simp [Weights.rowWeights]

theorem An_pos (n : ℕ) {s : ℚ} (hs : 0 < s) : 0 < An n s := by
  unfold An; positivity

theorem eps0_pos (W : Weights m) {σ : ℚ} (hσ : 0 < σ) : 0 < eps0 W σ := by
  have := W.w₀_pos; have := W.v₀_pos
  unfold eps0
  exact lt_min hσ (by positivity)

theorem C4_pos (W : Weights m) {σ : ℚ} (hσ : 0 < σ) : 0 < C4 W σ := by
  have h1 := An_pos m hσ
  have h2 := An_pos (m + 1) (eps0_pos W hσ)
  unfold C4; positivity

theorem qStar_pos (W : Weights m) : 0 < qStar W := by
  have := W.w₀_pos; have := W.v₀_pos; have := W.θ_pos
  unfold qStar
  have : 0 < min 1 W.w₀ := lt_min one_pos W.w₀_pos
  have : 0 < max 1 W.v₀ := lt_max_of_lt_left one_pos
  positivity

end CatalanCore.Elliptic.EPA
