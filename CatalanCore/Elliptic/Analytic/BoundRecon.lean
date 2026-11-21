module

public import CatalanCore.Elliptic.Analytic.BoundDefs
public import CatalanCore.Elliptic.Params.Counting

@[expose] public section

/-!
# Reconciliation of the counting file (E3) with the contract (`Interfaces`) and C3

E3 (`Params/Counting.lean`) defines its own `kappa`, `s0`, `rhoH`, `jetCount`, `tagSet`, `NH`,
`eH`, `cH`, `cInf` over natural-number weights `w : Fin m → ℕ`, `v₀ θ : ℚ`. `Interfaces` defines
`collisionKappa`, `collisionS0`, `rhoH`, `eH`, `cH`, `cInfty` over a `Weights m` (rational weights
`W.w i`). C3 (`Analytic/Collision.lean`) uses the OAI `Collision.collisionRemainder`.

For `W : Weights m` with `W.w i = (w i : ℚ)` all of them agree:

* `kappa = collisionKappa`, `s0 = collisionS0` (literal closed forms),
  `Collision.collisionRemainder M H = rhoH M H` (`collisionRemainder_eq_rhoH`, `BoundDefs`);
* `jetCount W.v₀ W.θ w H = W.J H` (`𝒥_H`), `tagSet w H = W.tSet H`, `NH w a₀ H = W.NH a₀ H`;
* `Params.eH`, `Params.cH`, `Params.cInf` equal `eH`, `cH`, `cInfty` of `Interfaces`;
* `cor_limits_weights`: `cor:limits` for `eH W K C_Λ H` and `cH W K a₀ γ H`.
-/

namespace CatalanCore.Elliptic.Params

open Filter Topology

theorem kappa_eq : kappa = collisionKappa := rfl

theorem s0_eq : s0 = collisionS0 := (collisionS0_eq).symm

theorem rhoH_eq (M H : ℝ) : Params.rhoH M H = CatalanCore.Elliptic.rhoH M H := by
  unfold Params.rhoH CatalanCore.Elliptic.rhoH
  rw [kappa_eq, s0_eq]

section Weights

variable {m : ℕ} (W : Weights m) (w : Fin m → ℕ) (hw : ∀ i, W.w i = (w i : ℚ))

include hw in
theorem wdeg_eq (β : Fin m → ℕ) : (wdeg w β : ℝ) = ((W.wt β : ℚ) : ℝ) := by
  rw [W.wt_cast]
  unfold wdeg
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hw i, Rat.cast_natCast]

include hw in
theorem tagSet_eq_tSet (hwpos : ∀ i, 0 < w i) (H : ℝ) : tagSet w H = W.tSet H := by
  ext ξ
  rw [mem_tagSet hwpos, W.mem_tSet_iff, wdeg_eq W w hw]

include hw in
theorem NH_eq (hwpos : ∀ i, 0 < w i) (a₀ H : ℝ) : Params.NH w a₀ H = W.NH a₀ H := by
  unfold Params.NH Weights.NH
  rw [tagSet_eq_tSet W w hw hwpos]

include hw in
theorem jetCount_eq_J (hwpos : ∀ i, 0 < w i) (H : ℝ) : jetCount W.v₀ W.θ w H = W.J H := by
  rw [jetCount_eq]
  unfold Weights.J
  congr 1
  ext a
  rw [mem_jetSet W.v₀_pos W.θ_pos hwpos, W.mem_rowSet_iff', wdeg_eq W w hw]

include hw in
theorem eH_eq (hwpos : ∀ i, 0 < w i) (CΛ : ℝ) (K : ℕ) (H : ℝ) :
    Params.eH CΛ K W.v₀ W.θ w H = CatalanCore.Elliptic.eH W K CΛ H := by
  unfold Params.eH CatalanCore.Elliptic.eH
  rw [rhoH_eq, jetCount_eq_J W w hw hwpos, tagSet_eq_tSet W w hw hwpos] <;> rfl

include hw in
theorem cH_eq (hwpos : ∀ i, 0 < w i) (K : ℕ) (a₀ γ H : ℝ) :
    Params.cH K W.v₀ W.θ w a₀ γ H = CatalanCore.Elliptic.cH W K a₀ γ H := by
  unfold Params.cH CatalanCore.Elliptic.cH
  rw [kappa_eq, jetCount_eq_J W w hw hwpos, NH_eq W w hw hwpos] <;> rfl

theorem cInf_eq (K : ℕ) (a₀ γ : ℝ) :
    Params.cInf (m := m) K W.v₀ W.θ a₀ γ = CatalanCore.Elliptic.cInfty W K a₀ γ := by
  unfold Params.cInf CatalanCore.Elliptic.cInfty
  rw [kappa_eq]

include hw in
/-- **`cor:limits` for the contract definitions** (E15): with all data other than `H` fixed,
`e_H → 0` and `c_H → c_∞ = κ γ² K θ^m / ((m+1) v₀ a₀^m)`. -/
theorem cor_limits_weights (hwpos : ∀ i, 0 < w i) (CΛ : ℝ) {K : ℕ} (hK : 1 ≤ K) {a₀ : ℝ}
    (ha : 0 < a₀) (γ : ℝ) :
    Tendsto (fun H : ℝ => CatalanCore.Elliptic.eH W K CΛ H) atTop (𝓝 0) ∧
      Tendsto (fun H : ℝ => CatalanCore.Elliptic.cH W K a₀ γ H) atTop
        (𝓝 (CatalanCore.Elliptic.cInfty W K a₀ γ)) := by
  obtain ⟨h1, h2⟩ := cor_limits CΛ hK W.v₀_pos W.θ_pos hwpos ha γ
  have e1 : (fun H : ℝ => CatalanCore.Elliptic.eH W K CΛ H) =
      fun H => Params.eH CΛ K W.v₀ W.θ w H := funext fun H => (eH_eq W w hw hwpos CΛ K H).symm
  have e2 : (fun H : ℝ => CatalanCore.Elliptic.cH W K a₀ γ H) =
      fun H => Params.cH K W.v₀ W.θ w a₀ γ H := funext fun H => (cH_eq W w hw hwpos K a₀ γ H).symm
  refine ⟨?_, ?_⟩
  · rw [e1]
    exact h1
  · rw [e2, ← cInf_eq W K a₀ γ]
    exact h2

end Weights

end CatalanCore.Elliptic.Params
