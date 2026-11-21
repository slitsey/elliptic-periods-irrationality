module

public import CatalanCore.Elliptic.EPA.Params
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Numerics of `thm:epa` (row E09.0)

Chudnovsky--Chudnovsky §12, "From curve excess to the terminal budget" and "All thresholds can
be chosen before the centers" (cited by the paper, `thm:epa`).

* `scalar_margin`: `ε₀ > 0`, `ε₀ ≤ σ`, `g < 3/2`, `g (1+σ) ≤ 1 + (3/2) σ` and
  `(1+3σ) − ε₀ − g(1+σ) ≥ σ/2`.
  Proof. `λ ε₀ (1+σ) ≤ λ · σ v₀/(4 w₀) = σ/2` with `λ = 2 w₀/v₀`; since `σ/2 < (1+σ)/2`,
  `λ ε₀ < 1/2`; the rest is linear arithmetic.
* `coeff_bound`: for `1 ≤ k ≤ m+1`, `4 g^k k^k ((m+3)/ε₀)^k ≤ C₄`. Proof. `g < 2`, `k ≤ m+3`,
  and `(m+3)/ε₀ ≤ 1 + (m+3)/ε₀`, so the left side is at most
  `4 · 2^{m+3} (m+3)^{m+3} (1 + (m+3)/ε₀)^{m+3} ≤ 4 · 2^{m+3} A_{m+1}(ε₀) ≤ C₄`.
* `explicit_separation` (`lem:origin-explicit-separation`): for `i ≠ 0` in `S \ T` with equal
  membership above `i`, `C₄ ∏_{j∈T} v_j < ∏_{j∈S} r_j`. (Equal cardinality of `S`, `T` is not
  needed.) Proof. Write `a_k = w_k` if `k+1 ∈ S` and `1` otherwise, `b_k` likewise for `T`, and
  `c_k = w_k/θ` if `k+1 ∈ T` and `1` otherwise. Then `∏_S r = e_S ∏ a`, `∏_T v = e_T ∏ c`,
  `e_S ≥ min(1,w₀)`, `e_T ≤ max(1,v₀)`, and `∏ c ≤ ∏ b / θ^m`. With `i = k₀ + 1`,
  comparing factor by factor (`k < k₀`: `b_k ≤ w_k ≤ a_k w_k`; `k = k₀`: both sides `w_{k₀}`;
  `k > k₀`: `a_k = b_k`) gives `(∏ a)(∏_{l<k₀} w_l) ≥ w_{k₀} ∏ b`. The threshold
  `(C₄/q_*) ∏_{l<k₀} w_l < w_{k₀}` then gives `C₄ ∏ b < q_* ∏ a`, and the definition of `q_*`
  finishes.

The OAI form of the constant, `An m σ = PersistentWeightComparison.comparisonConstant m σ`, is not
stated here: that module of the vendored engine is stated for reals and is consumed in row E09.9.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

open CatalanCore.Elliptic Finset

variable {m K : ℕ}

/-- CM l.2660-2672. -/
theorem scalar_margin (W : Weights m) {σ : ℚ} (hσ : 0 < σ) :
    0 < eps0 W σ ∧ eps0 W σ ≤ σ ∧ gConst W σ < 3 / 2 ∧
      gConst W σ * (1 + σ) ≤ 1 + 3 / 2 * σ ∧
      σ / 2 ≤ (1 + 3 * σ) - eps0 W σ - gConst W σ * (1 + σ) := by
  have hw := W.w₀_pos
  have hv := W.v₀_pos
  have hpos : 0 < eps0 W σ := eps0_pos W hσ
  have hε1 : eps0 W σ ≤ σ := min_le_left _ _
  have hε2 : eps0 W σ ≤ σ * W.v₀ / (4 * (1 + σ) * W.w₀) := min_le_right _ _
  have h1σ : 0 < 1 + σ := by linarith
  have hk : 2 * W.w₀ / W.v₀ * eps0 W σ * (1 + σ) ≤ σ / 2 := by
    have heq : 2 * W.w₀ / W.v₀ * (σ * W.v₀ / (4 * (1 + σ) * W.w₀)) * (1 + σ) = σ / 2 := by
      field_simp
      ring
    calc 2 * W.w₀ / W.v₀ * eps0 W σ * (1 + σ)
        ≤ 2 * W.w₀ / W.v₀ * (σ * W.v₀ / (4 * (1 + σ) * W.w₀)) * (1 + σ) := by gcongr
      _ = σ / 2 := heq
  have hL : 2 * W.w₀ / W.v₀ * eps0 W σ < 1 / 2 := by
    have : 2 * W.w₀ / W.v₀ * eps0 W σ * (1 + σ) < 1 / 2 * (1 + σ) := by linarith
    exact lt_of_mul_lt_mul_right this h1σ.le
  have hg : gConst W σ * (1 + σ) = (1 + σ) + 2 * W.w₀ / W.v₀ * eps0 W σ * (1 + σ) := by
    unfold gConst; ring
  refine ⟨hpos, hε1, ?_, ?_, ?_⟩
  · unfold gConst; linarith
  · rw [hg]; linarith
  · rw [hg]; linarith

/-- CM l.1438-1447, 3230-3236. -/
theorem coeff_bound (W : Weights m) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ m + 1) {σ : ℚ} (hσ : 0 < σ) :
    4 * gConst W σ ^ k * (k : ℚ) ^ k * (((m : ℚ) + 3) / eps0 W σ) ^ k ≤ C4 W σ := by
  obtain ⟨hpos, -, hg32, -, -⟩ := scalar_margin W hσ
  set ε := eps0 W σ with hε
  set X : ℚ := ((m : ℚ) + 3) / ε with hX
  have hX0 : 0 ≤ X := by positivity
  have hg0 : 0 ≤ gConst W σ := by
    unfold gConst; have := W.w₀_pos; have := W.v₀_pos; positivity
  have hg2 : gConst W σ ≤ 2 := by linarith
  have hkm : k ≤ m + 3 := by omega
  have hm3 : (1 : ℚ) ≤ (m : ℚ) + 3 := by
    have : (0 : ℚ) ≤ m := Nat.cast_nonneg m
    linarith
  have hgk : gConst W σ ^ k ≤ 2 ^ (m + 3) :=
    calc gConst W σ ^ k ≤ 2 ^ k := pow_le_pow_left₀ hg0 hg2 k
      _ ≤ 2 ^ (m + 3) := pow_le_pow_right₀ (by norm_num) hkm
  have hkk : (k : ℚ) ^ k ≤ ((m : ℚ) + 3) ^ (m + 3) :=
    calc (k : ℚ) ^ k ≤ ((m : ℚ) + 3) ^ k :=
          pow_le_pow_left₀ (Nat.cast_nonneg k) (by exact_mod_cast hkm) k
      _ ≤ ((m : ℚ) + 3) ^ (m + 3) := pow_le_pow_right₀ hm3 hkm
  have hXk : X ^ k ≤ (1 + X) ^ (m + 3) :=
    calc X ^ k ≤ (1 + X) ^ k := pow_le_pow_left₀ hX0 (by linarith) k
      _ ≤ (1 + X) ^ (m + 3) := pow_le_pow_right₀ (by linarith) hkm
  have hA : An (m + 1) ε = 2 * ((m : ℚ) + 3) ^ (m + 3) * (1 + X) ^ (m + 3) := by
    unfold An
    have h : (((m + 1 : ℕ) : ℚ) + 2) = (m : ℚ) + 3 := by push_cast; ring
    rw [h]
  have hAm : 0 ≤ An m σ := (An_pos m hσ).le
  have hP : 0 ≤ ((m : ℚ) + 3) ^ (m + 3) := by positivity
  have hQ : 0 ≤ (1 + X) ^ (m + 3) := by positivity
  have hkk0 : 0 ≤ (k : ℚ) ^ k := by positivity
  have hXk0 : 0 ≤ X ^ k := by positivity
  have hgk0 : 0 ≤ gConst W σ ^ k := by positivity
  calc 4 * gConst W σ ^ k * (k : ℚ) ^ k * X ^ k
      ≤ 4 * 2 ^ (m + 3) * ((m : ℚ) + 3) ^ (m + 3) * (1 + X) ^ (m + 3) := by
        gcongr
    _ ≤ 4 * 2 ^ (m + 3) * An (m + 1) ε := by
        rw [hA]; nlinarith [mul_nonneg hP hQ, pow_pos (show (0 : ℚ) < 2 by norm_num) (m + 3)]
    _ ≤ C4 W σ := by unfold C4; linarith

private theorem prod_split (S : Finset (Fin (m + 1))) (f : Fin (m + 1) → ℚ) :
    ∏ j ∈ S, f j = (if (0 : Fin (m + 1)) ∈ S then f 0 else 1) *
      ∏ k : Fin m, (if k.succ ∈ S then f k.succ else 1) := by
  classical
  have h : ∏ j ∈ S, f j = ∏ j, (if j ∈ S then f j else 1) := by
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  rw [h, Fin.prod_univ_succ]

/-- CM l.3138-3162 (`lem:origin-explicit-separation`), over `ℚ`. -/
theorem explicit_separation (W : Weights m) {σ : ℚ} (hthr : EpaThresholds W σ)
    (S T : Finset (Fin (m + 1))) (i : Fin (m + 1)) (hi : i ≠ 0) (hiS : i ∈ S) (hiT : i ∉ T)
    (habove : ∀ j, i < j → (j ∈ S ↔ j ∈ T)) :
    C4 W σ * ∏ j ∈ T, jetWt W j < ∏ j ∈ S, radWt W j := by
  classical
  obtain ⟨k₀, rfl⟩ := Fin.exists_succ_eq.mpr hi
  have hθ := W.θ_pos
  have hθ1 := W.θ_lt_one
  have hw0 := W.w₀_pos
  have hv0 := W.v₀_pos
  have hw1 : ∀ k, 1 < W.w k := fun k => (hthr k).1
  have hw0' : ∀ k, 0 < W.w k := fun k => lt_trans one_pos (hw1 k)
  -- the product factors
  set a : Fin m → ℚ := fun k => if k.succ ∈ S then W.w k else 1 with ha
  set b : Fin m → ℚ := fun k => if k.succ ∈ T then W.w k else 1 with hb
  set c : Fin m → ℚ := fun k => if k.succ ∈ T then W.w k / W.θ else 1 with hc
  have ha1 : ∀ k, 1 ≤ a k := fun k => by
    simp only [ha]; split_ifs
    · exact (hw1 k).le
    · exact le_rfl
  have hb1 : ∀ k, 1 ≤ b k := fun k => by
    simp only [hb]; split_ifs
    · exact (hw1 k).le
    · exact le_rfl
  have hbw : ∀ k, b k ≤ W.w k := fun k => by
    simp only [hb]; split_ifs
    · exact le_rfl
    · exact (hw1 k).le
  have hc0 : ∀ k, 0 ≤ c k := fun k => by
    simp only [hc]; split_ifs
    · exact (div_pos (hw0' k) hθ).le
    · exact zero_le_one
  have hcb : ∀ k, c k ≤ b k / W.θ := fun k => by
    simp only [hc, hb]; split_ifs
    · exact le_rfl
    · rw [le_div_iff₀ hθ]; linarith
  have hPa : 0 < ∏ k, a k := Finset.prod_pos fun k _ => lt_of_lt_of_le one_pos (ha1 k)
  have hPb : 0 < ∏ k, b k := Finset.prod_pos fun k _ => lt_of_lt_of_le one_pos (hb1 k)
  -- decomposition of the two products
  have hS : ∏ j ∈ S, radWt W j =
      (if (0 : Fin (m + 1)) ∈ S then W.w₀ else 1) * ∏ k, a k := by
    rw [prod_split]; simp [ha]
  have hT : ∏ j ∈ T, jetWt W j =
      (if (0 : Fin (m + 1)) ∈ T then W.v₀ else 1) * ∏ k, c k := by
    rw [prod_split]; simp [hc]
  -- key comparison
  have hkey : W.w k₀ * ∏ k, b k ≤
      (∏ k, a k) * ∏ l ∈ Finset.univ.filter (· < k₀), W.w l := by
    have hL : (∏ k, a k) * ∏ l ∈ Finset.univ.filter (· < k₀), W.w l =
        ∏ k, (a k * (if k < k₀ then W.w k else 1)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_filter]
    have hR : W.w k₀ * ∏ k, b k = ∏ k, (b k * (if k = k₀ then W.w k₀ else 1)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k₀ (fun _ => W.w k₀)]
      simp [mul_comm]
    rw [hL, hR]
    refine Finset.prod_le_prod₀ (fun k _ => ?_) (fun k _ => ?_)
    · have := hb1 k
      split_ifs
      · exact mul_nonneg (by linarith) (hw0' _).le
      · positivity
    · rcases lt_trichotomy k k₀ with hlt | heq | hgt
      · have hne : k ≠ k₀ := hlt.ne
        simp only [if_pos hlt, if_neg hne, mul_one]
        have := ha1 k; have := hbw k; have := hw0' k
        nlinarith
      · subst heq
        have hak : a k = W.w k := by simp [ha, hiS]
        have hbk : b k = 1 := by simp [hb, hiT]
        simp [hak, hbk]
      · have hne : k ≠ k₀ := hgt.ne'
        have hnl : ¬ k < k₀ := not_lt.mpr hgt.le
        have hab : a k = b k := by
          have := habove k.succ (Fin.succ_lt_succ_iff.mpr hgt)
          simp only [ha, hb]
          by_cases h : k.succ ∈ S
          · simp [h, this.mp h]
          · have : k.succ ∉ T := fun h' => h (this.mpr h')
            simp [h, this]
        simp [if_neg hnl, if_neg hne, hab]
  -- the bound on the product of the `c`
  have hcprod : ∏ k, c k ≤ (∏ k, b k) / W.θ ^ m := by
    calc ∏ k, c k ≤ ∏ k, (b k / W.θ) :=
          Finset.prod_le_prod₀ (fun k _ => hc0 k) (fun k _ => hcb k)
      _ = (∏ k, b k) / W.θ ^ m := by
          rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- bounds on the two scalar prefactors
  have heS : min 1 W.w₀ ≤ (if (0 : Fin (m + 1)) ∈ S then W.w₀ else 1) := by
    split_ifs
    · exact min_le_right _ _
    · exact min_le_left _ _
  have heS0 : 0 < (if (0 : Fin (m + 1)) ∈ S then W.w₀ else 1) := by
    split_ifs <;> positivity
  have heT : (if (0 : Fin (m + 1)) ∈ T then W.v₀ else 1) ≤ max 1 W.v₀ := by
    split_ifs
    · exact le_max_right _ _
    · exact le_max_left _ _
  have heT0 : 0 ≤ (if (0 : Fin (m + 1)) ∈ T then W.v₀ else 1) := by
    split_ifs <;> positivity
  have hP : 0 < ∏ j ∈ S, radWt W j := by rw [hS]; positivity
  by_cases hC : C4 W σ ≤ 0
  · have hQ : 0 ≤ ∏ j ∈ T, jetWt W j := by rw [hT]; exact mul_nonneg heT0 (Finset.prod_nonneg fun k _ => hc0 k)
    nlinarith
  · push Not at hC
    have hqs := qStar_pos W
    have hmin : 0 < min 1 W.w₀ := lt_min one_pos hw0
    have hmax : 0 < max 1 W.v₀ := lt_max_of_lt_left one_pos
    have hθm : 0 < W.θ ^ m := pow_pos hθ m
    have hPi : 0 < ∏ l ∈ Finset.univ.filter (· < k₀), W.w l :=
      Finset.prod_pos fun l _ => hw0' l
    -- C4 * Pb < q* * Pa
    have h1 : C4 W σ / qStar W * ∏ l ∈ Finset.univ.filter (· < k₀), W.w l < W.w k₀ :=
      (hthr k₀).2
    have h2 : C4 W σ / qStar W * ∏ k, b k <  ∏ k, a k := by
      have : C4 W σ / qStar W * (∏ l ∈ Finset.univ.filter (· < k₀), W.w l) * ∏ k, b k <
          (∏ k, a k) * ∏ l ∈ Finset.univ.filter (· < k₀), W.w l :=
        calc _ < W.w k₀ * ∏ k, b k := mul_lt_mul_of_pos_right h1 hPb
          _ ≤ _ := hkey
      have h3 : (C4 W σ / qStar W * ∏ k, b k) *
            (∏ l ∈ Finset.univ.filter (· < k₀), W.w l) <
          (∏ k, a k) * ∏ l ∈ Finset.univ.filter (· < k₀), W.w l := by
        calc _ = C4 W σ / qStar W * (∏ l ∈ Finset.univ.filter (· < k₀), W.w l) * ∏ k, b k := by
              ring
          _ < _ := this
      exact lt_of_mul_lt_mul_right h3 hPi.le
    have h4 : C4 W σ * ∏ k, b k < qStar W * ∏ k, a k := by
      have := mul_lt_mul_of_pos_left h2 hqs
      calc C4 W σ * ∏ k, b k = qStar W * (C4 W σ / qStar W * ∏ k, b k) := by
            field_simp
        _ < _ := this
    -- unfold q* and clear denominators
    have h5 : C4 W σ * (∏ k, b k) * max 1 W.v₀ < W.θ ^ m * min 1 W.w₀ * ∏ k, a k := by
      have hq : qStar W * max 1 W.v₀ = W.θ ^ m * min 1 W.w₀ := by
        unfold qStar; field_simp
      calc C4 W σ * (∏ k, b k) * max 1 W.v₀ < qStar W * (∏ k, a k) * max 1 W.v₀ :=
            mul_lt_mul_of_pos_right h4 hmax
        _ = (qStar W * max 1 W.v₀) * ∏ k, a k := by ring
        _ = _ := by rw [hq]
    have h6 : W.θ ^ m * min 1 W.w₀ * ∏ k, a k ≤ W.θ ^ m * ∏ j ∈ S, radWt W j := by
      rw [hS]
      have : min 1 W.w₀ * ∏ k, a k ≤
          (if (0 : Fin (m + 1)) ∈ S then W.w₀ else 1) * ∏ k, a k :=
        mul_le_mul_of_nonneg_right heS hPa.le
      nlinarith
    have h7 : ∏ j ∈ T, jetWt W j ≤ max 1 W.v₀ * ((∏ k, b k) / W.θ ^ m) := by
      rw [hT]
      calc _ ≤ max 1 W.v₀ * ∏ k, c k :=
            mul_le_mul heT (le_rfl) (Finset.prod_nonneg fun k _ => hc0 k) hmax.le
        _ ≤ _ := mul_le_mul_of_nonneg_left hcprod hmax.le
    calc C4 W σ * ∏ j ∈ T, jetWt W j
        ≤ C4 W σ * (max 1 W.v₀ * ((∏ k, b k) / W.θ ^ m)) :=
          mul_le_mul_of_nonneg_left h7 hC.le
      _ = (C4 W σ * (∏ k, b k) * max 1 W.v₀) / W.θ ^ m := by
          field_simp
      _ < (W.θ ^ m * ∏ j ∈ S, radWt W j) / W.θ ^ m := by
          apply div_lt_div_of_pos_right _ hθm
          linarith
      _ = _ := by field_simp

/-- `explicit_separation` with real casts (the form fed to the OAI curve inequality). -/
theorem explicit_separation_real (W : Weights m) {σ : ℚ} (hthr : EpaThresholds W σ)
    (S T : Finset (Fin (m + 1))) (i : Fin (m + 1)) (hi : i ≠ 0) (hiS : i ∈ S) (hiT : i ∉ T)
    (habove : ∀ j, i < j → (j ∈ S ↔ j ∈ T)) :
    (C4 W σ : ℝ) * ∏ j ∈ T, (jetWt W j : ℝ) < ∏ j ∈ S, (radWt W j : ℝ) := by
  have := explicit_separation W hthr S T i hi hiS hiT habove
  exact_mod_cast this

end CatalanCore.Elliptic.EPA
