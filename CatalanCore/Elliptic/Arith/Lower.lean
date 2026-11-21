module

public import CatalanCore.Elliptic.Arith.Trunc
public import CatalanCore.Elliptic.Arith.LcmBound
public import CatalanCore.Elliptic.Chart.Formal
public import CatalanCore.Elliptic.EPA.Packet

@[expose] public section

/-!
# E11: the arithmetic lower bound (`prop:arith`)

Labels refer to `paper/elliptic-periods.tex`, §"The arithmetic lower bound".

Let `F₀ ≥ 1/θ` and let `Δ ≠ 0` be a selected minor of the packet matrix (eq:entry) for the centres
`c_{ji} = j p_i / q_i`, with `log q_i ≤ w_i` (the paper has `w_i = ⌈log q_i⌉`). Then
`log|Δ| / (M H) ≥ −(1 − b̄) − E_ar` with `E_ar = c₀ F₀ / v₀`, where `c₀` is any constant with
`log lcm(1..n) ≤ c₀ n` (`arith_lower_bound_of_lcm`); `arith_lower_bound` takes the constant of
`Arith.LcmBound`.

Paper proof, as formalised.
* `T_i = ⌈F₀ w_i / v₀⌉`, `ℓ_i = lcm(1, …, T_i − 1)`, `c_i = q_i ℓ_i`. Then `w_i/θ ≤ T_i v₀`, so
  `lem:trunc` (`det_packet_trunc`) gives `Δ = det A^{tr}`.
* `U ∈ ℤ[[T]]` and `n [Tⁿ] L ∈ ℤ`, so `ℓ_i L_i^{tr} ∈ ℤ[T]` (`lcm_mul_trunc_mem`) and
  `c_i (j p_i / q_i + L_i^{tr}) ∈ ℤ[T]` (`scaled_factor_mem`). Hence
  `∏_i c_i^{α_i − β_i} A^{tr}_{rc} ∈ ℤ` (`entry_scaled_int`) for every entry.
* The integer matrix `N_{rc} = ∏_i c_i^{α_{ci} − β_{ri}} A^{tr}_{rc}` is `diag(u) A^{tr} diag(v)`
  (`abstract_det_bound`), with `∏ u_r v_r = ∏_i c_i^{E_i}` and `E_i = Σ_c α_{ci} − Σ_r β_{ri} ≥ 0`
  (a nonzero Leibniz term forces `β_r ≤ α_{φ(r)}`). So `det N = Δ ∏ c_i^{E_i}` is a nonzero
  integer, `1 ≤ |Δ| ∏ c_i^{E_i}`.
* `log c_i ≤ w_i + c₀ (T_i − 1) ≤ (1 + c₀F₀/v₀) w_i`, and `Σ_i w_i E_i = Σ_c W(α_c) − Σ_r W(β_r)
  ≤ M H − b̄ M H` by (S). Then `log|Δ| ≥ −(1 + E_ar) M H (1 − b̄) ≥ −M H ((1 − b̄) + E_ar)`.

The determinant argument is written over `ℚ` (the paper's `ℤ`-in-place-of-`ℤ[i√d]` case); the
Gaussian-integer statement of `Arithmetic.cleared_det_log_bound_of_entries` in openai/math is not used.
-/

namespace CatalanCore.Elliptic.Arith

open CatalanCore.Elliptic

/-! ### Series with integer coefficients -/

/-- The subring `ℤ⟦X⟧ ⊆ ℚ⟦X⟧` of power series with integer coefficients. -/
noncomputable def intSeries : Subring (PowerSeries ℚ) :=
  (PowerSeries.map (Int.castRingHom ℚ)).range

theorem mem_intSeries_of_map (P : PowerSeries ℤ) :
    PowerSeries.map (Int.castRingHom ℚ) P ∈ intSeries :=
  RingHom.mem_range.mpr ⟨P, rfl⟩

theorem mem_intSeries_iff (f : PowerSeries ℚ) :
    f ∈ intSeries ↔ ∀ n, ∃ k : ℤ, PowerSeries.coeff n f = (k : ℚ) := by
  constructor
  · intro hf n
    obtain ⟨P, rfl⟩ := RingHom.mem_range.mp hf
    exact ⟨PowerSeries.coeff n P, by simp [PowerSeries.coeff_map]⟩
  · intro h
    choose k hk using h
    refine RingHom.mem_range.mpr ⟨PowerSeries.mk k, ?_⟩
    ext n
    simp [PowerSeries.coeff_map, hk]

theorem C_int_mem (k : ℤ) : PowerSeries.C (k : ℚ) ∈ intSeries := by
  have := mem_intSeries_of_map (PowerSeries.C k)
  simpa using this

theorem X_mem_intSeries : (PowerSeries.X : PowerSeries ℚ) ∈ intSeries := by
  have := mem_intSeries_of_map (PowerSeries.X : PowerSeries ℤ)
  simpa using this

/-- `ℓ_T L^{tr}_T ∈ ℤ[[T]]` for `ℓ_T = lcm(1, …, T − 1)`: `n [Tⁿ] L ∈ ℤ` and `n ∣ ℓ_T` for
`1 ≤ n < T`. -/
theorem lcm_mul_trunc_mem {ch : OriginChart} (s : OriginSeries ch) (T : ℕ) :
    PowerSeries.C (Nat.lcmUpto (T - 1) : ℚ) * truncSeries s.L T ∈ intSeries := by
  rw [mem_intSeries_iff]
  intro n
  by_cases hn : n < T
  · rw [PowerSeries.coeff_C_mul, coeff_truncSeries, if_pos hn]
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · refine ⟨0, ?_⟩
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, s.L_zero]
      simp
    · obtain ⟨k, hk⟩ := s.L_integral (by omega : 1 ≤ n)
      have hmem : n ∈ Finset.Icc 1 (T - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hdvd : n ∣ Nat.lcmUpto (T - 1) := by
        unfold Nat.lcmUpto
        exact Finset.dvd_lcm (f := id) hmem
      obtain ⟨t, ht⟩ := hdvd
      refine ⟨(t : ℤ) * k, ?_⟩
      rw [ht]
      push_cast
      linear_combination (t : ℚ) * hk
  · rw [PowerSeries.coeff_C_mul, coeff_truncSeries, if_neg hn]
    exact ⟨0, by simp⟩

/-- `c_i (cen + L^{tr}) ∈ ℤ[[T]]` for `c_i = q_i ℓ_i` and `q_i · cen ∈ ℤ`. -/
theorem scaled_factor_mem (T qi : ℕ) (cenv : ℚ) (z0 : ℤ) (hz0 : (qi : ℚ) * cenv = z0)
    (L : PowerSeries ℚ)
    (hL : PowerSeries.C (Nat.lcmUpto (T - 1) : ℚ) * truncSeries L T ∈ intSeries) :
    PowerSeries.C (((qi * Nat.lcmUpto (T - 1) : ℕ) : ℚ)) *
      (PowerSeries.C cenv + truncSeries L T) ∈ intSeries := by
  have e : (((qi * Nat.lcmUpto (T - 1) : ℕ) : ℚ)) * cenv =
      (((Nat.lcmUpto (T - 1) : ℤ) * z0 : ℤ) : ℚ) := by
    push_cast
    linear_combination ((Nat.lcmUpto (T - 1) : ℕ) : ℚ) * hz0
  have h2 : PowerSeries.C (((qi * Nat.lcmUpto (T - 1) : ℕ) : ℚ)) * truncSeries L T =
      PowerSeries.C (qi : ℚ) * (PowerSeries.C (Nat.lcmUpto (T - 1) : ℚ) * truncSeries L T) := by
    rw [← mul_assoc, ← map_mul, Nat.cast_mul]
  have hsum : PowerSeries.C (((qi * Nat.lcmUpto (T - 1) : ℕ) : ℚ)) *
        (PowerSeries.C cenv + truncSeries L T) =
      PowerSeries.C ((((Nat.lcmUpto (T - 1) : ℤ) * z0 : ℤ) : ℚ)) +
        PowerSeries.C (qi : ℚ) * (PowerSeries.C (Nat.lcmUpto (T - 1) : ℚ) * truncSeries L T) := by
    rw [mul_add, ← map_mul, e, h2]
  rw [hsum]
  have hq : PowerSeries.C (qi : ℚ) ∈ intSeries := by
    simpa using C_int_mem (qi : ℤ)
  exact add_mem (C_int_mem _) (mul_mem hq hL)

/-- One scaled entry is an integer:
`∏_i cc_i^{α_i − β_i} · (∏_i C(α_i, β_i)) [Tⁿ] (Y ∏_i x_i^{α_i − β_i}) ∈ ℤ`
when `Y ∈ ℤ[[T]]` and `cc_i x_i ∈ ℤ[[T]]`. -/
theorem entry_scaled_int {m : ℕ} (Y : PowerSeries ℚ) (hY : Y ∈ intSeries) (cc : Fin m → ℚ)
    (x : Fin m → PowerSeries ℚ) (hx : ∀ i, PowerSeries.C (cc i) * x i ∈ intSeries)
    (α β : Fin m → ℕ) (n : ℕ) :
    ∃ z : ℤ, (∏ i, cc i ^ (α i - β i)) *
      ((∏ i, (((α i).choose (β i) : ℕ) : ℚ)) *
        PowerSeries.coeff n (Y * ∏ i, x i ^ (α i - β i))) = (z : ℚ) := by
  have hprod : PowerSeries.C (∏ i, cc i ^ (α i - β i)) * (Y * ∏ i, x i ^ (α i - β i)) =
      Y * ∏ i, (PowerSeries.C (cc i) * x i) ^ (α i - β i) := by
    rw [map_prod]
    simp only [map_pow]
    rw [mul_left_comm, ← Finset.prod_mul_distrib]
    simp only [mul_pow]
  have hmem : Y * ∏ i, (PowerSeries.C (cc i) * x i) ^ (α i - β i) ∈ intSeries :=
    mul_mem hY (prod_mem fun i _ => pow_mem (hx i) _)
  rw [← hprod] at hmem
  obtain ⟨k, hk⟩ := (mem_intSeries_iff _).mp hmem n
  rw [PowerSeries.coeff_C_mul] at hk
  refine ⟨(∏ i, (((α i).choose (β i) : ℕ) : ℤ)) * k, ?_⟩
  push_cast
  rw [mul_left_comm, hk]

/-! ### The determinant argument, abstractly -/

/-- If the scaled entries `∏ c_i^{α_{r'i} − β_{ri}} A_{rr'}` are integers, `A_{rr'} ≠ 0` forces
`β_r ≤ α_{r'}`, and `det A ≠ 0`, then `1 ≤ |det A| ∏ c_i^{E_i}` with
`Σ_r β_{ri} + E_i = Σ_r α_{ri}`. -/
theorem abstract_det_bound {R : Type*} [Fintype R] [DecidableEq R] {m : ℕ}
    (A : Matrix R R ℚ) (α β : R → Fin m → ℕ) (c : Fin m → ℚ) (hc : ∀ i, 0 < c i)
    (hint : ∀ r r', ∃ z : ℤ, (∏ i, c i ^ (α r' i - β r i)) * A r r' = (z : ℚ))
    (hzero : ∀ r r', A r r' ≠ 0 → ∀ i, β r i ≤ α r' i)
    (hA : A.det ≠ 0) :
    ∃ E : Fin m → ℕ, (∀ i, ∑ r, β r i + E i = ∑ r, α r i) ∧
      1 ≤ |A.det| * ∏ i, c i ^ E i := by
  -- a nonvanishing term of the Leibniz expansion
  have hA' := hA
  rw [Matrix.det_apply'] at hA'
  obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hA'
  have hprod : (∏ k, A (σ k) k) ≠ 0 := fun h => hσ (by rw [h, mul_zero])
  have hle : ∀ k i, β (σ k) i ≤ α k i := fun k i =>
    hzero (σ k) k (Finset.prod_ne_zero_iff.mp hprod k (Finset.mem_univ k)) i
  have hb : ∀ i, ∑ r, β r i ≤ ∑ r, α r i := by
    intro i
    calc ∑ r, β r i = ∑ k, β (σ k) i := (Equiv.sum_comp σ (fun r => β r i)).symm
      _ ≤ ∑ k, α k i := Finset.sum_le_sum fun k _ => hle k i
  refine ⟨fun i => (∑ r, α r i) - ∑ r, β r i, fun i => Nat.add_sub_cancel' (hb i), ?_⟩
  -- the integer matrix
  choose z hz using hint
  have hN : (Matrix.of fun r r' => (∏ i, c i ^ (α r' i - β r i)) * A r r') =
      (Matrix.of fun r r' => z r r').map (Int.castRingHom ℚ) := by
    ext r r'
    simp only [Matrix.of_apply, Matrix.map_apply, eq_intCast]
    exact hz r r'
  have hdetN : (Matrix.of fun r r' => (∏ i, c i ^ (α r' i - β r i)) * A r r').det =
      (((Matrix.of fun r r' => z r r').det : ℤ) : ℚ) := by
    rw [hN]
    have := RingHom.map_det (Int.castRingHom ℚ) (Matrix.of fun r r' => z r r')
    rw [RingHom.mapMatrix_apply] at this
    exact this.symm
  -- `N = diag u * A * diag v`
  obtain ⟨u, hu⟩ : ∃ u : R → ℚ, ∀ r, u r = ∏ i, (c i)⁻¹ ^ β r i := ⟨_, fun _ => rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : R → ℚ, ∀ r, v r = ∏ i, c i ^ α r i := ⟨_, fun _ => rfl⟩
  have hNeq : (Matrix.of fun r r' => (∏ i, c i ^ (α r' i - β r i)) * A r r') =
      Matrix.diagonal u * A * Matrix.diagonal v := by
    ext r r'
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
    by_cases h0 : A r r' = 0
    · rw [h0]; simp
    · have hle' := hzero r r' h0
      have hprod' : ∏ i, c i ^ (α r' i - β r i) = u r * v r' := by
        rw [hu, hv, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [inv_pow, eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ (hc i).ne'), ← pow_add,
          Nat.add_sub_cancel' (hle' i)]
      rw [hprod']; ring
  have hup : ∏ r, u r = ∏ i, (c i)⁻¹ ^ (∑ r, β r i) := by
    simp_rw [hu]
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_pow_eq_pow_sum _ _ _
  have hvp : ∏ r, v r = ∏ i, c i ^ (∑ r, α r i) := by
    simp_rw [hv]
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_pow_eq_pow_sum _ _ _
  have hcomb : (∏ i, (c i)⁻¹ ^ (∑ r, β r i)) * ∏ i, c i ^ (∑ r, α r i) =
      ∏ i, c i ^ (∑ r, α r i - ∑ r, β r i) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (hb i)
    rw [he, Nat.add_sub_cancel_left, pow_add, inv_pow,
      inv_mul_cancel_left₀ (pow_ne_zero _ (hc i).ne')]
  have hdetN2 : (Matrix.of fun r r' => (∏ i, c i ^ (α r' i - β r i)) * A r r').det =
      A.det * ∏ i, c i ^ (∑ r, α r i - ∑ r, β r i) := by
    rw [hNeq, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, hup, hvp,
      ← hcomb]
    ring
  have hPpos : 0 < ∏ i, c i ^ (∑ r, α r i - ∑ r, β r i) :=
    Finset.prod_pos fun i _ => pow_pos (hc i) _
  have hZ : (Matrix.of fun r r' => z r r').det ≠ 0 := by
    intro h0
    have h1 := hdetN2.symm.trans hdetN
    rw [h0, Int.cast_zero] at h1
    exact mul_ne_zero hA hPpos.ne' h1
  have hone : (1 : ℚ) ≤ |(((Matrix.of fun r r' => z r r').det : ℤ) : ℚ)| := by
    exact_mod_cast Int.one_le_abs hZ
  rw [← hdetN, hdetN2, abs_mul, abs_of_pos hPpos] at hone
  exact hone

/-- The logarithmic form: if `log c_i ≤ X w_i` with `X, w_i ≥ 0` then
`log |det A| ≥ −X (Σ_r Σ_i w_i α_{ri} − Σ_r Σ_i w_i β_{ri})`. -/
theorem log_det_lower {R : Type*} [Fintype R] [DecidableEq R] {m : ℕ}
    (A : Matrix R R ℚ) (α β : R → Fin m → ℕ) (c : Fin m → ℚ) (hc : ∀ i, 0 < c i)
    (hint : ∀ r r', ∃ z : ℤ, (∏ i, c i ^ (α r' i - β r i)) * A r r' = (z : ℚ))
    (hzero : ∀ r r', A r r' ≠ 0 → ∀ i, β r i ≤ α r' i)
    (hA : A.det ≠ 0) (w : Fin m → ℝ) (X : ℝ) (hX : 0 ≤ X)
    (hlog : ∀ i, Real.log ((c i : ℚ) : ℝ) ≤ X * w i) (Sα Sβ : ℝ)
    (hSα : ∑ r, ∑ i, w i * (α r i : ℝ) = Sα) (hSβ : ∑ r, ∑ i, w i * (β r i : ℝ) = Sβ) :
    -(X * (Sα - Sβ)) ≤ Real.log |((A.det : ℚ) : ℝ)| := by
  obtain ⟨E, hE, h1⟩ := abstract_det_bound A α β c hc hint hzero hA
  have hD : (0 : ℝ) < |((A.det : ℚ) : ℝ)| := abs_pos.mpr (by exact_mod_cast hA)
  have hcR : ∀ i, (0 : ℝ) < ((c i : ℚ) : ℝ) := fun i => by exact_mod_cast hc i
  have h1R : (1 : ℝ) ≤ |((A.det : ℚ) : ℝ)| * ∏ i, ((c i : ℚ) : ℝ) ^ E i := by
    exact_mod_cast h1
  have hP : (0 : ℝ) < ∏ i, ((c i : ℚ) : ℝ) ^ E i :=
    Finset.prod_pos fun i _ => pow_pos (hcR i) _
  have hlog1 : 0 ≤ Real.log |((A.det : ℚ) : ℝ)| + ∑ i, (E i : ℝ) * Real.log ((c i : ℚ) : ℝ) := by
    have h := Real.log_nonneg h1R
    rw [Real.log_mul hD.ne' hP.ne',
      Real.log_prod (s := Finset.univ) (f := fun i => ((c i : ℚ) : ℝ) ^ E i)
        (fun i _ => (pow_pos (hcR i) _).ne')] at h
    simp only [Real.log_pow] at h
    exact h
  have hEi : ∀ i, (E i : ℝ) = ∑ r, (α r i : ℝ) - ∑ r, (β r i : ℝ) := by
    intro i
    have h := congrArg (Nat.cast : ℕ → ℝ) (hE i)
    push_cast at h
    linarith
  have hE' : ∑ i, w i * (E i : ℝ) = Sα - Sβ := by
    rw [← hSα, ← hSβ]
    simp_rw [hEi, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_comm
  have hsum2 : ∑ i, (E i : ℝ) * Real.log ((c i : ℚ) : ℝ) ≤ X * ∑ i, w i * (E i : ℝ) := by
    calc ∑ i, (E i : ℝ) * Real.log ((c i : ℚ) : ℝ) ≤ ∑ i, (E i : ℝ) * (X * w i) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hlog i) (Nat.cast_nonneg _)
      _ = X * ∑ i, w i * (E i : ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
  rw [hE'] at hsum2
  linarith

/-! ### The arithmetic lower bound -/

theorem submatrix_trunc_apply {m K : ℕ} (W : Weights m) {ch : OriginChart} (s : OriginSeries ch)
    (T : Fin m → ℕ) (cen : Fin K → Fin m → ℚ) (H : ℝ) (sel : Row W K H → Col W H)
    (r r' : Row W K H) :
    ((packetMatrixTr W s T cen H).submatrix id sel) r r' =
      packetEntryTr s T cen r.1 r.2.1 (sel r').1 := rfl

/-- `⌈x⌉₊ − 1 ≤ x` for `x ≥ 0`. -/
theorem natCeil_pred_le (x : ℝ) (hx : 0 ≤ x) : ((⌈x⌉₊ - 1 : ℕ) : ℝ) ≤ x := by
  rcases Nat.eq_zero_or_pos ⌈x⌉₊ with h | h
  · rw [h]; simpa using hx
  · have : ((⌈x⌉₊ - 1 : ℕ) : ℝ) < x := by
      apply Nat.lt_ceil.mp
      omega
    exact this.le

/-- **E11** (`prop:arith`, CM Lemma 15.2 and Corollary 15.3 over `ℤ`), for any constant `c₀` with
`log lcm(1..n) ≤ c₀ n`. Let `F₀ ≥ 1/θ`, let the weights satisfy `log q_i ≤ w_i`, and let `Δ ≠ 0` be
the minor of the packet matrix for the centres `j p_i / q_i` with columns `sel`, which satisfy (S)
(they are columns of `Col W H`). Then `log|Δ|/(M H) ≥ −(1 − b̄) − c₀ F₀ / v₀`. -/
theorem arith_lower_bound_of_lcm {m K : ℕ} (hK : 1 ≤ K) (W : Weights m) {ch : OriginChart}
    (s : OriginSeries ch) (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 1 ≤ q i)
    (hqw : ∀ i, Real.log (q i : ℝ) ≤ (W.w i : ℝ))
    (c₀ : ℝ) (hc₀ : 0 ≤ c₀) (hlcm : ∀ n : ℕ, Real.log (Nat.lcmUpto n : ℝ) ≤ c₀ * n)
    (F₀ : ℝ) (hF₀ : 1 / (W.θ : ℝ) ≤ F₀) {H : ℝ} (hH : 0 < H)
    (sel : Row W K H → Col W H)
    (hΔ : packetDelta W s (gridCentres K p q) H sel ≠ 0) :
    ArithLowerBound (Real.log |((packetDelta W s (gridCentres K p q) H sel : ℚ) : ℝ)|)
      (W.M K H : ℝ) H (W.bbar K H) (c₀ * F₀ / (W.v₀ : ℝ)) := by
  have hv : (0 : ℝ) < W.v₀ := by exact_mod_cast W.v₀_pos
  have hθ : (0 : ℝ) < W.θ := by exact_mod_cast W.θ_pos
  have hw0 : (0 : ℝ) < W.w₀ := by exact_mod_cast W.w₀_pos
  have hF0pos : 0 < F₀ := lt_of_lt_of_le (one_div_pos.mpr hθ) hF₀
  have hEar : 0 ≤ c₀ * F₀ / (W.v₀ : ℝ) := div_nonneg (mul_nonneg hc₀ hF0pos.le) hv.le
  obtain ⟨T, hTdef⟩ : ∃ T : Fin m → ℕ, ∀ i, T i = ⌈F₀ * (W.w i : ℝ) / (W.v₀ : ℝ)⌉₊ :=
    ⟨_, fun _ => rfl⟩
  have hx0 : ∀ i, 0 ≤ F₀ * (W.w i : ℝ) / (W.v₀ : ℝ) := fun i => by
    have : (0 : ℝ) < W.w i := by exact_mod_cast W.w_pos i
    exact div_nonneg (mul_nonneg hF0pos.le this.le) hv.le
  -- the truncation hypothesis of `lem:trunc`
  have hT' : ∀ i, W.w i / W.θ ≤ (T i : ℚ) * W.v₀ := by
    intro i
    have hx : F₀ * (W.w i : ℝ) / (W.v₀ : ℝ) ≤ (T i : ℝ) := by
      rw [hTdef i]; exact Nat.le_ceil _
    have hwi : (0 : ℝ) < W.w i := by exact_mod_cast W.w_pos i
    have h1 : F₀ * (W.w i : ℝ) ≤ (T i : ℝ) * W.v₀ := by
      rwa [div_le_iff₀ hv] at hx
    have h2 : (W.w i : ℝ) / W.θ ≤ F₀ * W.w i := by
      have h := mul_le_mul_of_nonneg_right hF₀ hwi.le
      calc (W.w i : ℝ) / W.θ = 1 / (W.θ : ℝ) * W.w i := by ring
        _ ≤ F₀ * W.w i := h
    have h3 : ((W.w i / W.θ : ℚ) : ℝ) ≤ (((T i : ℚ) * W.v₀ : ℚ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h3
  -- `Δ = det A^{tr}`
  have hdel : packetDelta W s (gridCentres K p q) H sel =
      ((packetMatrixTr W s T (gridCentres K p q) H).submatrix id sel).det :=
    det_packet_trunc W s T hT' (gridCentres K p q) H sel
  have hA : ((packetMatrixTr W s T (gridCentres K p q) H).submatrix id sel).det ≠ 0 := by
    rw [← hdel]; exact hΔ
  unfold ArithLowerBound
  rw [hdel]
  -- the scaling factors `c_i = q_i ℓ_i`
  obtain ⟨c, hcdef⟩ : ∃ c : Fin m → ℚ,
      ∀ i, c i = ((q i * Nat.lcmUpto (T i - 1) : ℕ) : ℚ) := ⟨_, fun _ => rfl⟩
  have hqpos : ∀ i, 0 < q i := fun i => by have := hq i; omega
  have hcpos : ∀ i, 0 < c i := fun i => by
    rw [hcdef i]
    exact_mod_cast Nat.mul_pos (hqpos i) (Nat.lcmUpto_pos _)
  have hq0 : ∀ i, (q i : ℚ) ≠ 0 := fun i => Nat.cast_ne_zero.mpr (hqpos i).ne'
  have hcenint : ∀ (j : Fin K) (i : Fin m),
      ∃ z : ℤ, (q i : ℚ) * gridCentres K p q j i = (z : ℚ) := fun j i =>
    ⟨((j : ℕ) : ℤ) * p i, by
      have := hq0 i
      simp only [gridCentres]
      push_cast
      field_simp⟩
  -- integrality of the scaled entries
  have hint : ∀ r r' : Row W K H,
      ∃ z : ℤ, (∏ i, c i ^ ((sel r').1.2.2 i - r.2.1 i.succ)) *
        (((packetMatrixTr W s T (gridCentres K p q) H).submatrix id sel) r r') = (z : ℚ) := by
    intro r r'
    have hY : (s.U ^ (sel r').1.1 * PowerSeries.X ^ (sel r').1.2.1.val : PowerSeries ℚ) ∈
        intSeries := by
      obtain ⟨Wz, hWz⟩ := s.U_integral
      have hU : s.U ∈ intSeries := by rw [hWz]; exact mem_intSeries_of_map Wz
      exact mul_mem (pow_mem hU _) (pow_mem X_mem_intSeries _)
    have hx : ∀ i, PowerSeries.C (c i) *
        (PowerSeries.C (gridCentres K p q r.1 i) + truncSeries s.L (T i)) ∈ intSeries := by
      intro i
      rw [hcdef i]
      obtain ⟨z0, hz0⟩ := hcenint r.1 i
      exact scaled_factor_mem (T i) (q i) _ z0 hz0 s.L (lcm_mul_trunc_mem s (T i))
    have h := entry_scaled_int
      (s.U ^ (sel r').1.1 * PowerSeries.X ^ (sel r').1.2.1.val) hY c
      (fun i => PowerSeries.C (gridCentres K p q r.1 i) + truncSeries s.L (T i)) hx
      (sel r').1.2.2 (fun i => r.2.1 i.succ) (r.2.1 0)
    rw [submatrix_trunc_apply]
    exact h
  have hzero : ∀ r r' : Row W K H,
      (((packetMatrixTr W s T (gridCentres K p q) H).submatrix id sel) r r') ≠ 0 →
        ∀ i, r.2.1 i.succ ≤ (sel r').1.2.2 i := by
    intro r r' h0 i
    by_contra hlt
    push_neg at hlt
    apply h0
    have hz : ((((sel r').1.2.2 i).choose (r.2.1 i.succ) : ℕ) : ℚ) = 0 := by
      rw [Nat.choose_eq_zero_of_lt hlt]; simp
    rw [submatrix_trunc_apply]
    unfold packetEntryTr
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hz, zero_mul]
  -- logarithm of the scaling factors
  have hlog : ∀ i, Real.log ((c i : ℚ) : ℝ) ≤ (1 + c₀ * F₀ / (W.v₀ : ℝ)) * (W.w i : ℝ) := by
    intro i
    have hqr : (0 : ℝ) < (q i : ℝ) := by exact_mod_cast hqpos i
    have hlr : (0 : ℝ) < (Nat.lcmUpto (T i - 1) : ℝ) := by exact_mod_cast Nat.lcmUpto_pos _
    have hcast : ((c i : ℚ) : ℝ) = (q i : ℝ) * (Nat.lcmUpto (T i - 1) : ℝ) := by
      rw [hcdef i]; norm_cast
    have hTm : ((T i - 1 : ℕ) : ℝ) ≤ F₀ * (W.w i : ℝ) / (W.v₀ : ℝ) := by
      rw [hTdef i]; exact natCeil_pred_le _ (hx0 i)
    calc Real.log ((c i : ℚ) : ℝ)
        = Real.log (q i : ℝ) + Real.log (Nat.lcmUpto (T i - 1) : ℝ) := by
          rw [hcast, Real.log_mul hqr.ne' hlr.ne']
      _ ≤ (W.w i : ℝ) + c₀ * (F₀ * (W.w i : ℝ) / (W.v₀ : ℝ)) :=
          add_le_add (hqw i) ((hlcm _).trans (mul_le_mul_of_nonneg_left hTm hc₀))
      _ = (1 + c₀ * F₀ / (W.v₀ : ℝ)) * (W.w i : ℝ) := by ring
  -- the weight sums
  have hMpos : 0 < W.M K H := Nat.mul_pos (by omega) (W.J_pos hH)
  have hMr : (0 : ℝ) < (W.M K H : ℝ) := by exact_mod_cast hMpos
  have hMH : 0 < (W.M K H : ℝ) * H := mul_pos hMr hH
  have hbb0 : 0 ≤ W.bbar K H := W.bbar_nonneg K hH.le
  have hcol : ∀ r : Row W K H, ((W.wt (sel r).1.2.2 : ℚ) : ℝ) ≤ H := by
    intro r
    have h := W.col_cond (sel r)
    have h0 : 0 ≤ 2 * (W.w₀ : ℝ) * (((sel r).1.1 : ℝ) + 2 * ((sel r).1.2.1.val : ℝ)) :=
      mul_nonneg (mul_nonneg (by norm_num) hw0.le)
        (add_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
    linarith
  have hSα : ∑ r : Row W K H, ((W.wt (sel r).1.2.2 : ℚ) : ℝ) ≤ (W.M K H : ℝ) * H := by
    calc ∑ r : Row W K H, ((W.wt (sel r).1.2.2 : ℚ) : ℝ) ≤ ∑ _r : Row W K H, H :=
          Finset.sum_le_sum fun r _ => hcol r
      _ = (W.M K H : ℝ) * H := by
          rw [Finset.sum_const, Finset.card_univ, W.card_row, nsmul_eq_mul]
  have hSβ : ∑ r : Row W K H, ((W.wt (fun i => r.2.1 i.succ) : ℚ) : ℝ) =
      W.bbar K H * ((W.M K H : ℝ) * H) := by
    have hb : W.bbar K H =
        (∑ r : Row W K H, ((W.wt (fun i => r.2.1 i.succ) : ℚ) : ℝ)) / ((W.M K H : ℝ) * H) := rfl
    exact ((eq_div_iff hMH.ne').mp hb).symm
  have hkey := log_det_lower
    ((packetMatrixTr W s T (gridCentres K p q) H).submatrix id sel)
    (fun r' => (sel r').1.2.2) (fun r i => r.2.1 i.succ) c hcpos hint hzero hA
    (fun i => (W.w i : ℝ)) (1 + c₀ * F₀ / (W.v₀ : ℝ)) (by linarith)
    hlog (∑ r : Row W K H, ((W.wt (sel r).1.2.2 : ℚ) : ℝ))
    (∑ r : Row W K H, ((W.wt (fun i => r.2.1 i.succ) : ℚ) : ℝ))
    (Finset.sum_congr rfl fun r _ => (W.wt_cast _).symm)
    (Finset.sum_congr rfl fun r _ => (W.wt_cast _).symm)
  rw [le_div_iff₀ hMH]
  have h1 : (1 + c₀ * F₀ / (W.v₀ : ℝ)) *
      (∑ r : Row W K H, ((W.wt (sel r).1.2.2 : ℚ) : ℝ) -
        ∑ r : Row W K H, ((W.wt (fun i => r.2.1 i.succ) : ℚ) : ℝ)) ≤
      (1 + c₀ * F₀ / (W.v₀ : ℝ)) * ((W.M K H : ℝ) * H - W.bbar K H * ((W.M K H : ℝ) * H)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 := mul_nonneg (mul_nonneg hEar hbb0) hMH.le
  nlinarith [h1, h2, hkey]

/-- **E11** (`prop:arith`) with the lcm constant of `Arith.LcmBound`: `c₀ = log 4 + 4`.
The paper quotes the Rosser–Schoenfeld constant `1.03883`; any absolute constant serves
(`arith_lower_bound_of_lcm`). -/
theorem arith_lower_bound {m K : ℕ} (hK : 1 ≤ K) (W : Weights m) {ch : OriginChart}
    (s : OriginSeries ch) (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 1 ≤ q i)
    (hqw : ∀ i, Real.log (q i : ℝ) ≤ (W.w i : ℝ))
    (F₀ : ℝ) (hF₀ : 1 / (W.θ : ℝ) ≤ F₀) {H : ℝ} (hH : 0 < H)
    (sel : Row W K H → Col W H)
    (hΔ : packetDelta W s (gridCentres K p q) H sel ≠ 0) :
    ArithLowerBound (Real.log |((packetDelta W s (gridCentres K p q) H sel : ℚ) : ℝ)|)
      (W.M K H : ℝ) H (W.bbar K H) (lcmConst * F₀ / (W.v₀ : ℝ)) :=
  arith_lower_bound_of_lcm hK W s p q hq hqw lcmConst lcmConst_pos.le log_lcmUpto_le F₀ hF₀ hH
    sel hΔ

end CatalanCore.Elliptic.Arith
