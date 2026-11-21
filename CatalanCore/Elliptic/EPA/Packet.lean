module

public import CatalanCore.Elliptic.Interfaces
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The determinant data and the packet matrix (row E23)

Labels refer to `work/paper-elliptic/elliptic-periods.tex`, §"The interpolation determinant".

* `Weights.mem_rowSet_iff'`, `Weights.mem_colSet_iff`: the finite sets of `Interfaces` are the
  paper's `𝒥_H = {(s,β) : v₀ s + W(β)/θ < H}` and the columns of `ℱ_H` under (S).
* `Weights.card_row`, `Weights.J_pos`, `Weights.bbar_nonneg`, `Weights.bbar_lt_theta`:
  `|Row| = M = K J_H` and `0 ≤ b̄ < θ`.
* `packetPoly`, `packetEntry_eq_coeff`: eq:packet → eq:entry. The expression
  `P(U(T), T, c_j + V + L(T))` for `P = u^k t^b Z^α` is an element of `ℚ⟦T⟧[V₁,…,V_m]`, and its
  coefficient at `V^β` is `C(α, β) · [T^s](…)` read off by `packetEntry`.
* `exists_full_row_minor_of_surjective`, `exists_minor_of_surjective`: a surjective packet map has
  a nonzero selected minor `Δ`, and its columns are columns of `Col W H`, i.e. satisfy (S).
* `PacketSurjective`, `PacketMinor`, `packetMinor_of_packetSurjective`: the same with the
  quantifier order of `thm:epa` (row E09): `D_EPA` before the centres, `H₀` after them.

`exists_full_row_minor_of_surjective` is adapted from `exists_full_row_minor_of_surjective` in
`Approximation/InterpolationMatrix.lean` of openai/math (fd4aeeb2, Apache License 2.0,
Copyright OpenAI), restated for any field and over our `Row`/`Col` types without the
`InterpolationMatrix` closure.
-/

@[expose] public section

namespace CatalanCore.Elliptic

/-! ### The sets `𝒥_H`, columns, `b̄` -/

namespace Weights

variable {m : ℕ} (W : Weights m)

theorem rowWeights_zero : W.rowWeights 0 = (W.v₀ : ℝ) := by simp [rowWeights]

theorem rowWeights_succ (i : Fin m) : W.rowWeights i.succ = (W.w i : ℝ) / (W.θ : ℝ) := by
  simp [rowWeights]

theorem rowWeights_pos (i : Fin (m + 1)) : 0 < W.rowWeights i := by
  induction i using Fin.cases with
  | zero => rw [rowWeights_zero]; exact_mod_cast W.v₀_pos
  | succ i =>
    rw [rowWeights_succ]
    exact div_pos (by exact_mod_cast W.w_pos i) (by exact_mod_cast W.θ_pos)

theorem wt_cast (β : Fin m → ℕ) :
    ((W.wt β : ℚ) : ℝ) = ∑ i, (W.w i : ℝ) * (β i : ℝ) := by
  simp [wt]

theorem wt_nonneg (β : Fin m → ℕ) : 0 ≤ ((W.wt β : ℚ) : ℝ) := by
  rw [wt_cast]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (by exact_mod_cast (W.w_pos i).le) (Nat.cast_nonneg _)

/-- Membership in `𝒥_H`, in terms of the row weights. -/
theorem mem_rowSet_iff (H : ℝ) (a : Fin (m + 1) → ℕ) :
    a ∈ W.rowSet H ↔ ∑ i, W.rowWeights i * (a i : ℝ) < H := by
  simp only [rowSet, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i => ?_, h⟩
    have h1 : W.rowWeights i * (a i : ℝ) ≤ ∑ j, W.rowWeights j * (a j : ℝ) :=
      Finset.single_le_sum (f := fun j => W.rowWeights j * (a j : ℝ))
        (fun j _ => mul_nonneg (W.rowWeights_pos j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
    have h2 : (a i : ℝ) ≤ H / W.rowWeights i := by
      rw [le_div_iff₀ (W.rowWeights_pos i)]
      linarith [mul_comm (W.rowWeights i) (a i : ℝ)]
    exact Nat.lt_succ_of_le (Nat.le_floor h2)

/-- Membership in `𝒥_H`, in the form of the paper: `v₀ s + W(β)/θ < H`. -/
theorem mem_rowSet_iff' (H : ℝ) (a : Fin (m + 1) → ℕ) :
    a ∈ W.rowSet H ↔
      (W.v₀ : ℝ) * (a 0 : ℝ) + ((W.wt (fun i => a i.succ) : ℚ) : ℝ) / (W.θ : ℝ) < H := by
  rw [mem_rowSet_iff, Fin.sum_univ_succ, rowWeights_zero, wt_cast, Finset.sum_div]
  simp only [rowWeights_succ, div_mul_eq_mul_div]

/-- Membership in the column set: condition (S), `2 w₀ (k + 2b) + W(α) ≤ H`. -/
theorem mem_colSet_iff (H : ℝ) (c : ColIdx m) :
    c ∈ W.colSet H ↔
      2 * (W.w₀ : ℝ) * ((c.1 : ℝ) + 2 * (c.2.1.val : ℝ)) + ((W.wt c.2.2 : ℚ) : ℝ) ≤ H := by
  have hw0 : (0 : ℝ) < W.w₀ := by exact_mod_cast W.w₀_pos
  have hwnn := W.wt_nonneg c.2.2
  have hb : (0 : ℝ) ≤ (c.2.1.val : ℝ) := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ (c.1 : ℝ) := Nat.cast_nonneg _
  have hpos : 0 ≤ 2 * (W.w₀ : ℝ) * ((c.1 : ℝ) + 2 * (c.2.1.val : ℝ)) :=
    mul_nonneg (by positivity) (by positivity)
  simp only [colSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_univ,
    Fintype.mem_piFinset, true_and]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨?_, fun i => ?_⟩, h⟩
    · have h2 : (c.1 : ℝ) ≤ H / (2 * (W.w₀ : ℝ)) := by
        rw [le_div_iff₀ (by positivity)]
        have := mul_nonneg hw0.le hb
        nlinarith
      exact Nat.lt_succ_of_le (Nat.le_floor h2)
    · have hwi : (0 : ℝ) < W.w i := by exact_mod_cast W.w_pos i
      have h1 : (W.w i : ℝ) * (c.2.2 i : ℝ) ≤ ((W.wt c.2.2 : ℚ) : ℝ) := by
        rw [wt_cast]
        exact Finset.single_le_sum (f := fun j => (W.w j : ℝ) * (c.2.2 j : ℝ))
          (fun j _ => mul_nonneg (by exact_mod_cast (W.w_pos j).le) (Nat.cast_nonneg _))
          (Finset.mem_univ i)
      have h2 : (c.2.2 i : ℝ) ≤ H / (W.w i : ℝ) := by
        rw [le_div_iff₀ hwi]
        linarith [mul_comm (W.w i : ℝ) (c.2.2 i : ℝ)]
      exact Nat.lt_succ_of_le (Nat.le_floor h2)

/-- Every column of the packet matrix satisfies (S). -/
theorem col_cond {H : ℝ} (c : Col W H) :
    2 * (W.w₀ : ℝ) * ((c.1.1 : ℝ) + 2 * (c.1.2.1.val : ℝ)) + ((W.wt c.1.2.2 : ℚ) : ℝ) ≤ H :=
  (W.mem_colSet_iff H c.1).mp c.2

theorem zero_mem_rowSet {H : ℝ} (hH : 0 < H) : (0 : Fin (m + 1) → ℕ) ∈ W.rowSet H := by
  rw [mem_rowSet_iff]
  simpa using hH

theorem J_pos {H : ℝ} (hH : 0 < H) : 0 < W.J H :=
  Finset.card_pos.mpr ⟨0, W.zero_mem_rowSet hH⟩

/-- `|Row| = M = K J_H`. -/
theorem card_row (K : ℕ) (H : ℝ) : Fintype.card (Row W K H) = W.M K H := by
  simp [Row, M, J]

/-- Each row of `𝒥_H` has `W(β) < θ H`. -/
theorem wt_row_lt {H : ℝ} {a : Fin (m + 1) → ℕ} (ha : a ∈ W.rowSet H) :
    ((W.wt (fun i => a i.succ) : ℚ) : ℝ) < (W.θ : ℝ) * H := by
  rw [mem_rowSet_iff'] at ha
  have hθ : (0 : ℝ) < W.θ := by exact_mod_cast W.θ_pos
  have h0 : 0 ≤ (W.v₀ : ℝ) * (a 0 : ℝ) :=
    mul_nonneg (by exact_mod_cast W.v₀_pos.le) (Nat.cast_nonneg _)
  have h3 : ((W.wt (fun i => a i.succ) : ℚ) : ℝ) / (W.θ : ℝ) < H := by linarith
  have := (div_lt_iff₀ hθ).mp h3
  linarith

theorem bbar_nonneg (K : ℕ) {H : ℝ} (hH : 0 ≤ H) : 0 ≤ W.bbar K H := by
  unfold bbar
  exact div_nonneg (Finset.sum_nonneg fun ρ _ => W.wt_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) hH)

/-- `b̄ < θ` (paper, after `eq:entry`). -/
theorem bbar_lt_theta {K : ℕ} (hK : 1 ≤ K) {H : ℝ} (hH : 0 < H) : W.bbar K H < (W.θ : ℝ) := by
  have hJ := W.J_pos hH
  have hMn : 0 < W.M K H := Nat.mul_pos hK hJ
  have hM : (0 : ℝ) < (W.M K H : ℝ) := by exact_mod_cast hMn
  have hne : (Finset.univ : Finset (Row W K H)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_univ, W.card_row]
    exact hMn
  unfold bbar
  rw [div_lt_iff₀ (mul_pos hM hH)]
  calc ∑ ρ : Row W K H, ((W.wt (fun i => ρ.2.1 i.succ) : ℚ) : ℝ)
      < ∑ _ρ : Row W K H, (W.θ : ℝ) * H :=
        Finset.sum_lt_sum_of_nonempty hne fun ρ _ => W.wt_row_lt ρ.2.2
    _ = (W.θ : ℝ) * ((W.M K H : ℝ) * H) := by
        rw [Finset.sum_const, Finset.card_univ, W.card_row, nsmul_eq_mul]
        ring

end Weights

/-! ### eq:packet → eq:entry -/

section Expansion

open MvPolynomial

theorem monomial_prod_single {R : Type*} [CommSemiring R] {m : ℕ} (p : Fin m → ℕ)
    (c : Fin m → R) :
    ∏ i, (monomial (Finsupp.single i (p i)) (c i) : MvPolynomial (Fin m) R) =
      monomial (Finsupp.equivFunOnFinite.symm p) (∏ i, c i) := by
  classical
  have key : ∀ s : Finset (Fin m),
      ∏ i ∈ s, (monomial (Finsupp.single i (p i)) (c i) : MvPolynomial (Fin m) R) =
        monomial (∑ i ∈ s, Finsupp.single i (p i)) (∏ i ∈ s, c i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha, ih, monomial_mul_monomial]
  have e : ∑ i, Finsupp.single i (p i) = Finsupp.equivFunOnFinite.symm p := by
    ext j
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [key, e]

theorem X_add_C_pow_eq {R : Type*} [CommRing R] {m : ℕ} (i : Fin m) (g : R) (n : ℕ) :
    ((X i + C g) ^ n : MvPolynomial (Fin m) R) =
      ∑ k ∈ Finset.range (n + 1),
        monomial (Finsupp.single i k) (((n.choose k : ℕ) : R) * g ^ (n - k)) := by
  rw [add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← C_mul_X_pow_eq_monomial]
  simp only [map_mul, map_pow, map_natCast]
  ring

/-- `[V^β] ∏_i (V_i + g_i)^{α_i} = ∏_i C(α_i, β_i) g_i^{α_i − β_i}` (zero unless `β ≤ α`, where the
binomial coefficient vanishes). -/
theorem coeff_prod_X_add_C {R : Type*} [CommRing R] {m : ℕ} (g : Fin m → R) (α β : Fin m → ℕ) :
    (∏ i, (X i + C (g i)) ^ α i : MvPolynomial (Fin m) R).coeff
        (Finsupp.equivFunOnFinite.symm β) =
      ∏ i, (((α i).choose (β i) : ℕ) : R) * g i ^ (α i - β i) := by
  classical
  simp_rw [X_add_C_pow_eq]
  rw [Finset.prod_univ_sum, coeff_sum]
  have h2 : ∀ p : Fin m → ℕ,
      (∏ i, (monomial (Finsupp.single i (p i))
        (((α i).choose (p i) : R) * g i ^ (α i - p i)) : MvPolynomial (Fin m) R)).coeff
          (Finsupp.equivFunOnFinite.symm β) =
        if p = β then ∏ i, (((α i).choose (p i) : R) * g i ^ (α i - p i)) else 0 := by
    intro p
    rw [monomial_prod_single, coeff_monomial]
    by_cases h : p = β
    · subst h; simp
    · have h' : Finsupp.equivFunOnFinite.symm p ≠ Finsupp.equivFunOnFinite.symm β :=
        fun e => h (Finsupp.equivFunOnFinite.symm.injective e)
      simp [h, h']
  rw [Finset.sum_congr rfl fun p _ => h2 p, Finset.sum_ite_eq']
  by_cases hβ : β ∈ Fintype.piFinset (fun i => Finset.range (α i + 1))
  · simp [hβ]
  · simp only [hβ, ↓reduceIte]
    rw [Fintype.mem_piFinset] at hβ
    simp only [not_forall] at hβ
    obtain ⟨i, hi⟩ := hβ
    rw [Finset.mem_range, not_lt] at hi
    symm
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- `P(U(T), T, c_{j1} + V₁ + L(T), …, c_{jm} + V_m + L(T)) ∈ ℚ⟦T⟧[V₁, …, V_m]` for the monomial
`P = u^k t^b Z^α` of the column `c = (k, b, α)` and the centre `cen j`. -/
noncomputable def packetPoly {m K : ℕ} {ch : OriginChart} (s : OriginSeries ch)
    (cen : Fin K → Fin m → ℚ) (j : Fin K) (c : ColIdx m) :
    MvPolynomial (Fin m) (PowerSeries ℚ) :=
  MvPolynomial.C (s.U ^ c.1 * PowerSeries.X ^ c.2.1.val) *
    ∏ i : Fin m,
      (MvPolynomial.X i + MvPolynomial.C (PowerSeries.C (cen j i) + s.L)) ^ c.2.2 i

/-- eq:packet → eq:entry: the coefficient `[T^s V^β]` of `packetPoly` is the entry
`C(α, β) [T^s] (U^k T^b ∏_i (c_{ji} + L)^{α_i − β_i})` (`packetEntry`). -/
theorem packetEntry_eq_coeff {m K : ℕ} {ch : OriginChart} (s : OriginSeries ch)
    (cen : Fin K → Fin m → ℚ) (j : Fin K) (r : Fin (m + 1) → ℕ) (c : ColIdx m) :
    packetEntry s cen j r c =
      PowerSeries.coeff (r 0)
        ((packetPoly s cen j c).coeff
          (Finsupp.equivFunOnFinite.symm (fun i : Fin m => r i.succ))) := by
  unfold packetEntry packetPoly
  rw [MvPolynomial.coeff_C_mul, coeff_prod_X_add_C]
  have hP : (∏ i : Fin m, (((c.2.2 i).choose (r i.succ) : ℕ) : PowerSeries ℚ) *
        (PowerSeries.C (cen j i) + s.L) ^ (c.2.2 i - r i.succ)) =
      PowerSeries.C (∏ i : Fin m, (((c.2.2 i).choose (r i.succ) : ℕ) : ℚ)) *
        ∏ i : Fin m, (PowerSeries.C (cen j i) + s.L) ^ (c.2.2 i - r i.succ) := by
    rw [Finset.prod_mul_distrib, map_prod]
    simp
  rw [hP, mul_left_comm, PowerSeries.coeff_C_mul]

end Expansion

theorem packetMatrix_apply {m K : ℕ} (W : Weights m) {ch : OriginChart} (s : OriginSeries ch)
    (cen : Fin K → Fin m → ℚ) (H : ℝ) (ρ : Row W K H) (c : Col W H) :
    packetMatrix W s cen H ρ c = packetEntry s cen ρ.1 ρ.2.1 c.1 := rfl

/-- The packet minor `Δ` for a selection of columns. -/
noncomputable def packetDelta {m K : ℕ} (W : Weights m) {ch : OriginChart} (s : OriginSeries ch)
    (cen : Fin K → Fin m → ℚ) (H : ℝ) (sel : Row W K H → Col W H) : ℚ :=
  ((packetMatrix W s cen H).submatrix id sel).det

/-! ### Surjective packet map ⇒ a nonzero minor -/

/-- A matrix over a field whose `mulVecLin` is surjective has a nonzero maximal minor, with
injective column selection. Adapted from openai/math `exists_full_row_minor_of_surjective`
(Apache License 2.0). -/
theorem exists_full_row_minor_of_surjective
    {R C F : Type*} [Fintype R] [Fintype C] [DecidableEq R] [Field F]
    (A : Matrix R C F) (hA : Function.Surjective A.mulVecLin) :
    ∃ selection : R → C, Function.Injective selection ∧
      (A.submatrix id selection).det ≠ 0 := by
  classical
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hA
  have hexp : (A * B).det =
      ∑ p : R → C, (A.submatrix id p).det * ∏ i, B (p i) i := by
    calc
      (A * B).det = ∑ p : R → C, ∑ σ : Equiv.Perm R,
          ((Equiv.Perm.sign σ : ℤ) : F) * ∏ i, A (σ i) (p i) * B (p i) i := by
        simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
          Finset.mul_sum, Fintype.piFinset_univ]
        rw [Finset.sum_comm]
      _ = ∑ p : R → C, (A.submatrix id p).det * ∏ i, B (p i) i := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq,
          Finset.prod_mul_distrib, ← mul_assoc, ← Finset.sum_mul]
  have hsum : (∑ p : R → C, (A.submatrix id p).det * ∏ i, B (p i) i) ≠ 0 := by
    rw [← hexp, hB, Matrix.det_one]
    exact one_ne_zero
  obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hdet : (A.submatrix id p).det ≠ 0 := by
    intro h
    apply hp
    rw [h, zero_mul]
  refine ⟨p, ?_, hdet⟩
  intro i j hij
  by_contra hne
  exact hdet (Matrix.det_zero_of_column_eq hne (fun k => congrArg (A k) hij))

/-- Surjective packet map over `ℚ` ⇒ some selected minor `Δ ≠ 0`; the columns are columns of
`Col W H`, so they satisfy (S) (`Weights.col_cond`). -/
theorem exists_minor_of_surjective_rat {m K : ℕ} (W : Weights m) {ch : OriginChart}
    (s : OriginSeries ch) (cen : Fin K → Fin m → ℚ) (H : ℝ)
    (hsurj : Function.Surjective (packetMatrix W s cen H).mulVecLin) :
    ∃ sel : Row W K H → Col W H, Function.Injective sel ∧
      packetDelta W s cen H sel ≠ 0 ∧
      ∀ ρ, 2 * (W.w₀ : ℝ) * (((sel ρ).1.1 : ℝ) + 2 * ((sel ρ).1.2.1.val : ℝ)) +
        ((W.wt (sel ρ).1.2.2 : ℚ) : ℝ) ≤ H := by
  obtain ⟨sel, hinj, hdet⟩ := exists_full_row_minor_of_surjective _ hsurj
  exact ⟨sel, hinj, hdet, fun ρ => W.col_cond (sel ρ)⟩

/-- The same over any field `F ⊇ ℚ` (the paper's `F = ℂ`): the matrix is rational, so a minor that
is nonzero in `F` is nonzero in `ℚ`. -/
theorem exists_minor_of_surjective {m K : ℕ} (W : Weights m) {ch : OriginChart}
    (s : OriginSeries ch) (cen : Fin K → Fin m → ℚ) (H : ℝ) {F : Type*} [Field F] [Algebra ℚ F]
    (hsurj : Function.Surjective
      ((packetMatrix W s cen H).map (algebraMap ℚ F)).mulVecLin) :
    ∃ sel : Row W K H → Col W H, Function.Injective sel ∧
      packetDelta W s cen H sel ≠ 0 ∧
      ∀ ρ, 2 * (W.w₀ : ℝ) * (((sel ρ).1.1 : ℝ) + 2 * ((sel ρ).1.2.1.val : ℝ)) +
        ((W.wt (sel ρ).1.2.2 : ℚ) : ℝ) ≤ H := by
  obtain ⟨sel, hinj, hdet⟩ := exists_full_row_minor_of_surjective _ hsurj
  refine ⟨sel, hinj, ?_, fun ρ => W.col_cond (sel ρ)⟩
  have h : (algebraMap ℚ F) (packetDelta W s cen H sel) =
      (((packetMatrix W s cen H).map (algebraMap ℚ F)).submatrix id sel).det := by
    unfold packetDelta
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    rfl
  intro h0
  apply hdet
  rw [← h, h0, map_zero]

/-! ### The quantifier order of `thm:epa` -/

/-- The conclusion of `thm:epa` (row E09) for fixed data `W` (weights, thresholds), the chart series
`s` and the number `K` of centres: there is `D_EPA`, depending on those data and **not** on the
centres, such that for every centre array with each coordinate injective in `j` there is `H₀`
(depending on the centres) such that for every integer `H ≥ H₀` divisible by `D_EPA` the packet map
is surjective (over `ℂ`). The centres are rational, as in the application `c_{ji} = j p_i / q_i`. -/
def PacketSurjective {m : ℕ} (W : Weights m) (K : ℕ) {ch : OriginChart}
    (s : OriginSeries ch) : Prop :=
  ∃ D : ℕ, 0 < D ∧ ∀ cen : Fin K → Fin m → ℚ, (∀ i : Fin m, Function.Injective fun j => cen j i) →
    ∃ H₀ : ℕ, ∀ H : ℕ, H₀ ≤ H → D ∣ H →
      Function.Surjective ((packetMatrix W s cen (H : ℝ)).map (algebraMap ℚ ℂ)).mulVecLin

/-- "Some selected minor is nonzero", with the same quantifier order as `PacketSurjective`. -/
def PacketMinor {m : ℕ} (W : Weights m) (K : ℕ) {ch : OriginChart}
    (s : OriginSeries ch) : Prop :=
  ∃ D : ℕ, 0 < D ∧ ∀ cen : Fin K → Fin m → ℚ, (∀ i : Fin m, Function.Injective fun j => cen j i) →
    ∃ H₀ : ℕ, ∀ H : ℕ, H₀ ≤ H → D ∣ H →
      ∃ sel : Row W K (H : ℝ) → Col W (H : ℝ), Function.Injective sel ∧
        packetDelta W s cen (H : ℝ) sel ≠ 0

/-- E23: the surjectivity of `thm:epa` gives the nonzero minor `Δ`, with `D_EPA` independent of the
centres and `H₀` depending on them. -/
theorem packetMinor_of_packetSurjective {m : ℕ} (W : Weights m) (K : ℕ) {ch : OriginChart}
    (s : OriginSeries ch) (h : PacketSurjective W K s) : PacketMinor W K s := by
  obtain ⟨D, hD, hall⟩ := h
  refine ⟨D, hD, fun cen hcen => ?_⟩
  obtain ⟨H₀, hH₀⟩ := hall cen hcen
  refine ⟨H₀, fun H hH hdvd => ?_⟩
  obtain ⟨sel, hinj, hdet, -⟩ := exists_minor_of_surjective W s cen (H : ℝ) (hH₀ H hH hdvd)
  exact ⟨sel, hinj, hdet⟩

end CatalanCore.Elliptic
