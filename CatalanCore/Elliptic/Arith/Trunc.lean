module

public import CatalanCore.Elliptic.Interfaces

@[expose] public section

/-!
# E10: the truncation lemma (`lem:trunc`, CM Lemma 15.1)

Let `T₁, …, T_m` be natural numbers with `w_i / θ ≤ T_i v₀`, and let `L_i^{tr}` be the part of `L` of
degree `< T_i`. Let `A^{tr}` be the packet matrix (eq:entry) with `L` replaced by `L_i^{tr}` in the
factor of index `i`. Then `det A^{tr} = det A` for every choice of the columns.

Proof (paper). Put `R_i = L − L_i^{tr}`. The substitution `V_i ↦ V_i + R_i(T)` does not decrease the
weight `v₀ s + W(β)/θ`, since every term of `R_i` has degree `≥ T_i`, hence weight `≥ T_i v₀ ≥ w_i/θ`.
It carries the truncated evaluation to the full one, and its matrix on the rows `𝒥_H` is unitriangular
for the order by `|β|`.

Lean form. With `Y = U^k T^b`, `x_i = c_{ji} + L_i^{tr}` and the binomial identity
`C(α,β) (x + R)^{α−β} = Σ_γ C(γ,β) R^{γ−β} · C(α,γ) x^{α−γ}` the entry of `A` in row `(j, s, β)` is
`Σ_{(s',γ)} S_{(s,β),(s',γ)} A^{tr}_{(j,s',γ)}`, with the shear coefficient
`S_{(s,β),(s',γ)} = C(γ,β) [T^{s−s'}] ∏ R_i^{γ_i−β_i}` (`entry_shear`). A nonzero coefficient forces
`weight(s',γ) ≤ weight(s,β)` (`shearEntry_weight_le`), so only rows of `𝒥_H` occur, and
`A = Pbig · A^{tr}` (`packetMatrix_eq_shear_mul`) with `Pbig` block triangular with identity diagonal
blocks (`det_shearMatrix`). The statement is `det_packet_trunc`.
-/

namespace CatalanCore.Elliptic.Arith

open CatalanCore.Elliptic

/-! ### Truncation of power series -/

/-- The part of `f` of degree `< n`, as a power series. -/
noncomputable def truncSeries (f : PowerSeries ℚ) (n : ℕ) : PowerSeries ℚ :=
  ((PowerSeries.trunc n f : Polynomial ℚ) : PowerSeries ℚ)

/-- `f − truncSeries f n`: the terms of degree `≥ n`. -/
noncomputable def tailSeries (f : PowerSeries ℚ) (n : ℕ) : PowerSeries ℚ := f - truncSeries f n

theorem coeff_truncSeries (f : PowerSeries ℚ) (n k : ℕ) :
    PowerSeries.coeff k (truncSeries f n) = if k < n then PowerSeries.coeff k f else 0 := by
  simp [truncSeries, Polynomial.coeff_coe, PowerSeries.coeff_trunc]

theorem X_pow_dvd_tailSeries (f : PowerSeries ℚ) (n : ℕ) :
    (PowerSeries.X : PowerSeries ℚ) ^ n ∣ tailSeries f n := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro k hk
  simp [tailSeries, coeff_truncSeries, hk]

/-! ### Algebra: binomial shift and the expansion of one entry -/

theorem coeff_natProd_mul {ι : Type*} (t : Finset ι) (n : ι → ℕ) (s : ℕ) (F : PowerSeries ℚ) :
    PowerSeries.coeff s ((∏ i ∈ t, ((n i : ℕ) : PowerSeries ℚ)) * F) =
      (∏ i ∈ t, ((n i : ℕ) : ℚ)) * PowerSeries.coeff s F := by
  have h : (∏ i ∈ t, ((n i : ℕ) : PowerSeries ℚ)) =
      PowerSeries.C (∏ i ∈ t, ((n i : ℕ) : ℚ)) := by
    rw [map_prod]; simp
  rw [h, PowerSeries.coeff_C_mul]

/-- `C(α,β) (x + R)^{α−β} = Σ_{γ ≤ α} C(γ,β) R^{γ−β} · C(α,γ) x^{α−γ}`. -/
theorem binom_shift {S : Type*} [CommSemiring S] (x R : S) (α β : ℕ) :
    ((α.choose β : ℕ) : S) * (x + R) ^ (α - β) =
      ∑ γ ∈ Finset.range (α + 1),
        ((γ.choose β : ℕ) : S) * R ^ (γ - β) * (((α.choose γ : ℕ) : S) * x ^ (α - γ)) := by
  by_cases hβ : β ≤ α
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hβ
    have h1 : β + e + 1 = β + (e + 1) := by omega
    rw [h1, Finset.sum_range_add]
    have hz : ∑ γ ∈ Finset.range β,
        ((γ.choose β : ℕ) : S) * R ^ (γ - β) * ((((β + e).choose γ : ℕ) : S) * x ^ (β + e - γ)) = 0 := by
      apply Finset.sum_eq_zero
      intro γ hγ
      rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hγ)]
      simp
    rw [hz, zero_add, Nat.add_sub_cancel_left, add_comm x R, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hc : (β + e).choose (β + k) * (β + k).choose β =
        (β + e).choose β * (β + e - β).choose (β + k - β) := Nat.choose_mul (by omega)
    have e1 : β + e - β = e := by omega
    have e2 : β + k - β = k := by omega
    have e3 : β + e - (β + k) = e - k := by omega
    rw [e1, e2] at hc
    rw [e3, e2]
    have hc' : (((β + e).choose (β + k) : ℕ) : S) * (((β + k).choose β : ℕ) : S) =
        (((β + e).choose β : ℕ) : S) * ((e.choose k : ℕ) : S) := by
      have := congrArg (Nat.cast : ℕ → S) hc
      push_cast at this
      exact this
    calc ((((β + e).choose β : ℕ) : S)) * (R ^ k * x ^ (e - k) * ((e.choose k : ℕ) : S))
        = ((((β + e).choose β : ℕ) : S) * ((e.choose k : ℕ) : S)) * (R ^ k * x ^ (e - k)) := by ring
      _ = ((((β + e).choose (β + k) : ℕ) : S) * (((β + k).choose β : ℕ) : S)) *
            (R ^ k * x ^ (e - k)) := by rw [hc']
      _ = _ := by ring
  · have h0 : α.choose β = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h0]
    simp only [Nat.cast_zero, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro γ hγ
    have : γ.choose β = 0 := Nat.choose_eq_zero_of_lt (by have := Finset.mem_range.mp hγ; omega)
    rw [this]
    simp

/-- Expansion of one packet entry along the binomial shift. -/
theorem entry_expand {m : ℕ} (Y : PowerSeries ℚ) (x R : Fin m → PowerSeries ℚ)
    (α β : Fin m → ℕ) (s : ℕ) :
    (∏ i, (((α i).choose (β i) : ℕ) : ℚ)) *
        PowerSeries.coeff s (Y * ∏ i, (x i + R i) ^ (α i - β i)) =
      ∑ g ∈ Finset.range (s + 1) ×ˢ Fintype.piFinset (fun i => Finset.range (α i + 1)),
        ((∏ i, (((g.2 i).choose (β i) : ℕ) : ℚ)) *
            PowerSeries.coeff (s - g.1) (∏ i, R i ^ (g.2 i - β i))) *
          ((∏ i, (((α i).choose (g.2 i) : ℕ) : ℚ)) *
            PowerSeries.coeff g.1 (Y * ∏ i, x i ^ (α i - g.2 i))) := by
  have hA : (∏ i, (((α i).choose (β i) : ℕ) : PowerSeries ℚ)) * ∏ i, (x i + R i) ^ (α i - β i) =
      ∑ t ∈ Fintype.piFinset (fun i => Finset.range (α i + 1)),
        ((∏ i, (((t i).choose (β i) : ℕ) : PowerSeries ℚ)) * ∏ i, R i ^ (t i - β i)) *
          ((∏ i, (((α i).choose (t i) : ℕ) : PowerSeries ℚ)) * ∏ i, x i ^ (α i - t i)) := by
    rw [← Finset.prod_mul_distrib]
    simp_rw [binom_shift]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Finset.prod_mul_distrib]
    try ring
  have h1 : (∏ i, (((α i).choose (β i) : ℕ) : ℚ)) *
        PowerSeries.coeff s (Y * ∏ i, (x i + R i) ^ (α i - β i)) =
      PowerSeries.coeff s (Y * ((∏ i, (((α i).choose (β i) : ℕ) : PowerSeries ℚ)) *
        ∏ i, (x i + R i) ^ (α i - β i))) := by
    rw [mul_left_comm Y, coeff_natProd_mul]
  have h2 : ∀ t : Fin m → ℕ,
      PowerSeries.coeff s (Y * (((∏ i, (((t i).choose (β i) : ℕ) : PowerSeries ℚ)) *
          ∏ i, R i ^ (t i - β i)) *
          ((∏ i, (((α i).choose (t i) : ℕ) : PowerSeries ℚ)) * ∏ i, x i ^ (α i - t i)))) =
      ∑ k ∈ Finset.range (s + 1),
        ((∏ i, (((t i).choose (β i) : ℕ) : ℚ)) *
            PowerSeries.coeff (s - k) (∏ i, R i ^ (t i - β i))) *
          ((∏ i, (((α i).choose (t i) : ℕ) : ℚ)) *
            PowerSeries.coeff k (Y * ∏ i, x i ^ (α i - t i))) := by
    intro t
    have e : Y * (((∏ i, (((t i).choose (β i) : ℕ) : PowerSeries ℚ)) * ∏ i, R i ^ (t i - β i)) *
          ((∏ i, (((α i).choose (t i) : ℕ) : PowerSeries ℚ)) * ∏ i, x i ^ (α i - t i))) =
        ((∏ i, (((α i).choose (t i) : ℕ) : PowerSeries ℚ)) * (Y * ∏ i, x i ^ (α i - t i))) *
          ((∏ i, (((t i).choose (β i) : ℕ) : PowerSeries ℚ)) * ∏ i, R i ^ (t i - β i)) := by
      ring
    rw [e, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp only
    rw [coeff_natProd_mul, coeff_natProd_mul]
    ring
  rw [h1, hA, Finset.mul_sum, map_sum, Finset.sum_product_right]
  exact Finset.sum_congr rfl fun t _ => h2 t

/-! ### Weights and row pairs -/

/-- A row `r = (s, β)` as the pair `(s, β)`. -/
def rowPair {m : ℕ} (r : Fin (m + 1) → ℕ) : ℕ × (Fin m → ℕ) := (r 0, fun i => r i.succ)

theorem rowPair_injective {m : ℕ} : Function.Injective (rowPair (m := m)) := by
  intro r r' h
  simp only [rowPair, Prod.mk.injEq] at h
  funext i
  induction i using Fin.cases with
  | zero => exact h.1
  | succ i => exact congrFun h.2 i

/-- The weight `v₀ s + W(β)/θ` of a pair `(s, β)`. -/
noncomputable def pairWeight {m : ℕ} (W : Weights m) (p : ℕ × (Fin m → ℕ)) : ℝ :=
  (W.v₀ : ℝ) * p.1 + ∑ i, ((W.w i : ℝ) / (W.θ : ℝ)) * p.2 i

theorem rowWeights_zero {m : ℕ} (W : Weights m) : W.rowWeights 0 = (W.v₀ : ℝ) := by
  simp [Weights.rowWeights]

theorem rowWeights_succ {m : ℕ} (W : Weights m) (i : Fin m) :
    W.rowWeights i.succ = (W.w i : ℝ) / (W.θ : ℝ) := by
  simp [Weights.rowWeights]

theorem rowWeights_pos {m : ℕ} (W : Weights m) (i : Fin (m + 1)) : 0 < W.rowWeights i := by
  induction i using Fin.cases with
  | zero => rw [rowWeights_zero]; exact_mod_cast W.v₀_pos
  | succ i =>
    rw [rowWeights_succ]
    exact div_pos (by exact_mod_cast W.w_pos i) (by exact_mod_cast W.θ_pos)

theorem sum_rowWeights {m : ℕ} (W : Weights m) (r : Fin (m + 1) → ℕ) :
    ∑ i, W.rowWeights i * (r i : ℝ) = pairWeight W (rowPair r) := by
  rw [Fin.sum_univ_succ]
  simp [pairWeight, rowPair, rowWeights_zero, rowWeights_succ]

theorem mem_rowSet_iff {m : ℕ} (W : Weights m) (H : ℝ) (r : Fin (m + 1) → ℕ) :
    r ∈ W.rowSet H ↔ pairWeight W (rowPair r) < H := by
  rw [← sum_rowWeights]
  unfold Weights.rowSet
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i => ?_, h⟩
    have hle : W.rowWeights i * (r i : ℝ) ≤ ∑ j, W.rowWeights j * (r j : ℝ) :=
      Finset.single_le_sum (f := fun j => W.rowWeights j * (r j : ℝ))
        (fun j _ => mul_nonneg (rowWeights_pos W j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
    have h2 : (r i : ℝ) ≤ H / W.rowWeights i := by
      rw [le_div_iff₀ (rowWeights_pos W i)]
      linarith [mul_comm (W.rowWeights i) (r i : ℝ)]
    exact Nat.lt_succ_of_le (Nat.le_floor h2)

theorem mem_image_rowPair_iff {m : ℕ} (W : Weights m) (H : ℝ) (p : ℕ × (Fin m → ℕ)) :
    p ∈ (W.rowSet H).image rowPair ↔ pairWeight W p < H := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact (mem_rowSet_iff W H r).1 hr
  · intro h
    refine ⟨(Fin.cons p.1 p.2 : Fin (m + 1) → ℕ), ?_, ?_⟩
    · rw [mem_rowSet_iff]
      have : rowPair (Fin.cons p.1 p.2 : Fin (m + 1) → ℕ) = p := by simp [rowPair]
      rwa [this]
    · simp [rowPair]

/-! ### The shear coefficients -/

/-- The shear coefficient `S_{(s,β),(s',γ)} = C(γ,β) [T^{s−s'}] ∏ R_i^{γ_i−β_i}` (zero if `s' > s`). -/
noncomputable def shearEntry {m : ℕ} (R : Fin m → PowerSeries ℚ) (a g : ℕ × (Fin m → ℕ)) : ℚ :=
  (∏ i, (((g.2 i).choose (a.2 i) : ℕ) : ℚ)) *
    (if g.1 ≤ a.1 then PowerSeries.coeff (a.1 - g.1) (∏ i, R i ^ (g.2 i - a.2 i)) else 0)

theorem shearEntry_ne_zero_imp {m : ℕ} {R : Fin m → PowerSeries ℚ} {a g : ℕ × (Fin m → ℕ)}
    (h : shearEntry R a g ≠ 0) : (∀ i, a.2 i ≤ g.2 i) ∧ g.1 ≤ a.1 := by
  unfold shearEntry at h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h
  refine ⟨fun i => ?_, ?_⟩
  · have := Finset.prod_ne_zero_iff.mp h1 i (Finset.mem_univ i)
    by_contra hlt
    apply this
    rw [Nat.cast_eq_zero]
    exact Nat.choose_eq_zero_of_lt (by omega)
  · by_contra hlt
    rw [if_neg hlt] at h2
    exact h2 rfl

theorem shearEntry_diag {m : ℕ} (R : Fin m → PowerSeries ℚ) (a : ℕ × (Fin m → ℕ)) :
    shearEntry R a a = 1 := by
  simp [shearEntry]

theorem shearEntry_ne_zero_same {m : ℕ} {R : Fin m → PowerSeries ℚ} {a g : ℕ × (Fin m → ℕ)}
    (h2 : g.2 = a.2) (h : shearEntry R a g ≠ 0) : g = a := by
  have hg1 : g.1 ≤ a.1 := (shearEntry_ne_zero_imp h).2
  unfold shearEntry at h
  rw [if_pos hg1, h2] at h
  simp only [Nat.sub_self, pow_zero, Finset.prod_const_one, PowerSeries.coeff_one] at h
  split_ifs at h with h0
  · exact Prod.ext (by omega) h2
  · simp at h

/-- Weight monotonicity: a nonzero shear coefficient forces `weight g ≤ weight a`, provided each
`R_i` is divisible by `X^{T_i}` and `w_i/θ ≤ T_i v₀`. -/
theorem shearEntry_weight_le {m : ℕ} (W : Weights m) (R : Fin m → PowerSeries ℚ) (T : Fin m → ℕ)
    (hT : ∀ i, (W.w i : ℝ) / (W.θ : ℝ) ≤ (T i : ℝ) * (W.v₀ : ℝ))
    (hR : ∀ i, (PowerSeries.X : PowerSeries ℚ) ^ (T i) ∣ R i)
    {a g : ℕ × (Fin m → ℕ)} (h : shearEntry R a g ≠ 0) : pairWeight W g ≤ pairWeight W a := by
  obtain ⟨hle, hg1⟩ := shearEntry_ne_zero_imp h
  unfold shearEntry at h
  obtain ⟨_, h2⟩ := mul_ne_zero_iff.mp h
  rw [if_pos hg1] at h2
  have hd : (PowerSeries.X : PowerSeries ℚ) ^ (∑ i, T i * (g.2 i - a.2 i)) ∣
      ∏ i, R i ^ (g.2 i - a.2 i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_dvd_prod_of_dvd
    intro i _
    rw [pow_mul]
    exact pow_dvd_pow_of_dvd (hR i) _
  have hsum : ∑ i, T i * (g.2 i - a.2 i) ≤ a.1 - g.1 := by
    by_contra hlt
    exact h2 (PowerSeries.X_pow_dvd_iff.mp hd _ (by omega))
  have hsumR : ∑ i, (T i : ℝ) * ((g.2 i - a.2 i : ℕ) : ℝ) ≤ (a.1 : ℝ) - (g.1 : ℝ) := by
    have h3 : ((∑ i, T i * (g.2 i - a.2 i) : ℕ) : ℝ) ≤ ((a.1 - g.1 : ℕ) : ℝ) := by
      exact_mod_cast hsum
    rw [Nat.cast_sub hg1] at h3
    push_cast at h3
    exact h3
  have hv : (0 : ℝ) ≤ (W.v₀ : ℝ) := by exact_mod_cast W.v₀_pos.le
  have hterm : ∀ i, ((W.w i : ℝ) / (W.θ : ℝ)) * (g.2 i : ℝ) ≤
      ((W.w i : ℝ) / (W.θ : ℝ)) * (a.2 i : ℝ) + (W.v₀ : ℝ) * ((T i : ℝ) * ((g.2 i - a.2 i : ℕ) : ℝ)) := by
    intro i
    have hcast : (g.2 i : ℝ) = (a.2 i : ℝ) + ((g.2 i - a.2 i : ℕ) : ℝ) := by
      rw [Nat.cast_sub (hle i)]; ring
    have hδ : (0 : ℝ) ≤ ((g.2 i - a.2 i : ℕ) : ℝ) := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_right (hT i) hδ
    rw [hcast]
    nlinarith [this]
  have hS : ∑ i, ((W.w i : ℝ) / (W.θ : ℝ)) * (g.2 i : ℝ) ≤
      ∑ i, ((W.w i : ℝ) / (W.θ : ℝ)) * (a.2 i : ℝ) +
        (W.v₀ : ℝ) * ∑ i, (T i : ℝ) * ((g.2 i - a.2 i : ℕ) : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => hterm i
  unfold pairWeight
  have := mul_le_mul_of_nonneg_left hsumR hv
  nlinarith [this, hS]

/-! ### The matrices -/

/-- The truncated packet entry: `L` replaced by `L_i^{tr} = truncSeries L (T i)` in the factor `i`. -/
noncomputable def packetEntryTr {m K : ℕ} {ch : OriginChart} (s : OriginSeries ch)
    (T : Fin m → ℕ) (cen : Fin K → Fin m → ℚ) (j : Fin K) (r : Fin (m + 1) → ℕ)
    (c : ColIdx m) : ℚ :=
  (∏ i : Fin m, ((c.2.2 i).choose (r i.succ) : ℚ)) *
    PowerSeries.coeff (r 0)
      (s.U ^ c.1 * PowerSeries.X ^ c.2.1.val *
        ∏ i : Fin m, (PowerSeries.C (cen j i) + truncSeries s.L (T i)) ^ (c.2.2 i - r i.succ))

/-- The truncated packet matrix `A^{tr}`. -/
noncomputable def packetMatrixTr {m K : ℕ} (W : Weights m) {ch : OriginChart}
    (s : OriginSeries ch) (T : Fin m → ℕ) (cen : Fin K → Fin m → ℚ) (H : ℝ) :
    Matrix (Row W K H) (Col W H) ℚ :=
  fun ρ c => packetEntryTr s T cen ρ.1 ρ.2.1 c.1

/-- The shear matrix on the rows `Row W K H`: block diagonal in the centre index, with the shear
coefficients on `𝒥_H`. -/
noncomputable def shearMatrix {m : ℕ} (K : ℕ) (W : Weights m) (R : Fin m → PowerSeries ℚ) (H : ℝ) :
    Matrix (Row W K H) (Row W K H) ℚ :=
  fun ρ ρ' => if ρ.1 = ρ'.1 then shearEntry R (rowPair ρ.2.1) (rowPair ρ'.2.1) else 0

/-- One entry of `A` as a combination of entries of `A^{tr}` over the rows of `𝒥_H`. -/
theorem entry_shear {m K : ℕ} (W : Weights m) {ch : OriginChart} (s : OriginSeries ch)
    (T : Fin m → ℕ) (hT : ∀ i, W.w i / W.θ ≤ (T i : ℚ) * W.v₀)
    (cen : Fin K → Fin m → ℚ) (H : ℝ) (j : Fin K) (r : Fin (m + 1) → ℕ) (hr : r ∈ W.rowSet H)
    (c : ColIdx m) :
    packetEntry s cen j r c =
      ∑ g : ↥(W.rowSet H),
        shearEntry (fun i => tailSeries s.L (T i)) (rowPair r) (rowPair g.1) *
          packetEntryTr s T cen j g.1 c := by
  have hxR : ∀ i, PowerSeries.C (cen j i) + s.L =
      (PowerSeries.C (cen j i) + truncSeries s.L (T i)) + tailSeries s.L (T i) := by
    intro i; unfold tailSeries; ring
  have hE := entry_expand (s.U ^ c.1 * PowerSeries.X ^ c.2.1.val)
    (fun i => PowerSeries.C (cen j i) + truncSeries s.L (T i))
    (fun i => tailSeries s.L (T i)) c.2.2 (fun i => r i.succ) (r 0)
  try dsimp only at hE
  have hL : packetEntry s cen j r c = (∏ i : Fin m, ((c.2.2 i).choose (r i.succ) : ℚ)) *
      PowerSeries.coeff (r 0) (s.U ^ c.1 * PowerSeries.X ^ c.2.1.val *
        ∏ i : Fin m, ((PowerSeries.C (cen j i) + truncSeries s.L (T i)) +
          tailSeries s.L (T i)) ^ (c.2.2 i - r i.succ)) := by
    unfold packetEntry
    simp only [hxR]
  rw [hL, hE]
  have hrow : pairWeight W (rowPair r) < H := (mem_rowSet_iff W H r).1 hr
  have hR : ∀ i, (PowerSeries.X : PowerSeries ℚ) ^ (T i) ∣ tailSeries s.L (T i) :=
    fun i => X_pow_dvd_tailSeries s.L (T i)
  have hTR : ∀ i, (W.w i : ℝ) / (W.θ : ℝ) ≤ (T i : ℝ) * (W.v₀ : ℝ) := by
    intro i
    have := hT i
    exact_mod_cast this
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℕ × (Fin m → ℕ) → ℚ, ∀ p, Φ p =
      shearEntry (fun i => tailSeries s.L (T i)) (rowPair r) p *
        ((∏ i, (((c.2.2 i).choose (p.2 i) : ℕ) : ℚ)) *
          PowerSeries.coeff p.1 ((s.U ^ c.1 * PowerSeries.X ^ c.2.1.val) *
            ∏ i, (PowerSeries.C (cen j i) + truncSeries s.L (T i)) ^ (c.2.2 i - p.2 i))) :=
    ⟨_, fun _ => rfl⟩
  have hRHS : ∑ g : ↥(W.rowSet H),
      shearEntry (fun i => tailSeries s.L (T i)) (rowPair r) (rowPair g.1) *
        packetEntryTr s T cen j g.1 c = ∑ p ∈ (W.rowSet H).image rowPair, Φ p := by
    rw [Finset.sum_image (fun a _ b _ h => rowPair_injective h),
      ← Finset.sum_coe_sort (W.rowSet H) (fun g => Φ (rowPair g))]
    refine Finset.sum_congr rfl fun g _ => ?_
    show _ = Φ (rowPair g.1)
    rw [hΦ]
    rfl
  have hsub : ∀ (J' G : Finset (ℕ × (Fin m → ℕ))), (∀ p ∈ G, p ∉ J' → Φ p = 0) →
      (∀ p ∈ J', p ∉ G → Φ p = 0) → ∑ p ∈ J', Φ p = ∑ p ∈ G, Φ p := by
    intro J' G h1 h2
    have a : ∑ p ∈ J', Φ p = ∑ p ∈ J' ∪ G, Φ p :=
      Finset.sum_subset Finset.subset_union_left (fun p hp hn => by
        rcases Finset.mem_union.1 hp with h | h
        · exact absurd h hn
        · exact h1 p h hn)
    have b : ∑ p ∈ G, Φ p = ∑ p ∈ J' ∪ G, Φ p :=
      Finset.sum_subset Finset.subset_union_right (fun p hp hn => by
        rcases Finset.mem_union.1 hp with h | h
        · exact h2 p h hn
        · exact absurd h hn)
    rw [a, b]
  have hz1 : ∀ p ∈ Finset.range (r 0 + 1) ×ˢ Fintype.piFinset (fun i => Finset.range (c.2.2 i + 1)),
      p ∉ (W.rowSet H).image rowPair → Φ p = 0 := by
    intro p _ hp
    have hnot : ¬ pairWeight W p < H := fun h => hp ((mem_image_rowPair_iff W H p).2 h)
    have : shearEntry (fun i => tailSeries s.L (T i)) (rowPair r) p = 0 := by
      by_contra hne
      exact hnot (lt_of_le_of_lt (shearEntry_weight_le W (fun i => tailSeries s.L (T i)) T hTR hR hne) hrow)
    rw [hΦ, this, zero_mul]
  have hz2 : ∀ p ∈ (W.rowSet H).image rowPair,
      p ∉ Finset.range (r 0 + 1) ×ˢ Fintype.piFinset (fun i => Finset.range (c.2.2 i + 1)) →
        Φ p = 0 := by
    intro p _ hp
    rw [Finset.mem_product, Fintype.mem_piFinset] at hp
    by_cases h1 : p.1 < r 0 + 1
    · have h2 : ∃ i, ¬ p.2 i < c.2.2 i + 1 := by
        by_contra hall
        push_neg at hall
        exact hp ⟨Finset.mem_range.2 h1, fun i => Finset.mem_range.2 (hall i)⟩
      obtain ⟨i, hi⟩ := h2
      have hc : ((c.2.2 i).choose (p.2 i) : ℕ) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have hprod : (∏ i, (((c.2.2 i).choose (p.2 i) : ℕ) : ℚ)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hc])
      rw [hΦ, hprod]
      simp
    · have : shearEntry (fun i => tailSeries s.L (T i)) (rowPair r) p = 0 := by
        unfold shearEntry
        have h3 : ¬ p.1 ≤ (rowPair r).1 := by simp only [rowPair]; omega
        rw [if_neg h3]; simp
      rw [hΦ, this, zero_mul]
  rw [hRHS, hsub ((W.rowSet H).image rowPair)
    (Finset.range (r 0 + 1) ×ˢ Fintype.piFinset (fun i => Finset.range (c.2.2 i + 1))) hz1 hz2]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp1 : p.1 ≤ r 0 := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_product.1 hp).1)
  rw [hΦ]
  unfold shearEntry
  simp only [rowPair, hp1, ↓reduceIte]

/-- `A = (shear) · A^{tr}`. -/
theorem packetMatrix_eq_shear_mul {m K : ℕ} (W : Weights m) {ch : OriginChart}
    (s : OriginSeries ch) (T : Fin m → ℕ) (hT : ∀ i, W.w i / W.θ ≤ (T i : ℚ) * W.v₀)
    (cen : Fin K → Fin m → ℚ) (H : ℝ) :
    packetMatrix W s cen H =
      shearMatrix K W (fun i => tailSeries s.L (T i)) H * packetMatrixTr W s T cen H := by
  ext ρ c
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [shearMatrix, packetMatrixTr, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  exact entry_shear W s T hT cen H ρ.1 ρ.2.1 ρ.2.2 c.1

/-- The shear matrix has determinant `1`. -/
theorem det_shearMatrix {m : ℕ} (K : ℕ) (W : Weights m) (R : Fin m → PowerSeries ℚ) (H : ℝ) :
    (shearMatrix K W R H).det = 1 := by
  have hbt : (shearMatrix K W R H).BlockTriangular
      (fun ρ => ∑ i, (rowPair ρ.2.1).2 i) := by
    intro ρ ρ' hlt
    unfold shearMatrix
    split_ifs with hj
    · by_contra hne
      have h1 := (shearEntry_ne_zero_imp hne).1
      have h2 : ∑ i, (rowPair ρ.2.1).2 i ≤ ∑ i, (rowPair ρ'.2.1).2 i :=
        Finset.sum_le_sum fun i _ => h1 i
      have hlt' : ∑ i, (rowPair ρ'.2.1).2 i < ∑ i, (rowPair ρ.2.1).2 i := hlt
      omega
    · rfl
  rw [hbt.det]
  apply Finset.prod_eq_one
  intro k _
  have hblock : (shearMatrix K W R H).toSquareBlock
      (fun ρ => ∑ i, (rowPair ρ.2.1).2 i) k = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Matrix.toSquareBlock_def, Matrix.submatrix_apply, Matrix.one_apply,
      Subtype.mk.injEq]
    by_cases hij : i = j
    · subst hij
      simp [shearMatrix, shearEntry_diag]
    · rw [if_neg hij]
      show (if i.1 = j.1 then shearEntry R (rowPair i.2.1) (rowPair j.2.1) else 0) = 0
      by_cases hj' : i.1 = j.1
      · simp only [hj', ↓reduceIte]
        by_contra hne
        apply hij
        have h1 := (shearEntry_ne_zero_imp hne).1
        have h2 : ∀ x ∈ Finset.univ, (rowPair i.2.1).2 x ≤ (rowPair j.2.1).2 x :=
          fun x _ => h1 x
        have h3 : ∑ x, (rowPair i.2.1).2 x = ∑ x, (rowPair j.2.1).2 x := by
          have hi' : ∑ x, (rowPair i.2.1).2 x = k := hi
          have hj'' : ∑ x, (rowPair j.2.1).2 x = k := hj
          omega
        have h4 := (Finset.sum_eq_sum_iff_of_le h2).1 h3
        have h5 : (rowPair j.2.1).2 = (rowPair i.2.1).2 := funext fun x => (h4 x (Finset.mem_univ x)).symm
        have h6 := shearEntry_ne_zero_same h5 hne
        have h7 : i.2.1 = j.2.1 := (rowPair_injective h6).symm
        exact Prod.ext hj' (Subtype.ext h7)
      · simp only [hj', ↓reduceIte]
  rw [hblock, Matrix.det_one]

/-- **E10** (`lem:trunc`, CM Lemma 15.1). Let `T_i` be natural numbers with `w_i/θ ≤ T_i v₀`, and let
the truncated packet matrix use `L_i^{tr}` (the terms of `L` of degree `< T_i`) in the factor of index
`i`. Then for every choice of columns the determinants of the full and truncated packet matrices
agree. -/
theorem det_packet_trunc {m K : ℕ} (W : Weights m) {ch : OriginChart} (s : OriginSeries ch)
    (T : Fin m → ℕ) (hT : ∀ i, W.w i / W.θ ≤ (T i : ℚ) * W.v₀)
    (cen : Fin K → Fin m → ℚ) (H : ℝ) (cols : Row W K H → Col W H) :
    ((packetMatrix W s cen H).submatrix id cols).det =
      ((packetMatrixTr W s T cen H).submatrix id cols).det := by
  rw [packetMatrix_eq_shear_mul W s T hT cen H,
    Matrix.submatrix_mul _ _ id id cols Function.bijective_id, Matrix.submatrix_id_id,
    Matrix.det_mul, det_shearMatrix, one_mul]

end CatalanCore.Elliptic.Arith
