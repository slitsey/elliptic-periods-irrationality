module

public import CatalanCore.Elliptic.EPA.Jet
public import CatalanCore.Elliptic.EPA.Reduce
public import OAI.NumberTheory.PiExponent.Polynomials.SimplexRational
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The auxiliary polynomial (row E09.6)

Labels refer to `D2-DESIGN-2026-11-20.md` §5 E09.6 (CM Thm `origin-polar-auxiliary`, l.2528, and the
"precise route" l.2587–2628).

`ell_auxiliary`: for `K (w₀/v₀) θ^m ρ^{m+1} < 1` there is a threshold `N₀`, independent of the
centres `c`, such that for every `N ≥ N₀` and every array of centres `c : Fin K → Fin m → ℂ` there
is a nonzero `P ∈ ℂ[u, t, Z]` of `t`-degree `≤ 1`, not a multiple of `f`, with `SrcDeg W N P` and
`Φ_{c_j}(P) ∈ j_{ρ N}` for all `j`.

Proof (a pigeonhole, as in OAI `Polynomials/AuxiliaryPolynomial`, whose two counting lemmas
`tendsto_card_strictWeightedSimplex_scale` and `eventually_auxiliary_card_lt` are copied here in
shape so that this module imports only the built OAI module `SimplexRational`; OAI
openai/math fd4aeeb2, Apache License 2.0, Copyright OpenAI): unknowns are the coefficients of the
monomials `u^{⌊a₀/2⌋} t^{a₀ % 2} Z^{a'}` with `w₀ a₀ + Σ w_i a_i ≤ N − 3 w₀`, which have source
weight `≤ N`; the conditions are the vanishing of the coefficients of `Φ_{c_j}(P)` at the `K ·
#{jet weight < b (N − 3 w₀)}` exponents, `b > ρ` with the volume inequality still true.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

open CatalanCore.Elliptic OAI.PiExponent OAI.PiExponent.JetGeometry Filter Topology
open scoped BigOperators

variable {m K : ℕ}

/-! ### Weights -/

theorem aux_radWt_pos (W : Weights m) (j : Fin (m + 1)) : 0 < radWt W j := by
  induction j using Fin.cases with
  | zero => rw [radWt_zero]; exact W.w₀_pos
  | succ i => rw [radWt_succ]; exact W.w_pos i

theorem aux_jetWt_pos (W : Weights m) (j : Fin (m + 1)) : 0 < jetWt W j := by
  induction j using Fin.cases with
  | zero => rw [jetWt_zero]; exact W.v₀_pos
  | succ i => rw [jetWt_succ]; exact div_pos (W.w_pos i) W.θ_pos

theorem aux_jetWt_nonneg (W : Weights m) (j : Fin (m + 1)) : 0 ≤ jetWt W j := (aux_jetWt_pos W j).le

theorem prod_radWt_div_jetWt (W : Weights m) :
    (∏ i, ((radWt W i : ℚ) : ℝ)) / ∏ i, ((jetWt W i : ℚ) : ℝ) =
      (W.w₀ : ℝ) / (W.v₀ : ℝ) * (W.θ : ℝ) ^ m := by
  have hP : (∏ i : Fin m, (W.w i : ℝ)) ≠ 0 :=
    (Finset.prod_pos (fun i _ => by exact_mod_cast W.w_pos i)).ne'
  have h0 : (W.w₀ : ℝ) ≠ 0 := by exact_mod_cast W.w₀_pos.ne'
  have h1 : (W.v₀ : ℝ) ≠ 0 := by exact_mod_cast W.v₀_pos.ne'
  have h2 : (W.θ : ℝ) ≠ 0 := by exact_mod_cast W.θ_pos.ne'
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [radWt_zero, radWt_succ, jetWt_zero, jetWt_succ, Rat.cast_div]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  field_simp <;> ring

/-! ### Counting (copied in shape from OAI `Polynomials/AuxiliaryPolynomial`) -/

theorem tendsto_card_strictSimplex_scale {d : ℕ} (V : Fin d → ℚ)
    (hV : ∀ i, 0 < V i) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℝ =>
      ((strictWeightedSimplex (fun i => (V i : ℝ)) (a * N)).card : ℝ) / N ^ d)
      atTop (𝓝 (a ^ d / ((d.factorial : ℝ) * ∏ i, (V i : ℝ)))) := by
  have ht : Tendsto (fun N : ℝ => a * N) atTop atTop :=
    Tendsto.const_mul_atTop ha tendsto_id
  have h := ((tendsto_card_strictWeightedSimplex_rational V hV).comp ht).mul_const (a ^ d)
  have heq : 1 / ((d.factorial : ℝ) * ∏ i, (V i : ℝ)) * a ^ d =
      a ^ d / ((d.factorial : ℝ) * ∏ i, (V i : ℝ)) := by ring
  rw [heq] at h
  apply h.congr'
  exact Eventually.of_forall (fun N => by
    simp only [Function.comp_apply, mul_pow]
    field_simp)

theorem eventually_aux_card_lt {d : ℕ} (W V : Fin d → ℚ)
    (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i) (K : ℕ)
    {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a ^ d * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1) :
    ∀ᶠ N : ℝ in atTop,
      K * (strictWeightedSimplex (fun i => (V i : ℝ)) (a * N)).card <
        (realWeightedSimplex (fun i => (W i : ℝ)) N).card := by
  have hPW : 0 < ∏ i, (W i : ℝ) := Finset.prod_pos (fun i _ => by exact_mod_cast hW i)
  have hPV : 0 < ∏ i, (V i : ℝ) := Finset.prod_pos (fun i _ => by exact_mod_cast hV i)
  have hF : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  have hconst : (K : ℝ) * (a ^ d / ((d.factorial : ℝ) * ∏ i, (V i : ℝ))) <
      1 / ((d.factorial : ℝ) * ∏ i, (W i : ℝ)) := by
    have hmain := (div_lt_one hPV).mp hvol
    apply (lt_div_iff₀ (mul_pos hF hPW)).mpr
    have heq : (K : ℝ) * (a ^ d / ((d.factorial : ℝ) * ∏ i, (V i : ℝ))) *
        ((d.factorial : ℝ) * ∏ i, (W i : ℝ)) =
        (K : ℝ) * a ^ d * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) := by
      field_simp
    rw [heq]
    exact hvol
  have hsmall := ((tendsto_card_strictSimplex_scale V hV ha).const_mul (K : ℝ)).eventually_lt
    (tendsto_card_realWeightedSimplex_rational W hW) hconst
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with N hN hNpos
  have hscaled : ((K * (strictWeightedSimplex (fun i => (V i : ℝ)) (a * N)).card : ℕ) : ℝ) /
      N ^ d < ((realWeightedSimplex (fun i => (W i : ℝ)) N).card : ℝ) / N ^ d := by
    simpa only [Nat.cast_mul, mul_div_assoc] using hN
  exact_mod_cast (div_lt_div_iff_of_pos_right (pow_pos hNpos d)).mp hscaled

theorem exists_nonzero_kernel_of_card_lt' {C R : Type*} [Fintype C] [Fintype R]
    (E : (C → ℂ) →ₗ[ℂ] (R → ℂ)) (h : Fintype.card R < Fintype.card C) :
    ∃ x : C → ℂ, x ≠ 0 ∧ E x = 0 := by
  have hk : LinearMap.ker E ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt
    (by simpa only [Module.finrank_fintype_fun_eq_card] using h)
  obtain ⟨x, hx, hn⟩ := (LinearMap.ker E).ne_bot_iff.mp hk
  exact ⟨x, hn, LinearMap.mem_ker.mp hx⟩

/-! ### The embedding `X₀^{a₀} Z^{a'} ↦ u^{⌊a₀/2⌋} t^{a₀ % 2} Z^{a'}` -/

/-- The exponent vector of `u^{⌊a₀/2⌋} t^{a₀ % 2} Z^{a'}`, as a function. -/
def embedFun (a : Fin (m + 1) → ℕ) : Fin (m + 2) → ℕ :=
  Fin.cases (motive := fun _ => ℕ) (a 0 / 2)
    (Fin.cases (motive := fun _ => ℕ) (a 0 % 2) (fun i => a i.succ))

/-- The exponent vector of `u^{⌊a₀/2⌋} t^{a₀ % 2} Z^{a'}`. -/
noncomputable def embedExp (a : Fin (m + 1) → ℕ) : Fin (m + 2) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (embedFun a)

theorem embedExp_zero (a : Fin (m + 1) → ℕ) : embedExp a 0 = a 0 / 2 := by
  first | rfl | simp only [embedExp, embedFun, Finsupp.coe_equivFunOnFinite_symm,
    Fin.cases_zero, Fin.cases_succ]

theorem embedExp_succ_zero (a : Fin (m + 1) → ℕ) : embedExp a (Fin.succ 0) = a 0 % 2 := by
  first | rfl | simp only [embedExp, embedFun, Finsupp.coe_equivFunOnFinite_symm,
    Fin.cases_zero, Fin.cases_succ]

theorem embedExp_one (a : Fin (m + 1) → ℕ) : embedExp a 1 = a 0 % 2 := by
  rw [one_eq_succ_zero (m := m)]; exact embedExp_succ_zero a

theorem embedExp_succ_succ (a : Fin (m + 1) → ℕ) (i : Fin m) :
    embedExp a i.succ.succ = a i.succ := by
  first | rfl | simp only [embedExp, embedFun, Finsupp.coe_equivFunOnFinite_symm,
    Fin.cases_zero, Fin.cases_succ]

theorem embedExp_injective : Function.Injective (embedExp (m := m)) := by
  intro a b h
  have h0 := DFunLike.congr_fun h 0
  have h1 := DFunLike.congr_fun h (Fin.succ 0)
  rw [embedExp_zero, embedExp_zero] at h0
  rw [embedExp_succ_zero, embedExp_succ_zero] at h1
  funext j
  induction j using Fin.cases with
  | zero => omega
  | succ i =>
    have := DFunLike.congr_fun h i.succ.succ
    rwa [embedExp_succ_succ, embedExp_succ_succ] at this

theorem srcRho_succ_zero (W : Weights m) : srcRho W (Fin.succ 0) = 4 * (W.w₀ : ℝ) := by
  rw [← one_eq_succ_zero (m := m)]; exact srcRho_one W

/-- The source weight of `u^{⌊a₀/2⌋} t^{a₀ % 2} Z^{a'}` is at most `Σ w_j a_j + 3 w₀`. -/
theorem weight_embedExp (W : Weights m) (a : Fin (m + 1) → ℕ) :
    Finsupp.weight (fun j => srcRho W j) (embedExp a) ≤
      (∑ j, ((radWt W j : ℚ) : ℝ) * (a j : ℝ)) + 3 * (W.w₀ : ℝ) := by
  have hL : Finsupp.weight (fun j => srcRho W j) (embedExp a) =
      ((a 0 / 2 : ℕ) : ℝ) * (2 * (W.w₀ : ℝ)) + ((a 0 % 2 : ℕ) : ℝ) * (4 * (W.w₀ : ℝ)) +
        ∑ i : Fin m, (a i.succ : ℝ) * (W.w i : ℝ) := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun i => by simp), Fin.sum_univ_succ,
      Fin.sum_univ_succ]
    simp only [embedExp_zero, embedExp_succ_zero, embedExp_succ_succ, srcRho_zero,
      srcRho_succ_zero, srcRho_succ_succ, nsmul_eq_mul]
    try ring
  have hR : ∑ j, ((radWt W j : ℚ) : ℝ) * (a j : ℝ) =
      (W.w₀ : ℝ) * (a 0 : ℝ) + ∑ i : Fin m, (W.w i : ℝ) * (a i.succ : ℝ) := by
    rw [Fin.sum_univ_succ]
    simp only [radWt_zero, radWt_succ]
  have hdm : (a 0 : ℝ) = 2 * ((a 0 / 2 : ℕ) : ℝ) + ((a 0 % 2 : ℕ) : ℝ) := by
    have hnat : a 0 = 2 * (a 0 / 2) + a 0 % 2 := by omega
    exact_mod_cast hnat
  have hr1 : ((a 0 % 2 : ℕ) : ℝ) ≤ 1 := by
    have : a 0 % 2 ≤ 1 := by omega
    exact_mod_cast this
  have hw0 : (0 : ℝ) < W.w₀ := by exact_mod_cast W.w₀_pos
  have hsw : ∑ i : Fin m, (a i.succ : ℝ) * (W.w i : ℝ) =
      ∑ i : Fin m, (W.w i : ℝ) * (a i.succ : ℝ) :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have h4 : (W.w₀ : ℝ) * (a 0 : ℝ) =
      2 * ((W.w₀ : ℝ) * ((a 0 / 2 : ℕ) : ℝ)) + (W.w₀ : ℝ) * ((a 0 % 2 : ℕ) : ℝ) := by
    rw [hdm]; ring
  rw [hL, hR, hsw]
  have := mul_le_mul_of_nonneg_left hr1 hw0.le
  nlinarith [h4, this]

/-! ### The linear maps -/

/-- `x ↦ Σ_a x_a · monomial (e a)`. -/
noncomputable def auxPoly {ι : Type*} [Fintype ι] (e : ι → (Fin (m + 2) →₀ ℕ)) :
    (ι → ℂ) →ₗ[ℂ] AmbRing m where
  toFun x := ∑ a, MvPolynomial.monomial (e a) (x a)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' z x := by
    simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

theorem coeff_auxPoly {ι : Type*} [Fintype ι] (e : ι → (Fin (m + 2) →₀ ℕ))
    (he : Function.Injective e) (x : ι → ℂ) (a : ι) :
    (auxPoly e x).coeff (e a) = x a := by
  classical
  change (∑ b, MvPolynomial.monomial (e b) (x b)).coeff (e a) = x a
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    have hne : e b ≠ e a := fun h => hba (he h)
    simp [hne]
  · simp

theorem support_auxPoly {ι : Type*} [Fintype ι] (e : ι → (Fin (m + 2) →₀ ℕ)) (x : ι → ℂ)
    {d : Fin (m + 2) →₀ ℕ} (hd : d ∈ (auxPoly e x).support) : ∃ a, d = e a := by
  classical
  by_contra hn
  push_neg at hn
  apply (MvPolynomial.mem_support_iff.mp hd)
  change (∑ b, MvPolynomial.monomial (e b) (x b)).coeff d = 0
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro a _
  have hne : e a ≠ d := fun h => hn a h.symm
  simp [MvPolynomial.coeff_monomial, hne]

variable {ch : OriginChart}

/-- The linear conditions: the coefficients of `Φ_{c_j}(P_x)` at the exponents of `T`. -/
noncomputable def auxJetMap (s : OriginSeries ch) (c : Fin K → Fin m → ℂ) {ι : Type*} [Fintype ι]
    (e : ι → (Fin (m + 2) →₀ ℕ)) (T : Finset (Fin (m + 1) → ℕ)) :
    (ι → ℂ) →ₗ[ℂ] ((Fin K × T) → ℂ) where
  toFun x jr := MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm jr.2.1)
    (ellJet s (c jr.1) (auxPoly e x))
  map_add' x y := by
    funext jr
    simp [map_add]
  map_smul' z x := by
    funext jr
    simp [map_smul]

/-- The exponent set of `Σ_i v_i d_i < H` through the cast to `ℝ`. -/
theorem weight_jetWt_cast (W : Weights m) (d : Fin (m + 1) →₀ ℕ) :
    ((Finsupp.weight (jetWt W) d : ℚ) : ℝ) = ∑ i, ((jetWt W i : ℚ) : ℝ) * (d i : ℝ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun i => by simp)]
  simp only [nsmul_eq_mul]
  push_cast
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-! ### The auxiliary polynomial -/

/-- **Row E09.6** (CM Thm `origin-polar-auxiliary`, l.2528 and l.2587–2628). -/
theorem ell_auxiliary (s : OriginSeries ch) (W : Weights m) {ρ : ℚ} (hρ : 0 < ρ)
    (hvol : (K : ℚ) * (W.w₀ / W.v₀) * W.θ ^ m * ρ ^ (m + 1) < 1) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ c : Fin K → Fin m → ℂ, ∃ P : AmbRing m, P ≠ 0 ∧
      P ∉ (Ideal.span {relation ch} : Ideal (AmbRing m)) ∧ SrcDeg W (N : ℝ) P ∧
      (∀ d ∈ P.support, d 1 ≤ 1) ∧
      ∀ j, ellJet s (c j) P ∈ rationalWeightedIdeal (jetWt W) (aux_jetWt_nonneg W) (ρ * N) := by
  classical
  have hW : ∀ i, 0 < radWt W i := aux_radWt_pos W
  have hV : ∀ i, 0 < jetWt W i := aux_jetWt_pos W
  have hρR : (0 : ℝ) < ρ := by exact_mod_cast hρ
  have hvolR : (K : ℝ) * ((W.w₀ : ℝ) / (W.v₀ : ℝ)) * (W.θ : ℝ) ^ m * (ρ : ℝ) ^ (m + 1) < 1 := by
    exact_mod_cast hvol
  -- a slightly larger radius `b > ρ` for which the volume inequality still holds
  obtain ⟨b, hbρ, hb⟩ : ∃ b : ℝ, (ρ : ℝ) < b ∧
      (K : ℝ) * ((W.w₀ : ℝ) / (W.v₀ : ℝ)) * (W.θ : ℝ) ^ m * b ^ (m + 1) < 1 := by
    have hlim : Tendsto (fun x : ℝ =>
        (K : ℝ) * ((W.w₀ : ℝ) / (W.v₀ : ℝ)) * (W.θ : ℝ) ^ m * x ^ (m + 1)) (𝓝 (ρ : ℝ))
        (𝓝 ((K : ℝ) * ((W.w₀ : ℝ) / (W.v₀ : ℝ)) * (W.θ : ℝ) ^ m * (ρ : ℝ) ^ (m + 1))) :=
      (continuous_const.mul (continuous_pow (m + 1))).tendsto _
    have hev := Filter.Tendsto.eventually_lt_const hvolR hlim
    have hev' : ∀ᶠ x in 𝓝[>] (ρ : ℝ), (K : ℝ) * ((W.w₀ : ℝ) / (W.v₀ : ℝ)) * (W.θ : ℝ) ^ m *
        x ^ (m + 1) < 1 := hev.filter_mono nhdsWithin_le_nhds
    obtain ⟨b, hb1, hb2⟩ := (hev'.and (eventually_mem_nhdsWithin (a := (ρ : ℝ)))).exists
    exact ⟨b, hb2, hb1⟩
  have hbpos : 0 < b := hρR.trans hbρ
  have hvol' : (K : ℝ) * b ^ (m + 1) * (∏ i, ((radWt W i : ℚ) : ℝ)) /
      (∏ i, ((jetWt W i : ℚ) : ℝ)) < 1 := by
    rw [mul_div_assoc, prod_radWt_div_jetWt]
    calc (K : ℝ) * b ^ (m + 1) * ((W.w₀ : ℝ) / (W.v₀ : ℝ) * (W.θ : ℝ) ^ m)
        = (K : ℝ) * ((W.w₀ : ℝ) / (W.v₀ : ℝ)) * (W.θ : ℝ) ^ m * b ^ (m + 1) := by ring
      _ < 1 := hb
  have hev := eventually_aux_card_lt (radWt W) (jetWt W) hW hV K hbpos hvol'
  obtain ⟨R, hR⟩ := eventually_atTop.mp hev
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge
    (max (R + 3 * (W.w₀ : ℝ)) (3 * b * (W.w₀ : ℝ) / (b - ρ)))
  refine ⟨N₀, fun N hN c => ?_⟩
  have hNge : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : R + 3 * (W.w₀ : ℝ) ≤ N := (le_max_left _ _).trans (hN₀.trans hNge)
  have h2 : 3 * b * (W.w₀ : ℝ) / (b - ρ) ≤ N := (le_max_right _ _).trans (hN₀.trans hNge)
  have hw0 : (0 : ℝ) < W.w₀ := by exact_mod_cast W.w₀_pos
  have hN'R : R ≤ (N : ℝ) - 3 * (W.w₀ : ℝ) := by linarith
  have hbN : (ρ : ℝ) * N ≤ b * ((N : ℝ) - 3 * (W.w₀ : ℝ)) := by
    have h3 : 3 * b * (W.w₀ : ℝ) ≤ N * (b - ρ) := (div_le_iff₀ (sub_pos.2 hbρ)).mp h2
    nlinarith
  set N' : ℝ := (N : ℝ) - 3 * (W.w₀ : ℝ) with hN'
  have hcard := hR N' hN'R
  set S := realWeightedSimplex (fun i => ((radWt W i : ℚ) : ℝ)) N' with hS
  set T := strictWeightedSimplex (fun i => ((jetWt W i : ℚ) : ℝ)) (b * N') with hT
  let e : S → (Fin (m + 2) →₀ ℕ) := fun a => embedExp a.1
  have he : Function.Injective e := fun a a' h => Subtype.ext (embedExp_injective h)
  have hcard' : Fintype.card (Fin K × T) < Fintype.card S := by
    simpa [Fintype.card_prod] using hcard
  obtain ⟨x, hx, hEx⟩ := exists_nonzero_kernel_of_card_lt' (auxJetMap s c e T) hcard'
  have hPne : auxPoly e x ≠ 0 := by
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hx
    intro hP0
    have := coeff_auxPoly e he x a
    rw [hP0] at this
    simp only [MvPolynomial.coeff_zero] at this
    exact ha this.symm
  have htdeg : ∀ d ∈ (auxPoly e x).support, d 1 ≤ 1 := by
    intro d hd
    obtain ⟨a, rfl⟩ := support_auxPoly e x hd
    show embedExp a.1 1 ≤ 1
    rw [embedExp_one]
    omega
  refine ⟨auxPoly e x, hPne, not_mem_span_of_reduced hPne htdeg, ?_, htdeg, ?_⟩
  · intro d hd
    obtain ⟨a, rfl⟩ := support_auxPoly e x hd
    have hmem := (mem_realWeightedSimplex (w := fun i => ((radWt W i : ℚ) : ℝ))
      (fun i => by exact_mod_cast hW i)).mp a.2
    refine (weight_embedExp W a.1).trans ?_
    linarith [hN']
  · intro j
    rw [mem_rationalWeightedIdeal]
    intro d hd
    have hdR : ((Finsupp.weight (jetWt W) d : ℚ) : ℝ) < (ρ : ℝ) * N := by
      have : ((Finsupp.weight (jetWt W) d : ℚ) : ℝ) < ((ρ * (N : ℚ) : ℚ) : ℝ) := by
        exact_mod_cast hd
      push_cast at this
      exact this
    have hmemT : (⇑d : Fin (m + 1) → ℕ) ∈ T := by
      rw [hT, mem_strictWeightedSimplex (w := fun i => ((jetWt W i : ℚ) : ℝ))
        (fun i => by exact_mod_cast hV i)]
      rw [weight_jetWt_cast] at hdR
      exact hdR.trans_le hbN
    have hz := congrFun hEx (j, ⟨⇑d, hmemT⟩)
    change MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (⇑d))
      (ellJet s (c j) (auxPoly e x)) = 0 at hz
    have hd' : (Finsupp.equivFunOnFinite.symm (⇑d) : Fin (m + 1) →₀ ℕ) = d := by
      ext i; simp
    rwa [hd'] at hz

end CatalanCore.Elliptic.EPA
