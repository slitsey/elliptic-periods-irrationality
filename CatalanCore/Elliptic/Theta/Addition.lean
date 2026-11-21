module

public import CatalanCore.Elliptic.Theta.Product
public import CatalanCore.Elliptic.Theta.Liouville

@[expose] public section

/-!
# Θ on the lattice `Λ = ℤω₁ + ℤω₂` and the addition formula

For `L : PeriodPair` with `0 < Im (ω₂/ω₁)` put `thetaL L z := Θ_{ω₂/ω₁}(z / ω₁)`. Then

* `thetaL_eq_zero_iff`: `Θ_Λ(z) = 0 ↔ z ∈ Λ`; every zero is simple (`deriv_thetaL_zero_ne_zero`,
  `thetaL = z * thetaD`);
* **Proposition 4.1** (`thetaL_sub_mul_add`): for `c ∉ Λ` and `z ∉ Λ`,
  `Θ_Λ(z - c) Θ_Λ(z + c) = κ_c Θ_Λ(z)² (℘(z) - ℘(c))`,
  `κ_c = -e^{-2π i c/ω₁} Θ_Λ(c)² / Θ_Λ'(0)²`;
* **Corollary 4.2(a)** (`weierstrassP_eq_iff`): `℘(z) = ℘(c) ↔ z - c ∈ Λ ∨ z + c ∈ Λ`.
-/

namespace CatalanCore.Elliptic.Theta

open Complex Real Filter Topology Function Set

variable (L : PeriodPair)

/-- The hypothesis `0 < Im (ω₂ / ω₁)`. -/
abbrev TauPos : Prop := 0 < (L.ω₂ / L.ω₁).im

lemma ω₁_ne_zero : L.ω₁ ≠ 0 := by
  simpa using L.indep.ne_zero 0

/-- `Θ` in lattice coordinates: `Θ_Λ(z) = Θ_τ(z / ω₁)`, `τ = ω₂ / ω₁`. -/
noncomputable def thetaL (z : ℂ) : ℂ := theta (L.ω₂ / L.ω₁) (z / L.ω₁)

variable {L}

theorem differentiable_thetaL (hτ : TauPos L) : Differentiable ℂ (thetaL L) :=
  (differentiable_theta hτ).comp (differentiable_id.div_const _)

@[simp] theorem thetaL_zero : thetaL L 0 = 0 := by simp [thetaL]

theorem thetaL_eq_zero_iff (hτ : TauPos L) (z : ℂ) : thetaL L z = 0 ↔ z ∈ L.lattice := by
  have hω := ω₁_ne_zero L
  unfold thetaL
  rw [theta_eq_zero_iff hτ, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, h⟩
    refine ⟨m, n, ?_⟩
    rw [div_eq_iff hω] at h
    rw [h]
    field_simp
  · rintro ⟨m, n, h⟩
    refine ⟨m, n, ?_⟩
    rw [← h]
    field_simp

theorem thetaL_ne_zero (hτ : TauPos L) {z : ℂ} (hz : z ∉ L.lattice) : thetaL L z ≠ 0 :=
  fun h => hz ((thetaL_eq_zero_iff hτ z).1 h)

/-- Quasi-periodicity of `Θ_Λ` for a lattice vector. -/
theorem thetaL_add_lattice (hτ : TauPos L) {l : ℂ} (hl : l ∈ L.lattice) :
    ∃ n : ℤ, ∀ z, thetaL L (z + l) = thetaMult (L.ω₂ / L.ω₁) n (z / L.ω₁) * thetaL L z := by
  have hω := ω₁_ne_zero L
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 hl
  refine ⟨n, fun z => ?_⟩
  unfold thetaL
  have h : (z + (m * L.ω₁ + n * L.ω₂)) / L.ω₁ = z / L.ω₁ + m + n * (L.ω₂ / L.ω₁) := by
    field_simp
    ring
  rw [h]
  exact theta_add_int_add_zsmul_tau hτ m n _

/-- Reflection: `Θ_Λ(-z) = -e^{-2π i z/ω₁} Θ_Λ(z)`. -/
theorem thetaL_neg (z : ℂ) :
    thetaL L (-z) = -cexp (-(2 * π * I * (z / L.ω₁))) * thetaL L z := by
  unfold thetaL
  rw [neg_div, theta_neg]

/-- `Θ_Λ'(0)`. -/
theorem hasDerivAt_thetaL_zero (hτ : TauPos L) :
    HasDerivAt (thetaL L)
      ((-(2 * π * I) * eulerP (L.ω₂ / L.ω₁) ^ 2) * (1 / L.ω₁)) 0 := by
  have h := (hasDerivAt_theta_zero hτ).comp_of_eq (0 : ℂ)
    ((hasDerivAt_id (0 : ℂ)).div_const L.ω₁) (by simp)
  exact h

theorem deriv_thetaL_zero_ne_zero (hτ : TauPos L) : deriv (thetaL L) 0 ≠ 0 := by
  rw [(hasDerivAt_thetaL_zero hτ).deriv]
  have hω := ω₁_ne_zero L
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.2 two_pi_I_ne_zero)
    (pow_ne_zero 2 (eulerP_ne_zero hτ))) (by simpa using hω)

variable (L)

/-- The dslope `Θ_Λ(z) / z` (entire, with value `Θ_Λ'(0)` at `0`). -/
noncomputable def thetaD : ℂ → ℂ := dslope (thetaL L) 0

variable {L}

theorem differentiable_thetaD (hτ : TauPos L) : Differentiable ℂ (thetaD L) := by
  have h := (Complex.differentiableOn_dslope (c := (0 : ℂ)) (s := Set.univ) Filter.univ_mem).2
    (differentiable_thetaL hτ).differentiableOn
  exact differentiableOn_univ.1 h

@[simp] theorem thetaD_zero : thetaD L 0 = deriv (thetaL L) 0 := by
  simp [thetaD]

theorem thetaL_eq_mul_thetaD (z : ℂ) : thetaL L z = z * thetaD L z := by
  have := sub_smul_dslope (thetaL L) 0 z
  simpa [thetaD] using this.symm

theorem thetaD_ne_zero_zero (hτ : TauPos L) : thetaD L 0 ≠ 0 := by
  rw [thetaD_zero]; exact deriv_thetaL_zero_ne_zero hτ

theorem thetaD_neg (z : ℂ) :
    thetaD L (-z) = cexp (-(2 * π * I * (z / L.ω₁))) * thetaD L z := by
  by_cases hz : z = 0
  · subst hz; simp
  · have h1 := thetaL_eq_mul_thetaD (L := L) (-z)
    rw [thetaL_neg, thetaL_eq_mul_thetaD (L := L) z] at h1
    have hz' : -z ≠ 0 := neg_ne_zero.2 hz
    apply mul_left_cancel₀ hz'
    linear_combination -h1

theorem differentiable_thetaMult (τ : ℂ) (n : ℤ) : Differentiable ℂ (thetaMult τ n) := by
  unfold thetaMult
  fun_prop

/-- **Simple zeros (T7c).** At each lattice point `l`, `Θ_Λ(z) = (z - l) f(z)` with `f` entire and
`f(l) ≠ 0`. -/
theorem thetaL_simple_zero (hτ : TauPos L) {l : ℂ} (hl : l ∈ L.lattice) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ f l ≠ 0 ∧ ∀ z, thetaL L z = (z - l) * f z := by
  obtain ⟨n, hn⟩ := thetaL_add_lattice hτ hl
  have h1 := differentiable_thetaD hτ
  have h2 := differentiable_thetaMult (L.ω₂ / L.ω₁) n
  refine ⟨fun z => thetaMult (L.ω₂ / L.ω₁) n ((z - l) / L.ω₁) * thetaD L (z - l), ?_, ?_,
    fun z => ?_⟩
  · fun_prop
  · simp only [sub_self, zero_div]
    exact mul_ne_zero (thetaMult_ne_zero _ _ _) (thetaD_ne_zero_zero hτ)
  · have := hn (z - l)
    rw [sub_add_cancel] at this
    rw [this, thetaL_eq_mul_thetaD (L := L) (z - l)]
    ring

section Addition

variable (L)

/-- `N_c(z) = Θ_Λ(z - c) Θ_Λ(z + c)`. -/
noncomputable def thetaN (c z : ℂ) : ℂ := thetaL L (z - c) * thetaL L (z + c)

/-- `M_c = N_c / (Θ_Λ / z)²`. -/
noncomputable def thetaM (c z : ℂ) : ℂ := thetaN L c z / thetaD L z ^ 2

/-- The constant `κ_c = -e^{-2π i c/ω₁} Θ_Λ(c)² / Θ_Λ'(0)²`. -/
noncomputable def thetaKappa (c : ℂ) : ℂ :=
  -cexp (-(2 * π * I * (c / L.ω₁))) * thetaL L c ^ 2 / (deriv (thetaL L) 0) ^ 2

variable {L}

theorem thetaN_neg (c z : ℂ) :
    thetaN L c (-z) = cexp (-(2 * π * I * (z / L.ω₁))) ^ 2 * thetaN L c z := by
  unfold thetaN
  have h1 : -z - c = -(z + c) := by ring
  have h2 : -z + c = -(z - c) := by ring
  rw [h1, h2, thetaL_neg, thetaL_neg]
  have : cexp (-(2 * π * I * ((z + c) / L.ω₁))) * cexp (-(2 * π * I * ((z - c) / L.ω₁))) =
      cexp (-(2 * π * I * (z / L.ω₁))) ^ 2 := by
    rw [sq, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  linear_combination (thetaL L (z + c) * thetaL L (z - c)) * this

theorem thetaM_neg (c z : ℂ) : thetaM L c (-z) = thetaM L c z := by
  unfold thetaM
  rw [thetaN_neg, thetaD_neg, mul_pow]
  have hε : cexp (-(2 * π * I * (z / L.ω₁))) ^ 2 ≠ 0 := pow_ne_zero 2 (Complex.exp_ne_zero _)
  rw [mul_div_mul_left _ _ hε]

theorem thetaM_zero (c : ℂ) : thetaM L c 0 = thetaKappa L c := by
  unfold thetaM thetaN thetaKappa
  rw [thetaD_zero]
  simp only [zero_sub, zero_add]
  rw [thetaL_neg]
  ring

/-- The Taylor expansion of `M_c` at `0`: `M_c(z) = κ_c + z² M₂(z)`, `M₂` continuous at `0`. -/
theorem thetaM_expand (hτ : TauPos L) (c : ℂ) :
    ∃ M₂ : ℂ → ℂ, ContinuousAt M₂ 0 ∧ ∀ z, thetaM L c z = thetaKappa L c + z ^ 2 * M₂ z := by
  have hD := differentiable_thetaD hτ
  set U : Set ℂ := {z | thetaD L z ≠ 0} with hUdef
  have hUo : IsOpen U := isOpen_ne_fun hD.continuous continuous_const
  have hU0 : U ∈ 𝓝 (0 : ℂ) := hUo.mem_nhds (thetaD_ne_zero_zero hτ)
  have hN : Differentiable ℂ (thetaN L c) := by
    unfold thetaN
    have := differentiable_thetaL hτ
    fun_prop
  have hMd : DifferentiableOn ℂ (thetaM L c) U :=
    hN.differentiableOn.div (hD.pow 2).differentiableOn (fun z hz => pow_ne_zero 2 hz)
  have hM1 : DifferentiableOn ℂ (dslope (thetaM L c) 0) U :=
    (Complex.differentiableOn_dslope hU0).2 hMd
  have hM2 : DifferentiableOn ℂ (dslope (dslope (thetaM L c) 0) 0) U :=
    (Complex.differentiableOn_dslope hU0).2 hM1
  -- the derivative of the even function `M_c` vanishes at `0`
  have hMat : HasDerivAt (thetaM L c) (deriv (thetaM L c) 0) 0 :=
    (hMd.differentiableAt hU0).hasDerivAt
  have hMneg : HasDerivAt (thetaM L c) (deriv (thetaM L c) 0 * (-1)) 0 := by
    have h := hMat.comp_of_eq (0 : ℂ) (hasDerivAt_neg (0 : ℂ)) (by simp)
    have hfun : (thetaM L c ∘ Neg.neg) = thetaM L c := by
      funext z; simp [thetaM_neg]
    rw [hfun] at h
    exact h
  have hd0 : deriv (thetaM L c) 0 = 0 := by
    have := hMat.unique hMneg
    linear_combination (1 / 2 : ℂ) * this
  refine ⟨dslope (dslope (thetaM L c) 0) 0, hM2.continuousOn.continuousAt hU0, fun z => ?_⟩
  have e1 := sub_smul_dslope (thetaM L c) 0 z
  have e2 := sub_smul_dslope (dslope (thetaM L c) 0) 0 z
  have e0 : dslope (thetaM L c) 0 0 = 0 := by rw [dslope_same, hd0]
  simp only [sub_zero, smul_eq_mul, e0] at e1 e2
  rw [thetaM_zero] at e1
  linear_combination -e1 - z * e2

theorem thetaKappa_ne_zero (hτ : TauPos L) {c : ℂ} (hc : c ∉ L.lattice) :
    thetaKappa L c ≠ 0 := by
  unfold thetaKappa
  exact div_ne_zero (mul_ne_zero (neg_ne_zero.2 (Complex.exp_ne_zero _))
    (pow_ne_zero 2 (thetaL_ne_zero hτ hc))) (pow_ne_zero 2 (deriv_thetaL_zero_ne_zero hτ))

/-- The function `G_c(z) = N_c(z) / Θ_Λ(z)² - κ_c (℘(z) - ℘(c))`. -/
noncomputable def addG (c z : ℂ) : ℂ :=
  thetaN L c z / thetaL L z ^ 2 - thetaKappa L c * (L.weierstrassP z - L.weierstrassP c)

theorem addG_periodic (hτ : TauPos L) (c : ℂ) {l : ℂ} (hl : l ∈ L.lattice) {z : ℂ}
    (hz : z ∉ L.lattice) : addG (L := L) c (z + l) = addG (L := L) c z := by
  obtain ⟨n, hn⟩ := thetaL_add_lattice hτ hl
  unfold addG thetaN
  have e1 : thetaL L (z + l - c) = thetaMult (L.ω₂ / L.ω₁) n ((z - c) / L.ω₁) *
      thetaL L (z - c) := by
    rw [show z + l - c = (z - c) + l by ring]; exact hn _
  have e2 : thetaL L (z + l + c) = thetaMult (L.ω₂ / L.ω₁) n ((z + c) / L.ω₁) *
      thetaL L (z + c) := by
    rw [show z + l + c = (z + c) + l by ring]; exact hn _
  have e3 : thetaMult (L.ω₂ / L.ω₁) n ((z - c) / L.ω₁) *
      thetaMult (L.ω₂ / L.ω₁) n ((z + c) / L.ω₁) =
      thetaMult (L.ω₂ / L.ω₁) n (z / L.ω₁) ^ 2 := by
    rw [← thetaMult_sub_mul_add (L.ω₂ / L.ω₁) n (z / L.ω₁) (c / L.ω₁)]
    congr 2 <;> ring
  have hP : L.weierstrassP (z + l) = L.weierstrassP z := L.weierstrassP_add_coe z ⟨l, hl⟩
  rw [hn, e1, e2, hP]
  have hμ := thetaMult_ne_zero (L.ω₂ / L.ω₁) n (z / L.ω₁)
  have hθ := thetaL_ne_zero hτ hz
  have : thetaMult (L.ω₂ / L.ω₁) n (z / L.ω₁) * thetaL L z ≠ 0 := mul_ne_zero hμ hθ
  congr 1
  rw [mul_mul_mul_comm, e3]
  field_simp

theorem differentiableOn_addG (hτ : TauPos L) (c : ℂ) :
    DifferentiableOn ℂ (addG (L := L) c) ((L.lattice : Set ℂ)ᶜ) := by
  have hθ := differentiable_thetaL hτ
  have hN : Differentiable ℂ (thetaN L c) := by
    unfold thetaN; fun_prop
  unfold addG
  refine DifferentiableOn.sub (hN.differentiableOn.div (hθ.pow 2).differentiableOn ?_) ?_
  · intro z hz
    exact pow_ne_zero 2 (thetaL_ne_zero hτ hz)
  · exact (L.differentiableOn_weierstrassP.sub_const _).const_mul _

/-- Near `0`, `G_c` is a continuous germ. -/
theorem addG_germ (hτ : TauPos L) (c : ℂ) :
    ∃ k : ℂ → ℂ, ContinuousAt k 0 ∧ addG (L := L) c =ᶠ[𝓝[≠] (0 : ℂ)] k := by
  obtain ⟨M₂, hM₂, hM⟩ := thetaM_expand hτ c
  refine ⟨fun z => M₂ z - thetaKappa L c * (L.weierstrassPExcept 0 z - L.weierstrassP c), ?_, ?_⟩
  · have h1 : ContinuousAt (L.weierstrassPExcept 0) 0 :=
      (L.analyticAt_weierstrassPExcept 0).continuousAt
    exact hM₂.sub ((h1.sub continuousAt_const).const_mul _)
  · have hs := L.compl_lattice_sdiff_singleton_mem_nhds (0 : ℂ)
    have hs' := nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)) hs
    filter_upwards [hs', self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    have hzl : z ∉ L.lattice := fun h => hz ⟨h, hz0'⟩
    have hP := L.weierstrassPExcept_add 0 z
    simp only [ZeroMemClass.coe_zero, sub_zero, one_div, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, inv_zero] at hP
    have hQ : thetaN L c z / thetaL L z ^ 2 = thetaM L c z / z ^ 2 := by
      rw [thetaL_eq_mul_thetaD (L := L) z]
      unfold thetaM
      rw [mul_pow, div_div, mul_comm (thetaD L z ^ 2)]
    unfold addG
    rw [hQ, hM z, ← hP]
    field_simp
    ring

/-- **Proposition 4.1 (addition formula).** For `c ∉ Λ` and `z ∉ Λ`,
`Θ_Λ(z - c) Θ_Λ(z + c) = κ_c Θ_Λ(z)² (℘(z) - ℘(c))`. -/
theorem thetaL_sub_mul_add (hτ : TauPos L) {c z : ℂ} (hc : c ∉ L.lattice) (hz : z ∉ L.lattice) :
    thetaL L (z - c) * thetaL L (z + c) =
      thetaKappa L c * thetaL L z ^ 2 * (L.weierstrassP z - L.weierstrassP c) := by
  obtain ⟨k, hk, hgk⟩ := addG_germ hτ c
  obtain ⟨G, hGd, hGg, hGp⟩ := exists_entire_extension_periodic L (addG (L := L) c)
    (differentiableOn_addG hτ c) (fun l hl z hz => addG_periodic hτ c hl hz)
    (bounded_near_zero_of_germ hk hgk)
  have hconst := periodic_entire_const L hGd (fun z l hl => hGp l hl z) z c
  have hGc : G c = 0 := by
    rw [hGg c hc]
    unfold addG thetaN
    simp
  have hGz : G z = 0 := by rw [hconst, hGc]
  rw [hGg z hz] at hGz
  unfold addG thetaN at hGz
  have hθ := thetaL_ne_zero hτ hz
  have h2 : thetaL L z ^ 2 ≠ 0 := pow_ne_zero 2 hθ
  field_simp at hGz
  linear_combination hGz

/-- Proposition 4.1 with `κ_c` written out:
`Θ_Λ(z - c) Θ_Λ(z + c) Θ_Λ'(0)² = e^{-2π i c/ω₁} Θ_Λ(c)² Θ_Λ(z)² (℘(c) - ℘(z))`. -/
theorem thetaL_sub_mul_add_explicit (hτ : TauPos L) {c z : ℂ} (hc : c ∉ L.lattice)
    (hz : z ∉ L.lattice) :
    thetaL L (z - c) * thetaL L (z + c) * deriv (thetaL L) 0 ^ 2 =
      cexp (-(2 * π * I * (c / L.ω₁))) * thetaL L c ^ 2 * thetaL L z ^ 2 *
        (L.weierstrassP c - L.weierstrassP z) := by
  have h := thetaL_sub_mul_add hτ hc hz
  have hd0 := deriv_thetaL_zero_ne_zero hτ
  have hd := pow_ne_zero 2 hd0
  rw [h]
  unfold thetaKappa
  field_simp
  ring

/-- **Corollary 4.2(a).** For `z, c ∉ Λ`: `℘(z) = ℘(c)` iff `z - c ∈ Λ` or `z + c ∈ Λ`. -/
theorem weierstrassP_eq_iff (hτ : TauPos L) {c z : ℂ} (hc : c ∉ L.lattice)
    (hz : z ∉ L.lattice) :
    L.weierstrassP z = L.weierstrassP c ↔ z - c ∈ L.lattice ∨ z + c ∈ L.lattice := by
  have h := thetaL_sub_mul_add hτ hc hz
  have hκ := thetaKappa_ne_zero hτ hc
  have hθ := pow_ne_zero 2 (thetaL_ne_zero hτ hz)
  have key : L.weierstrassP z = L.weierstrassP c ↔
      thetaL L (z - c) * thetaL L (z + c) = 0 := by
    rw [h]
    constructor
    · intro e; rw [e]; ring
    · intro e
      have := mul_eq_zero.1 e
      rcases this with e1 | e1
      · exact absurd e1 (mul_ne_zero hκ hθ)
      · exact sub_eq_zero.1 e1
  rw [key, mul_eq_zero, thetaL_eq_zero_iff hτ, thetaL_eq_zero_iff hτ]

end Addition

end CatalanCore.Elliptic.Theta
