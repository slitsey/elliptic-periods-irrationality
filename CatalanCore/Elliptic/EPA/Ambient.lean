module

public import CatalanCore.Elliptic.EPA.Params
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Tactic.ComputeDegree

/-!
# The ambient ring of `thm:epa` and its weighted degree (row E09.1)

Labels refer to the proof design (§1, §2 P2, §5 E09.1, §A4) and to the paper
`paper/elliptic-periods.tex`, `thm:epa` (CM Cor 13.5).

The ambient design (D2-design §0.1): work on `𝔸^{m+2} = Spec ℂ[u, t, Z₁, …, Z_m]` and put the
relation `f = t² − F(u)` of the quartic `t² = F(u)` into the centre ideal, instead of building the
compactification of `Spec ℂ[u,t,Z]/(f)`.

* `AmbRing m`: `ℂ[u, t, Z]` with coordinates `Fin (m+2)`: `0 = u`, `1 = t`, `i.succ.succ = Z_i`.
* `Fc ch`: the quartic `F` of the chart over `ℂ`; `relation ch = t² − F(u)`.
* `srcWt W = (2w₀, 4w₀, w₁, …, w_m)`: the source (degree) weights; `SrcDeg W N P` is
  `weight(d) ≤ N` for every monomial `d` of `P` (the shape of OAI
  `WeightedSliceDegree.SupportBound`, with which it agrees by `Iff.rfl`).
* `SrcDeg` is closed under sums, products (adding the bounds), and `∂/∂x_i` (subtracting the
  weight of `x_i`).
* `relation_srcDeg_le`: `SrcDeg W (8 w₀) (relation ch)` (design §A4).

`radWt` and `jetWt` are in `Params.lean`.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

open CatalanCore.Elliptic
open scoped Pointwise

variable {m : ℕ}

/-- The ambient ring `ℂ[u, t, Z₁, …, Z_m]`; coordinates `0 = u`, `1 = t`, `i.succ.succ = Z_i`. -/
abbrev AmbRing (m : ℕ) : Type := MvPolynomial (Fin (m + 2)) ℂ

/-- The quartic `F(U) = U + 3aU² + (3a²+A)U³ + f(a)U⁴` of the chart, over `ℂ`. -/
noncomputable def Fc (ch : OriginChart) : Polynomial ℂ := ch.F.map (Int.castRingHom ℂ)

/-- The coordinate `u`. -/
noncomputable def uV : AmbRing m := MvPolynomial.X 0

/-- The coordinate `t`. -/
noncomputable def tV : AmbRing m := MvPolynomial.X 1

/-- The coordinate `Z_i`. -/
noncomputable def zV (i : Fin m) : AmbRing m := MvPolynomial.X i.succ.succ

/-- The relation `f = t² − F(u)`. -/
noncomputable def relation (ch : OriginChart) : AmbRing m :=
  tV ^ 2 - Polynomial.aeval uV (Fc ch)

theorem one_eq_succ_zero : (1 : Fin (m + 2)) = Fin.succ (0 : Fin (m + 1)) := by simp

theorem zero_ne_one_amb : (0 : Fin (m + 2)) ≠ 1 := by
  rw [one_eq_succ_zero]; exact (Fin.succ_ne_zero _).symm

theorem zero_ne_succ_succ (i : Fin m) : (0 : Fin (m + 2)) ≠ i.succ.succ :=
  (Fin.succ_ne_zero _).symm

theorem one_ne_succ_succ (i : Fin m) : (1 : Fin (m + 2)) ≠ i.succ.succ := by
  rw [one_eq_succ_zero]
  exact fun h => Fin.succ_ne_zero i (Fin.succ_injective _ h).symm

/-! ### Source weights -/

/-- Source weights `(2w₀, 4w₀, w₁, …, w_m)` on `Fin (m+2)` (`u`, `t`, `Z_i`). -/
def srcWt (W : Weights m) : Fin (m + 2) → ℚ :=
  Fin.cases (motive := fun _ => ℚ) (2 * W.w₀)
    (Fin.cases (motive := fun _ => ℚ) (4 * W.w₀) W.w)

@[simp] theorem srcWt_zero (W : Weights m) : srcWt W 0 = 2 * W.w₀ := rfl

theorem srcWt_one (W : Weights m) : srcWt W 1 = 4 * W.w₀ := by
  rw [one_eq_succ_zero]; rfl

@[simp] theorem srcWt_succ_succ (W : Weights m) (i : Fin m) : srcWt W i.succ.succ = W.w i := rfl

theorem srcWt_pos (W : Weights m) (j : Fin (m + 2)) : 0 < srcWt W j := by
  induction j using Fin.cases with
  | zero => show (0 : ℚ) < 2 * W.w₀; exact mul_pos two_pos W.w₀_pos
  | succ j =>
    induction j using Fin.cases with
    | zero => show (0 : ℚ) < 4 * W.w₀; exact mul_pos (by norm_num) W.w₀_pos
    | succ i => show (0 : ℚ) < W.w i; exact W.w_pos i

/-- The source weights as reals. -/
noncomputable def srcRho (W : Weights m) (j : Fin (m + 2)) : ℝ := ((srcWt W j : ℚ) : ℝ)

theorem srcRho_pos (W : Weights m) (j : Fin (m + 2)) : 0 < srcRho W j := by
  unfold srcRho; exact_mod_cast srcWt_pos W j

theorem srcRho_zero (W : Weights m) : srcRho W 0 = 2 * (W.w₀ : ℝ) := by
  simp [srcRho]

theorem srcRho_one (W : Weights m) : srcRho W 1 = 4 * (W.w₀ : ℝ) := by
  simp [srcRho, srcWt_one]

theorem srcRho_succ_succ (W : Weights m) (i : Fin m) : srcRho W i.succ.succ = (W.w i : ℝ) := by
  simp [srcRho]

/-- `SrcDeg W N P`: every monomial of `P` has source weight `≤ N`. -/
def SrcDeg (W : Weights m) (N : ℝ) (P : AmbRing m) : Prop :=
  ∀ d ∈ P.support, Finsupp.weight (fun j => srcRho W j) d ≤ N

namespace SrcDeg

variable {W : Weights m} {N M : ℝ} {P Q : AmbRing m}

theorem mono (h : SrcDeg W N P) (hNM : N ≤ M) : SrcDeg W M P :=
  fun d hd => (h d hd).trans hNM

theorem zero : SrcDeg W N (0 : AmbRing m) := fun d hd => by simp at hd

theorem add (hP : SrcDeg W N P) (hQ : SrcDeg W N Q) : SrcDeg W N (P + Q) := by
  classical
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact hP d h
  · exact hQ d h

theorem neg (hP : SrcDeg W N P) : SrcDeg W N (-P) := by
  intro d hd
  rw [MvPolynomial.support_neg] at hd
  exact hP d hd

theorem sub (hP : SrcDeg W N P) (hQ : SrcDeg W N Q) : SrcDeg W N (P - Q) := by
  rw [sub_eq_add_neg]; exact hP.add hQ.neg

theorem sum {ι : Type*} (s : Finset ι) {f : ι → AmbRing m} (h : ∀ i ∈ s, SrcDeg W N (f i)) :
    SrcDeg W N (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : SrcDeg W N (0 : AmbRing m))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem monomial (d : Fin (m + 2) →₀ ℕ) (a : ℂ) (h : Finsupp.weight (fun j => srcRho W j) d ≤ N) :
    SrcDeg W N (MvPolynomial.monomial d a) := by
  intro e he
  have := MvPolynomial.support_monomial_subset he
  rw [Finset.mem_singleton] at this
  subst this
  exact h

theorem C (a : ℂ) (hN : 0 ≤ N) : SrcDeg W N (MvPolynomial.C a : AmbRing m) := by
  rw [MvPolynomial.C_apply]
  exact monomial 0 a (by simpa using hN)

theorem X (i : Fin (m + 2)) : SrcDeg W (srcRho W i) (MvPolynomial.X i : AmbRing m) := by
  intro d hd
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hd
  subst hd
  simp [Finsupp.weight_single]

theorem X_pow (i : Fin (m + 2)) (k : ℕ) :
    SrcDeg W ((k : ℝ) * srcRho W i) ((MvPolynomial.X i : AmbRing m) ^ k) := by
  rw [MvPolynomial.X_pow_eq_monomial]
  exact monomial _ _ (by simp [Finsupp.weight_single])

theorem mul (hP : SrcDeg W N P) (hQ : SrcDeg W M Q) : SrcDeg W (N + M) (P * Q) := by
  classical
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  rw [map_add]
  exact add_le_add (hP a ha) (hQ b hb)

theorem smul (c : ℂ) (hP : SrcDeg W N P) : SrcDeg W N (c • P) := by
  intro d hd
  exact hP d (MvPolynomial.support_smul hd)

/-- `∂/∂x_i` lowers the source degree by the weight of `x_i`. -/
theorem pderiv (hP : SrcDeg W N P) (i : Fin (m + 2)) :
    SrcDeg W (N - srcRho W i) (MvPolynomial.pderiv i P) := by
  intro d hd
  have hc : (MvPolynomial.pderiv i P).coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  rw [MvPolynomial.coeff_pderiv] at hc
  have h1 : P.coeff (d + Finsupp.single i 1) ≠ 0 := left_ne_zero_of_mul hc
  have := hP _ (MvPolynomial.mem_support_iff.mpr h1)
  simp only [map_add, Finsupp.weight_single, one_smul] at this
  linarith

/-- The image of a polynomial of degree `≤ n` in `u` has source degree `≤ n · 2w₀`. -/
theorem aeval_uV (p : Polynomial ℂ) (n : ℕ) (hp : p.natDegree ≤ n) :
    SrcDeg W ((n : ℝ) * srcRho W 0) (Polynomial.aeval (uV : AmbRing m) p) := by
  rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hp)]
  refine sum _ fun k hk => ?_
  have hk' : (k : ℝ) ≤ n := by
    exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact (smul _ (X_pow (W := W) (0 : Fin (m + 2)) k)).mono
    (mul_le_mul_of_nonneg_right hk' (srcRho_pos W 0).le)

end SrcDeg

/-- `SrcDeg` is the OAI `SupportBound` for the weights `srcRho`. -/
theorem srcDeg_iff (W : Weights m) (N : ℝ) (P : AmbRing m) :
    SrcDeg W N P ↔ ∀ d ∈ P.support, Finsupp.weight (fun j => srcRho W j) d ≤ N := Iff.rfl

/-! ### Signed cost of a frame letter -/

/-- The signed cost `2 w₀` for `T`, `−w_i` for `V_i`. -/
def srcCost (W : Weights m) : Fin (m + 1) → ℚ :=
  Fin.cases (motive := fun _ => ℚ) (2 * W.w₀) (fun i => - W.w i)

@[simp] theorem srcCost_zero (W : Weights m) : srcCost W 0 = 2 * W.w₀ := rfl
@[simp] theorem srcCost_succ (W : Weights m) (i : Fin m) : srcCost W i.succ = - W.w i := rfl

/-! ### The relation -/

theorem natDegree_F_le (ch : OriginChart) : ch.F.natDegree ≤ 4 := by
  unfold OriginChart.F
  compute_degree

theorem natDegree_Fc_le (ch : OriginChart) : (Fc ch).natDegree ≤ 4 :=
  (Polynomial.natDegree_map_le).trans (natDegree_F_le ch)

theorem natDegree_Fc_derivative_le (ch : OriginChart) :
    (Polynomial.derivative (Fc ch)).natDegree ≤ 3 := by
  refine (Polynomial.natDegree_derivative_le _).trans ?_
  have := natDegree_Fc_le ch
  omega

/-- Design §A4: every monomial of `relation = t² − F(u)` has source weight `≤ 8 w₀`
(`t²` has weight `8 w₀`, `u^k` has weight `2 w₀ k`, `k ≤ 4`). -/
theorem relation_srcDeg_le (W : Weights m) (ch : OriginChart) :
    SrcDeg W (8 * (W.w₀ : ℝ)) (relation ch) := by
  unfold relation
  have h1 : SrcDeg W (8 * (W.w₀ : ℝ)) (tV ^ 2 : AmbRing m) := by
    have := SrcDeg.X_pow (W := W) (1 : Fin (m + 2)) 2
    rw [srcRho_one] at this
    refine (this.mono (le_of_eq ?_))
    push_cast; ring
  have h2 : SrcDeg W (8 * (W.w₀ : ℝ)) (Polynomial.aeval (uV : AmbRing m) (Fc ch)) := by
    have := SrcDeg.aeval_uV (W := W) (Fc ch) 4 (natDegree_Fc_le ch)
    rw [srcRho_zero] at this
    refine (this.mono (le_of_eq ?_))
    push_cast; ring
  exact h1.sub h2

end CatalanCore.Elliptic.EPA
