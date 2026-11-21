module

public import CatalanCore.Elliptic.EPA.Ambient

/-!
# The frame derivations and the signed word bound (row E09.1)

Labels refer to the proof design §5 E09.1 and to CM §6 (`l.1325–1360`, `l.809–839`).

On the curve `P ↦ P(U(T), T, c + V + L(T))` the frame is the family of derivations of `AmbRing m`
indexed by `Fin (m+1)` (`0` for `T`, `i.succ` for `V_i`):

* `frameDeriv ch 0 = −2 t ∂_u − F′(u) ∂_t + Σ_i ∂_{Z_i}`;
* `frameDeriv ch i.succ = ∂_{Z_i}`.

`frameDeriv_relation`: every frame derivation kills `f = t² − F(u)` (CM l.1336).

`srcDeg_frameDeriv`, `srcDeg_frameWord`: a frame derivation of index `j` raises the source degree by
at most `srcCost W j`, where `srcCost W 0 = 2 w₀` and `srcCost W i.succ = −w_i`; a word raises it by
the sum of the costs (CM l.809–833). `srcCost_sum_le`: that sum is at most
`(2 w₀ / v₀)` times the jet weight of the word (CM l.835–839).

The derivation `frameDeriv ch 0` has the shape of OAI `PolynomialFrame.logarithmicDerivation`
(openai/math fd4aeeb2, Apache License 2.0, Copyright OpenAI), with the logarithmic derivation
`x₀ ∂_{x₀} + Σ ∂_{x_i}` replaced by the frame of the quartic `t² = F(u)`.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

open CatalanCore.Elliptic

variable {m : ℕ}

theorem derivation_finset_sum_apply {α : Type*} (s : Finset α)
    (D : α → Derivation ℂ (AmbRing m) (AmbRing m)) (p : AmbRing m) :
    (∑ a ∈ s, D a) p = ∑ a ∈ s, D a p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Derivation.zero_apply]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

/-- `frameDeriv ch 0 = −2 t ∂_u − F′(u) ∂_t + Σ_i ∂_{Z_i}`. -/
noncomputable def frameZero (ch : OriginChart) : Derivation ℂ (AmbRing m) (AmbRing m) :=
  (MvPolynomial.C (-2 : ℂ) * tV : AmbRing m) • MvPolynomial.pderiv (0 : Fin (m + 2)) -
    (Polynomial.aeval uV (Polynomial.derivative (Fc ch)) : AmbRing m) •
      MvPolynomial.pderiv (1 : Fin (m + 2)) +
    ∑ i : Fin m, MvPolynomial.pderiv i.succ.succ

/-- The frame derivations: index `0` is `T`, index `i.succ` is `V_i`. -/
noncomputable def frameDeriv (ch : OriginChart) :
    Fin (m + 1) → Derivation ℂ (AmbRing m) (AmbRing m) :=
  Fin.cases (motive := fun _ => Derivation ℂ (AmbRing m) (AmbRing m)) (frameZero ch)
    (fun i => MvPolynomial.pderiv i.succ.succ)

/-- The iterated frame derivation along a word (head applied last, as `foldr`). -/
noncomputable def frameWord (ch : OriginChart) (word : List (Fin (m + 1))) (P : AmbRing m) :
    AmbRing m :=
  word.foldr (fun i q => frameDeriv ch i q) P

@[simp] theorem frameWord_nil (ch : OriginChart) (P : AmbRing m) : frameWord ch [] P = P := rfl

@[simp] theorem frameWord_cons (ch : OriginChart) (i : Fin (m + 1)) (word : List (Fin (m + 1)))
    (P : AmbRing m) :
    frameWord ch (i :: word) P = frameDeriv ch i (frameWord ch word P) := rfl

@[simp] theorem frameDeriv_zero (ch : OriginChart) : frameDeriv ch (0 : Fin (m + 1)) = frameZero ch :=
  rfl

@[simp] theorem frameDeriv_succ (ch : OriginChart) (i : Fin m) :
    frameDeriv ch i.succ = MvPolynomial.pderiv i.succ.succ := rfl

theorem frameDeriv_zero_apply (ch : OriginChart) (P : AmbRing m) :
    frameDeriv ch 0 P =
      (MvPolynomial.C (-2 : ℂ) * tV) * MvPolynomial.pderiv 0 P -
        Polynomial.aeval uV (Polynomial.derivative (Fc ch)) * MvPolynomial.pderiv 1 P +
        ∑ i : Fin m, MvPolynomial.pderiv i.succ.succ P := by
  simp only [frameDeriv_zero, frameZero, Derivation.add_apply, Derivation.sub_apply,
    Derivation.smul_apply, smul_eq_mul, derivation_finset_sum_apply]

/-! ### Partial derivatives of the generators and of `f` -/

theorem pderiv_uV (i : Fin (m + 2)) :
    MvPolynomial.pderiv i (uV : AmbRing m) = if i = 0 then 1 else 0 := by
  unfold uV
  by_cases h : i = 0
  · subst h; simp [MvPolynomial.pderiv_X_self]
  · rw [if_neg h, MvPolynomial.pderiv_X_of_ne]; exact fun e => h e.symm

theorem pderiv_tV (i : Fin (m + 2)) :
    MvPolynomial.pderiv i (tV : AmbRing m) = if i = 1 then 1 else 0 := by
  unfold tV
  by_cases h : i = 1
  · subst h; simp [MvPolynomial.pderiv_X_self]
  · rw [if_neg h, MvPolynomial.pderiv_X_of_ne]; exact fun e => h e.symm

theorem pderiv_aeval_uV (i : Fin (m + 2)) (p : Polynomial ℂ) :
    MvPolynomial.pderiv i (Polynomial.aeval (uV : AmbRing m) p) =
      Polynomial.aeval uV (Polynomial.derivative p) * (if i = 0 then 1 else 0) := by
  rw [Derivation.map_aeval, pderiv_uV, smul_eq_mul]

theorem pderiv_relation (ch : OriginChart) (i : Fin (m + 2)) :
    MvPolynomial.pderiv i (relation ch : AmbRing m) =
      2 * tV * (if i = 1 then 1 else 0) -
        Polynomial.aeval uV (Polynomial.derivative (Fc ch)) * (if i = 0 then 1 else 0) := by
  unfold relation
  rw [map_sub, Derivation.leibniz_pow, pderiv_aeval_uV, pderiv_tV]
  simp [smul_eq_mul, nsmul_eq_mul] <;> ring

/-- CM l.1336: every frame derivation kills `f = t² − F(u)`. -/
theorem frameDeriv_relation (ch : OriginChart) (j : Fin (m + 1)) :
    frameDeriv ch j (relation ch : AmbRing m) = 0 := by
  induction j using Fin.cases with
  | zero =>
    have h0 : ∀ i : Fin m, MvPolynomial.pderiv i.succ.succ (relation ch : AmbRing m) = 0 := by
      intro i
      rw [pderiv_relation, if_neg (one_ne_succ_succ i).symm, if_neg (zero_ne_succ_succ i).symm]
      simp
    have hC : (MvPolynomial.C (-2 : ℂ) : AmbRing m) = -2 := by rw [map_neg, map_ofNat]
    rw [frameDeriv_zero_apply]
    simp only [h0, Finset.sum_const_zero, add_zero]
    rw [pderiv_relation, pderiv_relation]
    simp [zero_ne_one_amb, zero_ne_one_amb.symm, hC] <;> ring
  | succ i =>
    rw [frameDeriv_succ, pderiv_relation, if_neg (one_ne_succ_succ i).symm,
      if_neg (zero_ne_succ_succ i).symm]
    simp

/-! ### Signed degree bound -/

theorem srcDeg_frameDeriv {W : Weights m} {ch : OriginChart} {N : ℝ} {P : AmbRing m}
    (hP : SrcDeg W N P) (j : Fin (m + 1)) :
    SrcDeg W (N + ((srcCost W j : ℚ) : ℝ)) (frameDeriv ch j P) := by
  have hw0 : (0 : ℝ) < W.w₀ := by exact_mod_cast W.w₀_pos
  induction j using Fin.cases with
  | zero =>
    rw [frameDeriv_zero_apply, srcCost_zero]
    push_cast
    have ht : SrcDeg W (4 * (W.w₀ : ℝ)) (MvPolynomial.C (-2 : ℂ) * tV : AmbRing m) := by
      have h := (SrcDeg.C (W := W) (m := m) (-2 : ℂ) le_rfl).mul
        (SrcDeg.X (W := W) (1 : Fin (m + 2)))
      rw [srcRho_one] at h
      exact h.mono (le_of_eq (by ring))
    have h1 : SrcDeg W (N + 2 * (W.w₀ : ℝ))
        ((MvPolynomial.C (-2 : ℂ) * tV) * MvPolynomial.pderiv 0 P) := by
      have h := ht.mul (hP.pderiv 0)
      rw [srcRho_zero] at h
      exact h.mono (le_of_eq (by ring))
    have h2 : SrcDeg W (N + 2 * (W.w₀ : ℝ))
        (Polynomial.aeval uV (Polynomial.derivative (Fc ch)) * MvPolynomial.pderiv 1 P) := by
      have h := (SrcDeg.aeval_uV (W := W) (Polynomial.derivative (Fc ch)) 3
        (natDegree_Fc_derivative_le ch)).mul (hP.pderiv 1)
      rw [srcRho_zero, srcRho_one] at h
      exact h.mono (le_of_eq (by push_cast; ring))
    have h3 : SrcDeg W (N + 2 * (W.w₀ : ℝ)) (∑ i : Fin m, MvPolynomial.pderiv i.succ.succ P) := by
      refine SrcDeg.sum _ fun i _ => ?_
      have h := hP.pderiv i.succ.succ
      rw [srcRho_succ_succ] at h
      have hwi : (0 : ℝ) < W.w i := by exact_mod_cast W.w_pos i
      exact h.mono (by linarith)
    exact (h1.sub h2).add h3
  | succ i =>
    rw [frameDeriv_succ, srcCost_succ]
    push_cast
    have h := hP.pderiv i.succ.succ
    rw [srcRho_succ_succ] at h
    exact h.mono (le_of_eq (by ring))

/-- CM l.809–833: a word raises the source degree by the sum of its costs. -/
theorem srcDeg_frameWord {W : Weights m} {ch : OriginChart} {N : ℝ} {P : AmbRing m}
    (hP : SrcDeg W N P) (word : List (Fin (m + 1))) :
    SrcDeg W (N + (((word.map (srcCost W)).sum : ℚ) : ℝ)) (frameWord ch word P) := by
  induction word with
  | nil => simpa using hP
  | cons j word ih =>
    rw [frameWord_cons]
    have h := srcDeg_frameDeriv (ch := ch) ih j
    refine h.mono (le_of_eq ?_)
    simp only [List.map_cons, List.sum_cons]
    push_cast
    ring

/-- Per letter: `srcCost ≤ (2 w₀ / v₀) · jetWt`. -/
theorem srcCost_le (W : Weights m) (j : Fin (m + 1)) :
    srcCost W j ≤ 2 * W.w₀ / W.v₀ * jetWt W j := by
  induction j using Fin.cases with
  | zero =>
    rw [srcCost_zero, jetWt_zero, div_mul_cancel₀ _ W.v₀_pos.ne']
  | succ i =>
    rw [srcCost_succ, jetWt_succ]
    have hw := W.w_pos i
    have hw0 := W.w₀_pos
    have hv := W.v₀_pos
    have hθ := W.θ_pos
    have : 0 ≤ 2 * W.w₀ / W.v₀ * (W.w i / W.θ) :=
      (mul_pos (div_pos (mul_pos two_pos hw0) hv) (div_pos hw hθ)).le
    linarith

/-- CM l.835–839: the signed source cost of a word is at most `(2 w₀ / v₀)` times its jet weight. -/
theorem srcCost_sum_le (W : Weights m) (word : List (Fin (m + 1))) :
    (word.map (srcCost W)).sum ≤ 2 * W.w₀ / W.v₀ * (word.map (jetWt W)).sum := by
  induction word with
  | nil => simp
  | cons j word ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [mul_add]
    exact add_le_add (srcCost_le W j) ih

end CatalanCore.Elliptic.EPA
