module

public import OAI.NumberTheory.PiExponent.Jets.CommutingTaylor
public import OAI.NumberTheory.PiExponent.Jets.PrimeTaylorCotangent
public import OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity

/-!
# Taylor lower bound for a general frame (row E09.4b)

Labels refer to the proof design §5 E09.4b and to CM Lemma `lem:p1-generic-taylor-lower`
(arXiv 2610.31112, l.962 and its corollary l.1048–1060).

For a prime `Q` of `ℂ[X₁..X_n]` and derivations `D_i` of `ℂ[X]` (letters `i : ι`), let `B : Fin k → ι`
select `k` letters whose coefficient vectors `(D_{B j}(X_l))_l`, reduced modulo `Q`, are independent
in the normal space `K^n / T_Q`. If every `p ∈ I` has all iterated derivatives
`D_{i₁} ⋯ D_{i_r} p` of total cost at most `δ` in `Q` (cost of a word = sum of the costs of its
letters), then, for any rectangle `nn : Fin k → ℕ` with `nn i ≥ 2` and
`∑ (nn i - 1) cost(B i) ≤ δ`, the local length of `ℂ[X]/I` at `Q` is at least `∏ nn i`.

The statement is OAI `PrimeFrameMultiplicity.prime_frame_rectangular_length_lower`
(openai/math fd4aeeb2, Apache License 2.0, Copyright OpenAI), typed there on `FramePolynomial m`
and the frame `polynomialFrame m`, restated for an arbitrary family of derivations. The proof
follows OAI `FrameTransverseMultiplicity` and `TaylorRectangular`: the Taylor map along the chosen
derivations, localized at `Q`, with the generic `prime_rectangular_mapCotangent_surjective`.
No commutation of the `D_i` is needed (`taylorHomFin` is a composite of ring homomorphisms; the
order of a word is that of `mixedIter`).
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA.Local

noncomputable section

open scoped BigOperators
open OAI OAI.PiExponent OAI.PiExponent.CommutingTaylor OAI.PiExponentApprox.TransverseMultiplicity

variable {n : ℕ} {ι : Type*}

/-- Iterated derivation along a word, head applied last (the shape of `frameWord`). -/
def derivWord (D : ι → Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ))
    (word : List ι) (p : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  word.foldr (fun i q => D i q) p

@[simp] theorem derivWord_nil (D : ι → Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ))
    (p : MvPolynomial (Fin n) ℂ) : derivWord D [] p = p := rfl

@[simp] theorem derivWord_cons (D : ι → Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ))
    (i : ι) (word : List ι) (p : MvPolynomial (Fin n) ℂ) :
    derivWord D (i :: word) p = D i (derivWord D word p) := rfl

/-- The `ℚ`-derivation underlying a `ℂ`-derivation. -/
def ratDeriv (D : Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ)) :
    Derivation ℚ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ) :=
  D.restrictScalars ℚ

@[simp] theorem ratDeriv_apply
    (D : Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ))
    (p : MvPolynomial (Fin n) ℂ) : ratDeriv D p = D p := rfl

/-- A derivation of `ℂ[X₁..X_n]` is determined by its values on the variables. -/
theorem derivation_apply_eq_sum
    (D : Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ))
    (p : MvPolynomial (Fin n) ℂ) :
    D p = ∑ i, D (MvPolynomial.X i) * MvPolynomial.pderiv i p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h1 : D (MvPolynomial.C a) = 0 := by
      have := D.map_algebraMap a
      simp [MvPolynomial.algebraMap_eq]
    simp [h1]
  | add p q hp hq =>
    rw [map_add, hp, hq]
    simp [map_add, mul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
    rw [Derivation.leibniz, hp]
    simp only [map_mul, Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, Pi.single_apply]
    simp [Finset.mul_sum, mul_comm, mul_left_comm]

/-- The word of letters `B 0` (`α 0` times), …, as in OAI `TaylorRectangular.derivativeWord`. -/
def derivativeWord : (k : ℕ) → (Fin k → ι) → (Fin k →₀ ℕ) → List ι
  | 0, _, _ => []
  | k+1, B, α => derivativeWord k (fun i => B i.succ) α.tail ++ List.replicate (α 0) (B 0)

theorem derivWord_append
    (D : ι → Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ))
    (u v : List ι) (p : MvPolynomial (Fin n) ℂ) :
    derivWord D (u ++ v) p = derivWord D u (derivWord D v p) := by
  simp only [derivWord, List.foldr_append]

theorem derivWord_replicate
    (D : ι → Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ))
    (i : ι) (m : ℕ) (p : MvPolynomial (Fin n) ℂ) :
    derivWord D (List.replicate m i) p = iter (ratDeriv (D i)) m p := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [iter_succ, ← ih]
    rfl

theorem mixedIter_eq_derivWord (k : ℕ)
    (D : ι → Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ))
    (B : Fin k → ι) (α : Fin k →₀ ℕ) (p : MvPolynomial (Fin n) ℂ) :
    mixedIter k (fun i => ratDeriv (D (B i))) α p = derivWord D (derivativeWord k B α) p := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    simp only [mixedIter, LinearMap.comp_apply, derivativeWord, derivWord_append,
      derivWord_replicate]
    exact ih (fun i => B i.succ) α.tail _

theorem derivativeWord_cost (k : ℕ) (B : Fin k → ι) (α : Fin k →₀ ℕ) (cost : ι → ℝ) :
    ((derivativeWord k B α).map cost).sum = ∑ i, (α i : ℝ) * cost (B i) := by
  induction k with
  | zero => simp [derivativeWord]
  | succ k ih =>
    simp only [derivativeWord, List.map_append, List.sum_append, List.map_replicate,
      List.sum_replicate]
    rw [ih (fun i => B i.succ) α.tail, Fin.sum_univ_succ]
    simp only [Finsupp.tail_apply, nsmul_eq_mul]
    ring

theorem derivativeWord_cost_le (k : ℕ) (B : Fin k → ι) (α : Fin k →₀ ℕ) (cost : ι → ℝ)
    (nn : Fin k → ℕ) (δ : ℝ) (hcost : ∀ i, 0 ≤ cost i) (hα : ∀ i, α i < nn i)
    (hn : ∑ i, ((nn i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ) :
    ((derivativeWord k B α).map cost).sum ≤ δ := by
  rw [derivativeWord_cost]
  refine le_trans ?_ hn
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (hcost _)
  exact_mod_cast (by have := hα i; omega : α i ≤ nn i - 1)

/-- The residue Taylor map of `ℂ[X]` along the derivations `D (B j)`, with values in the residue
field at `Q`. -/
def taylorMap0 (Q : Ideal (MvPolynomial (Fin n) ℂ)) [Q.IsPrime]
    (D : ι → Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ))
    {k : ℕ} (B : Fin k → ι) :
    MvPolynomial (Fin n) ℂ →+* MvPowerSeries (Fin k) Q.ResidueField :=
  residueTaylorFin k (fun j => ratDeriv (D (B j))) (primeResidueMap Q).toRingHom

theorem taylorMap0_constant (Q : Ideal (MvPolynomial (Fin n) ℂ)) [Q.IsPrime]
    (D : ι → Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ))
    {k : ℕ} (B : Fin k → ι) (p : MvPolynomial (Fin n) ℂ) :
    MvPowerSeries.constantCoeff (taylorMap0 Q D B p) =
      algebraMap (Localization.AtPrime Q) Q.ResidueField
        (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime Q) p) := by
  unfold taylorMap0
  rw [constantCoeff_residueTaylorFin]
  exact (IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) ℂ) (Localization.AtPrime Q)
    Q.ResidueField p).symm

theorem taylorMap0_firstCoeff (Q : Ideal (MvPolynomial (Fin n) ℂ)) [Q.IsPrime]
    (D : ι → Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ))
    {k : ℕ} (B : Fin k → ι) (j : Fin k) (p : MvPolynomial (Fin n) ℂ) :
    MvPowerSeries.coeff (Finsupp.single j 1) (taylorMap0 Q D B p) =
      ∑ i, primeResidueMap Q (D (B j) (MvPolynomial.X i)) *
        primeResidueMap Q (MvPolynomial.pderiv i p) := by
  unfold taylorMap0
  rw [coeff_single_residueTaylorFin]
  change primeResidueMap Q (D (B j) p) = _
  rw [derivation_apply_eq_sum (D (B j)) p, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]

theorem taylorMap0_mem_rectangular (Q : Ideal (MvPolynomial (Fin n) ℂ)) [Q.IsPrime]
    (D : ι → Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ))
    {k : ℕ} (B : Fin k → ι) (cost : ι → ℝ) (nn : Fin k → ℕ) (δ : ℝ)
    (hcost : ∀ i, 0 ≤ cost i) (hbudget : ∑ i, ((nn i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ)
    (p : MvPolynomial (Fin n) ℂ)
    (hp : ∀ word : List ι, (word.map cost).sum ≤ δ → derivWord D word p ∈ Q) :
    taylorMap0 Q D B p ∈ rectangularIdeal (K := Q.ResidueField) nn := by
  intro α hα
  unfold taylorMap0
  rw [coeff_residueTaylorFin]
  have hz : (primeResidueMap Q).toRingHom
      (mixedIter k (fun j => ratDeriv (D (B j))) α p) = 0 := by
    rw [mixedIter_eq_derivWord]
    exact Ideal.algebraMap_residueField_eq_zero.mpr
      (hp _ (derivativeWord_cost_le k B α cost nn δ hcost hα hbudget))
  rw [hz]
  simp

/-- CM Lemma `lem:p1-generic-taylor-lower` for a general family of derivations: the local length of
`ℂ[X]/I` at the prime `Q` is at least `∏ nn i` whenever the iterated derivatives of cost at most
`δ` of every element of `I` lie in `Q`, the chosen letters `B j` have independent normal
residues, and `∑ (nn i - 1) cost (B i) ≤ δ`. -/
theorem prime_rectangular_length_lower {k : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) ℂ)) [Q.IsPrime]
    (D : ι → Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ))
    (B : Fin k → ι)
    (hB : LinearIndependent Q.ResidueField fun j =>
      (polynomialTangent (primeResidueMap Q) Q).mkQ
        (fun i => primeResidueMap Q (D (B j) (MvPolynomial.X i))))
    (I : Ideal (MvPolynomial (Fin n) ℂ)) (cost : ι → ℝ) (nn : Fin k → ℕ) (δ : ℝ)
    (hn : ∀ i, 2 ≤ nn i) (hcost : ∀ i, 0 ≤ cost i)
    (hbudget : ∑ i, ((nn i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ)
    (hvanish : ∀ p ∈ I, ∀ word : List ι, (word.map cost).sum ≤ δ → derivWord D word p ∈ Q) :
    (∏ i, nn i : ℕ) ≤
      Module.length (Localization.AtPrime Q)
        (Localization.AtPrime Q ⧸ I.map
          (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime Q))) := by
  have hconst0 := taylorMap0_constant Q D B
  let tau := localizedTaylorMap Q.primeCompl (taylorMap0 Q D B)
    (algebraMap (Localization.AtPrime Q) Q.ResidueField) hconst0
  have hzero : ∀ x, MvPowerSeries.constantCoeff (tau x) =
      algebraMap (Localization.AtPrime Q) Q.ResidueField x :=
    fun x => RingHom.congr_fun (localizedTaylorMap_constant Q.primeCompl (taylorMap0 Q D B)
      (algebraMap (Localization.AtPrime Q) Q.ResidueField) hconst0) x
  have hfirst : ∀ j x, MvPowerSeries.coeff (Finsupp.single j 1) (tau x) =
      primeLocalDirectional Q
        (fun i => primeResidueMap Q (D (B j) (MvPolynomial.X i))) x :=
    fun j x => prime_localizedTaylor_firstCoefficient Q (taylorMap0 Q D B) hconst0
      (fun j i => primeResidueMap Q (D (B j) (MvPolynomial.X i)))
      (taylorMap0_firstCoeff Q D B) j x
  have hCot := prime_rectangular_mapCotangent_surjective Q tau hzero
    (fun j i => primeResidueMap Q (D (B j) (MvPolynomial.X i))) hB hfirst nn hn
  have hP : IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≤
      RingHom.ker (algebraMap (Localization.AtPrime Q) Q.ResidueField) := by
    rw [show RingHom.ker (algebraMap (Localization.AtPrime Q) Q.ResidueField) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) from IsLocalRing.ker_residue]
  refine rectangularTaylor_length_lower (K := Q.ResidueField) nn (rectangularPositive nn hn) tau
    (algebraMap (Localization.AtPrime Q) Q.ResidueField) IsLocalRing.residue_surjective hzero
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime Q))) hP hCot ?_
  exact localizedTaylorMap_ideal_le Q.primeCompl (taylorMap0 Q D B)
    (algebraMap (Localization.AtPrime Q) Q.ResidueField) hconst0 nn I
    (fun p hp d hd => taylorMap0_mem_rectangular Q D B cost nn δ hcost hbudget p
      (hvanish p hp) d hd)

end

end CatalanCore.Elliptic.EPA.Local
