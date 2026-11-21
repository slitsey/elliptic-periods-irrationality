module

public import OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezoutBound

/-!
# Fixed-equation weighted point bound (row E09.4a, point level)

Labels refer to `D2-DESIGN-2026-11-20.md` §5 E09.4a and to CM Lemma `lem:p1-weighted-point-fixed`
(`cm-2610.31112-nolean.tex`, l.1149–1217).

CM bounds the local length of `E[Y]/J` at a point `a` that is minimal over `J`, retaining one
fixed nonzero equation `h ∈ J` as the first parameter:
`length ≤ d₀ M^{r-1} / ∏ ρ_i` when `deg_ρ h ≤ d₀` and `deg_ρ f_j ≤ M` for all generators.

The OAI chain `weighted_prime_length_bound` ← `rational_pointLength_bound` ←
`pointLength_mul_le_of_substituted_degree` ← `localIsolatedBezout` ←
`affine_local_regular_list_bezout` bounds every parameter by the same degree `D`. Here:

* `affine_local_regular_list_bezout_deg`: the isolated-point Bézout bound with a degree
  `ds i` for the `i`-th parameter. The proof is that of OAI `affine_local_regular_list_bezout`
  (`LocalAlgebra/AffineLocalRegularBezout.lean`), which already proves the per-element product
  `∏ degreeAt degrees i` and relaxes it to `D ^ length` only at its last line.
* `exists_prefixed_constant_regular_parameters`, `polynomialLocal_exists_prefixed_regular_parameters`:
  the regular parameters of OAI `polynomialLocal_exists_degree_bounded_regular_parameters`
  (`LocalAlgebra/RegularParameterSelection.lean`) chosen as constant combinations of the
  generators, but starting from a prescribed regular head `g₀`.
* `pointLength_mul_le_fixed` (natural weights), `rational_pointLength_fixed_bound` (rational
  weights): CM's lemma.

The prime-local version (CM Thm `thm:p1-generic-prime-upper`) is in `FixedBezoutPrime.lean`.

The proofs follow the Apache-2.0 library `openai/math` (commit fd4aeeb2), Copyright OpenAI, whose
lemmas `affine_local_regular_list_bezout`, `exists_constant_regular_parameters_of_no_maximal_associated`,
`polynomialLocal_exists_degree_bounded_regular_parameters`, `pointLength_mul_le_of_substituted_degree`
and `rational_pointLength_bound` are adapted with the head prescribed.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA.Local

open scoped BigOperators
open OAI OAI.PiExponent OAI.PiExponent.WeightedBezout
open OAI.PiExponentJets.W22 OAI.PiExponentJets.W64
open OAI.PiExponentSiegel.W17.ConeLocalLength OAI.PiExponentSiegel.W58

open scoped Classical in
/-- OAI `affine_local_regular_list_bezout` with a degree `ds i` for the `i`-th parameter:
the length of the localized quotient at an isolated point is at most `∏ i, ds i`. -/
theorem affine_local_regular_list_bezout_deg
    {k : Type} [Field k] (n : ℕ)
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
    (gs : List (MvPolynomial (Fin n) k)) (ds : ℕ → ℕ)
    (hdegree : ∀ (i : ℕ) (hi : i < gs.length), (gs[i]'hi).totalDegree ≤ ds i)
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime P)
      (gs.map (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))))
    (hlen : gs.length ≤ n) (hP : P ∈ (Ideal.ofList gs).minimalPrimes) :
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ (Ideal.ofList gs).map
        (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))) ≤
      ((∏ i ∈ Finset.range gs.length, ds i : ℕ) : ℕ∞) := by
  let hs := gs.map homogenize
  let degrees : Fin hs.length → ℕ := fun i =>
    (gs[i.val]'(by simpa only [hs,List.length_map] using i.isLt)).totalDegree
  have hhom : ∀ i : Fin hs.length, hs[i].IsHomogeneous (degrees i) := by
    intro i
    simpa only [hs, List.getElem_map, Fin.getElem_fin, degrees] using
      homogenize_isHomogeneous (gs[i.val]'(by simpa only [hs,List.length_map] using i.isLt))
  have hconeReg := homogenized_list_regular_at_cone k (Fin n) P gs hreg
  have hget : P ∈ (Ideal.span (Set.range gs.get)).minimalPrimes := by
    simpa only [span_range_list_get] using hP
  have hconeMin := conePrime_minimal_over_homogenized k (Fin n) P gs.get hget
  rw [span_range_map_list_get] at hconeMin
  have hconeLen : hs.length < Fintype.card (Option (Fin n)) := by
    simp only [hs,List.length_map,Fintype.card_option,Fintype.card_fin]
    omega
  have hbound := homogeneous_local_regular_bezout (conePrime k (Fin n) P) none
    (homogenizing_coordinate_not_mem_conePrime k (Fin n) P)
    hs degrees hhom hconeReg hconeLen hconeMin
  have hfinite := finiteLength_localized_minimal_quotient
    (Ideal.span (Set.range gs.get)) P hget
  have hlength := homogenized_cone_local_length_eq k (Fin n) P gs.get hfinite
  rw [span_range_list_get, span_range_map_list_get] at hlength
  have hl : hs.length = gs.length := by simp only [hs, List.length_map]
  have hprod : (∏ i ∈ Finset.range hs.length, degreeAt degrees i) ≤
      ∏ i ∈ Finset.range gs.length, ds i := by
    calc
      (∏ i ∈ Finset.range hs.length, degreeAt degrees i)
          ≤ ∏ i ∈ Finset.range hs.length, ds i := by
        apply Finset.prod_le_prod'
        intro i hi
        have hi' : i < hs.length := Finset.mem_range.mp hi
        have hi'' : i < gs.length := by omega
        simp only [degreeAt, dif_pos hi', degrees]
        exact hdegree i hi''
      _ = ∏ i ∈ Finset.range gs.length, ds i := by rw [hl]
  calc
    _ = Module.length (Localization.AtPrime (conePrime k (Fin n) P))
      (Localization.AtPrime (conePrime k (Fin n) P) ⧸ (Ideal.ofList hs).map
        (algebraMap (MvPolynomial (Option (Fin n)) k)
          (Localization.AtPrime (conePrime k (Fin n) P)))) := hlength.symm
    _ ≤ ((∏ i ∈ Finset.range hs.length, degreeAt degrees i : ℕ) : ℕ∞) := hbound
    _ ≤ _ := by exact_mod_cast hprod

/-- OAI `exists_constant_regular_parameters_of_no_maximal_associated` with a prescribed regular
head `r₀`: the remaining `h - 1` parameters are constant combinations of the generators. -/
theorem exists_prefixed_constant_regular_parameters
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {k J : Type*} [Field k] [Infinite k] [Algebra k R]
    (generators : J → R)
    (hrad : (Ideal.span (Set.range generators)).radical = IsLocalRing.maximalIdeal R)
    (h : ℕ) (hdim : ringKrullDim R = h)
    (hnot : ∀ rs : List R, RingTheory.Sequence.IsRegular R rs → rs.length < h →
      ¬ IsAssociatedPrime (IsLocalRing.maximalIdeal R) (R ⧸ Ideal.ofList rs))
    (r₀ : R) (hr₀ : RingTheory.Sequence.IsRegular R [r₀]) (hh : 1 ≤ h) :
    ∃ cs : List (J →₀ k), cs.length + 1 = h ∧
      RingTheory.Sequence.IsRegular R
        (r₀ :: cs.map (Finsupp.linearCombination k generators)) ∧
      (Ideal.ofList (r₀ :: cs.map (Finsupp.linearCombination k generators))).radical =
        IsLocalRing.maximalIdeal R := by
  have build : ∀ t : ℕ, t + 1 ≤ h → ∃ cs : List (J →₀ k), cs.length = t ∧
      RingTheory.Sequence.IsRegular R
        (r₀ :: cs.map (Finsupp.linearCombination k generators)) := by
    intro t
    induction t with
    | zero =>
      intro _
      exact ⟨[], rfl, by simpa using hr₀⟩
    | succ t ih =>
      intro ht
      obtain ⟨cs, hlen, hreg⟩ := ih (by omega)
      have hshort : (r₀ :: cs.map (Finsupp.linearCombination k generators)).length < h := by
        simp only [List.length_cons, List.length_map, hlen]
        omega
      obtain ⟨c, _, hc⟩ := exists_constant_regular_extension (k := k) generators hrad _ hreg
        (hnot _ hreg hshort)
      refine ⟨cs ++ [c], by simp [hlen], ?_⟩
      simpa only [List.map_append, List.map_cons, List.map_nil, List.cons_append] using hc
  obtain ⟨cs, hlen, hreg⟩ := build (h - 1) (by omega)
  have hl : (r₀ :: cs.map (Finsupp.linearCombination k generators)).length = h := by
    simp only [List.length_cons, List.length_map, hlen]
    omega
  refine ⟨cs, by omega, hreg, regular_full_length_radical_eq_maximalIdeal _ hreg ?_⟩
  rw [hl]
  exact hdim

/-- The OAI polynomial-local parameter selection with a prescribed regular head `g₀ ∈ (f)`. -/
theorem polynomialLocal_exists_prefixed_regular_parameters
    {k : Type} [Field k] [Infinite k] (n : ℕ)
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
    {J : Type*} (f : J → MvPolynomial (Fin n) k) (d h : ℕ)
    (hdegree : ∀ j, (f j).totalDegree ≤ d) (hheight : P.height = (h : ℕ∞))
    (hrad : ((Ideal.span (Set.range f)).map
      (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (g₀ : MvPolynomial (Fin n) k) (hg₀ : g₀ ∈ Ideal.span (Set.range f))
    (hg₀reg : RingTheory.Sequence.IsRegular (Localization.AtPrime P)
      [algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P) g₀])
    (hh : 1 ≤ h) :
    ∃ gs : List (MvPolynomial (Fin n) k), gs.length + 1 = h ∧
      (∀ g ∈ gs, g.totalDegree ≤ d) ∧
      Ideal.ofList (g₀ :: gs) ≤ Ideal.span (Set.range f) ∧
      RingTheory.Sequence.IsRegular (Localization.AtPrime P)
        ((g₀ :: gs).map (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))) ∧
      ((Ideal.ofList (g₀ :: gs)).map
        (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))).radical =
          IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  let φ : MvPolynomial (Fin n) k →ₐ[k] Localization.AtPrime P :=
    IsScalarTower.toAlgHom k (MvPolynomial (Fin n) k) (Localization.AtPrime P)
  have hgen : (Ideal.span (Set.range (φ ∘ f))).radical =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    change (Ideal.span (Set.range
      (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P) ∘ f))).radical = _
    simpa only [Ideal.map_span, ← Set.range_comp] using hrad
  have hdim : ringKrullDim (Localization.AtPrime P) = h := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P), hheight]
    rfl
  have hnot : ∀ rs : List (Localization.AtPrime P),
      RingTheory.Sequence.IsRegular (Localization.AtPrime P) rs → rs.length < h →
      ¬ IsAssociatedPrime (IsLocalRing.maximalIdeal (Localization.AtPrime P))
        (Localization.AtPrime P ⧸ Ideal.ofList rs) := by
    intro rs hreg hshort
    apply polynomialLocal_regular_prefix_maximal_not_associated k n P rs hreg
    rw [hheight]
    exact_mod_cast hshort
  obtain ⟨cs, hlen, hreg, hmax⟩ := exists_prefixed_constant_regular_parameters (k := k)
    (φ ∘ f) hgen h hdim hnot
    (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P) g₀) hg₀reg hh
  have hmap : (cs.map (Finsupp.linearCombination k f)).map
      (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P)) =
      cs.map (Finsupp.linearCombination k (φ ∘ f)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro c _
    exact Finsupp.apply_linearCombination k φ.toLinearMap f c
  refine ⟨cs.map (Finsupp.linearCombination k f), by simpa only [List.length_map] using hlen,
    ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hg
    exact linearCombination_totalDegree_le f c hdegree
  · apply Ideal.span_le.mpr
    intro g hg
    rcases List.mem_cons.mp hg with hg0 | hg
    · rw [hg0]
      exact hg₀
    · obtain ⟨c, _, rfl⟩ := List.mem_map.mp hg
      exact linearCombination_mem_ideal f c _ (fun j => Ideal.subset_span (Set.mem_range_self j))
  · rw [List.map_cons, hmap]
    exact hreg
  · rw [Ideal.map_ofList, List.map_cons, hmap]
    exact hmax

/-- A nonzero element of a prime `P` is a regular element of the localization at `P`. -/
theorem isRegular_singleton_localization {k : Type} [Field k] (n : ℕ)
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime] (g : MvPolynomial (Fin n) k)
    (hg0 : g ≠ 0) (hgP : g ∈ P) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime P)
      [algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P) g] := by
  have hmax : algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P) g ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P g).mpr hgP
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P)) :=
    IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
  have hne : algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P) g ≠ 0 :=
    fun h0 => hg0 (hinj (by rw [h0, map_zero]))
  refine (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
    (M := Localization.AtPrime P) ?_).mpr ?_
  · intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact hmax
  · rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    exact (IsRegular.of_ne_zero hne).left

/-- The translated power substitution is injective. -/
theorem translatedPowerSubstitution_injective {k : Type*} [Field k] {n : ℕ}
    (w : Fin n → ℕ) (a : Fin n → k) (hw : ∀ i, 0 < w i) :
    Function.Injective (translatedPowerSubstitution w a) := by
  rw [translatedPowerSubstitution_factor]
  exact (OAI.PiExponent.PowerCover.powerSubstitution_injective (k := k) w hw).comp
    (translationEquiv a).injective

theorem prod_range_head (D₀ D : ℕ) (N : ℕ) :
    (∏ i ∈ Finset.range (N + 1), (fun i : ℕ => if i = 0 then D₀ else D) i) = D₀ * D ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ, ih]
    simp [pow_succ, mul_assoc]

/-- CM l.1149–1217 with natural weights `w`: the point length times `∏ w_i` is at most
`D₀ D^{n-1}`, where `D₀` bounds the substituted degree of the fixed equation `h` and `D` that of
the generators. -/
theorem pointLength_mul_le_fixed
    (k : Type) [Field k] [Infinite k] {n : ℕ} (hn : 1 ≤ n) {J : Type*}
    (f : J → MvPolynomial (Fin n) k) (a : Fin n → k)
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) (D₀ D : ℕ)
    (h : MvPolynomial (Fin n) k) (hh : h ∈ Ideal.span (Set.range f)) (hh0 : h ≠ 0)
    (hdeg₀ : (translatedPowerSubstitution w a h).totalDegree ≤ D₀)
    (hdegree : ∀ j, (translatedPowerSubstitution w a (f j)).totalDegree ≤ D)
    (hminimal : pointIdeal a ∈ (Ideal.span (Set.range f)).minimalPrimes) :
    pointLength a (Ideal.span (Set.range f)) * ((∏ i, w i : ℕ) : ℕ∞) ≤
      ((D₀ * D ^ (n - 1) : ℕ) : ℕ∞) := by
  classical
  have hmap : (Ideal.span (Set.range f)).map (translatedPowerSubstitution w a).toRingHom =
      Ideal.span (Set.range (fun j => translatedPowerSubstitution w a (f j))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hminimal0 := origin_minimalPrimes_map w a hw (Ideal.span (Set.range f)) hminimal
  rw [hmap] at hminimal0
  have hheight := PiExponentSiegelAux.W09.polynomialMaximal_height k n
    (pointIdeal (0 : Fin n → k))
  have hrad := localized_radical_eq_maximal_of_mem_minimalPrimes
    (Ideal.span (Set.range (fun j => translatedPowerSubstitution w a (f j))))
    (pointIdeal (0 : Fin n → k)) hminimal0
  have hσh : translatedPowerSubstitution w a h ∈
      Ideal.span (Set.range (fun j => translatedPowerSubstitution w a (f j))) := by
    have hm := Ideal.mem_map_of_mem (translatedPowerSubstitution w a).toRingHom hh
    rw [hmap] at hm
    exact hm
  have hσh0 : translatedPowerSubstitution w a h ≠ 0 := fun h0 =>
    hh0 (translatedPowerSubstitution_injective w a hw (by rw [h0, map_zero]))
  have hσhP : translatedPowerSubstitution w a h ∈ pointIdeal (0 : Fin n → k) :=
    hminimal0.1.2 hσh
  have hreg₀ := isRegular_singleton_localization n (pointIdeal (0 : Fin n → k))
    (translatedPowerSubstitution w a h) hσh0 hσhP
  obtain ⟨gs, hlen, hgsdeg, hgscont, hgsreg, hgsrad⟩ :=
    polynomialLocal_exists_prefixed_regular_parameters (k := k) n (pointIdeal (0 : Fin n → k))
      (fun j => translatedPowerSubstitution w a (f j)) D n hdegree hheight hrad
      (translatedPowerSubstitution w a h) hσh hreg₀ hn
  have hgsmin := mem_minimalPrimes_of_localized_radical
    (Ideal.ofList (translatedPowerSubstitution w a h :: gs)) (pointIdeal (0 : Fin n → k)) hgsrad
  have hdegAll : ∀ (i : ℕ) (hi : i < (translatedPowerSubstitution w a h :: gs).length),
      ((translatedPowerSubstitution w a h :: gs)[i]'hi).totalDegree ≤
        (fun i : ℕ => if i = 0 then D₀ else D) i := by
    intro i hi
    cases i with
    | zero => simpa using hdeg₀
    | succ i =>
      have hi' : i < gs.length := by simpa using hi
      have hmem := hgsdeg _ (List.getElem_mem hi')
      show (gs[i]'hi').totalDegree ≤ if i + 1 = 0 then D₀ else D
      rw [if_neg (Nat.succ_ne_zero i)]
      exact hmem
  have hselected := affine_local_regular_list_bezout_deg n (pointIdeal (0 : Fin n → k))
    (translatedPowerSubstitution w a h :: gs) (fun i : ℕ => if i = 0 then D₀ else D)
    hdegAll hgsreg (by simp only [List.length_cons]; omega) hgsmin
  have hgl : gs.length = n - 1 := by omega
  have hprodeq : (∏ i ∈ Finset.range (translatedPowerSubstitution w a h :: gs).length,
      (fun i : ℕ => if i = 0 then D₀ else D) i) = D₀ * D ^ (n - 1) := by
    have hl1 : (translatedPowerSubstitution w a h :: gs).length = (n - 1) + 1 := by
      simp only [List.length_cons]
      omega
    rw [hl1]
    exact prod_range_head D₀ D (n - 1)
  have hcast : (((∏ i ∈ Finset.range (translatedPowerSubstitution w a h :: gs).length,
      (fun i : ℕ => if i = 0 then D₀ else D) i : ℕ)) : ℕ∞) ≤ ((D₀ * D ^ (n - 1) : ℕ) : ℕ∞) := by
    exact_mod_cast hprodeq.le
  have hb := (ideal_quotient_length_le_of_bound (Ideal.map_mono hgscont) hselected).trans hcast
  have hb' : pointLength (0 : Fin n → k)
      ((Ideal.span (Set.range f)).map (translatedPowerSubstitution w a).toRingHom) ≤
      ((D₀ * D ^ (n - 1) : ℕ) : ℕ∞) := by
    rw [hmap]
    exact hb
  rw [pointLength_translatedPowerSubstitution a w hw (Ideal.span (Set.range f))] at hb'
  exact hb'

/-- CM Lemma `lem:p1-weighted-point-fixed` (l.1149): rational weights `ρ`, fixed nonzero equation
`h ∈ J` with `deg_ρ h ≤ d₀`, generators of `deg_ρ ≤ M`; the point `a` minimal over `J`;
`length ≤ d₀ M^{n-1} / ∏ ρ_i`. -/
theorem rational_pointLength_fixed_bound
    (k : Type) [Field k] [Infinite k] {n : ℕ} (hn : 1 ≤ n) {J : Type*}
    (f : J → MvPolynomial (Fin n) k) (a : Fin n → k)
    (h : MvPolynomial (Fin n) k) (hh : h ∈ Ideal.span (Set.range f)) (hh0 : h ≠ 0)
    (ρ : Fin n → ℚ) (hρ : ∀ i, 0 < ρ i) (d₀ M : ℝ) (hd₀ : 0 ≤ d₀) (hM : 0 ≤ M)
    (hdh : ∀ d ∈ h.support, (∑ i ∈ d.support, (d i : ℝ) * (ρ i : ℝ)) ≤ d₀)
    (hdegree : ∀ j, ∀ d ∈ (f j).support, (∑ i ∈ d.support, (d i : ℝ) * (ρ i : ℝ)) ≤ M)
    (hminimal : pointIdeal a ∈ (Ideal.span (Set.range f)).minimalPrimes) :
    ∃ L : ℕ, pointLength a (Ideal.span (Set.range f)) = (L : ℕ∞) ∧
      (L : ℝ) ≤ d₀ * M ^ (n - 1) / ∏ i, (ρ i : ℝ) := by
  classical
  obtain ⟨M₀, hM₀, w, hw, hweights⟩ := positive_rational_weights_common_denominator ρ hρ
  have hM₀R : (0 : ℝ) < M₀ := by exact_mod_cast hM₀
  have hscale : ∀ i, (w i : ℝ) = (M₀ : ℝ) * (ρ i : ℝ) := by
    intro i
    rw [hweights i]
    field_simp
  have hD₀nn : 0 ≤ (M₀ : ℝ) * d₀ := mul_nonneg hM₀R.le hd₀
  have hDnn : 0 ≤ (M₀ : ℝ) * M := mul_nonneg hM₀R.le hM
  have hdeg₀ : (translatedPowerSubstitution w a h).totalDegree ≤ ⌊(M₀ : ℝ) * d₀⌋₊ := by
    apply (Nat.le_floor_iff hD₀nn).mpr
    exact translatedPowerSubstitution_totalDegree_real w a (fun i => (ρ i : ℝ)) M₀ d₀
      hM₀R.le hD₀nn hscale h hdh
  have hdegD : ∀ j, (translatedPowerSubstitution w a (f j)).totalDegree ≤ ⌊(M₀ : ℝ) * M⌋₊ := by
    intro j
    apply (Nat.le_floor_iff hDnn).mpr
    exact translatedPowerSubstitution_totalDegree_real w a (fun i => (ρ i : ℝ)) M₀ M
      hM₀R.le hDnn hscale (f j) (hdegree j)
  have hbound := pointLength_mul_le_fixed k hn f a w hw ⌊(M₀ : ℝ) * d₀⌋₊ ⌊(M₀ : ℝ) * M⌋₊ h hh hh0
    hdeg₀ hdegD hminimal
  have hprod : 0 < ∏ i, w i := Finset.prod_pos (fun i _ => hw i)
  obtain ⟨L, hL, hLbound⟩ := finite_length_of_rank_bound hprod hbound
  refine ⟨L, hL, ?_⟩
  have hρp : 0 < ∏ i, (ρ i : ℝ) := Finset.prod_pos (fun i _ => by exact_mod_cast hρ i)
  have hwprod : (∏ i, (w i : ℝ)) = (M₀ : ℝ) ^ n * ∏ i, (ρ i : ℝ) := by
    simp_rw [hscale]
    rw [Finset.prod_mul_distrib]
    simp
  have hD₀le : ((⌊(M₀ : ℝ) * d₀⌋₊ : ℕ) : ℝ) ≤ (M₀ : ℝ) * d₀ := Nat.floor_le hD₀nn
  have hDle : ((⌊(M₀ : ℝ) * M⌋₊ : ℕ) : ℝ) ≤ (M₀ : ℝ) * M := Nat.floor_le hDnn
  have hcast : (L : ℝ) * ∏ i, (w i : ℝ) ≤
      ((⌊(M₀ : ℝ) * d₀⌋₊ : ℕ) : ℝ) * ((⌊(M₀ : ℝ) * M⌋₊ : ℕ) : ℝ) ^ (n - 1) := by
    exact_mod_cast hLbound
  have hmain : ((⌊(M₀ : ℝ) * d₀⌋₊ : ℕ) : ℝ) * ((⌊(M₀ : ℝ) * M⌋₊ : ℕ) : ℝ) ^ (n - 1) ≤
      (M₀ : ℝ) * d₀ * ((M₀ : ℝ) * M) ^ (n - 1) :=
    mul_le_mul hD₀le (pow_le_pow_left₀ (Nat.cast_nonneg _) hDle _) (by positivity) hD₀nn
  have hpow : (M₀ : ℝ) ^ n = (M₀ : ℝ) * (M₀ : ℝ) ^ (n - 1) := by
    calc (M₀ : ℝ) ^ n = (M₀ : ℝ) ^ ((n - 1) + 1) := by rw [Nat.sub_add_cancel hn]
      _ = _ := pow_succ' _ _
  rw [le_div_iff₀ hρp]
  have hMpos : 0 < (M₀ : ℝ) ^ n := pow_pos hM₀R n
  apply le_of_mul_le_mul_left _ hMpos
  calc (M₀ : ℝ) ^ n * ((L : ℝ) * ∏ i, (ρ i : ℝ)) = (L : ℝ) * ∏ i, (w i : ℝ) := by
        rw [hwprod]
        ring
    _ ≤ _ := hcast
    _ ≤ _ := hmain
    _ = (M₀ : ℝ) ^ n * (d₀ * M ^ (n - 1)) := by
        rw [hpow, mul_pow]
        ring

end CatalanCore.Elliptic.EPA.Local
