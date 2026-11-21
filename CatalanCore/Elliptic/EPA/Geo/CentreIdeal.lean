module

public import CatalanCore.Elliptic.EPA.Geo.Compactification
public import OAI.NumberTheory.PiExponent.Jets.CompactJetIdealCoherent
public import OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal
public import OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout

/-!
# The centre ideal of `thm:epa` (row E09.10b, part 1)

Labels refer to `D2-DESIGN-2026-11-20.md` (§2 P1, §5 E09.10b) and to the OpenAI/Apache-2.0 files
`Ampleness/AdmissibleBlowupGeometry.lean` (lines 64--160), `Jets/CompactLogJetIdeal.lean`,
`Jets/CompactJetPolynomial.lean` (templates; the `inverseTriangularMap` machinery is not needed here
because the generators are explicit).

For a centre `c₀ ∈ ℂ^m` put
`I_{c₀} = (t^a, u^a, f, (Z_i − c₀_i − L_{<T₀}(t))^{b_i} : 1 ≤ i ≤ m) ⊂ ℂ[u,t,Z]`
(`centreGens`), and for `K` centres `J = ∏_j I_{c_j}` (`centreIdealAff`). Its extension to the
compactification is `centreIdeal`.

* `radical_centre`: `√I_{c₀}` is the maximal ideal of the point `(0, 0, c₀)` (design P1).
* `centreIdeal_restrict`, `centreIdeal_support`, `centreIdeal_support_ne_top`,
  `centreIdeal_isFinitePresentation`.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

namespace Geo

open CatalanCore.Elliptic
open AlgebraicGeometry CategoryTheory TopologicalSpace
open OAI.PiExponent
open OAI.PiExponentSeshadri

variable {m K : ℕ} {W : Weights m} {σ : ℚ} {ch : OriginChart}

/-! ### Points and the truncation of `L` -/

/-- The point `(u, t, Z) = (0, 0, c)` of `𝔸^{m+2}`. -/
noncomputable def cenPt (c : Fin m → ℂ) : Fin (m + 2) → ℂ :=
  Fin.cases (motive := fun _ => ℂ) 0 (Fin.cases (motive := fun _ => ℂ) 0 c)

@[simp] theorem cenPt_zero (c : Fin m → ℂ) : cenPt c 0 = 0 := rfl

@[simp] theorem cenPt_succ_zero (c : Fin m → ℂ) : cenPt c (Fin.succ 0) = 0 := rfl

@[simp] theorem cenPt_succ_succ (c : Fin m → ℂ) (i : Fin m) : cenPt c i.succ.succ = c i := rfl

theorem cenPt_one (c : Fin m → ℂ) : cenPt c 1 = 0 := by
  rw [one_eq_succ_zero]; rfl

/-- The truncation `L_{<T₀}(t) = Σ_{k<T₀} [T^k]L · t^k ∈ ℂ[t]`, as an element of the ambient ring. -/
noncomputable def truncL (s : OriginSeries ch) (T₀ : ℕ) : AmbRing m :=
  ∑ k ∈ Finset.range T₀, MvPolynomial.C (((PowerSeries.coeff k s.L : ℚ) : ℂ)) * tV ^ k

theorem coeff_zero_L (s : OriginSeries ch) : PowerSeries.coeff 0 s.L = 0 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact s.L_zero

theorem aeval_cenPt_truncL (s : OriginSeries ch) (T₀ : ℕ) (c : Fin m → ℂ) :
    MvPolynomial.aeval (cenPt c) (truncL s T₀) = 0 := by
  unfold truncL
  rw [map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases k with _ | k
  · simp [coeff_zero_L s, s.L_zero]
  · simp [tV, cenPt_one]

theorem truncL_mem_span_tV (s : OriginSeries ch) (T₀ : ℕ) :
    truncL (m := m) s T₀ ∈ Ideal.span {(tV : AmbRing m)} := by
  unfold truncL
  refine Ideal.sum_mem _ fun k _ => ?_
  rcases k with _ | k
  · simp [coeff_zero_L s, s.L_zero]
  · exact Ideal.mul_mem_left _ _ (by
      rw [pow_succ']
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))

theorem aeval_cenPt_Fc (ch : OriginChart) (c : Fin m → ℂ) :
    MvPolynomial.aeval (cenPt c) (Polynomial.aeval (uV : AmbRing m) (Fc ch)) = 0 := by
  rw [← Polynomial.aeval_algHom_apply]
  have hu : MvPolynomial.aeval (cenPt c) (uV : AmbRing m) = 0 := by simp [uV]
  rw [hu, Polynomial.coe_aeval_eq_eval]
  simp [Fc, OriginChart.F, Polynomial.eval_map]

theorem aeval_cenPt_relation (ch : OriginChart) (c : Fin m → ℂ) :
    MvPolynomial.aeval (cenPt c) (relation (m := m) ch) = 0 := by
  unfold relation
  rw [map_sub, aeval_cenPt_Fc, map_pow]
  simp [tV, cenPt_one]

/-! ### The centre ideal in the affine chart -/

/-- Generators of the centre ideal `I_{c₀}` (design E09.10b, CM `origin-fixed-ideal` with `f`). -/
noncomputable def centreGens (sc : EpaScale W σ) (s : OriginSeries ch) (c₀ : Fin m → ℂ) : Set (AmbRing m) :=
  {tV ^ sc.a, uV ^ sc.a, relation ch} ∪
    Set.range fun i : Fin m => (zV i - MvPolynomial.C (c₀ i) - truncL s sc.T₀) ^ sc.b i

/-- `I_{c₀}`. -/
noncomputable def centreIdealPt (sc : EpaScale W σ) (s : OriginSeries ch) (c₀ : Fin m → ℂ) : Ideal (AmbRing m) :=
  Ideal.span (centreGens sc s c₀)

/-- `J = ∏_j I_{c_j}`. -/
noncomputable def centreIdealAff (sc : EpaScale W σ) (s : OriginSeries ch) (c : Fin K → Fin m → ℂ) :
    Ideal (AmbRing m) :=
  ∏ j, centreIdealPt sc s (c j)

theorem tpow_mem_centreIdealPt (sc : EpaScale W σ) (s : OriginSeries ch) (c₀ : Fin m → ℂ) :
    (tV : AmbRing m) ^ sc.a ∈ centreIdealPt sc s c₀ :=
  Ideal.subset_span (Or.inl (by simp))

theorem upow_mem_centreIdealPt (sc : EpaScale W σ) (s : OriginSeries ch) (c₀ : Fin m → ℂ) :
    (uV : AmbRing m) ^ sc.a ∈ centreIdealPt sc s c₀ :=
  Ideal.subset_span (Or.inl (by simp))

theorem relation_mem_centreIdealPt (sc : EpaScale W σ) (s : OriginSeries ch) (c₀ : Fin m → ℂ) :
    (relation ch : AmbRing m) ∈ centreIdealPt sc s c₀ :=
  Ideal.subset_span (Or.inl (by simp))

theorem zpow_mem_centreIdealPt (sc : EpaScale W σ) (s : OriginSeries ch) (c₀ : Fin m → ℂ)
    (i : Fin m) :
    (zV i - MvPolynomial.C (c₀ i) - truncL s sc.T₀) ^ sc.b i ∈ centreIdealPt sc s c₀ :=
  Ideal.subset_span (Or.inr ⟨i, rfl⟩)

/-- Design P1: the radical of `I_{c₀}` is the maximal ideal of the point `(0, 0, c₀)`. -/
theorem radical_centreIdealPt (sc : EpaScale W σ) (s : OriginSeries ch) (c₀ : Fin m → ℂ) :
    (centreIdealPt sc s c₀).radical = WeightedBezout.pointIdeal (cenPt c₀) := by
  apply le_antisymm
  · apply (Ideal.IsPrime.radical_le_iff
      (inferInstance : (WeightedBezout.pointIdeal (cenPt c₀)).IsPrime)).mpr
    apply Ideal.span_le.mpr
    rintro g (hg | ⟨i, rfl⟩)
    · rcases hg with rfl | rfl | rfl
      · change MvPolynomial.aeval (cenPt c₀) (tV ^ sc.a) = 0
        simp [tV, cenPt_one, sc.a_pos.ne']
      · change MvPolynomial.aeval (cenPt c₀) (uV ^ sc.a) = 0
        simp [uV, sc.a_pos.ne']
      · exact aeval_cenPt_relation ch c₀
    · change MvPolynomial.aeval (cenPt c₀) ((zV i - MvPolynomial.C (c₀ i) - truncL s sc.T₀) ^
        sc.b i) = 0
      rw [map_pow, map_sub, map_sub, aeval_cenPt_truncL]
      simp [zV, (sc.b_pos i).ne']
  · rw [WeightedBezout.pointIdeal_eq_span]
    apply Ideal.span_le.mpr
    have ht : (tV : AmbRing m) ∈ (centreIdealPt sc s c₀).radical :=
      ⟨sc.a, tpow_mem_centreIdealPt sc s c₀⟩
    have hu : (uV : AmbRing m) ∈ (centreIdealPt sc s c₀).radical :=
      ⟨sc.a, upow_mem_centreIdealPt sc s c₀⟩
    rintro g ⟨j, rfl⟩
    induction j using Fin.cases with
    | zero => simpa [uV] using hu
    | succ j =>
      induction j using Fin.cases with
      | zero => simpa [tV, cenPt_one] using ht
      | succ i =>
        have h1 : (zV i - MvPolynomial.C (c₀ i) - truncL s sc.T₀ : AmbRing m) ∈
            (centreIdealPt sc s c₀).radical := ⟨sc.b i, zpow_mem_centreIdealPt sc s c₀ i⟩
        have h2 : (truncL s sc.T₀ : AmbRing m) ∈ (centreIdealPt sc s c₀).radical := by
          have := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ht)
          exact this (truncL_mem_span_tV s sc.T₀)
        have h3 := Ideal.add_mem _ h1 h2
        simpa [zV] using h3

/-! ### The points -/

/-- The maximal ideal of `(0, 0, c₀)` as a point of `Spec ℂ[u,t,Z]`. -/
noncomputable def cenPrime (c₀ : Fin m → ℂ) : ambSpace m :=
  ⟨WeightedBezout.pointIdeal (cenPt c₀), inferInstance⟩

/-- The section `Spec ℂ → Spec ℂ[u,t,Z]` at `(0, 0, c₀)`. -/
noncomputable def ambPoint (c₀ : Fin m → ℂ) : baseC ⟶ ambSpace m :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (cenPt c₀)).toRingHom)

theorem ambPoint_section (c₀ : Fin m → ℂ) : ambPoint c₀ ≫ ambStructureMap m = 𝟙 baseC := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap ℂ (AmbRing m)) ≫
      CommRingCat.ofHom (MvPolynomial.aeval (cenPt c₀)).toRingHom =
      𝟙 (CommRingCat.of ℂ) := by
    ext a
    simp
  rw [h, Spec.map_id]

theorem range_ambPoint (c₀ : Fin m → ℂ) : Set.range (ambPoint c₀) = {cenPrime c₀} := by
  change Set.range (PrimeSpectrum.comap (MvPolynomial.aeval (cenPt c₀)).toRingHom) = _
  rw [range_comap_of_surjective _ _ (by
    intro a
    exact ⟨MvPolynomial.C a, by simp⟩)]
  exact PrimeSpectrum.zeroLocus_eq_singleton (WeightedBezout.pointIdeal (cenPt c₀))

/-- The zero locus of `J` is the set of centre points. -/
theorem zeroLocus_centreIdealPt (sc : EpaScale W σ) (s : OriginSeries ch) (c₀ : Fin m → ℂ) :
    PrimeSpectrum.zeroLocus (centreIdealPt sc s c₀ : Set (AmbRing m)) = {cenPrime c₀} := by
  rw [← PrimeSpectrum.zeroLocus_radical, radical_centreIdealPt]
  exact PrimeSpectrum.zeroLocus_eq_singleton _

theorem zeroLocus_centreIdealAff (sc : EpaScale W σ) (s : OriginSeries ch)
    (c : Fin K → Fin m → ℂ) :
    PrimeSpectrum.zeroLocus (centreIdealAff sc s c : Set (AmbRing m)) =
      Set.range (fun j => cenPrime (c j)) := by
  classical
  have key : ∀ t : Finset (Fin K),
      PrimeSpectrum.zeroLocus ((∏ j ∈ t, centreIdealPt sc s (c j) : Ideal (AmbRing m)) :
        Set (AmbRing m)) = (fun j => cenPrime (c j)) '' (t : Set (Fin K)) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp; rfl
    | @insert j t hj ih =>
      rw [Finset.prod_insert hj, PrimeSpectrum.zeroLocus_mul,
        zeroLocus_centreIdealPt, ih]
      simp
      exact Set.singleton_union
  simpa [centreIdealAff] using key Finset.univ

/-! ### The ideal sheaf on `P` -/

/-- The centre ideal sheaf on the compactification: the extension of `J` along the chart. -/
noncomputable def centreIdeal (sc : EpaScale W σ) (s : OriginSeries ch) (c : Fin K → Fin m → ℂ) :
    (ambX sc).IdealSheafData :=
  CompactJetIdeal.extend (IdealPullback.specIdeal (centreIdealAff sc s c)) (ambChart sc)

theorem centreIdeal_restrict (sc : EpaScale W σ) (s : OriginSeries ch) (c : Fin K → Fin m → ℂ) :
    (centreIdeal sc s c).comap (ambChart sc) = IdealPullback.specIdeal (centreIdealAff sc s c) :=
  CompactJetIdeal.restrict_extend _ _

theorem support_specIdeal' {R : Type} [CommRing R] (I : Ideal R) :
    ((IdealPullback.specIdeal I).support : Set (Spec (CommRingCat.of R))) =
      PrimeSpectrum.zeroLocus (I : Set R) := by
  rw [IdealPullback.specIdeal, Scheme.IdealSheafData.coe_support_ofIdealTop, Spec_zeroLocus,
    ← Ideal.coe_comap]
  rw [Ideal.comap_map_of_bijective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)]

theorem support_centreIdealAff (sc : EpaScale W σ) (s : OriginSeries ch) (c : Fin K → Fin m → ℂ) :
    ((IdealPullback.specIdeal (centreIdealAff sc s c)).support : Set (ambSpace m)) =
      ⋃ j, Set.range (ambPoint (c j)) := by
  rw [support_specIdeal', zeroLocus_centreIdealAff]
  simp only [range_ambPoint]
  ext p
  constructor
  · rintro ⟨a, rfl⟩
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_singleton _⟩
  · intro hp
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hp
    exact ⟨a, (Set.mem_singleton_iff.mp ha).symm⟩

/-- Design P1: the support of the centre ideal is the finite set of points `(0, 0, c_j)`. -/
theorem centreIdeal_support (sc : EpaScale W σ) (s : OriginSeries ch) (c : Fin K → Fin m → ℂ) :
    ((centreIdeal sc s c).support : Set (ambX sc)) =
      ⋃ j, Set.range (ambPoint (c j) ≫ ambChart sc) := by
  rw [centreIdeal, CompactJetIdeal.support_extend (IdealPullback.specIdeal (centreIdealAff sc s c))
    (ambChart sc) (ambProj sc) (fun a => ambPoint (c a)) (fun a => by
      rw [Category.assoc, ambChart_over, ambPoint_section]) (support_centreIdealAff sc s c),
    support_centreIdealAff, Set.image_iUnion]
  congr 1
  funext a
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

theorem centreIdeal_support_finite (sc : EpaScale W σ) (s : OriginSeries ch)
    (c : Fin K → Fin m → ℂ) : ((centreIdeal sc s c).support : Set (ambX sc)).Finite := by
  rw [centreIdeal_support]
  exact Set.finite_iUnion (fun _ => Set.finite_range _)

theorem centreIdeal_support_subset_chart (sc : EpaScale W σ) (s : OriginSeries ch)
    (c : Fin K → Fin m → ℂ) :
    ((centreIdeal sc s c).support : Set (ambX sc)) ⊆ (ambChart sc).opensRange := by
  rw [centreIdeal_support]
  intro x hx
  obtain ⟨j, z, rfl⟩ := Set.mem_iUnion.mp hx
  exact ⟨ambPoint (c j) z, rfl⟩

/-- The point `(u, t, Z) = (1, 0, 0)`, which is not a centre. -/
noncomputable def offPoint (m : ℕ) : ambSpace m :=
  ⟨WeightedBezout.pointIdeal (Fin.cases (motive := fun _ => ℂ) 1
    (fun _ => (0 : ℂ)) : Fin (m + 2) → ℂ), inferInstance⟩

theorem offPoint_ne_cenPrime (c₀ : Fin m → ℂ) : offPoint m ≠ cenPrime c₀ := by
  intro h
  have hx : (MvPolynomial.X 0 - MvPolynomial.C 1 : AmbRing m) ∈ (offPoint m).asIdeal := by
    change MvPolynomial.aeval (Fin.cases (motive := fun _ => ℂ) 1 (fun _ => (0 : ℂ)) :
      Fin (m + 2) → ℂ) (MvPolynomial.X 0 - MvPolynomial.C 1) = 0
    simp
  rw [h] at hx
  change MvPolynomial.aeval (cenPt c₀) (MvPolynomial.X 0 - MvPolynomial.C 1) = 0 at hx
  simp at hx

theorem offPoint_avoids (sc : EpaScale W σ) (s : OriginSeries ch) (c : Fin K → Fin m → ℂ) :
    ambChart sc (offPoint m) ∉ (centreIdeal sc s c).support := by
  change ambChart sc (offPoint m) ∉ ((centreIdeal sc s c).support : Set (ambX sc))
  rw [centreIdeal_support]
  intro h
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
  obtain ⟨z, hz⟩ := hj
  have he : ambPoint (c j) z = offPoint m := (ambChart sc).isOpenEmbedding.injective hz
  have hc : ambPoint (c j) z = cenPrime (c j) := by
    have hz' : ambPoint (c j) z ∈ Set.range (ambPoint (c j)) := ⟨z, rfl⟩
    rw [range_ambPoint] at hz'
    exact hz'
  exact offPoint_ne_cenPrime (c j) (he.symm.trans hc)

/-- The support is not everything (the centres are finitely many points). -/
theorem centreIdeal_support_ne_top (sc : EpaScale W σ) (s : OriginSeries ch)
    (c : Fin K → Fin m → ℂ) : (centreIdeal sc s c).support ≠ ⊤ := by
  intro h
  exact offPoint_avoids sc s c (by rw [h]; trivial)

theorem centreIdeal_isFinitePresentation (sc : EpaScale W σ) (s : OriginSeries ch)
    (c : Fin K → Fin m → ℂ) :
    (IdealModule.closedModule (centreIdeal sc s c)).IsFinitePresentation :=
  CompactJetIdeal.extend_isFinitePresentation _ _

end Geo

end CatalanCore.Elliptic.EPA
