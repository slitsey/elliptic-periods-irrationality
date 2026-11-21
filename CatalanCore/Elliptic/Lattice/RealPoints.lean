module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Topology.Algebra.Order.Archimedean
public import Mathlib.GroupTheory.Archimedean
public import CatalanCore.Elliptic.Lattice.Discriminant

/-!
# Real points of a lattice (row E21)

If the lattice of `L : PeriodPair` contains a nonzero real number `ω`, then there are `Ω > 0` and
`Ω′` with `Im Ω′ > 0` such that `Λ ∩ ℝ = ℤ Ω`, `Λ = ℤ Ω + ℤ Ω′` and `ω = N Ω` with `N ≠ 0`.

Proof. The real points form a discrete subgroup of `ℝ`, hence `ℤ b` with `b ≠ 0`; put `Ω = |b|`.
Write `Ω = m ω₁ + n ω₂`. Since `Ω` is not a proper multiple in the lattice, `gcd(m, n) = 1`;
Bezout gives `Ω′ = p ω₁ + q ω₂` with `m q - n p = 1`, so `(Ω, Ω′)` is a `ℤ`-basis. `Ω′` is not real
(else `ω₁, ω₂` are both real, against `ω₁/ω₂ ∉ ℝ`); replace `Ω′` by `-Ω′` if needed.
-/

@[expose] public section

noncomputable section

namespace CatalanCore.Elliptic.Lattice

open PeriodPair

lemma span_pair_neg (a b : ℂ) :
    Submodule.span ℤ {a, -b} = Submodule.span ℤ ({a, b} : Set ℂ) := by
  ext x
  rw [Submodule.mem_span_pair, Submodule.mem_span_pair]
  constructor <;> rintro ⟨s, t, h⟩ <;> exact ⟨s, -t, by rw [← h]; simp⟩

/-- The lattice has no nonzero points in a small disc around `0`. -/
lemma exists_isolated (L : PeriodPair) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ L.lattice, ‖z‖ < ε → z = 0 := by
  have h1 : IsOpen ({0} : Set L.lattice) := isOpen_discrete _
  obtain ⟨t, ht, htz⟩ := isOpen_induced_iff.mp h1
  have h0t : (0 : ℂ) ∈ t := by
    have : (0 : L.lattice) ∈ Subtype.val ⁻¹' t := by rw [htz]; rfl
    simpa using this
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ht 0 h0t
  refine ⟨ε, hε, fun z hz hzε => ?_⟩
  have h2 : (⟨z, hz⟩ : L.lattice) ∈ Subtype.val ⁻¹' t := hball (by simpa using hzε)
  rw [htz] at h2
  have h3 := congrArg Subtype.val (Set.mem_singleton_iff.mp h2)
  simpa using h3

/-- The real points of the lattice are `ℤ Ω` for a unique `Ω > 0`, provided there is a nonzero
one. -/
lemma exists_real_generator (L : PeriodPair) (ω : ℝ) (hω : (ω : ℂ) ∈ L.lattice) (h0 : ω ≠ 0) :
    ∃ Ω : ℝ, 0 < Ω ∧ ∀ x : ℝ, (x : ℂ) ∈ L.lattice ↔ ∃ n : ℤ, x = n * Ω := by
  let S : AddSubgroup ℝ :=
    { carrier := {x | (x : ℂ) ∈ L.lattice}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        have ha' : (a : ℂ) ∈ L.lattice := ha
        have hb' : (b : ℂ) ∈ L.lattice := hb
        show ((a + b : ℝ) : ℂ) ∈ L.lattice
        push_cast
        exact add_mem ha' hb'
      neg_mem' := fun {a} ha => by
        have ha' : (a : ℂ) ∈ L.lattice := ha
        show ((-a : ℝ) : ℂ) ∈ L.lattice
        push_cast
        exact neg_mem ha' }
  have hSmem : ∀ x : ℝ, x ∈ S ↔ (x : ℂ) ∈ L.lattice := fun x => Iff.rfl
  obtain ⟨ε, hε, hiso⟩ := exists_isolated L
  have hdisj : Disjoint (S : Set ℝ) (Set.Ioo 0 ε) := by
    refine Set.disjoint_left.2 fun x hx hxI => ?_
    have hx' : (x : ℂ) ∈ L.lattice := hx
    have hn : ‖(x : ℂ)‖ < ε := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxI.1]
      exact hxI.2
    have := hiso _ hx' hn
    have h00 : x = 0 := by exact_mod_cast this
    exact hxI.1.ne' h00
  obtain ⟨b, hb⟩ := AddSubgroup.cyclic_of_isolated_zero hε hdisj
  have hmem : ∀ x : ℝ, (x : ℂ) ∈ L.lattice ↔ ∃ n : ℤ, x = n * b := by
    intro x
    rw [← hSmem, hb, AddSubgroup.mem_closure_singleton]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [← hn, zsmul_eq_mul]⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [hn, zsmul_eq_mul]⟩
  have hbne : b ≠ 0 := by
    intro hb0
    obtain ⟨n, hn⟩ := (hmem ω).mp hω
    exact h0 (by rw [hn, hb0, mul_zero])
  rcases lt_or_gt_of_ne hbne with hneg | hpos
  · refine ⟨-b, neg_pos.mpr hneg, fun x => (hmem x).trans ?_⟩
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨-n, by rw [hn]; push_cast; ring⟩
    · rintro ⟨n, hn⟩
      exact ⟨-n, by rw [hn]; push_cast; ring⟩
  · exact ⟨b, hpos, hmem⟩

/-- **E21.** Real points and a basis `(Ω, Ω′)` with `Im Ω′ > 0`. -/
theorem exists_real_basis (L : PeriodPair) (ω : ℝ) (hω : (ω : ℂ) ∈ L.lattice) (h0 : ω ≠ 0) :
    ∃ (Ω : ℝ) (Ω' : ℂ) (N : ℤ), 0 < Ω ∧ 0 < Ω'.im ∧ N ≠ 0 ∧ ω = N * Ω ∧
      L.lattice = Submodule.span ℤ {(Ω : ℂ), Ω'} ∧
      (∀ z ∈ L.lattice, z.im = 0 → ∃ n : ℤ, z = (n : ℂ) * (Ω : ℂ)) := by
  obtain ⟨Ω, hΩ, hmem⟩ := exists_real_generator L ω hω h0
  have hΩL : (Ω : ℂ) ∈ L.lattice := (hmem Ω).mpr ⟨1, by simp⟩
  obtain ⟨m, n, hmn⟩ := mem_lattice.mp hΩL
  -- gcd (m, n) = 1
  have hcop : IsCoprime m n := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    set g : ℕ := Int.gcd m n with hg
    have hgm : (g : ℤ) ∣ m := Int.gcd_dvd_left ..
    have hgn : (g : ℤ) ∣ n := Int.gcd_dvd_right ..
    obtain ⟨m', hm'⟩ := hgm
    obtain ⟨n', hn'⟩ := hgn
    have hg0 : (g : ℂ) ≠ 0 := by
      intro h
      have hg0' : g = 0 := by exact_mod_cast h
      have hm0 : m = 0 := by rw [hm', hg0']; simp
      have hn0 : n = 0 := by rw [hn', hg0']; simp
      have : (Ω : ℂ) = 0 := by rw [← hmn, hm0, hn0]; simp
      exact hΩ.ne' (by exact_mod_cast this)
    have hxL : (((Ω / g : ℝ)) : ℂ) ∈ L.lattice := by
      have hΩg : (Ω : ℂ) = (g : ℂ) * ((m' : ℂ) * L.ω₁ + (n' : ℂ) * L.ω₂) := by
        rw [← hmn, hm', hn']
        push_cast
        ring
      have : (((Ω / g : ℝ)) : ℂ) = (m' : ℂ) * L.ω₁ + (n' : ℂ) * L.ω₂ := by
        push_cast
        rw [div_eq_iff hg0, hΩg]
        ring
      rw [this]
      exact mem_lattice.mpr ⟨m', n', rfl⟩
    obtain ⟨k, hk⟩ := (hmem _).mp hxL
    have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg0
    have h1 : (g : ℝ) * k = 1 := by
      rw [div_eq_iff hgR] at hk
      have hz : ((g : ℝ) * k - 1) * Ω = 0 := by linear_combination (-1 : ℝ) * hk
      rcases mul_eq_zero.mp hz with h | h
      · linarith
      · exact absurd h hΩ.ne'
    have h2 : (g : ℤ) * k = 1 := by exact_mod_cast h1
    have := Int.eq_one_of_mul_eq_one_right (Int.natCast_nonneg g) h2
    exact_mod_cast this
  obtain ⟨u, v, huv⟩ := hcop
  have huvC : (u : ℂ) * m + v * n = 1 := by exact_mod_cast huv
  set Ω₀ : ℂ := -(v : ℂ) * L.ω₁ + u * L.ω₂ with hΩ₀
  have hΩ₀L : Ω₀ ∈ L.lattice := mem_lattice.mpr ⟨-v, u, by rw [hΩ₀]; push_cast; ring⟩
  have e1 : L.ω₁ = u * (Ω : ℂ) - n * Ω₀ := by
    rw [hΩ₀]; linear_combination (-L.ω₁) * huvC + u * hmn
  have e2 : L.ω₂ = v * (Ω : ℂ) + m * Ω₀ := by
    rw [hΩ₀]; linear_combination (-L.ω₂) * huvC + v * hmn
  have hspan : L.lattice = Submodule.span ℤ {(Ω : ℂ), Ω₀} := by
    apply le_antisymm
    · rw [PeriodPair.lattice, Submodule.span_le]
      intro x hx
      rcases hx with rfl | rfl
      · rw [SetLike.mem_coe, Submodule.mem_span_pair]
        exact ⟨u, -n, by rw [e1, zsmul_eq_mul, zsmul_eq_mul]; push_cast; ring⟩
      · rw [SetLike.mem_coe, Submodule.mem_span_pair]
        exact ⟨v, m, by rw [e2, zsmul_eq_mul, zsmul_eq_mul]⟩
    · rw [Submodule.span_le]
      intro x hx
      rcases hx with rfl | hx
      · exact hΩL
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hΩ₀L
  have him : Ω₀.im ≠ 0 := by
    intro h
    apply im_ω₁_div_ω₂_ne_zero L
    have a1 : L.ω₁.im = 0 := by rw [e1]; simp [Complex.sub_im, Complex.mul_im, h]
    have a2 : L.ω₂.im = 0 := by rw [e2]; simp [Complex.add_im, Complex.mul_im, h]
    simp [Complex.div_im, a1, a2]
  have hreal : ∀ z ∈ L.lattice, z.im = 0 → ∃ n : ℤ, z = (n : ℂ) * (Ω : ℂ) := by
    intro z hz hzi
    have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hzi])
    obtain ⟨n, hn⟩ := (hmem z.re).mp (by rw [← hz']; exact hz)
    exact ⟨n, by rw [hz', hn]; simp⟩
  obtain ⟨N, hN⟩ := (hmem ω).mp hω
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact h0 (by rw [hN]; simp)
  rcases lt_or_gt_of_ne him with hlt | hgt
  · refine ⟨Ω, -Ω₀, N, hΩ, by rw [Complex.neg_im]; linarith, hN0, hN, ?_, hreal⟩
    rw [span_pair_neg]
    exact hspan
  · exact ⟨Ω, Ω₀, N, hΩ, hgt, hN0, hN, hspan, hreal⟩

/-- Real points of `L` descend to real points of the scaled lattice `Λ = d⁻¹ L`. -/
lemma real_div_mem_scaled (L Λ : PeriodPair) (d : ℕ) (hd : 1 ≤ d)
    (hlat : ∀ z : ℂ, z ∈ Λ.lattice ↔ (d : ℂ) * z ∈ L.lattice) (ω : ℝ)
    (hω : (ω : ℂ) ∈ L.lattice) : ((ω / d : ℝ) : ℂ) ∈ Λ.lattice := by
  have hdC : (d : ℂ) ≠ 0 := by
    have : d ≠ 0 := by omega
    exact_mod_cast this
  rw [hlat]
  convert hω using 1
  push_cast
  field_simp

end CatalanCore.Elliptic.Lattice
