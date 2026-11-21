module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Topology.Algebra.Module.Cardinality

@[expose] public section

/-!
# Liouville tools for functions on `ℂ / Λ`

For `L : PeriodPair` and `Λ = L.lattice`:

* `periodic_entire_const` (L1): an entire `Λ`-periodic function is constant;
* `exists_entire_extension_periodic` (L2): a function differentiable on `Λᶜ`, `Λ`-periodic there and
  bounded near `0` extends to an entire `Λ`-periodic function;
* `exists_entire_extension_multiplier` (L2′): the same with a multiplier,
  `g (z + l) = m l z * g z`, giving `G (z + l) = m l z * G z` for all `z`.
-/

namespace CatalanCore.Elliptic.Theta

open Filter Topology Function Set

variable (L : PeriodPair)

/-- **L1.** An entire function that is periodic for the lattice is constant. -/
theorem periodic_entire_const {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hper : ∀ z, ∀ l ∈ L.lattice, H (z + l) = H z) (z w : ℂ) : H z = H w :=
  hH.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L.lattice H hH.continuous hper).isBounded z w

lemma countable_lattice : (L.lattice : Set ℂ).Countable := by
  have : Countable L.lattice := L.latticeEquivProd.toEquiv.countable_iff.2 inferInstance
  exact Set.countable_coe_iff.mp this

lemma dense_compl_lattice : Dense ((L.lattice : Set ℂ)ᶜ) :=
  Set.Countable.dense_compl ℝ (countable_lattice L)

lemma add_mem_lattice_iff {z l : ℂ} (hl : l ∈ L.lattice) : z + l ∈ L.lattice ↔ z ∈ L.lattice :=
  ⟨fun h => by simpa using L.lattice.sub_mem h hl, fun h => L.lattice.add_mem h hl⟩

/-- **L2′.** A function `g` that is differentiable on `Λᶜ`, bounded near `0`, and satisfies
`g (z + l) = m l z * g z` off `Λ` (with each `m l` entire) extends to an entire function `G`
with `G (z + l) = m l z * G z` for all `z`. -/
theorem exists_entire_extension_multiplier (g : ℂ → ℂ) (m : ℂ → ℂ → ℂ)
    (hg : DifferentiableOn ℂ g ((L.lattice : Set ℂ)ᶜ))
    (hm : ∀ l ∈ L.lattice, Differentiable ℂ (m l))
    (hmul : ∀ l ∈ L.lattice, ∀ z, z ∉ L.lattice → g (z + l) = m l z * g z)
    (hb : ∃ C : ℝ, ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖g z‖ ≤ C) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ z, z ∉ L.lattice → G z = g z) ∧
      ∀ l ∈ L.lattice, ∀ z, G (z + l) = m l z * G z := by
  classical
  obtain ⟨C, hC⟩ := hb
  set a₀ : ℂ := limUnder (𝓝[≠] (0 : ℂ)) g with ha₀
  set h : ℂ → ℂ := Function.update g 0 a₀ with hh
  -- the removable singularity at `0`
  have hh0 : DifferentiableAt ℂ h 0 := by
    obtain ⟨u, hu, hu'⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hC
    have hs : (u ∩ (↑L.lattice \ {0})ᶜ) ∈ 𝓝 (0 : ℂ) :=
      Filter.inter_mem hu (L.compl_lattice_sdiff_singleton_mem_nhds 0)
    have hd : DifferentiableOn ℂ g ((u ∩ (↑L.lattice \ {0})ᶜ) \ {0}) := by
      refine hg.mono ?_
      intro z hz
      simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
        SetLike.mem_coe] at hz ⊢
      intro hzl
      exact hz.1.2 ⟨hzl, hz.2⟩
    have hb' : BddAbove (norm ∘ g '' ((u ∩ (↑L.lattice \ {0})ᶜ) \ {0})) := by
      refine ⟨C, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact hu' ⟨hz.1.1, hz.2⟩
    exact (Complex.differentiableOn_update_limUnder_of_bddAbove hs hd hb').differentiableAt hs
  let G : ℂ → ℂ := fun z => if z ∈ L.lattice then m z 0 * a₀ else g z
  have hGg : ∀ z, z ∉ L.lattice → G z = g z := fun z hz => if_neg hz
  have hGd : Differentiable ℂ G := by
    intro z
    by_cases hz : z ∈ L.lattice
    · have hev : G =ᶠ[𝓝 z] fun y => m z (y - z) * h (y - z) := by
        filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds z] with y hy
        by_cases hyz : y = z
        · subst hyz
          simp only [G, if_pos hz, sub_self, hh, Function.update_self]
        · have hyl : y ∉ L.lattice := fun hyl => hy ⟨hyl, hyz⟩
          have hyz' : y - z ≠ 0 := sub_ne_zero.2 hyz
          have hyz'' : y - z ∉ L.lattice := fun h' => hyl (by simpa using L.lattice.add_mem h' hz)
          have := hmul z hz (y - z) hyz''
          rw [sub_add_cancel] at this
          simp only [G, if_neg hyl, hh, Function.update_of_ne hyz']
          exact this
      have hd1 : DifferentiableAt ℂ (m z ∘ fun y => y - z) z :=
        DifferentiableAt.comp z (hm z hz (z - z)) (by fun_prop)
      have hd2 : DifferentiableAt ℂ (h ∘ fun y => y - z) z :=
        DifferentiableAt.comp z (by simpa using hh0) (by fun_prop)
      exact (hd1.mul hd2).congr_of_eventuallyEq hev
    · have hs : ((L.lattice : Set ℂ)ᶜ) ∈ 𝓝 z := L.isClosed_lattice.isOpen_compl.mem_nhds hz
      have : G =ᶠ[𝓝 z] g := by
        filter_upwards [hs] with y hy
        exact hGg y hy
      exact (hg.differentiableAt hs).congr_of_eventuallyEq this
  refine ⟨G, hGd, hGg, fun l hl => ?_⟩
  have hext : (fun z => G (z + l)) = fun z => m l z * G z := by
    refine Continuous.ext_on (dense_compl_lattice L) ?_ ?_ ?_
    · exact hGd.continuous.comp (continuous_id.add continuous_const)
    · exact (hm l hl).continuous.mul hGd.continuous
    · intro z hz
      have hz' : z ∉ L.lattice := hz
      have hzl : z + l ∉ L.lattice := fun h' => hz' ((add_mem_lattice_iff L hl).1 h')
      simp only [hGg z hz', hGg (z + l) hzl]
      exact hmul l hl z hz'
  intro z
  exact congrFun hext z

/-- **L2.** Periodic version of `exists_entire_extension_multiplier`. -/
theorem exists_entire_extension_periodic (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g ((L.lattice : Set ℂ)ᶜ))
    (hper : ∀ l ∈ L.lattice, ∀ z, z ∉ L.lattice → g (z + l) = g z)
    (hb : ∃ C : ℝ, ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖g z‖ ≤ C) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ z, z ∉ L.lattice → G z = g z) ∧
      ∀ l ∈ L.lattice, ∀ z, G (z + l) = G z := by
  obtain ⟨G, h1, h2, h3⟩ := exists_entire_extension_multiplier L g (fun _ _ => 1) hg
    (fun _ _ => differentiable_const _) (fun l hl z hz => by simpa using hper l hl z hz) hb
  exact ⟨G, h1, h2, fun l hl z => by simpa using h3 l hl z⟩

/-- Boundedness near `0` from a continuous germ. -/
theorem bounded_near_zero_of_germ {g k : ℂ → ℂ} (hk : ContinuousAt k 0)
    (hgk : g =ᶠ[𝓝[≠] (0 : ℂ)] k) : ∃ C : ℝ, ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖g z‖ ≤ C := by
  refine ⟨‖k 0‖ + 1, ?_⟩
  have h1 : ∀ᶠ z in 𝓝 (0 : ℂ), ‖k z‖ ≤ ‖k 0‖ + 1 := by
    have := hk.norm.eventually (Iio_mem_nhds (show ‖k 0‖ < ‖k 0‖ + 1 by linarith))
    filter_upwards [this] with z hz using le_of_lt hz
  filter_upwards [hgk, nhdsWithin_le_nhds h1] with z hz1 hz2
  rw [hz1]
  exact hz2

end CatalanCore.Elliptic.Theta
