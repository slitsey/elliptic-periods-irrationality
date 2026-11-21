module

public import CatalanCore.Elliptic.EPA.Reduce
public import CatalanCore.Elliptic.EPA.Frame
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
# Derivative ideals and persistence (row E09.3)

Labels refer to `D2-DESIGN-2026-11-20.md` §5 E09.3 and to the CM paper (arXiv 2610.31112) §8,
"Persistence for the actual origin derivative ideals" (l.2041-2109): the derivative ideal
`I_s = (f) + (D_ν P : c(ν) ≤ s)`, the inclusion `D_ν(I_s) ⊆ I_{s + c(ν)}`, and the persistent
component theorem.

* `derivIdeal ch P v s = (f) ⊔ (frameWord ch word P : cost word ≤ s)` with letter costs `v`.
* `frameWord_derivIdeal`: `g ∈ I_s → D_ν g ∈ I_{s + c(ν)}` (CM l.2073; Leibniz and
  `D_i f = 0`, no commutativity of the frame is used).
* `exists_persistent_minimalPrime_pair`: the pigeonhole on a monotone family of ideals under a
  prime of bounded height (the generic lemma of OAI `Approximation/PersistentComponents`, copied in
  shape so that this module needs no vendored OAI module).
* `persistent_prime`: the theorem of CM l.2041.

Deviation from the design statement: the height lower bound `2 ≤ ht Q` uses that `(f)` is prime
(`relation_isPrime`, row E09.5b); here it is an instance hypothesis, discharged by E09.5b.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA

open CatalanCore.Elliptic

/-! ### Generic pigeonhole on a monotone family of ideals -/

namespace Persist

variable {R : Type*} [CommRing R]

theorem prime_height_step {P Q : Ideal R} (hP : P.IsPrime) (hQ : Q.IsPrime)
    (hPQ : P < Q) : P.height + 1 ≤ Q.height := by
  let := hP
  let := hQ
  exact Ideal.height_add_one_le_of_lt_of_isPrime hPQ

theorem exists_adjacent_eq_of_height_bound (P : ℕ → Ideal R) (m : ℕ)
    (hPrime : ∀ i ≤ m + 1, (P i).IsPrime)
    (hstep : ∀ i ≤ m, P i ≤ P (i + 1))
    (hheight : (P (m + 1)).height ≤ m) :
    ∃ i ≤ m, P i = P (i + 1) := by
  by_contra h
  have hneq : ∀ i ≤ m, P i ≠ P (i + 1) := by simpa only [not_exists, not_and] using h
  have hgrowth : ∀ i ≤ m + 1, (i : ℕ∞) ≤ (P i).height := by
    intro i hi
    induction i with
    | zero => exact bot_le
    | succ i ih =>
      have him : i ≤ m := by omega
      have hip : i ≤ m + 1 := by omega
      have hs := prime_height_step (hPrime i hip) (hPrime (i + 1) hi)
        (lt_of_le_of_ne (hstep i him) (hneq i him))
      have hadd : (i : ℕ∞) + 1 ≤ (P i).height + 1 := by
        gcongr
        exact ih hip
      simpa only [Nat.cast_add, Nat.cast_one] using hadd.trans hs
  have hf := (hgrowth (m + 1) le_rfl).trans hheight
  exact (by exact_mod_cast (Nat.not_succ_le_self m) : ¬ ((m + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞)) hf

theorem exists_nested_minimalPrimes (I : ℕ → Ideal R) (hI : Monotone I)
    (n : ℕ) (P : Ideal R) (hP : P.IsPrime) (hIP : I n ≤ P) :
    ∃ Q : ℕ → Ideal R,
      (∀ i ≤ n, Q i ∈ (I i).minimalPrimes) ∧
      (∀ i < n, Q i ≤ Q (i + 1)) ∧ Q n ≤ P := by
  induction n generalizing P with
  | zero =>
    let := hP
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hIP
    refine ⟨fun _ => Q, ?_, ?_, hQP⟩
    · intro i hi
      have hi0 : i = 0 := by omega
      simpa only [hi0] using hQ
    · intro i hi
      omega
  | succ n ih =>
    let := hP
    obtain ⟨Qlast, hQlast, hQlastP⟩ := Ideal.exists_minimalPrimes_le hIP
    obtain ⟨Q, hQ, hstep, hQlastle⟩ :=
      ih Qlast hQlast.isPrime ((hI (Nat.le_succ n)).trans hQlast.le)
    refine ⟨fun i => if i = n + 1 then Qlast else Q i, ?_, ?_, ?_⟩
    · intro i hi
      by_cases hei : i = n + 1
      · simpa [hei] using hQlast
      · simpa [hei] using hQ i (by omega)
    · intro i hi
      have hin : i ≠ n + 1 := by omega
      by_cases hei : i = n
      · simpa [hei] using hQlastle
      · have hip : i + 1 ≠ n + 1 := by omega
        simpa [hin, hip, hei] using hstep i (by omega)
    · simpa [Nat.succ_eq_add_one] using hQlastP

theorem exists_persistent_minimalPrime (I : ℕ → Ideal R) (hI : Monotone I)
    (m : ℕ) (P : Ideal R) (hP : P.IsPrime)
    (hIP : I (m + 2) ≤ P) (hheight : P.height ≤ m) :
    ∃ r < m + 2, ∃ Q : Ideal R,
      Q ∈ (I r).minimalPrimes ∧ I (r + 1) ≤ Q ∧ Q ≤ P := by
  obtain ⟨Q, hQ, hstep, hQP⟩ := exists_nested_minimalPrimes I hI (m + 2) P hP hIP
  have hmono : ∀ i j, i ≤ j → j ≤ m + 2 → Q i ≤ Q j := by
    intro i j hij hj
    induction j with
    | zero =>
      have hi : i = 0 := by omega
      simp only [hi, le_refl]
    | succ j ih =>
      by_cases heq : i = j + 1
      · simp [heq]
      · exact (ih (by omega) (by omega)).trans (hstep j (by omega))
  have hbound : (Q (m + 1)).height ≤ m :=
    (Ideal.height_mono ((hmono (m + 1) (m + 2) (by omega) le_rfl).trans hQP)).trans hheight
  obtain ⟨r, hr, heq⟩ := exists_adjacent_eq_of_height_bound Q m
    (fun i hi => (hQ i (by omega)).isPrime) (fun i hi => hstep i (by omega)) hbound
  refine ⟨r, by omega, Q r, hQ r (by omega), ?_, ?_⟩
  · rw [heq]
    exact (hQ (r + 1) (by omega)).le
  · exact (hmono r (m + 2) (by omega) le_rfl).trans hQP

theorem minimalPrime_persists {I J Q : Ideal R} (hIJ : I ≤ J)
    (hQ : Q ∈ I.minimalPrimes) (hJQ : J ≤ Q) : Q ∈ J.minimalPrimes := by
  refine ⟨⟨hQ.isPrime, hJQ⟩, ?_⟩
  intro P hP hPQ
  exact hQ.2 ⟨hP.1, hIJ.trans hP.2⟩ hPQ

theorem exists_persistent_minimalPrime_pair (I : ℕ → Ideal R) (hI : Monotone I)
    (m : ℕ) (P : Ideal R) (hP : P.IsPrime)
    (hIP : I (m + 2) ≤ P) (hheight : P.height ≤ m) :
    ∃ r < m + 2, ∃ Q : Ideal R,
      Q ∈ (I r).minimalPrimes ∧ Q ∈ (I (r + 1)).minimalPrimes ∧ Q ≤ P := by
  obtain ⟨r, hr, Q, hQ, hnext, hQP⟩ :=
    exists_persistent_minimalPrime I hI m P hP hIP hheight
  exact ⟨r, hr, Q, hQ, minimalPrime_persists (hI (Nat.le_succ r)) hQ hnext, hQP⟩

end Persist

/-! ### The derivative ideals -/

section DerivIdeal

variable {m : ℕ} (ch : OriginChart) (P : AmbRing m) (v : Fin (m + 1) → ℚ)

/-- `I_s = (f) + (D_ν P : c(ν) ≤ s)` with letter costs `v` (CM l.2041). -/
noncomputable def derivIdeal (s : ℚ) : Ideal (AmbRing m) :=
  Ideal.span {relation ch} ⊔
    Ideal.span {g | ∃ word : List (Fin (m + 1)), (word.map v).sum ≤ s ∧ g = frameWord ch word P}

variable {ch P v}

theorem relation_mem_derivIdeal (s : ℚ) : relation ch ∈ derivIdeal ch P v s :=
  Ideal.mem_sup_left (Ideal.subset_span rfl)

theorem span_relation_le_derivIdeal (s : ℚ) :
    (Ideal.span {relation ch} : Ideal (AmbRing m)) ≤ derivIdeal ch P v s :=
  le_sup_left

theorem frameWord_mem_derivIdeal {s : ℚ} (word : List (Fin (m + 1)))
    (h : (word.map v).sum ≤ s) : frameWord ch word P ∈ derivIdeal ch P v s :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨word, h, rfl⟩)

theorem self_mem_derivIdeal {s : ℚ} (hs : 0 ≤ s) : P ∈ derivIdeal ch P v s := by
  simpa using frameWord_mem_derivIdeal (ch := ch) (P := P) (v := v) (s := s) [] (by simpa using hs)

theorem derivIdeal_mono {s t : ℚ} (h : s ≤ t) : derivIdeal ch P v s ≤ derivIdeal ch P v t :=
  sup_le_sup_left (Ideal.span_mono (by
    intro g hg
    obtain ⟨w, hw, e⟩ := hg
    exact ⟨w, hw.trans h, e⟩)) _

/-- One letter: `D_i (I_s) ⊆ I_{s + v_i}`. -/
theorem frameDeriv_mem_derivIdeal (hv : ∀ i, 0 ≤ v i) (i : Fin (m + 1)) {s : ℚ} {g : AmbRing m}
    (hg : g ∈ derivIdeal ch P v s) : frameDeriv ch i g ∈ derivIdeal ch P v (s + v i) := by
  have hsub : derivIdeal ch P v s ≤ derivIdeal ch P v (s + v i) :=
    derivIdeal_mono (by linarith [hv i])
  have hspan : derivIdeal ch P v s = Ideal.span
      ({relation ch} ∪ {g | ∃ word : List (Fin (m + 1)), (word.map v).sum ≤ s ∧
        g = frameWord ch word P}) := by
    rw [derivIdeal, Ideal.span_union]
  rw [hspan] at hg
  have key : g ∈ derivIdeal ch P v s ∧ frameDeriv ch i g ∈ derivIdeal ch P v (s + v i) := by
    induction hg using Submodule.span_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · have hx' : x = relation ch := hx
        subst hx'
        exact ⟨relation_mem_derivIdeal s, by
          rw [frameDeriv_relation]; exact Ideal.zero_mem _⟩
      · obtain ⟨w, hw, rfl⟩ := hx
        refine ⟨frameWord_mem_derivIdeal w hw, ?_⟩
        have := frameWord_mem_derivIdeal (ch := ch) (P := P) (v := v) (s := s + v i) (i :: w)
          (by simp only [List.map_cons, List.sum_cons]; linarith)
        simpa using this
    | zero => exact ⟨Ideal.zero_mem _, by rw [map_zero]; exact Ideal.zero_mem _⟩
    | add x y hx hy ihx ihy =>
      exact ⟨Ideal.add_mem _ ihx.1 ihy.1, by rw [map_add]; exact Ideal.add_mem _ ihx.2 ihy.2⟩
    | smul a x hx ihx =>
      refine ⟨Ideal.mul_mem_left _ a ihx.1, ?_⟩
      simp only [smul_eq_mul, Derivation.leibniz]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ a ihx.2) (Ideal.mul_mem_right _ _ (hsub ihx.1))
  exact key.2

/-- CM l.2073: `D_ν (I_s) ⊆ I_{s + c(ν)}`. -/
theorem frameWord_derivIdeal (hv : ∀ i, 0 ≤ v i) {s : ℚ} {g : AmbRing m}
    (hg : g ∈ derivIdeal ch P v s) (word : List (Fin (m + 1))) :
    frameWord ch word g ∈ derivIdeal ch P v (s + (word.map v).sum) := by
  induction word with
  | nil => simpa using hg
  | cons i w ih =>
    have := frameDeriv_mem_derivIdeal hv i ih
    have e : s + (w.map v).sum + v i = s + ((i :: w).map v).sum := by
      simp only [List.map_cons, List.sum_cons]; ring
    rw [e] at this
    simpa using this

/-- CM l.2041: the origin-chart persistent component. -/
theorem persistent_prime (hv : ∀ i, 0 ≤ v i) (δ : ℚ) (hδ : 0 ≤ δ)
    (hP : P ∉ (Ideal.span {relation ch} : Ideal (AmbRing m)))
    [hfp : (Ideal.span {relation ch} : Ideal (AmbRing m)).IsPrime]
    (𝔭 : Ideal (AmbRing m)) [h𝔭 : 𝔭.IsPrime]
    (hf : (Ideal.span {relation ch} : Ideal (AmbRing m)) ≤ 𝔭)
    (hht : 𝔭.height ≤ ((m + 1 : ℕ) : ℕ∞))
    (hvan : ∀ word : List (Fin (m + 1)), (word.map v).sum ≤ ((m : ℚ) + 3) * δ →
      frameWord ch word P ∈ 𝔭) :
    ∃ r : ℕ, r < m + 3 ∧ ∃ Q : Ideal (AmbRing m),
      Q ∈ (derivIdeal ch P v ((r : ℚ) * δ)).minimalPrimes ∧
      Q ∈ (derivIdeal ch P v (((r : ℚ) + 1) * δ)).minimalPrimes ∧ Q ≤ 𝔭 ∧
      (Ideal.span {relation ch} : Ideal (AmbRing m)) < Q ∧
      2 ≤ Q.height ∧ Q.height ≤ ((m + 1 : ℕ) : ℕ∞) ∧
      ∀ g ∈ derivIdeal ch P v ((r : ℚ) * δ), ∀ word : List (Fin (m + 1)),
        (word.map v).sum ≤ δ → frameWord ch word g ∈ Q := by
  set I : ℕ → Ideal (AmbRing m) := fun n => derivIdeal ch P v ((n : ℚ) * δ) with hI
  have hmono : Monotone I := fun a b hab =>
    derivIdeal_mono (mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hδ)
  have hIP : I (m + 1 + 2) ≤ 𝔭 := by
    refine sup_le hf (Ideal.span_le.mpr ?_)
    rintro g ⟨w, hw, rfl⟩
    apply hvan w
    have hw' : (w.map v).sum ≤ ((m + 1 + 2 : ℕ) : ℚ) * δ := hw
    have e : ((m + 1 + 2 : ℕ) : ℚ) = (m : ℚ) + 3 := by push_cast; ring
    rw [e] at hw'
    exact hw'
  obtain ⟨r, hr, Q, hQ, hQ', hQP⟩ :=
    Persist.exists_persistent_minimalPrime_pair I hmono (m + 1) 𝔭 h𝔭 hIP hht
  have hQprime : Q.IsPrime := hQ.isPrime
  have e1 : ((r + 1 : ℕ) : ℚ) * δ = ((r : ℚ) + 1) * δ := by push_cast; ring
  have hQ'' : Q ∈ (derivIdeal ch P v (((r : ℚ) + 1) * δ)).minimalPrimes := by
    rw [← e1]; exact hQ'
  have hr0 : 0 ≤ (r : ℚ) * δ := mul_nonneg (Nat.cast_nonneg r) hδ
  have hPQ : P ∈ Q := hQ.1.2 (self_mem_derivIdeal hr0)
  have hfQ : (Ideal.span {relation ch} : Ideal (AmbRing m)) ≤ Q :=
    (span_relation_le_derivIdeal _).trans hQ.1.2
  have hlt : (Ideal.span {relation ch} : Ideal (AmbRing m)) < Q :=
    lt_of_le_of_ne hfQ (fun h => hP (h ▸ hPQ))
  have hne : (Ideal.span {relation ch} : Ideal (AmbRing m)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact relation_ne_zero ch
  have h1 : 1 ≤ (Ideal.span {relation ch} : Ideal (AmbRing m)).height :=
    Order.one_le_iff_ne_zero.mpr (mt Ideal.height_eq_zero_iff_eq_bot.mp hne)
  have h2 : 2 ≤ Q.height := by
    have := Persist.prime_height_step hfp hQprime hlt
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ (Ideal.span {relation ch} : Ideal (AmbRing m)).height + 1 := by gcongr
      _ ≤ Q.height := this
  refine ⟨r, by omega, Q, hQ, hQ'', hQP, hlt, h2, (Ideal.height_mono hQP).trans hht, ?_⟩
  intro g hg word hw
  have h3 := frameWord_derivIdeal hv hg word
  have h4 : derivIdeal ch P v ((r : ℚ) * δ + (word.map v).sum) ≤
      derivIdeal ch P v (((r : ℚ) + 1) * δ) := derivIdeal_mono (by linarith)
  exact hQ''.1.2 (h4 h3)

end DerivIdeal

end CatalanCore.Elliptic.EPA
