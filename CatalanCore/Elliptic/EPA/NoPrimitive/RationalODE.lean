module

public import CatalanCore.Elliptic.EPA.NoPrimitive.RatFuncDeriv
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.Algebra.Squarefree.Basic

/-!
# The rational differential-equation obstruction

CM `lem:origin-rational-obstruction`: for a squarefree polynomial `H` of degree at least `2`
over a field of characteristic zero, there is no rational function `r` with
`2 H r' + H' r = 1`.

Paper proof (a rewrite of CM's pole-order argument that avoids an algebraic closure).  Put
`s = r² H`.  Then `s' = r (2 H r' + H' r) = r`, so `s = H (s')²`.  Write `s = p/q` in lowest terms;
`s ≠ 0` since `r ≠ 0`, and the identity becomes the polynomial identity
`q³ p = H (p' q - p q')²` (`(★)`) with `p ≠ 0`, `IsCoprime p q`.

* `q` a unit: `(★)` reads `q p = H p'²` after cancelling `q²`; `p ≠ 0` has degree `e`.  If `e = 0`
  then `p' = 0` and `p = 0`; if `e ≥ 1` the degrees give `e = deg H + 2 (e - 1) ≥ 2 e`.
* `q` not a unit: let `π` be an irreducible factor, `q = π^(j+1) u` with `π ∤ u`.  Then
  `q' = π^j w`, `w = (j+1) π' u + π u'`, and `π ∤ w` (char `0`, `π ∤ π'` for degree reasons).
  Further `p' q - p q' = π^j t` with `t = π p' u - p w` and `π ∤ t` (`π ∤ p` by coprimality).
  Cancelling `π^(2j)` in `(★)` gives `π^(j+3) u³ p = H t²`, so `π^(j+3) ∣ H`, contradicting
  squarefreeness of `H`.
-/

@[expose] public section

namespace CatalanCore.Elliptic.EPA.NoPrimitive

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

lemma natDegree_derivative_of_ne (p : K[X]) (hp : p.natDegree ≠ 0) :
    (derivative p).natDegree = p.natDegree - 1 := by
  refine le_antisymm (natDegree_derivative_le p) ?_
  apply le_natDegree_of_ne_zero
  rw [coeff_derivative]
  have h0 : p.coeff p.natDegree ≠ 0 := by
    have : p ≠ 0 := fun h => hp (by simp [h])
    simpa using this
  have h1 : p.natDegree - 1 + 1 = p.natDegree := Nat.sub_add_cancel (Nat.pos_of_ne_zero hp)
  rw [h1]
  exact mul_ne_zero h0 (Nat.cast_add_one_ne_zero _)

/-- An irreducible polynomial does not divide its (nonzero, in characteristic zero) derivative. -/
lemma not_dvd_derivative {π : K[X]} (hπ : Irreducible π) : ¬ π ∣ derivative π := by
  intro h
  have hpos : π.natDegree ≠ 0 := (natDegree_pos_iff_degree_pos.2
    (degree_pos_of_irreducible hπ)).ne'
  have hne : derivative π ≠ 0 := fun h0 => hpos (derivative_eq_zero.1 h0)
  have := natDegree_le_of_dvd h hne
  have := natDegree_derivative_lt hpos
  omega

/-- The polynomial form of the obstruction: `q³ p = H (p' q - p q')²` has no solution with
`p ≠ 0` coprime to `q`, for `H` squarefree of degree `≥ 2`. -/
theorem no_coprime_solution {H : K[X]} (hH : Squarefree H) (hdeg : 2 ≤ H.natDegree)
    {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) (hpq : IsCoprime p q) :
    q ^ 3 * p ≠ H * (derivative p * q - p * derivative q) ^ 2 := by
  intro heq
  have hH0 : H ≠ 0 := fun h => by simp [h] at hdeg
  by_cases hu : IsUnit q
  · -- `q` constant
    obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.1 hu
    have hdq : derivative (C c : K[X]) = 0 := derivative_C
    rw [hdq, mul_zero, sub_zero] at heq
    have hc0 : (C c : K[X]) ≠ 0 := hq
    have h2 : C c * p = H * derivative p ^ 2 := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hc0)
      calc C c ^ 2 * (C c * p) = C c ^ 3 * p := by ring
        _ = _ := heq
        _ = C c ^ 2 * (H * derivative p ^ 2) := by ring
    by_cases he : p.natDegree = 0
    · have hd0 : derivative p = 0 := by
        rw [eq_C_of_natDegree_eq_zero he]; exact derivative_C
      rw [hd0] at h2
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h2
      exact mul_ne_zero hc0 hp h2
    · have hd1 := natDegree_derivative_of_ne p he
      have hd0 : derivative p ≠ 0 := fun h => he (derivative_eq_zero.1 h)
      have := congrArg natDegree h2
      rw [natDegree_C_mul hc.ne_zero, natDegree_mul hH0 (pow_ne_zero 2 hd0), natDegree_pow, hd1] at this
      omega
  · -- `q` has an irreducible factor
    obtain ⟨π, hπ, hπq⟩ := WfDvdMonoid.exists_irreducible_factor hu hq
    have hπp : Prime π := hπ.prime
    obtain ⟨k, u, hπu, hqu⟩ := WfDvdMonoid.max_power_factor hq hπ
    have hk : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at hqu
      exact hπu (hqu ▸ hπq)
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hu0 : u ≠ 0 := fun h => hq (by rw [hqu, h, mul_zero])
    set w : K[X] := C ((j + 1 : ℕ) : K) * derivative π * u + π * derivative u with hw
    have hdq : derivative q = π ^ j * w := by
      rw [hqu, derivative_mul, derivative_pow, hw]
      simp only [Nat.add_sub_cancel]
      ring
    have hjK : ((j + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero j)
    have hπw : ¬ π ∣ w := by
      intro h
      have h1 : π ∣ C ((j + 1 : ℕ) : K) * derivative π * u := by
        have : π ∣ π * derivative u := dvd_mul_right _ _
        have h2 := (dvd_add_left this).1 (by rwa [hw] at h)
        exact h2
      rcases hπp.dvd_or_dvd h1 with h2 | h2
      · rcases hπp.dvd_or_dvd h2 with h3 | h3
        · exact hπ.not_isUnit (isUnit_of_dvd_unit h3 (isUnit_C.2 hjK.isUnit))
        · exact not_dvd_derivative hπ h3
      · exact hπu h2
    set t : K[X] := π * derivative p * u - p * w with ht
    have hdiff : derivative p * q - p * derivative q = π ^ j * t := by
      rw [hdq, hqu, ht]; ring
    have hπt : ¬ π ∣ t := by
      intro h
      have h1 : π ∣ p * w := by
        have : π ∣ π * derivative p * u := ⟨derivative p * u, by ring⟩
        have := dvd_sub this h
        simpa [ht] using this
      rcases hπp.dvd_or_dvd h1 with h2 | h2
      · exact hπ.not_isUnit (hpq.isUnit_of_dvd' h2 hπq)
      · exact hπw h2
    rw [hdiff, hqu] at heq
    have h3 : π ^ (j + 3) * (u ^ 3 * p) = H * t ^ 2 := by
      have hpj : π ^ (2 * j) ≠ 0 := pow_ne_zero _ hπp.ne_zero
      apply mul_left_cancel₀ hpj
      calc π ^ (2 * j) * (π ^ (j + 3) * (u ^ 3 * p)) = (π ^ (j + 1) * u) ^ 3 * p := by ring
        _ = H * (π ^ j * t) ^ 2 := heq
        _ = π ^ (2 * j) * (H * t ^ 2) := by ring
    have h4 : π ^ (j + 3) ∣ H * t ^ 2 := ⟨u ^ 3 * p, h3.symm.trans (by ring)⟩
    have h5 : π ^ (j + 3) ∣ H :=
      hπp.pow_dvd_of_dvd_mul_right _ (fun h => hπt (hπp.dvd_of_dvd_pow h)) h4
    have h6 : π * π ∣ H := by
      have := pow_dvd_pow π (show 2 ≤ j + 3 by omega)
      exact (pow_two π ▸ this).trans h5
    exact hπ.not_isUnit (hH π h6)

local notation "𝒞" => algebraMap K[X] (RatFunc K)

/-- CM `lem:origin-rational-obstruction`: `2 H r' + H' r = 1` has no solution `r ∈ K(X)`
for `H` squarefree of degree at least `2`. -/
theorem no_rational_solution {H : K[X]} (hH : Squarefree H) (hdeg : 2 ≤ H.natDegree) :
    ¬ ∃ r : RatFunc K, 2 * 𝒞 H * derivationX K r + 𝒞 (derivative H) * r = 1 := by
  rintro ⟨r, hr⟩
  have hH0 : H ≠ 0 := fun h => by simp [h] at hdeg
  have hHc : (𝒞 H : RatFunc K) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).2 hH0
  set s : RatFunc K := r ^ 2 * 𝒞 H with hs
  have hDs : derivationX K s = r := by
    have h1 : derivationX K s = 2 * r * 𝒞 H * derivationX K r + r ^ 2 * 𝒞 (derivative H) := by
      rw [hs, Derivation.leibniz, Derivation.leibniz_pow, derivationX_algebraMap]
      simp only [smul_eq_mul, Nat.add_one_sub_one]
      push_cast
      ring
    rw [h1]
    linear_combination r * hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero, mul_zero, add_zero] at hr
    exact zero_ne_one hr
  have hs0 : s ≠ 0 := mul_ne_zero (pow_ne_zero 2 hr0) hHc
  have hsH : s = 𝒞 H * (derivationX K s) ^ 2 := by rw [hDs, hs]; ring
  obtain ⟨p, q, hq, hcop, hspq⟩ : ∃ p q : K[X], q ≠ 0 ∧ IsCoprime p q ∧ s = 𝒞 p / 𝒞 q :=
    ⟨s.num, s.denom, RatFunc.denom_ne_zero s, RatFunc.isCoprime_num_denom s,
      (RatFunc.num_div_denom s).symm⟩
  have hqc : (𝒞 q : RatFunc K) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).2 hq
  have hp : p ≠ 0 := by
    rintro rfl
    apply hs0
    rw [hspq]; simp
  apply no_coprime_solution hH hdeg hp hq hcop
  apply RatFunc.algebraMap_injective K
  rw [hspq] at hsH
  rw [derivationX_apply, ratDer_div _ _ hq] at hsH
  simp only [map_mul, map_sub, map_pow]
  field_simp at hsH
  linear_combination hsH

end CatalanCore.Elliptic.EPA.NoPrimitive
