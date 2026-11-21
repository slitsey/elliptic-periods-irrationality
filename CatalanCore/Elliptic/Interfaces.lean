module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Contract types of the T3E campaign (interfaces)

Definitions and structures only. Producers and consumers of each type are listed in
`outputs/Compatibility programme/t3e-lean-plan/CONTRACT-TYPES.md`.

Labels refer to the paper `work/paper-elliptic/elliptic-periods.tex`.

* C0 `IntegralModel`: the package `(d, A, B, Λ, Ω, Ω′, Y, a, z_Q)` over `PeriodPair`
  (`lem:integral`, §"The lattice, the origin chart and the multiplier", `prop:chart`, D4).
* C1 `OriginChart`, `OriginSeries`: `prop:chart`, `prop:germ` (eq:quartic).
* C2 `Multiplier`: the theta multiplier `ψ̃ = Θ_Λ²(℘ − a)` with `ψ̃u`, `ψ̃²t` (W05-THETA §3, §8), its
  constants `χ`, `S_*`, `C_Λ` and the growth statement `lem:growth`.
* C3 `Weights`, `Row`, `Col`, `packetEntry`, `packetMatrix`: eq:packet, eq:entry; counting data
  `J_H`, `M`, `b̄`, `𝒯_H`, `N_H`, `c_H`, `ρ_H`.
* C4 `paramB` … `Choice`: the parameter system of `prop:params`.
* E11 / E14d outputs `ArithLowerBound`, `AnalyticUpperBound`.

All conventions: namespace `CatalanCore.Elliptic`; `ℕ` contains `0`; logarithms are natural.
-/

@[expose] public section

namespace CatalanCore.Elliptic

open PeriodPair

/-! ### C0. Integral model -/

/-- The integral-model package over `PeriodPair`.

`L` is the given lattice with rational `g₂, g₃`. `Λ = d⁻¹ L` is the scaled lattice, with
`g₂(Λ) = −4A`, `g₃(Λ) = −4B`, `4A³ + 27B² ≠ 0` (`lem:integral`, rows E03). `Ω > 0` generates
`Λ ∩ ℝ` and `Λ = ℤΩ + ℤΩ′` with `Y = Im Ω′ > 0` (row E21). `a ∈ {0,1,2,3}` has `f(a) ≠ 0`,
and `z_Q ∉ Λ` has `℘_Λ(z_Q) = a` (rows E20, E22(i)). -/
structure IntegralModel where
  /-- the given lattice -/
  L : PeriodPair
  /-- the scaling denominator -/
  d : ℕ
  d_pos : 1 ≤ d
  /-- the scaled lattice `Λ = d⁻¹ L` -/
  Λ : PeriodPair
  lattice_scale : ∀ z : ℂ, z ∈ Λ.lattice ↔ (d : ℂ) * z ∈ L.lattice
  A : ℤ
  B : ℤ
  g₂_eq : Λ.g₂ = -4 * (A : ℂ)
  g₃_eq : Λ.g₃ = -4 * (B : ℂ)
  disc_ne : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0
  /-- the generator of the real points, `Ω > 0` -/
  Ω : ℝ
  Ω_pos : 0 < Ω
  /-- the second basis vector, `Y = Im Ω′ > 0` -/
  Ω' : ℂ
  Y_pos : 0 < Ω'.im
  lattice_basis : Λ.lattice = Submodule.span ℤ {(Ω : ℂ), Ω'}
  real_points : ∀ z ∈ Λ.lattice, z.im = 0 → ∃ n : ℤ, z = (n : ℂ) * (Ω : ℂ)
  /-- the chart point `a`, one of `0, 1, 2, 3` with `f(a) ≠ 0` -/
  a : ℤ
  a_range : 0 ≤ a ∧ a ≤ 3
  fa_ne : a ^ 3 + A * a + B ≠ 0
  /-- the polar point: `℘_Λ(z_Q) = a`, `z_Q ∉ Λ` -/
  zQ : ℂ
  zQ_not_mem : zQ ∉ Λ.lattice
  wp_zQ : Λ.weierstrassP zQ = (a : ℂ)

/-- `Y = Im Ω′`. -/
def IntegralModel.Y (M : IntegralModel) : ℝ := M.Ω'.im

/-- The cubic `f(X) = X³ + A X + B` of the integral model. -/
noncomputable def IntegralModel.cubic (M : IntegralModel) : Polynomial ℤ :=
  Polynomial.X ^ 3 + Polynomial.C M.A * Polynomial.X + Polynomial.C M.B

/-- `r_* = 2(Ω + 1)`. -/
def IntegralModel.rStar (M : IntegralModel) : ℝ := 2 * (M.Ω + 1)

/-- `χ = 2π / (Ω Y)`. -/
noncomputable def IntegralModel.chi (M : IntegralModel) : ℝ := 2 * Real.pi / (M.Ω * M.Y)

/-! ### C1. Origin chart and series -/

/-- The origin chart of `y² = x³ + A x + B` at `x = a`: `u = (x − a)⁻¹`, `t = y (x − a)⁻²`,
`t² = F(u)` (eq:quartic). -/
structure OriginChart where
  A : ℤ
  B : ℤ
  a : ℤ
  disc_ne : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0
  fa_ne : a ^ 3 + A * a + B ≠ 0

/-- `F(U) = U + 3a U² + (3a² + A) U³ + f(a) U⁴ ∈ ℤ[U]` (eq:quartic). -/
noncomputable def OriginChart.F (c : OriginChart) : Polynomial ℤ :=
  Polynomial.X + Polynomial.C (3 * c.a) * Polynomial.X ^ 2 +
    Polynomial.C (3 * c.a ^ 2 + c.A) * Polynomial.X ^ 3 +
    Polynomial.C (c.a ^ 3 + c.A * c.a + c.B) * Polynomial.X ^ 4

/-- The chart attached to an integral model. -/
def IntegralModel.chart (M : IntegralModel) : OriginChart where
  A := M.A
  B := M.B
  a := M.a
  disc_ne := M.disc_ne
  fa_ne := M.fa_ne

/-- The series `U(T), L(T)` of `prop:chart`, over `ℚ`: `U(0) = 0`, `F(U(T)) = T²`, `L(0) = 0`,
`L′(T) F′(U(T)) = −1`. That `U ∈ ℤ[[T]]`, `−1/F′(U) ∈ ℤ[[T]]` and `n [T^n] L ∈ ℤ` are theorems
(producer A2), not part of the type. -/
structure OriginSeries (c : OriginChart) where
  U : PowerSeries ℚ
  L : PowerSeries ℚ
  U_zero : PowerSeries.constantCoeff U = 0
  U_eq : Polynomial.aeval U c.F = (PowerSeries.X : PowerSeries ℚ) ^ 2
  L_zero : PowerSeries.constantCoeff L = 0
  L_deriv : PowerSeries.derivative L * Polynomial.aeval U (Polynomial.derivative c.F) = -1

/-! ### C2. Multiplier (theta form) -/

/-- The multiplier package of W05-THETA §8 over a lattice `Λ`, real period `Ω`, second period `Ω′`
and chart point `a`. `F₀ = ψ̃ = Θ_Λ²(℘ − a)`, `F₁ = ψ̃ u = Θ_Λ²`, `F₂ = ψ̃² t = ½ Θ_Λ⁴ ℘′`.
`transport` is `lem:mult`(b) in theta form. -/
structure Multiplier (Λ : PeriodPair) (Ω : ℝ) (Ω' : ℂ) (a : ℤ) where
  F₀ : ℂ → ℂ
  F₁ : ℂ → ℂ
  F₂ : ℂ → ℂ
  diff₀ : Differentiable ℂ F₀
  diff₁ : Differentiable ℂ F₁
  diff₂ : Differentiable ℂ F₂
  per₀ : ∀ z, F₀ (z + Ω) = F₀ z
  per₁ : ∀ z, F₁ (z + Ω) = F₁ z
  per₂ : ∀ z, F₂ (z + Ω) = F₂ z
  transport₀ : ∀ (n : ℤ) (z : ℂ), F₀ (z + n * Ω') =
    F₀ z * Complex.exp (-(2 * Real.pi * Complex.I / Ω) * (2 * n * z + n ^ 2 * Ω'))
  transport₁ : ∀ (n : ℤ) (z : ℂ), F₁ (z + n * Ω') =
    F₁ z * Complex.exp (-(2 * Real.pi * Complex.I / Ω) * (2 * n * z + n ^ 2 * Ω'))
  transport₂ : ∀ (n : ℤ) (z : ℂ), F₂ (z + n * Ω') =
    F₂ z * Complex.exp (-(2 * Real.pi * Complex.I / Ω) * (2 * n * z + n ^ 2 * Ω')) ^ 2
  /-- `F₁ = ψ̃ u` off the lattice and off `℘ = a` -/
  eq_u : ∀ z : ℂ, z ∉ Λ.lattice → Λ.weierstrassP z ≠ (a : ℂ) →
    F₁ z = F₀ z * (Λ.weierstrassP z - a)⁻¹
  /-- `F₂ = ψ̃² t` off the lattice and off `℘ = a`, with `t = (℘′/2) u²` -/
  eq_t : ∀ z : ℂ, z ∉ Λ.lattice → Λ.weierstrassP z ≠ (a : ℂ) →
    F₂ z = F₀ z ^ 2 * (Λ.derivWeierstrassP z / 2 * ((Λ.weierstrassP z - a)⁻¹) ^ 2)
  ne_zero : F₀ 0 ≠ 0

namespace Multiplier

variable {Λ : PeriodPair} {Ω : ℝ} {Ω' : ℂ} {a : ℤ}

/-- The closed rectangle `{x + iy : 0 ≤ x ≤ Ω, 0 ≤ y ≤ Y}`. -/
def rect (Ω Y : ℝ) : Set ℂ := {z | 0 ≤ z.re ∧ z.re ≤ Ω ∧ 0 ≤ z.im ∧ z.im ≤ Y}

/-- `χ = 2π / (Ω Y)`, with `Y = Im Ω′`. -/
noncomputable def chi (_ : Multiplier Λ Ω Ω' a) : ℝ := 2 * Real.pi / (Ω * Ω'.im)

/-- `S_* = max {1, sup |F₀|, sup |F₁|, sup |F₂|}` over the rectangle (finite since the `F_i` are
continuous and the rectangle is compact; finiteness is a theorem of the producer). -/
noncomputable def Sstar (M : Multiplier Λ Ω Ω' a) : ℝ :=
  max 1 (sSup ((fun z => max (max ‖M.F₀ z‖ ‖M.F₁ z‖) ‖M.F₂ z‖) '' rect Ω Ω'.im))

/-- `r_* = 2(Ω + 1)`. -/
def rStar (_ : Multiplier Λ Ω Ω' a) : ℝ := 2 * (Ω + 1)

/-- `C_Λ = log S_* + log⁺(1/|ψ̃(0)|) + χ (r_* + Y)²` (`thm:analytic`). -/
noncomputable def CLam (M : Multiplier Λ Ω Ω' a) : ℝ :=
  Real.log M.Sstar + Real.log (max 1 ‖M.F₀ 0‖⁻¹) + M.chi * (M.rStar + Ω'.im) ^ 2

/-- The growth statement of `lem:growth` (strip form), with `g̃ = F₀^{D−k−2b} F₁^k F₂^b`.
It is a `Prop` to be proved by the producer (row E08). -/
def GrowthBound (M : Multiplier Λ Ω Ω' a) : Prop :=
  ∀ (D k b : ℕ), k + 2 * b ≤ D → ∀ z : ℂ,
    ‖M.F₀ z ^ (D - k - 2 * b) * M.F₁ z ^ k * M.F₂ z ^ b‖ ≤
      M.Sstar ^ D * Real.exp (D * M.chi * (|z.im| + Ω'.im) ^ 2)

end Multiplier

/-- The multiplier package of an integral model. -/
abbrev IntegralModel.Mult (M : IntegralModel) : Type :=
  Multiplier M.Λ M.Ω M.Ω' M.a

/-! ### C3. Weights, rows, columns, packet matrix -/

/-- Weights `w₀, v₀, θ` and `w₁, …, w_m` of `§"Weights, rows and columns"` (`thm:epa` allows
positive rational `w_i`; the paper's `w_i = ⌈log q_i⌉` is the integer case). -/
structure Weights (m : ℕ) where
  w₀ : ℚ
  v₀ : ℚ
  θ : ℚ
  w : Fin m → ℚ
  w₀_pos : 0 < w₀
  v₀_pos : 0 < v₀
  θ_pos : 0 < θ
  θ_lt_one : θ < 1
  w_pos : ∀ i, 0 < w i

/-- Column indices `(k, b, α)`, `b ∈ {0,1}`: the monomials `u^k t^b Z^α` of `ℱ_H`. -/
abbrev ColIdx (m : ℕ) : Type := ℕ × Fin 2 × (Fin m → ℕ)

namespace Weights

variable {m : ℕ} (W : Weights m)

/-- `W(β) = Σ_i w_i β_i`. -/
def wt (β : Fin m → ℕ) : ℚ := ∑ i, W.w i * (β i : ℚ)

/-- Row weights `(v₀, w₁/θ, …, w_m/θ)` on `ℕ^{1+m}` (index `0` is the exponent `s` of `T`;
the shape of OAI `rowWeights`). -/
noncomputable def rowWeights : Fin (m + 1) → ℝ :=
  Fin.cases (W.v₀ : ℝ) (fun i => (W.w i : ℝ) / (W.θ : ℝ))

/-- `𝒥_H = {(s, β) ∈ ℕ^{1+m} : v₀ s + W(β)/θ < H}` (the shape of OAI `strictWeightedSimplex`). -/
noncomputable def rowSet (H : ℝ) : Finset (Fin (m + 1) → ℕ) := by
  classical
  exact ((Fintype.piFinset (fun i => Finset.range (⌊H / W.rowWeights i⌋₊ + 1))).filter
    (fun a => ∑ i, W.rowWeights i * (a i : ℝ) < H))

/-- `J_H = |𝒥_H|`. -/
noncomputable def J (H : ℝ) : ℕ := (W.rowSet H).card

/-- The finite set of column indices of `ℱ_H`: `(k, b, α)` with `2w₀(k + 2b) + W(α) ≤ H`
(condition (S)). -/
noncomputable def colSet (H : ℝ) : Finset (ColIdx m) := by
  classical
  exact (((Finset.range (⌊H / (2 * (W.w₀ : ℝ))⌋₊ + 1)) ×ˢ (Finset.univ : Finset (Fin 2)) ×ˢ
      Fintype.piFinset (fun i => Finset.range (⌊H / (W.w i : ℝ)⌋₊ + 1))).filter
    (fun c => 2 * (W.w₀ : ℝ) * ((c.1 : ℝ) + 2 * (c.2.1.val : ℝ)) + (W.wt c.2.2 : ℝ) ≤ H))

/-- The set `𝒯_H = {ξ ∈ ℕ^m : W(ξ) ≤ H}`. -/
noncomputable def tSet (H : ℝ) : Finset (Fin m → ℕ) := by
  classical
  exact ((Fintype.piFinset (fun i => Finset.range (⌊H / (W.w i : ℝ)⌋₊ + 1))).filter
    (fun ξ => (W.wt ξ : ℝ) ≤ H))

/-- `N_H = |{ξ ∈ ℕ^m : W(ξ) ≤ a₀ H}|`. -/
noncomputable def NH (a₀ H : ℝ) : ℕ := (W.tSet (a₀ * H)).card

end Weights

/-- Rows `r = (j, s, β)` with `0 ≤ j < K` and `(s, β) ∈ 𝒥_H`; `r.2.1 0 = s`, `r.2.1 i.succ = β_i`. -/
abbrev Row {m : ℕ} (W : Weights m) (K : ℕ) (H : ℝ) : Type := Fin K × ↥(W.rowSet H)

/-- Columns of the packet matrix: the monomials `(k, b, α)` of `ℱ_H`. -/
abbrev Col {m : ℕ} (W : Weights m) (H : ℝ) : Type := ↥(W.colSet H)

/-- The centres `c_{ji} = j p_i / q_i` (`§"Weights, rows and columns"`). -/
def gridCentres {m : ℕ} (K : ℕ) (p : Fin m → ℤ) (q : Fin m → ℕ) : Fin K → Fin m → ℚ :=
  fun j i => (j : ℚ) * (p i : ℚ) / (q i : ℚ)

/-- The packet entry (eq:entry) for centres `cen`, centre index `j`, row exponents `r = (s, β)` and
column `c = (k, b, α)`:
`C(α, β) · [T^s] (U^k T^b ∏_i (c_{ji} + L)^{α_i − β_i})`, with `C(α, β) = ∏_i C(α_i, β_i)`
(zero unless `β ≤ α`, so the truncated subtraction is harmless). -/
noncomputable def packetEntry {m K : ℕ} {ch : OriginChart} (s : OriginSeries ch)
    (cen : Fin K → Fin m → ℚ) (j : Fin K) (r : Fin (m + 1) → ℕ) (c : ColIdx m) : ℚ :=
  (∏ i : Fin m, ((c.2.2 i).choose (r i.succ) : ℚ)) *
    PowerSeries.coeff (r 0)
      (s.U ^ c.1 * PowerSeries.X ^ c.2.1.val *
        ∏ i : Fin m, (PowerSeries.C (cen j i) + s.L) ^ (c.2.2 i - r i.succ))

/-- The packet matrix `A` (eq:entry), rows `Row W K H`, columns `Col W H`, over `ℚ`. -/
noncomputable def packetMatrix {m K : ℕ} (W : Weights m) {ch : OriginChart} (s : OriginSeries ch)
    (cen : Fin K → Fin m → ℚ) (H : ℝ) : Matrix (Row W K H) (Col W H) ℚ :=
  fun ρ c => packetEntry s cen ρ.1 ρ.2.1 c.1

namespace Weights

variable {m : ℕ} (W : Weights m)

/-- `M = K J_H`. -/
noncomputable def M (K : ℕ) (H : ℝ) : ℕ := K * W.J H

/-- `b̄ = (1/(M H)) Σ_{(j,s,β)} W(β)`. -/
noncomputable def bbar (K : ℕ) (H : ℝ) : ℝ :=
  (∑ ρ : Row W K H, (W.wt (fun i => ρ.2.1 i.succ) : ℝ)) / ((W.M K H : ℝ) * H)

end Weights

/-- `κ = (log 2)/4` (`lem:collision`). -/
noncomputable def collisionKappa : ℝ := Real.log 2 / 4

/-- `s₀ = 2^{−1/2}` (`lem:collision`). -/
noncomputable def collisionS0 : ℝ := (Real.sqrt 2)⁻¹

/-- `ρ_H = (log M + κ − log(1 − s₀)) / H` (`lem:collision`). -/
noncomputable def rhoH (M H : ℝ) : ℝ :=
  (Real.log M + collisionKappa - Real.log (1 - collisionS0)) / H

/-- `c_H = κ γ² M / (H N_H)` (`thm:analytic`). -/
noncomputable def cH {m : ℕ} (W : Weights m) (K : ℕ) (a₀ γ H : ℝ) : ℝ :=
  collisionKappa * γ ^ 2 * (W.M K H : ℝ) / (H * (W.NH a₀ H : ℝ))

/-- The limit `c_∞ = κ γ² K θ^m / ((m+1) v₀ a₀^m)` of `cor:limits`. -/
noncomputable def cInfty {m : ℕ} (W : Weights m) (K : ℕ) (a₀ γ : ℝ) : ℝ :=
  collisionKappa * γ ^ 2 * K * (W.θ : ℝ) ^ m / ((m + 1) * (W.v₀ : ℝ) * a₀ ^ m)

/-- `e_H = C_Λ K²/H + ρ_H + log|𝒯_H| / H` (`thm:analytic`). -/
noncomputable def eH {m : ℕ} (W : Weights m) (K : ℕ) (CLam H : ℝ) : ℝ :=
  CLam * (K : ℝ) ^ 2 / H + rhoH (W.M K H : ℝ) H + Real.log ((W.tSet H).card : ℝ) / H

/-- E11 output (`prop:arith`): `log|Δ| / (M H) ≥ −(1 − b̄) − E_ar`, `E_ar = c₀ F₀ / v₀`. -/
def ArithLowerBound (logΔ M H bbar Ear : ℝ) : Prop :=
  -(1 - bbar) - Ear ≤ logΔ / (M * H)

/-- E14d output (`thm:analytic`): `log|Δ| / (M H) ≤ E_an + e_H + max {−c_H, −ν (a₀(1−γ) − b̄)}`. -/
def AnalyticUpperBound (logΔ M H bbar Ean eH cH ν a₀ γ : ℝ) : Prop :=
  logΔ / (M * H) ≤ Ean + eH + max (-cH) (-(ν * (a₀ * (1 - γ) - bbar)))

/-! ### C4. Parameter system (`prop:params`) -/

namespace Params

/-- `b = 5/6 − 1/(2ν)`. -/
def b (ν : ℚ) : ℚ := 5 / 6 - 1 / (2 * ν)
/-- `h = (ν − 3)/(4ν)`. -/
def h (ν : ℚ) : ℚ := (ν - 3) / (4 * ν)
/-- `θ = 1 − h`. -/
def θ (ν : ℚ) : ℚ := 1 - h ν
/-- `a₀ = 1 − b h`. -/
def a₀ (ν : ℚ) : ℚ := 1 - b ν * h ν
/-- `γ = h (ν − 3)/(12 ν)`. -/
def γ (ν : ℚ) : ℚ := h ν * (ν - 3) / (12 * ν)
/-- `F₀ = 1/θ`. -/
def F₀ (ν : ℚ) : ℚ := 1 / θ ν
/-- `g = ν (a₀(1 − γ) − θ) − (1 − θ)`. -/
def g (ν : ℚ) : ℚ := ν * (a₀ ν * (1 - γ ν) - θ ν) - (1 - θ ν)

end Params

/-- The rational choice of `c₁, c₂` after `lem:abc`:
`a₀/θ < c₁ < a₀^{−1/2}` (as `c₁² a₀ < 1`) and `a₀ < c₂ < min {c₁^{−2}, c₁ θ}`
(as `c₂ c₁² < 1`, `c₂ < c₁ θ`). -/
structure ParamChoice (ν : ℚ) where
  c₁ : ℚ
  c₂ : ℚ
  c₁_pos : 0 < c₁
  c₁_lo : Params.a₀ ν / Params.θ ν < c₁
  c₁_hi : c₁ ^ 2 * Params.a₀ ν < 1
  c₂_lo : Params.a₀ ν < c₂
  c₂_hi₁ : c₂ * c₁ ^ 2 < 1
  c₂_hi₂ : c₂ < c₁ * Params.θ ν

namespace ParamChoice

variable {ν : ℚ} (P : ParamChoice ν)

/-- `K = ⌊c₁^m⌋` (eq:choice). -/
def K (m : ℕ) : ℕ := ⌊P.c₁ ^ m⌋₊
/-- `w₀ = c₂^{−m}` (eq:choice). -/
def w₀ (m : ℕ) : ℚ := (P.c₂ ^ m)⁻¹
/-- `v₀ = 4 K θ^m w₀` (eq:choice). -/
def v₀ (m : ℕ) : ℚ := 4 * (P.K m : ℚ) * Params.θ ν ^ m * P.w₀ m

end ParamChoice

end CatalanCore.Elliptic
