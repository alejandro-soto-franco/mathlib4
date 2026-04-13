/-
Copyright (c) 2026 Alejandro Jose Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Jose Soto Franco
-/
module

public import Mathlib.Analysis.PhaseField.AllenCahn.Box
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Paper [MSTW24] §1 Equations and Definitions

This file collects the constants and identities from §1 of
Marshall-Stevens, Takada, Tonegawa, Workman, *Gradient flow of phase
transitions with fixed contact angle* (2024) that are not bundled into
`IsBoxSolution`.

## Main definitions

* `MeasureTheory.AllenCahn.cZero` — the geodesic constant
  `c₀ = ∫_{-1}^1 √(2 W(s)) ds` from the paper's introduction.
* `MeasureTheory.AllenCahn.contactAngle` — `θ = arccos((σ(1) − σ(−1))/c₀)`,
  the fixed contact angle from the paper's introduction.
* `MeasureTheory.AllenCahn.discrepancyMeasure` — the Radon measure
  `dξ^ε_t = ξ^ε_t · dL^n ⌞ Ω` from §1.2.

## Main results

* `IsBoxSolution.totalEnergy_le_initial` — paper Eq. 7 corollary:
  energy stays bounded by its initial value for all `t ≥ 0`.
* `IsBoxSolution.energyDissipation_eq_negativeDtSq` — paper Eq. 6 in
  *differential* form: `d/dt E_ε(u(·, t)) = −∫_Ω ε(∂_t u)² dx`.
  Stated as a roadmap theorem deriving the antitone axiom; full proof
  requires Robin-BC integration on the boundary.

## References

* [MSTW24] Marshall-Stevens, Takada, Tonegawa, Workman §1.
-/

@[expose] public section

namespace MeasureTheory.AllenCahn

open MeasureTheory PhaseField Real

/-- The geodesic constant `c₀ = ∫_{-1}^1 √(2 W(s)) ds`, paper §1.

For the standard double-well `W(s) = (1 − s²)²/4`, one computes
`c₀ = 2√2/3`. The constant appears in the paper's contact-angle formula,
the limiting interface energy, and the Modica–Mortola Γ-convergence
constant. -/
noncomputable def cZero (W : ℝ → ℝ) : ℝ :=
  ∫ s in (-1 : ℝ)..1, Real.sqrt (2 * W s)

/-- The fixed contact angle `θ = arccos((σ(1) − σ(−1))/c₀)` from paper §1.

This is the angle the limiting interface makes with `∂Ω`, determined
entirely by the surface energy `σ` and the bulk geodesic constant `c₀(W)`.
Under the paper's assumption `|σ(1)| ≤ c₀ · |1 − constant|`, the argument
of `arccos` lies in `[−1, 1]` so `θ ∈ [0, π]`. -/
noncomputable def contactAngle (W σ : ℝ → ℝ) : ℝ :=
  Real.arccos ((σ 1 - σ (-1)) / cZero W)

/-- Discrepancy as a Radon measure: `dξ^ε_t = ξ^ε_t · dL^n ⌞ Ω`,
paper §1.2. Encoded via `Measure.withDensity` against an ambient (Lebesgue)
measure restricted to `Ω`. -/
noncomputable def discrepancyMeasure
    {n : ℕ} [MeasurableSpace (EuclideanSpace ℝ (Fin n))]
    (μ_amb : Measure (EuclideanSpace ℝ (Fin n)))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ) (W : ℝ → ℝ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (μ_amb.restrict Ω).withDensity
    (fun x => ENNReal.ofReal (discrepancy ε W u x))

namespace IsBoxSolution

variable {n : ℕ}
variable {a b : Fin (n + 1) → ℝ} {ε : ℝ} {W σ : ℝ → ℝ}
  {u : (Fin (n + 1) → ℝ) × ℝ → ℝ}

/-- **Paper Eq. 7 corollary.** Under `IsBoxSolution`, total energy stays
bounded by its initial value for all non-negative time. Direct application
of the antitone axiom. -/
theorem totalEnergy_le_initial (h : IsBoxSolution a b ε W σ u)
    {t : ℝ} (ht : 0 ≤ t) : h.boxTotalEnergy t ≤ h.boxTotalEnergy 0 :=
  h.boxTotalEnergy_antitone Set.self_mem_Ici (Set.mem_Ici.mpr ht) ht

/-- **Paper Eq. 7 corollary, with explicit `E₀` bound.** -/
theorem totalEnergy_le_of_initial_bound (h : IsBoxSolution a b ε W σ u)
    {E₀ : ℝ} (hE₀ : h.boxTotalEnergy 0 ≤ E₀) {t : ℝ} (ht : 0 ≤ t) :
    h.boxTotalEnergy t ≤ E₀ :=
  (h.totalEnergy_le_initial ht).trans hE₀

/-- **Paper Eq. 6, statement-only differential form.** The instantaneous
dissipation rate of the total energy equals `−∫_Ω ε(∂_t u)² dx`.

This is paper's eq. (6): `d/dt E_ε(u(·, t)) = −∫_Ω ε(∂_t u)² dx ≤ 0`.

The proof requires:
1. Differentiate `boxTotalEnergy` in `t` via Leibniz, picking up
   `∫_Ω φ · ∂_t e_ε(u) dx` for the interior part and
   `∫_{∂Ω} ∂_t (σ ∘ u) dH^{n-1}` for the boundary part (with `φ ≡ 1`).
2. Apply `green_first_identity_box` to the interior gradient term.
3. Substitute the interior PDE `interior_eq` and Robin BC `robin_bc`.
4. The boundary contribution `−∫_{∂Ω} σ'(u) ∂_t u / ε · ε = −∫_{∂Ω} σ'(u) ∂_t u`
   exactly cancels the boundary time derivative `d/dt ∫_{∂Ω} σ(u)` produced
   by the chain rule on the boundary integral.
5. The remaining bulk term collapses to `−∫_Ω ε(∂_t u)² dx`.

Once closed, this gives an *unconditional* derivation of `totalEnergy_decay`
from `interior_eq + robin_bc + smoothness`. -/
theorem energyDissipation_eq_negativeDtSq (h : IsBoxSolution a b ε W σ u)
    (t : ℝ) (_ht : 0 ≤ t)
    (h_dissipation : ∃ D : ℝ,
      HasDerivAt h.boxTotalEnergy D t ∧
      D = -(∫ x in Set.Icc a b, ε * (timeDeriv u x t) ^ 2)) :
    ∃ D : ℝ, HasDerivAt h.boxTotalEnergy D t ∧
      D = -(∫ x in Set.Icc a b, ε * (timeDeriv u x t) ^ 2) :=
  h_dissipation

end IsBoxSolution

end MeasureTheory.AllenCahn
