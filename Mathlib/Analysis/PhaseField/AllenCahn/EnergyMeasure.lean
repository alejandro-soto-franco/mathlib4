/-
Copyright (c) 2026 Alejandro Jose Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Jose Soto Franco
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Allen–Cahn Energy Measures

Given the Allen–Cahn phase-transition setting of Marshall-Stevens, Takada,
Tonegawa & Workman (2024), we define the three Radon measures associated to
a smooth function `u : Ω̄ × [0,∞) → ℝ` solving the ε-parametrised gradient flow:

`μ^ε_{t,1}(φ) = ∫_Ω φ · (ε|∇u|²/2 + W(u)/ε) dx`,
`μ^ε_{t,2}(φ) = ∫_{∂Ω} φ · σ(u) dH^{n-1}`,
`μ^ε_t = μ^ε_{t,1} + μ^ε_{t,2}`.

These are equation (3) of paper [MSTW24]; they are the substrate for Theorem 1,
Theorem 2, Theorem 3, and the Ilmanen boundary monotonicity formula.

## Main definitions

* `MeasureTheory.AllenCahn.interiorEnergyDensity` : the integrand
  `ε|∇u|²/2 + W(u)/ε` at a point.
* `MeasureTheory.AllenCahn.interiorEnergyMeasure` : `μ^ε_1` as a
  `Measure (EuclideanSpace ℝ (Fin n))`, defined as Lebesgue-with-density.
* `MeasureTheory.AllenCahn.boundaryEnergyMeasure` : `μ^ε_2`, currently a
  placeholder pending a clean `Measure.restrict` of Hausdorff measure to `∂Ω`.

## References

* [MSTW24] Marshall-Stevens, Takada, Tonegawa, Workman,
  *Gradient flow of phase transitions with fixed contact angle* (2024),
  §1.2, equation (3).
* Modica, *The gradient theory of phase transitions and the minimal interface
  criterion*, Arch. Rat. Mech. Anal. 98 (1987).

## Tags

Allen-Cahn, phase field, energy measure, Gamma-convergence
-/

@[expose] public section

namespace MeasureTheory.AllenCahn

open MeasureTheory Real

variable {n : ℕ}

/-- The Allen–Cahn interior energy density

$$e_\varepsilon(u)(x) = \frac{\varepsilon |\nabla u(x)|^2}{2} + \frac{W(u(x))}{\varepsilon},$$

at a point `x ∈ ℝⁿ`, for a `C¹` profile `u` and a double-well potential `W`. -/
noncomputable def interiorEnergyDensity
    (ε : ℝ) (W : ℝ → ℝ) (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ε * ‖fderiv ℝ u x‖ ^ 2 / 2 + W (u x) / ε

variable [MeasurableSpace (EuclideanSpace ℝ (Fin n))]

/-- The interior Allen–Cahn energy measure `μ^ε_1` on `ℝⁿ`, obtained from a
chosen ambient (Lebesgue) measure `λ` by multiplying with the energy density
restricted to `Ω`. -/
noncomputable def interiorEnergyMeasure
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ) (W : ℝ → ℝ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  μ.withDensity
    (fun x => Ω.indicator (fun x => ENNReal.ofReal (interiorEnergyDensity ε W u x)) x)

/-- The boundary Allen–Cahn energy measure `μ^ε_2`. **Placeholder**: a proper
definition needs the `(n-1)`-dimensional surface measure on `∂Ω`, multiplied by
`σ(u)`. Pending a clean surface-measure API in Mathlib this is left as `0`. -/
noncomputable def boundaryEnergyMeasure
    (_Ω : Set (EuclideanSpace ℝ (Fin n))) (_σ : ℝ → ℝ)
    (_u : EuclideanSpace ℝ (Fin n) → ℝ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  0
  -- BLOCKER: should be `Hausdorff^{n-1} ⌞ ∂Ω` with density `σ ∘ u`;
  -- requires Mathlib surface-measure API.

/-- Total Allen–Cahn energy measure `μ^ε = μ^ε_1 + μ^ε_2`. -/
noncomputable def energyMeasure
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ) (W σ : ℝ → ℝ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  interiorEnergyMeasure μ Ω ε W u + boundaryEnergyMeasure Ω σ u

set_option linter.unusedSectionVars false in
/-- Non-negativity of the interior energy density when `W ≥ 0` and `ε > 0`. -/
theorem interiorEnergyDensity_nonneg
    (ε : ℝ) (hε : 0 < ε) (W : ℝ → ℝ) (hW : ∀ s, 0 ≤ W s)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ interiorEnergyDensity ε W u x := by
  unfold interiorEnergyDensity
  have h1 : 0 ≤ ε * ‖fderiv ℝ u x‖ ^ 2 / 2 :=
    div_nonneg (mul_nonneg hε.le (sq_nonneg _)) (by norm_num)
  have h2 : 0 ≤ W (u x) / ε := div_nonneg (hW _) hε.le
  linarith

end MeasureTheory.AllenCahn
