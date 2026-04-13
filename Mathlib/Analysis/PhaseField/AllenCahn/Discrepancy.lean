/-
Copyright (c) 2026 Alejandro Jose Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Jose Soto Franco
-/
module

public import Mathlib.Analysis.PhaseField.AllenCahn.EnergyMeasure

/-!
# Allen–Cahn Discrepancy Function

The *discrepancy* of a smooth Allen–Cahn profile `u` at scale `ε > 0` is

$$\xi^\varepsilon(u)(x) = \frac{\varepsilon |\nabla u(x)|^2}{2} - \frac{W(u(x))}{\varepsilon}.$$

This is the quantity whose vanishing in the `ε → 0` limit (assumption (A5) of
[MSTW24]) distinguishes good limiting behaviour from boundary concentration.

## Main definitions

* `MeasureTheory.AllenCahn.discrepancy` : `ξ^ε(u)(x)`.
* `MeasureTheory.AllenCahn.discrepancyMeasure` : `ξ^ε(u)` as a Radon
  measure on `Ω ⊆ ℝⁿ`, obtained by `Measure.withDensity` against the
  ambient Lebesgue measure restricted to `Ω`.

## Main results

* `MeasureTheory.AllenCahn.interiorEnergy_eq_discrepancy_add_twice_potential` :
  `e_ε(u) = ξ^ε(u) + 2 W(u)/ε`, the algebraic identity used throughout the
  paper.

## References

* [MSTW24] Marshall-Stevens, Takada, Tonegawa, Workman, §1.2.
* [Ilm93] Ilmanen, *Convergence of the Allen-Cahn equation to Brakke's motion
  by mean curvature* (J. Diff. Geom. 1993), §3.

## Tags

Allen-Cahn, discrepancy, phase field
-/

@[expose] public section

namespace MeasureTheory.AllenCahn

variable {n : ℕ}

/-- Allen–Cahn discrepancy `ξ^ε(u)(x) = ε|∇u(x)|²/2 − W(u(x))/ε`. -/
noncomputable def discrepancy
    (ε : ℝ) (W : ℝ → ℝ) (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ε * ‖fderiv ℝ u x‖ ^ 2 / 2 - W (u x) / ε

/-- The interior energy density decomposes as discrepancy plus twice the
normalised potential term:
`e_ε(u) = ξ^ε(u) + 2 W(u)/ε`. -/
theorem interiorEnergy_eq_discrepancy_add_twice_potential
    (ε : ℝ) (W : ℝ → ℝ) (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    interiorEnergyDensity ε W u x = discrepancy ε W u x + 2 * (W (u x) / ε) := by
  unfold interiorEnergyDensity discrepancy
  ring

/-- Symmetric companion: the gradient-energy term is the arithmetic mean of
`e_ε(u)` and `ξ^ε(u)`. -/
theorem gradient_term_eq_average
    (ε : ℝ) (W : ℝ → ℝ) (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ε * ‖fderiv ℝ u x‖ ^ 2 / 2 =
      (interiorEnergyDensity ε W u x + discrepancy ε W u x) / 2 := by
  unfold interiorEnergyDensity discrepancy
  ring

variable [MeasurableSpace (EuclideanSpace ℝ (Fin n))]

/-- The discrepancy as a Radon measure `ξ^ε_t · dL^n ⌞ Ω` on
`EuclideanSpace ℝ (Fin n)`. Encoded via `Measure.withDensity` against the
restriction of a chosen ambient (Lebesgue) measure to `Ω`. -/
noncomputable def discrepancyMeasure
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ) (W : ℝ → ℝ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (μ.restrict Ω).withDensity (fun x => ENNReal.ofReal (discrepancy ε W u x))

end MeasureTheory.AllenCahn
