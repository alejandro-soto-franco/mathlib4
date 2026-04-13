/-
Copyright (c) 2026 Alejandro Jose Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Jose Soto Franco
-/
module

public import Mathlib.MeasureTheory.Geometric.Varifold.Stationary
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Interior Monotonicity for Stationary Varifolds

Classical theorem of Allard: if `V` is a stationary `k`-varifold in an open
set `Ω ⊆ E`, then for every interior point `x₀` the density ratio

$$\Theta(V, x_0, r) = \frac{\|V\|(B(x_0, r))}{\omega_k r^k}$$

is monotone non-decreasing in `r` on `(0, \mathrm{dist}(x_0, \partial\Omega))`.

This file states the monotonicity formula; the proof is a long-horizon
formalisation target.

## Main definitions

* `MeasureTheory.unitBallVolume` : `ω_k = π^{k/2} / Γ(k/2 + 1)`.
* `MeasureTheory.Varifold.densityRatio` : the density quotient.

## Main results

* `MeasureTheory.Varifold.monotonicity_of_stationary` : statement-only.

## References

* Simon, *Lectures on Geometric Measure Theory*, §17.
* Allard, *On the First Variation of a Varifold*, §5.

## Tags

varifold, monotonicity, density, stationary
-/

@[expose] public section

namespace MeasureTheory

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The volume of the unit ball in `EuclideanSpace ℝ (Fin k)`:
`ω_k = π^(k/2) / Γ(k/2 + 1)`. -/
noncomputable def unitBallVolume (_k : ℕ) : ℝ :=
  -- BLOCKER: `Real.pi ^ (k / 2 : ℝ) / Real.Gamma (k / 2 + 1)`;
  -- half-integer Gamma identities.
  sorry

namespace Varifold

variable {k : ℕ}

/-- Density ratio of a varifold at a point `x₀` at scale `r`. -/
noncomputable def densityRatio (V : Varifold E k) (x₀ : E) (r : ℝ) : ENNReal :=
  V.mass (Metric.ball x₀ r) / ENNReal.ofReal (unitBallVolume k * r ^ k)

/-- **Allard's monotonicity formula (statement only).**

For a stationary `k`-varifold `V` in an open set `Ω ⊆ E`, the density ratio
`r ↦ Θ(V, x₀, r)` is monotone non-decreasing on `(0, dist(x₀, ∂Ω))`. -/
theorem monotonicity_of_stationary
    (V : Varifold E k)
    {Ω : Set E} (hΩ : IsOpen Ω) (hV : V.IsStationary)
    {x₀ : E} (hx : x₀ ∈ Ω) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂)
    (hr₂ : Metric.ball x₀ r₂ ⊆ Ω) :
    V.densityRatio x₀ r₁ ≤ V.densityRatio x₀ r₂ := by
  sorry -- BLOCKER: apply first variation to the radial test field
        -- `X(x) = φ(|x - x₀|/r) · (x - x₀)`; derive the ODE on mass ratio and integrate.
        -- This is the long-horizon formalisation target.

end Varifold

end MeasureTheory
