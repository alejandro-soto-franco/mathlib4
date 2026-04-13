/-
Copyright (c) 2026 Alejandro Jose Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Jose Soto Franco
-/
module

public import Mathlib.MeasureTheory.Geometric.Varifold.FirstVariation

/-!
# Stationary Varifolds

A varifold `V` is *stationary* if `δV(X) = 0` for every compactly supported
`C¹` vector field `X`. Stationary varifolds are the weak-solution class for
the minimal-surface equation and the starting point of Allard regularity
theory.

## Main definitions

* `MeasureTheory.Varifold.IsStationary` : the predicate.

## Main results

* `MeasureTheory.Varifold.IsStationary.of_measure_zero` : the zero varifold is
  stationary.

## References

* Simon, *Lectures on Geometric Measure Theory*, §17.
* Allard, *On the First Variation of a Varifold*.

## Tags

varifold, stationary, minimal surface, first variation
-/

@[expose] public section

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace Varifold

variable {k : ℕ}

/-- A varifold `V` is *stationary* if its first variation annihilates every
compactly supported `C¹` vector field. -/
def IsStationary (V : Varifold E k) : Prop :=
  ∀ X : E → E, ContDiff ℝ 1 X → HasCompactSupport X → V.firstVariation X = 0

/-- The zero varifold is stationary. -/
theorem IsStationary.of_measure_zero (V : Varifold E k) (h : V.measure = 0) :
    V.IsStationary := by
  -- BLOCKER: `firstVariation` integrates against `V.measure = 0`;
  -- unfolds once `firstVariation` lands.
  sorry

end Varifold

end MeasureTheory
