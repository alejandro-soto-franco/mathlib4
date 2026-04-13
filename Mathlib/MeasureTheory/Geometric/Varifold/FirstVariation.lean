/-
Copyright (c) 2026 Alejandro Jose Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Jose Soto Franco
-/
module

public import Mathlib.MeasureTheory.Geometric.Varifold.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# First Variation of a Varifold

The *first variation* of a `k`-varifold `V` under a compactly supported `C¹`
vector field `X : E → E` is

$$\delta V(X) = \int \mathrm{div}_S X(x) \, \mathrm{d}V(x, S),$$

where `div_S X(x)` is the divergence of `X` along the `k`-plane `S`. The
pairing `δV : C¹_c(E, E) → ℝ` is linear; a varifold is *stationary* iff its
first variation vanishes identically.

## Main definitions

* `MeasureTheory.tangentialDivergence` : `div_S X(x)` along a plane.
* `MeasureTheory.Varifold.firstVariation` : the pairing `δV(X)`.

## Main results

* `MeasureTheory.Varifold.firstVariation_add` : additivity in the vector field.
* `MeasureTheory.Varifold.firstVariation_smul` : homogeneity in the vector field.

## References

* Simon, *Lectures on Geometric Measure Theory*, §16.

## Tags

varifold, first variation, tangential divergence
-/

@[expose] public section

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Tangential divergence of a `C¹` vector field `X : E → E` along a `k`-plane
`S` at a point `x`: the trace of the orthogonal projection of `fderiv ℝ X x`
onto `S`. -/
noncomputable def tangentialDivergence {k : ℕ}
    (X : E → E) (_x : E) (_S : Plane E k) : ℝ :=
  sorry -- BLOCKER: `LinearMap.trace ℝ S ((orthogonalProjection S).comp (fderiv ℝ X x))`;
        -- needs the restriction of an operator to a subspace and its trace.

namespace Varifold

variable {k : ℕ}

/-- The first variation `δV(X)` of a varifold `V` against a vector field `X`. -/
noncomputable def firstVariation (V : Varifold E k) (X : E → E) : ℝ :=
  sorry -- BLOCKER: `∫ (tangentialDivergence X x S) ∂V.measure`; needs
        -- `MeasureTheory.integral` with the product space + finiteness hypothesis.

/-- Additivity of the first-variation pairing in the vector-field argument. -/
theorem firstVariation_add (V : Varifold E k) (X Y : E → E)
    (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 1 Y) :
    V.firstVariation (X + Y) = V.firstVariation X + V.firstVariation Y := by
  sorry -- BLOCKER: linearity of `fderiv` + linearity of integral.

/-- Homogeneity of the first-variation pairing in the vector-field argument. -/
theorem firstVariation_smul (V : Varifold E k) (c : ℝ) (X : E → E)
    (hX : ContDiff ℝ 1 X) :
    V.firstVariation (fun x => c • X x) = c * V.firstVariation X := by
  sorry -- BLOCKER: linearity of `fderiv` + linearity of integral.

end Varifold

end MeasureTheory
