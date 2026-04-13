/-
Copyright (c) 2026 Alejandro Jose Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Jose Soto Franco
-/
module

public import Mathlib.MeasureTheory.Geometric.Varifold.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

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
`S` at a point `x`: the trace of the composition of `fderiv ℝ X x` with the
orthogonal projection onto `S`. Equivalently `∑ᵢ ⟨DX(x) eᵢ, eᵢ⟩` for any
orthonormal basis `{eᵢ}` of `S`. -/
noncomputable def tangentialDivergence {k : ℕ}
    (X : E → E) (x : E) (S : Plane E k) : ℝ :=
  LinearMap.trace ℝ E
    ((S.1.starProjection : E →L[ℝ] E).toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap)

namespace Varifold

variable {k : ℕ}

/-- The integrand of the first variation: `(x, S) ↦ div_S X(x)`. -/
noncomputable def firstVariationIntegrand (X : E → E) : E × Plane E k → ℝ :=
  fun p => tangentialDivergence X p.1 p.2

/-- The first variation `δV(X) = ∫ div_S X(x) dV(x, S)`. -/
noncomputable def firstVariation (V : Varifold E k) (X : E → E) : ℝ :=
  ∫ p, firstVariationIntegrand X p ∂V.measure

/-- Integrability hypothesis bundled for reuse: the first-variation integrand
is integrable with respect to the varifold measure. For a `C¹_c` vector field
this follows from boundedness of `fderiv X` on its compact support and the
finiteness of `V.measure`. -/
def FirstVariationIntegrable (V : Varifold E k) (X : E → E) : Prop :=
  Integrable (firstVariationIntegrand X) V.measure

omit [MeasurableSpace E] [BorelSpace E] in
/-- The first-variation integrand is additive pointwise in the vector field. -/
theorem firstVariationIntegrand_add (X Y : E → E) (p : E × Plane E k)
    (hX : DifferentiableAt ℝ X p.1) (hY : DifferentiableAt ℝ Y p.1) :
    firstVariationIntegrand (X + Y) p =
      firstVariationIntegrand X p + firstVariationIntegrand Y p := by
  simp only [firstVariationIntegrand, tangentialDivergence]
  rw [fderiv_add hX hY]
  rw [ContinuousLinearMap.coe_add, LinearMap.comp_add, map_add]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The first-variation integrand is homogeneous pointwise in the vector field. -/
theorem firstVariationIntegrand_smul (c : ℝ) (X : E → E) (p : E × Plane E k)
    (hX : DifferentiableAt ℝ X p.1) :
    firstVariationIntegrand (fun y => c • X y) p = c * firstVariationIntegrand X p := by
  simp only [firstVariationIntegrand, tangentialDivergence]
  rw [show (fun y => c • X y) = c • X from rfl, fderiv_const_smul hX c]
  rw [ContinuousLinearMap.coe_smul, LinearMap.comp_smul, map_smul, smul_eq_mul]

omit [BorelSpace E] in
/-- Additivity of the first-variation pairing in the vector-field argument. -/
theorem firstVariation_add (V : Varifold E k) (X Y : E → E)
    (hIX : V.FirstVariationIntegrable X) (hIY : V.FirstVariationIntegrable Y)
    (hX : Differentiable ℝ X) (hY : Differentiable ℝ Y) :
    V.firstVariation (X + Y) = V.firstVariation X + V.firstVariation Y := by
  have hpt : ∀ p : E × Plane E k,
      firstVariationIntegrand (X + Y) p =
        firstVariationIntegrand X p + firstVariationIntegrand Y p :=
    fun p => firstVariationIntegrand_add X Y p (hX p.1) (hY p.1)
  simp only [firstVariation]
  rw [show (fun p => firstVariationIntegrand (X + Y) p) =
        (fun p => firstVariationIntegrand X p + firstVariationIntegrand Y p)
      from funext hpt]
  exact integral_add hIX hIY

omit [BorelSpace E] in
/-- Homogeneity of the first-variation pairing in the vector-field argument. -/
theorem firstVariation_smul (V : Varifold E k) (c : ℝ) (X : E → E)
    (hX : Differentiable ℝ X) :
    V.firstVariation (fun x => c • X x) = c * V.firstVariation X := by
  have hpt : ∀ p : E × Plane E k,
      firstVariationIntegrand (fun y => c • X y) p = c * firstVariationIntegrand X p :=
    fun p => firstVariationIntegrand_smul c X p (hX p.1)
  simp only [firstVariation]
  rw [show (fun p => firstVariationIntegrand (fun y => c • X y) p) =
        (fun p => c * firstVariationIntegrand X p)
      from funext hpt]
  exact integral_const_mul c _

end Varifold

end MeasureTheory
