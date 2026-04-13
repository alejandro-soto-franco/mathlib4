/-
Copyright (c) 2026 Alejandro Jose Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Jose Soto Franco
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Modica Geodesic Constant and Fixed Contact Angle

This file defines the two scalar constants associated with the Allen–Cahn
energy with surface-tension boundary potential `σ`:

* `MeasureTheory.AllenCahn.modicaConstant` (`c₀`), the one-dimensional
  geodesic `∫_{-1}^1 √(2 W(s)) \,\mathrm{d}s` in the double-well metric.
  This is the sharp-interface surface tension in the Modica–Mortola
  Γ-convergence theorem.
* `MeasureTheory.AllenCahn.contactAngle` (`θ`), the angle
  `arccos((σ(1) − σ(−1))/c₀)` that the limiting `{u = +1}` interface makes
  with the domain boundary.

## Main definitions

* `modicaConstant W` : the double-well geodesic constant `c₀`.
* `contactAngle W σ` : the fixed contact angle `θ`.

## References

* L. Modica, *The gradient theory of phase transitions and the minimal
  interface criterion*, Arch. Rat. Mech. Anal. **98** (1987).
* L. Cahn, *Critical point wetting*, J. Chem. Phys. **66** (1977).

## Tags

Allen-Cahn, Modica-Mortola, surface tension, contact angle
-/

@[expose] public section

namespace MeasureTheory.AllenCahn

open MeasureTheory Real

/-- The Modica geodesic constant `c₀ = ∫_{-1}^1 √(2 W(s)) ds`.

For the standard double-well potential `W(s) = (1 − s²)²/4`,
`c₀ = 2√2/3`. Geometrically, `c₀` is the length of the geodesic from
`s = −1` to `s = +1` in the Riemannian metric `2 W(s) \,\mathrm{d}s^2` on
the state space, and is the surface tension of the sharp-interface limit
in the Modica–Mortola theorem. -/
noncomputable def modicaConstant (W : ℝ → ℝ) : ℝ :=
  ∫ s in (-1 : ℝ)..1, Real.sqrt (2 * W s)

/-- The fixed contact angle `θ = arccos((σ(1) − σ(−1))/c₀)` determined by
the surface-tension potential `σ` and the Modica constant `c₀(W)`.

Under the paper's smallness assumption `|σ(1) − σ(−1)| ≤ c₀`, the argument
of `arccos` lies in `[−1, 1]` so `θ ∈ [0, π]`. -/
noncomputable def contactAngle (W σ : ℝ → ℝ) : ℝ :=
  Real.arccos ((σ 1 - σ (-1)) / modicaConstant W)

end MeasureTheory.AllenCahn
