/-
Copyright (c) 2026 Alejandro Jose Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Jose Soto Franco
-/
module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Integration by Parts on Smooth Domains (roadmap file)

This file states the multi-dimensional integration-by-parts identities required
to derive the localized dissipation inequality
`d/dt μ^ε_t(φ) ≤ ‖φ‖_{C²} · E_ε(u(·, t))` of [MSTW24, Lemma 1] from the raw
Allen–Cahn PDE plus Robin boundary condition. These identities are *not yet in
Mathlib* (Mathlib has the divergence theorem on rectangular boxes — see
`Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean` — but not on general
smooth bounded domains in `ℝⁿ`).

Each statement here is sorry'd with a named blocker; closing them is a
separate Mathlib contribution that, once landed, lets us discharge the
`IsSolution.localizedDissipation` hypothesis by direct calculation.

## Roadmap

1. **`SmoothDomain`** — the structural notion of an open bounded subset of
   `EuclideanSpace ℝ (Fin n)` with smooth boundary, equipped with an outward
   unit normal field `ν : ∂Ω → EuclideanSpace ℝ (Fin n)` and the surface
   measure `H^{n-1} ⌞ ∂Ω`.
2. **`divergence_theorem`** — Gauss–Green formula:
   `∫_Ω div X dx = ∫_{∂Ω} X · ν dH^{n-1}`,
   for `X ∈ C¹(Ω̄, ℝⁿ)`.
3. **`integration_by_parts_scalar`** — IBP for scalar functions:
   `∫_Ω (∇f) · g dx = ∫_{∂Ω} f g · ν dH^{n-1} - ∫_Ω f (div g) dx`,
   the standard consequence used pervasively in PDE.
4. **`green_first_identity`** — Green's first identity:
   `∫_Ω (∇f · ∇g) dx + ∫_Ω f (Δg) dx = ∫_{∂Ω} f (∇g · ν) dH^{n-1}`,
   the precise form invoked in the Allen–Cahn energy calculation.

## References

* Evans, *Partial Differential Equations*, Appendix C.2 (Gauss–Green theorem,
  Green's identities).
* Federer, *Geometric Measure Theory*, §4.5 (Stokes' theorem on rectifiable
  domains).
* Mathlib: `Mathlib.MeasureTheory.Integral.DivergenceTheorem` (box case
  only).

## Tags

divergence theorem, Gauss-Green, integration by parts, Green's identities
-/

@[expose] public section

namespace MeasureTheory

open Set

variable {n : ℕ} [MeasurableSpace (EuclideanSpace ℝ (Fin n))]

/-- A smooth bounded open domain `Ω ⊆ EuclideanSpace ℝ (Fin n)` carries an
outward unit normal field on its topological boundary. This is the minimum
structure required to state the divergence theorem; v0.1 packages it as a
predicate to be refined into a `structure` once the Mathlib API for smooth
boundaries lands. -/
def IsSmoothDomain (Ω : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsOpen Ω ∧ Bornology.IsBounded Ω ∧
  -- BLOCKER: smoothness of `∂Ω` as an `(n-1)`-dimensional submanifold;
  -- requires a Mathlib API for smooth hypersurfaces.
  True

/-- The (formal) outward unit normal field on `∂Ω`. Placeholder until
`Mathlib.Geometry.Manifold` exposes a clean smooth-hypersurface boundary API. -/
noncomputable def outwardNormal (_Ω : Set (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  -- BLOCKER: should return the unit outward normal at `x ∈ ∂Ω`; undefined
  -- (or zero) elsewhere.
  fun _ => 0

/-- Surface measure `H^{n-1} ⌞ ∂Ω`. Placeholder. -/
noncomputable def surfaceMeasure (_Ω : Set (EuclideanSpace ℝ (Fin n))) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  -- BLOCKER: `Hausdorff^{n-1}.restrict (frontier Ω)` once a numerically
  -- packaged variant of `MeasureTheory.Measure.hausdorffMeasure` is in
  -- Mathlib for `(n-1) : ℝ`.
  0

/-- Pointwise divergence of a `C¹` vector field
`X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)`. Defined as
`∑ᵢ ⟨D X(x) eᵢ, eᵢ⟩` for the standard basis. -/
noncomputable def divergence
    (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, fderiv ℝ X x (EuclideanSpace.single i 1) i

/-- Scalar Laplacian `Δf = div(grad f)`. Defined as the trace of the
Hessian. -/
noncomputable def laplacian
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x
    (EuclideanSpace.single i 1)

/-- Pointwise gradient as a function `Fin n → ℝ` underlying an
`EuclideanSpace ℝ (Fin n)`. -/
noncomputable def gradient
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm
    (fun i => fderiv ℝ f x (EuclideanSpace.single i 1))

/-- **Divergence theorem (Gauss–Green) on smooth bounded domains** —
statement only. -/
theorem divergence_theorem
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (_hΩ : IsSmoothDomain Ω)
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (_hX : ContDiff ℝ 1 X) :
    ∫ x in Ω, divergence X x ∂μ =
      ∫ x in frontier Ω, inner ℝ (X x) (outwardNormal Ω x) ∂(surfaceMeasure Ω) := by
  -- BLOCKER: requires (i) the outward normal as a measurable function on
  -- `∂Ω`, (ii) the surface measure `H^{n-1} ⌞ ∂Ω`, (iii) a partition-of-unity
  -- reduction from arbitrary smooth `Ω` to the box case, where Mathlib's
  -- existing `Mathlib.MeasureTheory.Integral.DivergenceTheorem` can be applied.
  sorry

/-- **Integration by parts for scalar–vector pairing** — statement only. -/
theorem integration_by_parts_scalar
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (_hΩ : IsSmoothDomain Ω)
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (_hf : ContDiff ℝ 1 f)
    (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (_hX : ContDiff ℝ 1 X) :
    ∫ x in Ω, inner ℝ (gradient f x) (X x) ∂μ =
      (∫ x in frontier Ω, f x * inner ℝ (X x) (outwardNormal Ω x)
          ∂(surfaceMeasure Ω)) -
        ∫ x in Ω, f x * divergence X x ∂μ := by
  -- BLOCKER: corollary of `divergence_theorem` applied to the product field
  -- `f · X`; standard.
  sorry

/-- **Green's first identity** — statement only. -/
theorem green_first_identity
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (_hΩ : IsSmoothDomain Ω)
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (_hf : ContDiff ℝ 1 f) (_hg : ContDiff ℝ 2 g) :
    (∫ x in Ω, inner ℝ (gradient f x) (gradient g x) ∂μ) +
        ∫ x in Ω, f x * laplacian g x ∂μ =
      ∫ x in frontier Ω, f x * inner ℝ (gradient g x) (outwardNormal Ω x)
        ∂(surfaceMeasure Ω) := by
  -- BLOCKER: apply `integration_by_parts_scalar` with `X = gradient g`
  -- and use `divergence (gradient g) = laplacian g`.
  sorry

end MeasureTheory
