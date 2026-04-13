/-
Copyright (c) 2026 Alejandro Jose Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Jose Soto Franco
-/
module

public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.MeasureTheory.Geometric.Rectifiable

/-!
# Varifolds

A `k`-*varifold* on a finite-dimensional real inner-product space `E` is a
Radon measure on `E × Gr(k, E)`, where `Gr(k, E)` is the Grassmannian of
`k`-dimensional linear subspaces of `E`. Pending a dedicated `Grassmannian`
type in Mathlib, we represent a `k`-plane as `{ S : Submodule ℝ E // finrank ℝ S = k }`.

This is the v0.1 foundation: the structure, total mass, and support. The first
variation and stationary-varifold theory live in
`Mathlib.MeasureTheory.Geometric.Varifold.FirstVariation` and
`Mathlib.MeasureTheory.Geometric.Varifold.Stationary`.

## Main definitions

* `MeasureTheory.Plane k E` : `k`-dimensional linear subspaces of `E` as a subtype.
* `MeasureTheory.Varifold E k` : the structure itself.
* `MeasureTheory.Varifold.mass` : total mass on a set.
* `MeasureTheory.Varifold.support` : spatial support.

## References

* Simon, *Lectures on Geometric Measure Theory*, Chapter 4.
* Allard, *On the First Variation of a Varifold*, Ann. of Math. 1972.

## Tags

varifold, geometric measure theory, Radon measure
-/

@[expose] public section

namespace MeasureTheory

open Module

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E]

/-- A `k`-plane in `E`: a linear subspace of dimension exactly `k`. Placeholder
for a proper `Grassmannian` type; see the Mathlib roadmap. -/
def Plane (k : ℕ) : Type _ :=
  { S : Submodule ℝ E // finrank ℝ S = k }

/-- The trivial measurable structure on `Plane E k` for v0.1. To be refined
once a smooth-manifold structure on the Grassmannian lands in Mathlib. -/
instance (k : ℕ) : MeasurableSpace (Plane E k) := ⊤

/-- A `k`-varifold on `E` is a Radon measure on `E × Plane E k` with finite
total mass. -/
structure Varifold (k : ℕ) where
  /-- Underlying Radon measure. -/
  measure : Measure (E × Plane E k)
  /-- Finiteness of total mass. -/
  finite : IsFiniteMeasure measure

namespace Varifold

variable {E}
variable {k : ℕ}

/-- The mass `‖V‖(Ω)` of a varifold on a set `Ω ⊆ E`, obtained by integrating
out the plane coordinate. -/
noncomputable def mass (V : Varifold E k) (Ω : Set E) : ENNReal :=
  V.measure (Ω ×ˢ (Set.univ : Set (Plane E k)))

/-- The support of a varifold is the support of its spatial projection. -/
noncomputable def support (V : Varifold E k) : Set E :=
  sorry -- BLOCKER: `(V.measure.map Prod.fst).support` once `Measure.support` is a clean API.

/-- A varifold with zero underlying measure has zero mass on every set. -/
@[simp]
theorem mass_zero_of_zero (V : Varifold E k) (Ω : Set E)
    (h : V.measure = 0) : V.mass Ω = 0 := by
  sorry -- BLOCKER: unfold `mass` and apply `Measure.zero_apply` on the rewritten measure.

end Varifold

end MeasureTheory
