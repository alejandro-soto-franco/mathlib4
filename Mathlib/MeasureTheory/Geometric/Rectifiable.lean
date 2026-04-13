/-
Copyright (c) 2026 Alejandro Jose Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Jose Soto Franco
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Countably `k`-Rectifiable Sets

A set `S` in a finite-dimensional real inner-product space `E` is *countably
`k`-rectifiable* if, up to an `ℋᵏ`-null set, it is the union of countably many
Lipschitz images of subsets of `EuclideanSpace ℝ (Fin k)`. This is the
geometric-measure-theoretic generalisation of a `k`-dimensional submanifold and
the substrate on which integer-rectifiable varifolds are defined.

## Main definitions

* `MeasureTheory.CountablyRectifiable k S` : the predicate.

## Main results

* `MeasureTheory.CountablyRectifiable.subset` : hereditary under subset.
* `MeasureTheory.CountablyRectifiable.iUnion` : closed under countable union.

## References

* Simon, *Lectures on Geometric Measure Theory*, Chapter 3.
* Federer, *Geometric Measure Theory*, §3.2.

## Tags

rectifiable, Hausdorff measure, geometric measure theory
-/

@[expose] public section

namespace MeasureTheory

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A set `S ⊆ E` is *countably `k`-rectifiable* if, up to an `ℋᵏ`-null set, it
is the union of countably many Lipschitz images of subsets of
`EuclideanSpace ℝ (Fin k)`. -/
def CountablyRectifiable (k : ℕ) (S : Set E) : Prop :=
  ∃ (N : Set E) (A : ℕ → Set (EuclideanSpace ℝ (Fin k))) (f : ℕ → EuclideanSpace ℝ (Fin k) → E),
    (Measure.hausdorffMeasure (k : ℝ) : Measure E) N = 0 ∧
    (∀ i, ∃ L : NNReal, LipschitzOnWith L (f i) (A i)) ∧
    S ⊆ N ∪ ⋃ i, (f i) '' (A i)

/-- Subsets of countably-rectifiable sets are countably rectifiable. -/
theorem CountablyRectifiable.subset {k : ℕ} {S T : Set E}
    (hT : CountablyRectifiable k T) (hST : S ⊆ T) : CountablyRectifiable k S := by
  sorry -- BLOCKER: unpack hT, restrict covering to S; needs `measure_mono_null` application.

/-- Countable unions of countably-rectifiable sets are countably rectifiable. -/
theorem CountablyRectifiable.iUnion {k : ℕ} {S : ℕ → Set E}
    (hS : ∀ n, CountablyRectifiable k (S n)) : CountablyRectifiable k (⋃ n, S n) := by
  sorry -- BLOCKER: diagonal reindexing over ℕ × ℕ via `Nat.pairEquiv`.

end MeasureTheory
