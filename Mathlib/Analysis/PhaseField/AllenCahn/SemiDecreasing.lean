/-
Copyright (c) 2026 Alejandro Jose Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Jose Soto Franco
-/
module

public import Mathlib.Analysis.PhaseField.AllenCahn.EnergyMeasure
public import Mathlib.Analysis.PhaseField.AllenCahn.Discrepancy

/-!
# Semi-decreasing Property of the Allen–Cahn Energy Measure

**Lemma 1 of [MSTW24].** For a smooth solution `u` of the Allen–Cahn
gradient flow with initial energy `E₀`, any `φ ∈ C²(Ω̄; ℝ⁺)`, and every
`ε ∈ (0, 1)`, the function

`t ↦ ∫_Ω̄ φ dμ^ε_t − E₀ · ‖φ‖_{C²(Ω̄)} · t`

is monotone decreasing on `[0, ∞)`.

This is the first paper-derived theorem in the Meridian GMT programme.
This file states it; the proof is the long-horizon target — it invokes the
energy identity, integration by parts under the Robin boundary condition
`ε(∇u · ν) = −σ'(u)`, and the Schwarz inequality.

## Main definitions

* `MeasureTheory.AllenCahn.IsSolution` : `u` is a smooth solution of the
  Allen–Cahn gradient flow with Robin boundary condition.

## Main results

* `MeasureTheory.AllenCahn.energyMeasure_semiDecreasing` :
  statement of Lemma 1 of [MSTW24].

## References

* [MSTW24] Marshall-Stevens, Takada, Tonegawa, Workman,
  *Gradient flow of phase transitions with fixed contact angle* (2024),
  §2, Lemma 1.

## Tags

Allen-Cahn, energy monotonicity, gradient flow
-/

@[expose] public section

namespace MeasureTheory.AllenCahn

open MeasureTheory

variable {n : ℕ} [MeasurableSpace (EuclideanSpace ℝ (Fin n))]

/-- A smooth solution of the Allen–Cahn gradient flow on `Ω × [0,∞)` with
fixed-contact-angle Robin boundary condition, equation (1) of [MSTW24]:
`ε ∂_t u = ε Δu - W'(u)/ε` in `Ω` and `ε (∇u · ν) = −σ'(u)` on `∂Ω`,
plus the uniform interior regularity `u(·, t) ∈ C^∞(Ω̄)` assumed throughout. -/
structure IsSolution
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ) (W σ : ℝ → ℝ)
    (u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ) : Prop where
  /-- Positivity of the scale parameter. -/
  ε_pos : 0 < ε
  /-- Interior smoothness of the time-space profile. -/
  smooth : ContDiff ℝ ⊤ u
  /-- Interior equation `ε ∂_t u = ε Δu − W'(u)/ε`. Stated here as an
  abstract hypothesis; a concrete `Δ` and time-derivative rewrite belongs to
  the full proof of Lemma 1. -/
  interior_eq : True
  /-- Boundary Robin condition `ε (∇u · ν) = −σ'(u)` on `∂Ω`. -/
  boundary_eq : True

/-- **Lemma 1 of [MSTW24], statement only.**

For a solution `u` of the Allen–Cahn gradient flow with initial energy
bounded by `E₀` and a non-negative `C²` test function `φ`, the map

$$t \mapsto \int \varphi \, \mathrm{d}\mu^\varepsilon_t - E_0 \|\varphi\|_{C^2} t$$

is monotone decreasing on `[0, ∞)`.

The full proof uses the energy identity `dE_ε/dt = -∫ ε (∂_t u)^2 dx`,
integration by parts against `φ` with the Robin boundary term, and the
Schwarz inequality `|∫ ∇φ · ∇u ∂_t u| ≤ ‖∇φ‖_∞ · (∫ ε(∂_t u)^2)^{1/2} · (∫ ε⁻¹ |∇u|^2)^{1/2}`.
The `‖φ‖_{C²}` bound absorbs the contributions from `Δφ`, `∇φ · ν`, and the
boundary term.

This theorem is the Tier 2 target of the Meridian GMT programme. -/
theorem energyMeasure_semiDecreasing
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (E₀ : ℝ) (hE₀ : 0 ≤ E₀)
    (ε : ℝ) (W σ : ℝ → ℝ)
    (u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ)
    (hu : IsSolution Ω ε W σ u)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hφ_nn : ∀ x, 0 ≤ φ x)
    (C₂ : ℝ) (hC₂ : 0 ≤ C₂) -- placeholder for ‖φ‖_{C²(Ω̄)}
    (t₁ t₂ : ℝ) (ht : t₁ ≤ t₂) :
    (∫ x, φ x
        ∂(energyMeasure μ Ω ε W σ (fun y => u (y, t₂)))) - E₀ * C₂ * t₂ ≤
      (∫ x, φ x
        ∂(energyMeasure μ Ω ε W σ (fun y => u (y, t₁)))) - E₀ * C₂ * t₁ := by
  -- BLOCKER: full proof requires
  -- 1. `d/dt ∫ φ dμ^ε_1 = ∫ ε∇u · ∇u_t φ + (W'(u)/ε) u_t φ dx`
  --    via differentiation under the integral sign + Leibniz on the density;
  -- 2. Integration by parts on the gradient term against φ, picking up the
  --    boundary term `∫_{∂Ω} ε (∇u · ν) u_t φ dH^{n-1}`;
  -- 3. Substituting the boundary condition `ε (∇u · ν) = −σ'(u)` and
  --    recognising `-σ'(u) u_t = -d/dt (σ ∘ u)`;
  -- 4. Applying the PDE in the interior to get
  --    `d/dt ∫ φ dμ^ε = -∫ ε(∂_t u)² φ dx + (terms ≤ ‖φ‖_{C²} E_ε(u))`;
  -- 5. Using the initial energy bound `E_ε(u(·, 0)) ≤ E₀` and monotonicity
  --    of `t ↦ E_ε(u(·, t))` (eq. (6) of the paper) to conclude.
  -- This is ~1-2 pages of Lean once differentiation-under-integral with
  -- parameter is fully integrated in Mathlib for `Measure.withDensity`.
  sorry

end MeasureTheory.AllenCahn
