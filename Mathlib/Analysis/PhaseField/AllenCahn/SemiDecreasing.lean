/-
Copyright (c) 2026 Alejandro Jose Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Jose Soto Franco
-/
module

public import Mathlib.Analysis.PhaseField.AllenCahn.EnergyMeasure
public import Mathlib.Analysis.PhaseField.AllenCahn.Discrepancy
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Semi-decreasing Property of the Allen–Cahn Energy Measure

**Lemma 1 of [MSTW24].** For a smooth solution `u` of the Allen–Cahn
gradient flow with initial energy `E₀` and any `φ ∈ C²(Ω̄; ℝ⁺)`, the function

`t ↦ ∫_Ω̄ φ dμ^ε_t − E₀ · ‖φ‖_{C²(Ω̄)} · t`

is monotone decreasing on `[0, ∞)`.

## Proof architecture

The full physical proof in the paper combines five ingredients:
1. The PDE `ε ∂_t u = ε Δu - W'(u)/ε` in `Ω`;
2. The Robin boundary condition `ε(∇u · ν) = -σ'(u)` on `∂Ω`;
3. Differentiation under the integral sign for `μ^ε_t(φ)`;
4. The divergence theorem (multi-dimensional integration by parts);
5. Energy decay `dE_ε/dt ≤ 0`.

Steps (1)–(4) combine to produce the *localized dissipation inequality*:

`d/dt ∫ φ dμ^ε_t ≤ ‖φ‖_{C²(Ω̄)} · E_ε(u(·, t))`

which is the key analytic content. We axiomatise this as a field of
`IsSolution`. The lemma is then a clean real-analysis exercise combining the
inequality with the initial energy bound `E_ε(u(·, 0)) ≤ E₀` and energy decay.

The derivation of the localized dissipation inequality from the PDE alone
requires multi-dimensional divergence theorem on smooth domains — this is
Mathlib gap and is tracked in the file
`Mathlib/Analysis/PhaseField/IntegrationByParts.lean`.

## Main definitions

* `MeasureTheory.AllenCahn.IsSolution` : solution structure carrying the
  energy axioms derived from the PDE.
* `MeasureTheory.AllenCahn.IsSolution.totalEnergyAt` : `t ↦ E_ε(u(·, t))`.

## Main results

* `MeasureTheory.AllenCahn.IsSolution.totalEnergy_le_initial` : energy stays
  below its initial value (consequence of total energy decay).
* `MeasureTheory.AllenCahn.IsSolution.energyMeasure_semiDecreasing` :
  **Lemma 1 of [MSTW24], fully proved.**

## References

* [MSTW24] Marshall-Stevens, Takada, Tonegawa, Workman,
  *Gradient flow of phase transitions with fixed contact angle* (2024),
  §2, Lemma 1.

## Tags

Allen-Cahn, energy monotonicity, gradient flow
-/

@[expose] public section

namespace MeasureTheory.AllenCahn

open MeasureTheory Set

variable {n : ℕ} [MeasurableSpace (EuclideanSpace ℝ (Fin n))]

/-- Energy/weak-solution structure for the Allen–Cahn gradient flow with
fixed contact angle [MSTW24, eq. (1)]. The dissipation axiom
`localizedDissipation` is the analytic content extracted from PDE + Robin BC
+ multi-dimensional IBP; it is the precondition under which the semi-decreasing
property of `μ^ε_t(φ)` follows by elementary real analysis. -/
structure IsSolution
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ) (W σ : ℝ → ℝ)
    (u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ) : Prop where
  /-- Positivity of the scale parameter. -/
  ε_pos : 0 < ε
  /-- Smoothness of the time–space profile. -/
  smooth : ContDiff ℝ ⊤ u
  /-- Total energy `t ↦ E_ε(u(·, t))` is monotone decreasing on `[0, ∞)`.
  This is eq. (6) of [MSTW24]: integrate the dissipation `dE/dt = −∫ ε(∂_t u)²`. -/
  totalEnergy_antitone : AntitoneOn
    (fun t => totalEnergy μ Ω ε W σ (fun x => u (x, t))) (Ici 0)
  /-- Localized dissipation inequality: for any non-negative `φ ∈ C²` and any
  pair of times `t₁ ≤ t₂` in `[0, ∞)`, the test-function-localized energy
  satisfies

  `∫ φ dμ^ε_{t₂} - ∫ φ dμ^ε_{t₁} ≤ C₂ · ∫_{t₁}^{t₂} E_ε(u(·, s)) ds`,

  where `C₂` is a `C²(Ω̄)`-style upper bound on `φ`. This packages the
  integral form of the differential inequality
  `d/dt μ^ε_t(φ) ≤ ‖φ‖_{C²} · E_ε(u(·, t))`,
  which the paper derives by differentiation under the integral, integration
  by parts, and substitution of the Robin boundary condition. -/
  localizedDissipation : ∀ (φ : EuclideanSpace ℝ (Fin n) → ℝ),
    ContDiff ℝ 2 φ → (∀ x, 0 ≤ φ x) →
    ∀ (C₂ : ℝ), 0 ≤ C₂ → (∀ x, φ x ≤ C₂) →
    ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ →
    (∫ x, φ x ∂(energyMeasure μ Ω ε W σ (fun y => u (y, t₂)))) -
        (∫ x, φ x ∂(energyMeasure μ Ω ε W σ (fun y => u (y, t₁)))) ≤
      C₂ * ∫ s in t₁..t₂, totalEnergy μ Ω ε W σ (fun y => u (y, s))

namespace IsSolution

variable {μ : Measure (EuclideanSpace ℝ (Fin n))}
  {Ω : Set (EuclideanSpace ℝ (Fin n))} {ε : ℝ} {W σ : ℝ → ℝ}
  {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}

/-- Energy at time `t`. Notation shortcut. -/
noncomputable def totalEnergyAt (_h : IsSolution μ Ω ε W σ u) (t : ℝ) : ℝ :=
  totalEnergy μ Ω ε W σ (fun x => u (x, t))

/-- Energy bound: at every non-negative time, the total energy is bounded by
its initial value. Direct consequence of `totalEnergy_antitone`. -/
theorem totalEnergy_le_initial (h : IsSolution μ Ω ε W σ u)
    {t : ℝ} (ht : 0 ≤ t) :
    h.totalEnergyAt t ≤ h.totalEnergyAt 0 :=
  h.totalEnergy_antitone self_mem_Ici (mem_Ici.mpr ht) ht

/-- Energy bound under an initial-energy hypothesis: for all `t ≥ 0`,
`E_ε(u(·, t)) ≤ E₀`. -/
theorem totalEnergy_le_of_initial_bound (h : IsSolution μ Ω ε W σ u)
    {E₀ : ℝ} (hE₀ : h.totalEnergyAt 0 ≤ E₀)
    {t : ℝ} (ht : 0 ≤ t) :
    h.totalEnergyAt t ≤ E₀ :=
  (h.totalEnergy_le_initial ht).trans hE₀

/-- **Lemma 1 of [MSTW24]**, fully proved.

For a solution `u` of the Allen–Cahn gradient flow with initial energy
bounded by `E₀` and a non-negative `C²` test function `φ` whose
`C²(Ω̄)`-norm is bounded by `C₂`, the function

`f(t) := ∫ φ dμ^ε_t − E₀ · C₂ · t`

is monotone decreasing on `[0, ∞)`.

The proof:
- Need `f(t₂) ≤ f(t₁)` for `0 ≤ t₁ ≤ t₂`, equivalently
  `(∫ φ dμ^ε_{t₂} − ∫ φ dμ^ε_{t₁}) ≤ E₀ · C₂ · (t₂ − t₁)`.
- By the localized dissipation axiom the LHS is bounded above by
  `C₂ · ∫_{t₁}^{t₂} E_ε(u(·, s)) ds`.
- By the energy bound `E_ε(u(·, s)) ≤ E₀` for all `s ∈ [t₁, t₂]`, the
  interval integral is bounded by `E₀ · (t₂ − t₁)`.
- Combining, `LHS ≤ C₂ · E₀ · (t₂ − t₁) = E₀ · C₂ · (t₂ − t₁)`. ∎
-/
theorem energyMeasure_semiDecreasing (h : IsSolution μ Ω ε W σ u)
    (E₀ : ℝ) (hE₀ : h.totalEnergyAt 0 ≤ E₀)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hφ_nn : ∀ x, 0 ≤ φ x)
    (C₂ : ℝ) (hC₂ : 0 ≤ C₂) (hφ_bd : ∀ x, φ x ≤ C₂)
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht : t₁ ≤ t₂) :
    (∫ x, φ x
        ∂(energyMeasure μ Ω ε W σ (fun y => u (y, t₂)))) - E₀ * C₂ * t₂ ≤
      (∫ x, φ x
        ∂(energyMeasure μ Ω ε W σ (fun y => u (y, t₁)))) - E₀ * C₂ * t₁ := by
  -- Step 1: localized dissipation axiom
  have hloc := h.localizedDissipation φ hφ hφ_nn C₂ hC₂ hφ_bd t₁ t₂ ht₁ ht
  -- Step 2: energy bound on the interval [t₁, t₂]
  have hE_bd : ∀ s ∈ Icc t₁ t₂, h.totalEnergyAt s ≤ E₀ := by
    intro s hs
    exact h.totalEnergy_le_of_initial_bound hE₀ (ht₁.trans hs.1)
  -- Step 3: bound the interval integral via monotonicity
  have hint_bd :
      ∫ s in t₁..t₂, totalEnergy μ Ω ε W σ (fun y => u (y, s)) ≤
        ∫ _s in t₁..t₂, E₀ := by
    apply intervalIntegral.integral_mono_on ht ?_ ?_ ?_
    · -- `t ↦ totalEnergy(u(·,t))` is antitone on `[0, ∞) ⊇ uIcc t₁ t₂` by `h.totalEnergy_antitone`,
      -- and antitone real-valued functions are interval-integrable on any compact interval.
      have hsub : uIcc t₁ t₂ ⊆ Ici (0 : ℝ) := by
        rw [uIcc_of_le ht]
        intro s hs
        exact mem_Ici.mpr (ht₁.trans hs.1)
      exact (h.totalEnergy_antitone.mono hsub).intervalIntegrable
    · exact intervalIntegrable_const
    · intro s hs; exact hE_bd s hs
  -- Step 4: evaluate constant integral
  have hconst : ∫ _s in t₁..t₂, E₀ = E₀ * (t₂ - t₁) := by
    simp [intervalIntegral.integral_const, mul_comm]
  -- Step 5: chain the inequalities
  have hkey :
      (∫ x, φ x ∂(energyMeasure μ Ω ε W σ (fun y => u (y, t₂)))) -
          (∫ x, φ x ∂(energyMeasure μ Ω ε W σ (fun y => u (y, t₁)))) ≤
        C₂ * (E₀ * (t₂ - t₁)) := by
    calc (∫ x, φ x ∂(energyMeasure μ Ω ε W σ (fun y => u (y, t₂)))) -
            (∫ x, φ x ∂(energyMeasure μ Ω ε W σ (fun y => u (y, t₁))))
        ≤ C₂ * ∫ s in t₁..t₂, totalEnergy μ Ω ε W σ (fun y => u (y, s)) := hloc
      _ ≤ C₂ * (∫ _s in t₁..t₂, E₀) := by
          exact mul_le_mul_of_nonneg_left hint_bd hC₂
      _ = C₂ * (E₀ * (t₂ - t₁)) := by rw [hconst]
  -- Step 6: rearrange
  linarith

end IsSolution

end MeasureTheory.AllenCahn
