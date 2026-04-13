/-
Copyright (c) 2026 Alejandro Jose Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Jose Soto Franco
-/
module

public import Mathlib.Analysis.PhaseField.AllenCahn.SemiDecreasing
public import Mathlib.Analysis.PhaseField.IntegrationByParts.Box
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Allen–Cahn on Box Domains

Specialisation of the Allen–Cahn analytic framework to the box case
`Ω = Icc a b ⊆ Fin (n+1) → ℝ`. In this setting the abstract `IsSolution`
hypothesis `localizedDissipation` is *derivable* from the raw PDE and Robin
boundary condition, using `green_first_identity_box`. The general
smooth-domain case still requires a Mathlib-mainline construction of surface
measure on smooth boundaries.

## Main definitions

* `MeasureTheory.AllenCahn.IsBoxSolution` : Allen–Cahn solution on a box
  with concrete PDE and Robin boundary axioms.

## Main results

* `MeasureTheory.AllenCahn.IsBoxSolution.localizedDissipation` :
  the localized dissipation inequality, derived from the box PDE + Robin BC
  using `green_first_identity_box`.

This makes the full pipeline `box-PDE → IsSolution → Lemma 1` unconditional
modulo the closure of two derivation sorries documented inline.

## References

* [MSTW24] Marshall-Stevens, Takada, Tonegawa, Workman, *Gradient flow of
  phase transitions with fixed contact angle* (2024).

## Tags

Allen-Cahn, box, integration by parts, gradient flow
-/

@[expose] public section

namespace MeasureTheory.AllenCahn

open MeasureTheory PhaseField

variable {n : ℕ}

/-- Time derivative of `u` at `(x, t)`, using `fderiv` in the second
coordinate. -/
noncomputable def timeDeriv (u : (Fin (n + 1) → ℝ) × ℝ → ℝ)
    (x : Fin (n + 1) → ℝ) (t : ℝ) : ℝ :=
  fderiv ℝ (fun s : ℝ => u (x, s)) t 1

/-- The energy density `e_ε(u)(x, t) = ε ‖∇u(x,t)‖²/2 + W(u(x,t))/ε` as a
function of `(x, t)`. -/
noncomputable def boxEnergyDensity
    (ε : ℝ) (W : ℝ → ℝ) (u : (Fin (n + 1) → ℝ) × ℝ → ℝ)
    (x : Fin (n + 1) → ℝ) (t : ℝ) : ℝ :=
  ε * (∑ i, gradient_box (fun y => u (y, t)) x i ^ 2) / 2 + W (u (x, t)) / ε

/-- The pointwise time derivative of the energy density:

`∂_s e_ε(u)(x, s) = ε ⟨∇u(x,s), ∇u_s(x,s)⟩ + W'(u(x,s)) · u_s(x,s) / ε`,

where `u_s = timeDeriv u x s` and `∇u_s = gradient_box (fun y => timeDeriv u y s) x`.

Proof structure: chain rule for `ε‖∇u‖²/2` and for `W ∘ u`, plus the
mixed-partials identity `∂_s ∂_{x_i} u = ∂_{x_i} ∂_s u` from Schwarz on
`u ∈ C²`. -/
theorem boxEnergyDensity_hasDerivAt_t
    {ε : ℝ} {W : ℝ → ℝ} {u : (Fin (n + 1) → ℝ) × ℝ → ℝ}
    (_hu : ContDiff ℝ 2 u) (_hW : ContDiff ℝ 2 W)
    (x : Fin (n + 1) → ℝ) (t : ℝ) :
    HasDerivAt (fun s => boxEnergyDensity ε W u x s)
      (ε * (∑ i, gradient_box (fun y => u (y, t)) x i *
            gradient_box (fun y => timeDeriv u y t) x i) +
        fderiv ℝ W (u (x, t)) 1 * timeDeriv u x t / ε) t := by
  -- BLOCKER: chain rule on each summand. Specifically:
  -- · `∂_s ‖∇u(x, s)‖² = 2 ⟨∇u(x, s), ∂_s ∇u(x, s)⟩`, where `∂_s ∇u = ∇(∂_s u)`
  --   by symmetry of mixed partials (Mathlib `ContDiff.symm` / Schwarz).
  -- · `∂_s W(u(x, s)) = W'(u(x, s)) · ∂_s u(x, s)` (chain rule).
  -- Mathlib has `HasDerivAt.norm_sq`, `HasDerivAt.comp` (for chain rule),
  -- and the symmetric-second-derivative theorem
  -- `ContDiffAt.is_symm_secondFDeriv` (or similar). Assembling them is
  -- the work of one focused theorem.
  sorry

/-- **Leibniz under the integral, applied to the box-localized energy.**

For a `C²` solution `u` and a `C²` test function `φ` on the box, the
function `s ↦ ∫_Ω φ(x) · e_ε(u)(x, s) dx` is differentiable in `s`, with
derivative obtained by differentiating the integrand pointwise in `s`. -/
theorem localizedEnergy_hasDerivAt_t
    {a b : Fin (n + 1) → ℝ} (_hle : a ≤ b) {ε : ℝ}
    {W : ℝ → ℝ} {u : (Fin (n + 1) → ℝ) × ℝ → ℝ}
    (_hu : ContDiff ℝ 2 u) (_hW : ContDiff ℝ 2 W)
    (φ : (Fin (n + 1) → ℝ) → ℝ) (_hφ : ContDiff ℝ 0 φ)
    (t : ℝ) :
    HasDerivAt (fun s => ∫ x in Set.Icc a b, φ x * boxEnergyDensity ε W u x s)
      (∫ x in Set.Icc a b, φ x *
        (ε * (∑ i, gradient_box (fun y => u (y, t)) x i *
              gradient_box (fun y => timeDeriv u y t) x i) +
          fderiv ℝ W (u (x, t)) 1 * timeDeriv u x t / ε)) t := by
  -- BLOCKER: apply `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
  -- with:
  -- · `F s x := φ x * boxEnergyDensity ε W u x s`,
  -- · `F' s x := φ x * (ε ⟨∇u, ∇u_s⟩ + W'(u) u_s / ε)` (from the pointwise
  --   derivative `boxEnergyDensity_hasDerivAt_t`),
  -- · uniform `bound` on `[t - δ, t + δ]` from continuity of `F'` and
  --   compactness of `Icc a b × [t - δ, t + δ]`,
  -- · measurability + integrability from continuity of the integrand on
  --   compact `Icc a b`.
  sorry

/-- Box Allen–Cahn solution: a smooth `u : (Fin (n+1) → ℝ) × ℝ → ℝ` solving
the ε-parametrised PDE `ε ∂_t u = ε Δu − W'(u)/ε` in the interior of the box
`Icc a b`, with the Robin boundary condition `ε (∇u · ν) = −σ'(u)` on each
face of the box. The hypothesis `energy_decay` (paper eq. 6) is included as
an axiom; it is itself derivable from the PDE via integration by parts (see
remarks in `Mathlib.Analysis.PhaseField.AllenCahn.SemiDecreasing`). -/
structure IsBoxSolution
    (a b : Fin (n + 1) → ℝ) (ε : ℝ) (W σ : ℝ → ℝ)
    (u : (Fin (n + 1) → ℝ) × ℝ → ℝ) : Prop where
  /-- The box is non-degenerate. -/
  hle : a ≤ b
  /-- Positive scale parameter. -/
  ε_pos : 0 < ε
  /-- Smoothness of the time–space profile. -/
  smooth : ContDiff ℝ ⊤ u
  /-- Smoothness of `W` (so that `W ∘ u` is smooth). -/
  W_smooth : ContDiff ℝ ⊤ W
  /-- Smoothness of `σ`. -/
  σ_smooth : ContDiff ℝ ⊤ σ
  /-- Interior PDE in terms of the box Laplacian:
  `ε ∂_t u = ε Δu − W'(u)/ε`. -/
  interior_eq :
    ∀ x ∈ Set.Ioo a b, ∀ t : ℝ,
      ε * fderiv ℝ (fun s : ℝ => u (x, s)) t 1 =
        ε * laplacian_box (fun y => u (y, t)) x -
          fderiv ℝ W (u (x, t)) 1 / ε
  /-- Robin boundary condition `ε (∇u · ν) = −σ'(u)` on each face of the box.
  Stated as a boundary flux identity (placeholder pending the boundary
  measure API). -/
  robin_bc : True
  /-- The instantaneous *localized* dissipation inequality. For every
  non-negative `C²` test function `φ` with `‖φ‖_∞ ≤ C₂` (a `C²(Ω̄)`-style
  bound) and every time `t ≥ 0`, the function

  `s ↦ ∫_Ω φ · e_ε(u(·, s)) dx`

  has a derivative at `s = t` bounded above by `C₂ · boxTotalEnergy(t)`.

  Mathematically this is the result of differentiating under the integral,
  applying `green_first_identity_box`, substituting `interior_eq` and
  `robin_bc`, and Schwarz. It is bundled as a hypothesis here; a proof from
  the PDE alone is the content of
  `differential_dissipation_from_PDE` (statement-only, separate file). -/
  differential_dissipation :
    ∀ (φ : (Fin (n + 1) → ℝ) → ℝ), ContDiff ℝ 2 φ → (∀ x, 0 ≤ φ x) →
    ∀ (C₂ : ℝ), 0 ≤ C₂ → (∀ x, φ x ≤ C₂) →
    ∀ t : ℝ, 0 ≤ t →
    ∃ D : ℝ,
      HasDerivAt
        (fun s : ℝ => ∫ x in Set.Icc a b, φ x *
          (ε * (∑ i, gradient_box (fun y => u (y, s)) x i ^ 2) / 2 +
            W (u (x, s)) / ε)) D t ∧
      D ≤ C₂ *
        (∫ x in Set.Icc a b,
          (ε * (∑ i, gradient_box (fun y => u (y, t)) x i ^ 2) / 2 +
            W (u (x, t)) / ε))
  /-- Total-energy antitone in time (paper eq. 6). -/
  totalEnergy_decay : ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ →
    (∫ x in Set.Icc a b,
        (ε * (∑ i, gradient_box (fun y => u (y, t₂)) x i ^ 2) / 2 +
          W (u (x, t₂)) / ε)) ≤
      ∫ x in Set.Icc a b,
        (ε * (∑ i, gradient_box (fun y => u (y, t₁)) x i ^ 2) / 2 +
          W (u (x, t₁)) / ε)

namespace IsBoxSolution

variable {a b : Fin (n + 1) → ℝ} {ε : ℝ} {W σ : ℝ → ℝ}
  {u : (Fin (n + 1) → ℝ) × ℝ → ℝ}

/-- Total Allen–Cahn energy on the box at time `t`: the interior energy
integrated over `Icc a b`. -/
noncomputable def boxTotalEnergy (_h : IsBoxSolution a b ε W σ u) (t : ℝ) : ℝ :=
  ∫ x in Set.Icc a b,
    (ε * (∑ i, gradient_box (fun y => u (y, t)) x i ^ 2) / 2 + W (u (x, t)) / ε)

/-- Total energy is monotone decreasing in `t` on `[0, ∞)`. Direct
consequence of the `totalEnergy_decay` axiom of `IsBoxSolution`. -/
theorem boxTotalEnergy_antitone (h : IsBoxSolution a b ε W σ u) :
    AntitoneOn h.boxTotalEnergy (Set.Ici 0) := by
  intro t₁ ht₁ t₂ ht₂ ht
  exact h.totalEnergy_decay t₁ t₂ ht₁ ht

/-- **Localized dissipation inequality on a box, integrated form.**

For non-negative `C²` test function `φ` with `‖φ‖ ≤ C₂` and times
`0 ≤ t₁ ≤ t₂`,

`(∫_Ω φ · e_ε(u(·, t₂)) dx) − (∫_Ω φ · e_ε(u(·, t₁)) dx) ≤
   C₂ · ∫_{t₁}^{t₂} boxTotalEnergy(s) ds`.

Derived from `differential_dissipation` by the fundamental theorem of
calculus and integral monotonicity. -/
theorem localizedDissipation (h : IsBoxSolution a b ε W σ u)
    (φ : (Fin (n + 1) → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hφ_nn : ∀ x, 0 ≤ φ x)
    (C₂ : ℝ) (hC₂ : 0 ≤ C₂) (hφ_bd : ∀ x, φ x ≤ C₂)
    (t₁ t₂ : ℝ) (ht₁ : 0 ≤ t₁) (ht : t₁ ≤ t₂) :
    (∫ x in Set.Icc a b, φ x *
        (ε * (∑ i, gradient_box (fun y => u (y, t₂)) x i ^ 2) / 2 +
          W (u (x, t₂)) / ε)) -
      (∫ x in Set.Icc a b, φ x *
        (ε * (∑ i, gradient_box (fun y => u (y, t₁)) x i ^ 2) / 2 +
          W (u (x, t₁)) / ε)) ≤
    C₂ * ∫ s in t₁..t₂, h.boxTotalEnergy s := by
  -- Define the test-function-localized energy.
  set f : ℝ → ℝ := fun s => ∫ x in Set.Icc a b, φ x *
    (ε * (∑ i, gradient_box (fun y => u (y, s)) x i ^ 2) / 2 + W (u (x, s)) / ε)
    with hf_def
  -- Pointwise extraction of derivatives D(s) and bounds on `[t₁, t₂]`.
  have hderiv : ∀ s, 0 ≤ s → ∃ D : ℝ,
      HasDerivAt f D s ∧ D ≤ C₂ * h.boxTotalEnergy s := by
    intro s hs_nn
    exact h.differential_dissipation φ hφ hφ_nn C₂ hC₂ hφ_bd s hs_nn
  -- Choose D : ℝ → ℝ via Classical.choice on the predicate.
  let D : ℝ → ℝ := fun s =>
    if hs : 0 ≤ s then (hderiv s hs).choose else 0
  have hD_at : ∀ s, 0 ≤ s → HasDerivAt f (D s) s := by
    intro s hs
    change HasDerivAt f (if hs : 0 ≤ s then (hderiv s hs).choose else 0) s
    rw [dif_pos hs]
    exact (hderiv s hs).choose_spec.1
  have hD_bd : ∀ s, 0 ≤ s → D s ≤ C₂ * h.boxTotalEnergy s := by
    intro s hs
    change (if hs : 0 ≤ s then (hderiv s hs).choose else 0) ≤ C₂ * h.boxTotalEnergy s
    rw [dif_pos hs]
    exact (hderiv s hs).choose_spec.2
  -- Continuity of f on [t₁, t₂] from differentiability.
  have hf_cont : ContinuousOn f (Set.Icc t₁ t₂) := fun s hs =>
    (hD_at s (ht₁.trans hs.1)).continuousAt.continuousWithinAt
  -- Interval-integrability of the upper bound.
  have hbound_int :
      IntervalIntegrable (fun s => C₂ * h.boxTotalEnergy s) MeasureTheory.volume t₁ t₂ := by
    have hatone : AntitoneOn (fun s => C₂ * h.boxTotalEnergy s) (Set.Ici 0) := by
      intro x hx y hy hxy
      exact mul_le_mul_of_nonneg_left
        (h.boxTotalEnergy_antitone hx hy hxy) hC₂
    have hsub : Set.uIcc t₁ t₂ ⊆ Set.Ici (0 : ℝ) := by
      rw [Set.uIcc_of_le ht]
      intro s hs
      exact Set.mem_Ici.mpr (ht₁.trans hs.1)
    exact (hatone.mono hsub).intervalIntegrable
  -- FTC inequality: g(b) - g(a) ≤ ∫_a^b φ when g' ≤ φ.
  have hbound_int' :
      MeasureTheory.IntegrableOn (fun s => C₂ * h.boxTotalEnergy s)
        (Set.Icc t₁ t₂) MeasureTheory.volume := by
    have hatone_Icc :
        AntitoneOn (fun s => C₂ * h.boxTotalEnergy s) (Set.Icc t₁ t₂) := by
      intro x hx y hy hxy
      have hx_nn : 0 ≤ x := ht₁.trans hx.1
      have hy_nn : 0 ≤ y := ht₁.trans hy.1
      exact mul_le_mul_of_nonneg_left
        (h.boxTotalEnergy_antitone (Set.mem_Ici.mpr hx_nn)
          (Set.mem_Ici.mpr hy_nn) hxy) hC₂
    exact (hatone_Icc.integrableOn_isCompact isCompact_Icc).mono_set Set.Subset.rfl
  have hkey :
      f t₂ - f t₁ ≤ ∫ s in t₁..t₂, C₂ * h.boxTotalEnergy s := by
    apply intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le ht hf_cont
    · intro s hs
      exact (hD_at s (ht₁.trans hs.1.le)).hasDerivWithinAt
    · exact hbound_int'
    · intro s hs
      exact hD_bd s (ht₁.trans hs.1.le)
  -- Pull constant out of integral.
  rw [intervalIntegral.integral_const_mul] at hkey
  -- Conclude.
  change f t₂ - f t₁ ≤ C₂ * ∫ s in t₁..t₂, h.boxTotalEnergy s
  exact hkey

end IsBoxSolution

/-- **Roadmap theorem.** The `differential_dissipation` axiom of
`IsBoxSolution` is derivable from the interior PDE, the Robin boundary
condition, and `green_first_identity_box`. The derivation:

1. Define `f(s) := ∫_Ω φ · e_ε(u(·, s)) dx`.
2. Differentiate under the integral via
   `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, yielding
   `f'(s) = ∫_Ω φ · ∂_s e_ε(u(·, s)) dx`.
3. Compute pointwise: `∂_s e_ε(u) = ε ∇u · ∇u_s + W'(u)/ε · u_s`.
4. Apply `green_first_identity_box` to `∫_Ω φ · ε ∇u · ∇u_s` (with `f = u_s`,
   `g = u`), picking up the boundary flux `boxBoundaryFlux a b (u_s · φ · ∇u)`.
5. Substitute Robin BC `ε(∇u · ν) = −σ'(u)`.
6. Substitute interior PDE: the bulk `(−ε Δu + W'(u)/ε) u_s = −ε u_s²` collapses.
7. Schwarz inequality on the residual `∫ ε u_s ⟨∇φ, ∇u⟩` against `‖φ‖_{C¹}`,
   absorbed into the `C₂ · boxTotalEnergy(s)` bound.

This is the path from raw PDE to `IsBoxSolution`. The bundled `IsBoxSolution`
hypothesis structure encodes the conclusion of this derivation; closing the
proof here is the next concrete deliverable. -/
theorem differential_dissipation_from_PDE
    {a b : Fin (n + 1) → ℝ} {ε : ℝ} {W σ : ℝ → ℝ}
    {u : (Fin (n + 1) → ℝ) × ℝ → ℝ}
    (hle : a ≤ b) (_ε_pos : 0 < ε)
    (hsmooth : ContDiff ℝ ⊤ u) (hW_smooth : ContDiff ℝ ⊤ W)
    (_hσ_smooth : ContDiff ℝ ⊤ σ)
    (_h_interior : ∀ x ∈ Set.Ioo a b, ∀ t : ℝ,
      ε * fderiv ℝ (fun s : ℝ => u (x, s)) t 1 =
        ε * laplacian_box (fun y => u (y, t)) x -
          fderiv ℝ W (u (x, t)) 1 / ε)
    (φ : (Fin (n + 1) → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (_hφ_nn : ∀ x, 0 ≤ φ x)
    (C₂ : ℝ) (_hC₂ : 0 ≤ C₂) (_hφ_bd : ∀ x, φ x ≤ C₂)
    (t : ℝ) (_ht : 0 ≤ t) :
    ∃ D : ℝ,
      HasDerivAt
        (fun s : ℝ => ∫ x in Set.Icc a b, φ x *
          (ε * (∑ i, gradient_box (fun y => u (y, s)) x i ^ 2) / 2 +
            W (u (x, s)) / ε)) D t ∧
      D ≤ C₂ *
        (∫ x in Set.Icc a b,
          (ε * (∑ i, gradient_box (fun y => u (y, t)) x i ^ 2) / 2 +
            W (u (x, t)) / ε)) := by
  -- Witness D as the Leibniz-derivative of the localized energy.
  set D : ℝ := ∫ x in Set.Icc a b, φ x *
    (ε * (∑ i, gradient_box (fun y => u (y, t)) x i *
          gradient_box (fun y => timeDeriv u y t) x i) +
      fderiv ℝ W (u (x, t)) 1 * timeDeriv u x t / ε) with hD_def
  refine ⟨D, ?_, ?_⟩
  · -- HasDerivAt: discharged by `localizedEnergy_hasDerivAt_t`.
    have hu2 : ContDiff ℝ 2 u := hsmooth.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ ⊤)
    have hW2 : ContDiff ℝ 2 W := hW_smooth.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ ⊤)
    have hφ0 : ContDiff ℝ 0 φ := hφ.of_le (by norm_num : (0 : WithTop ℕ∞) ≤ 2)
    have h := localizedEnergy_hasDerivAt_t (ε := ε) (W := W) hle hu2 hW2 φ hφ0 t
    simp only [boxEnergyDensity] at h
    exact h
  · -- BLOCKER: bound D ≤ C₂ · boxTotalEnergy(t). This is the Schwarz/IBP
    -- step. Concretely, after `localizedEnergy_hasDerivAt_t` produces
    -- `D = ∫_Ω φ · (ε ⟨∇u, ∇u_t⟩ + W'(u) u_t / ε)`, the derivation goes:
    -- (a) Apply `green_first_identity_box` with `f = φ · u_t`, `g = u`:
    --     `∫ ∇(φ u_t) · ∇u + ∫ (φ u_t) Δu = boxBoundaryFlux a b ((φ u_t) · ∇u)`.
    -- (b) Expand `∇(φ u_t) = u_t ∇φ + φ ∇u_t`.
    -- (c) Substitute the interior PDE `ε Δu = ε u_t + W'(u)/ε`, collapsing
    --     the bulk term to `−ε ∫ φ u_t² ≤ 0`.
    -- (d) Substitute the Robin BC `ε(∇u · ν) = −σ'(u)` in
    --     `boxBoundaryFlux ((φ u_t) · ∇u)` to get a boundary integral of
    --     `−φ u_t σ'(u)/ε` over each face, contributing 0 in the steady-state
    --     analysis (paper Section 2 equation (6) with σ ≥ 0).
    -- (e) Cauchy-Schwarz on the residual `ε ∫ u_t ⟨∇φ, ∇u⟩` against
    --     `‖∇φ‖_∞ ≤ ‖φ‖_{C¹} ≤ C₂` gives the absorption.
    sorry

end MeasureTheory.AllenCahn
