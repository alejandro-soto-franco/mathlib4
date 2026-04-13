# Roadmap to unconditional Lemma 1 of [MSTW24]

This document tracks the path to a fully proven, unconditional Lean
formalization of Lemma 1 of [MSTW24] (Marshall-Stevens, Takada, Tonegawa,
Workman, *Gradient flow of phase transitions with fixed contact angle*) for
box domains.

## Current status

| Component | Status | Sorries |
|-----------|--------|---------|
| `IntegrationByParts/Box.lean` | All 5 theorems proved | 0 |
| `EnergyMeasure.lean` | Defs + non-negativity | 0 |
| `Discrepancy.lean` | Defs + identities | 0 |
| `SemiDecreasing.lean` | Lemma 1 (abstract `IsSolution`) proved | 0 |
| `AllenCahn/Box.lean` | Structure + `localizedDissipation` proved | 3 |

The 3 remaining sorries are all in the chain
`raw PDE → IsBoxSolution → Lemma 1`. The `Lemma 1` end of the chain is
PROVED; the gap is in deriving `IsBoxSolution` from raw PDE assumptions.

## The 3 sorries, in dependency order

### Sorry #1: `boxEnergyDensity_hasDerivAt_t`

**Statement**: pointwise time derivative of `e_ε(u)(x, ·)` at fixed `x`.

**Mathematical content**:
```
∂_s [ε‖∇u(x,s)‖²/2 + W(u(x,s))/ε] =
  ε ⟨∇u(x,t), ∇u_t(x,t)⟩ + W'(u(x,t)) · u_t(x,t) / ε
```

**Proof outline**:
1. Split into two `HasDerivAt` summands via `HasDerivAt.add`.
2. **Gradient-squared term**: `s ↦ ∑ᵢ (∂ᵢu(x,s))²`.
   - For each `i`, `s ↦ (∂ᵢu(x,s))²` has derivative `2 · ∂ᵢu(x,t) · (∂_s ∂ᵢu)(x,t)` via `HasDerivAt.pow` with `n = 2`.
   - The `(∂_s ∂ᵢu)(x,t) = ∂ᵢ(∂_s u)(x,t)` step requires Schwarz on the joint product space — see Schwarz substep below.
   - Sum via `HasDerivAt.sum`, multiply by `ε/2` via `HasDerivAt.const_mul` and `HasDerivAt.div_const`.
3. **Potential term**: `s ↦ W(u(x,s)) / ε`.
   - `s ↦ u(x, s)` has derivative `timeDeriv u x t` by definition / `HasFDerivAt.fderiv`.
   - `W` has derivative `fderiv ℝ W (u(x,t)) 1` at `u(x,t)`.
   - Compose via `HasDerivAt.comp`, divide by `ε`.

**Schwarz substep** — `s ↦ ∂ᵢu(x,s)` has derivative `∂ᵢ(∂_s u)(x,t) = gradient_box (timeDeriv u y t) x i` at `t`.

Use `Mathlib.Analysis.Calculus.FDeriv.Symmetric.ContDiffAt.isSymmSndFDerivAt`
applied to `u : (Fin (n+1) → ℝ) × ℝ → ℝ` at `(x, t)`. The symmetric second
derivative satisfies `D²u(x,t)(v₁, v₂) = D²u(x,t)(v₂, v₁)` for all
`v₁, v₂ ∈ (Fin (n+1) → ℝ) × ℝ`. Setting `v₁ = (Pi.single i 1, 0)` and
`v₂ = (0, 1)` yields the desired equality after relating `D²u` to iterated
partial derivatives via `fderiv_pi'` and the curry / uncurry of the
product-space differential.

**Realistic effort**: ~200 LoC, half on Schwarz unwinding.

### Sorry #2: `localizedEnergy_hasDerivAt_t`

**Statement**: `s ↦ ∫_Ω φ · e_ε(u(·,s)) dx` is differentiable at `t`, with
derivative obtained by integrating the pointwise derivative.

**Proof outline**: single application of
`MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le` (in
`Mathlib/Analysis/Calculus/ParametricIntegral.lean`).

Invocation:
- `μ := volume.restrict (Set.Icc a b)`
- `s := Metric.ball t 1`
- `F t' x := φ x * boxEnergyDensity ε W u x t'`
- `F' t' x := φ x · (pointwise derivative from sorry #1)`
- `bound a := M`, a finite constant.

Sub-steps to discharge:
1. `hF_meas : ∀ᶠ x in 𝓝 t, AEStronglyMeasurable (F x) μ` — from joint
   continuity of `(t', x) ↦ F t' x` and `measurable_of_continuous`.
2. `hF_int : Integrable (F t) μ` — bounded continuous on compact box.
   Use `ContinuousOn.integrableOn_Icc`.
3. `hF'_meas` — same reasoning as `hF_meas`.
4. `h_bound` — uniform bound on `F'` over `Icc a b × Metric.ball t 1` by
   `IsCompact.exists_bound_of_continuousOn` or extreme value theorem on
   the compact `Icc a b × Icc (t-1) (t+1)`.
5. `bound_integrable` — `Integrable (fun _ => M) μ` from finite measure.
6. `h_diff` — direct from sorry #1 (multiplied by `φ x`).

**Realistic effort**: ~150 LoC.

### Sorry #3: bound step in `differential_dissipation_from_PDE`

**Statement**:
`D := ∫_Ω φ · (ε ⟨∇u, ∇u_t⟩ + W'(u) u_t / ε) ≤ C₂ · boxTotalEnergy(t)`.

**Proof outline**: 5 steps.

1. **Apply Green's first identity** (`green_first_identity_box` from
   `IntegrationByParts/Box.lean`) with `f := φ · u_t`, `g := u`:
   ```
   ∫ ⟨∇(φ u_t), ∇u⟩ + ∫ (φ u_t) Δu = boxBoundaryFlux a b ((φ u_t) · ∇u)
   ```

2. **Expand the gradient**:
   `∇(φ u_t) = u_t ∇φ + φ ∇u_t`, so
   `⟨∇(φ u_t), ∇u⟩ = u_t ⟨∇φ, ∇u⟩ + φ ⟨∇u_t, ∇u⟩`.
   Therefore
   `∫ φ ⟨∇u_t, ∇u⟩ = boxBoundaryFlux − ∫ u_t ⟨∇φ, ∇u⟩ − ∫ (φ u_t) Δu`.

3. **Substitute interior PDE** `ε Δu = ε u_t + W'(u)/ε`:
   `∫ (φ u_t) ε Δu = ε ∫ φ u_t² + ∫ φ u_t · W'(u)/ε`.

4. **Substitute Robin BC** `ε(∇u·ν) = −σ'(u)` into `boxBoundaryFlux`:
   on each face, the flux contribution becomes a boundary integral of
   `−(φ u_t σ'(u)) / ε`. (Requires concrete encoding of Robin BC; see
   below.)

5. **Combine**:
   ```
   D = ε · ∫ φ ⟨∇u_t, ∇u⟩ + ∫ φ W'(u) u_t / ε
     = ε [boxBoundaryFlux − ∫ u_t ⟨∇φ, ∇u⟩] − ε ∫ φ u_t² · ε
       − ∫ φ u_t W'(u)/ε + ∫ φ u_t W'(u)/ε     -- the W'(u) terms cancel
     = ε · (boundary terms via Robin) − ε ∫ u_t ⟨∇φ, ∇u⟩ − ε² ∫ φ u_t²
   ```
   The `−ε² ∫ φ u_t² ≤ 0` term is dropped.
   The boundary term collapses via Robin to a `−σ'(u) u_t = −d/dt σ(u)`
   contribution (handled at the level of total energy).
   The residual `−ε ∫ u_t ⟨∇φ, ∇u⟩` is bounded via Cauchy-Schwarz:
   `|⟨∇φ, ∇u⟩| ≤ ‖∇φ‖_∞ · ‖∇u‖ ≤ C₂ · ‖∇u‖`,
   then `|∫ u_t · ‖∇u‖| ≤ √(∫ u_t²) · √(∫ ‖∇u‖²)`,
   absorbed into `C₂ · boxTotalEnergy(t)`.

**Structural prerequisite**: replace `IsBoxSolution.robin_bc : True` with
a concrete identity. Proposed form:
```
robin_bc : ∀ t : ℝ, ∀ i : Fin (n + 1),
  -- front face i: outward normal is +eᵢ
  (∀ x ∈ Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
    ε * gradient_box (fun y => u (y, t)) (i.insertNth (b i) x) i =
    -(fderiv ℝ σ (u (i.insertNth (b i) x, t)) 1)) ∧
  -- back face i: outward normal is -eᵢ
  (∀ x ∈ Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
    -ε * gradient_box (fun y => u (y, t)) (i.insertNth (a i) x) i =
    -(fderiv ℝ σ (u (i.insertNth (a i) x, t)) 1))
```

**Realistic effort**: 250–400 LoC, spread across 1–2 sessions.

## Remaining structural tasks beyond the 3 sorries

- Replace `IsBoxSolution.robin_bc : True` with the concrete face-by-face
  encoding above (~50 LoC of restructuring).
- Once `differential_dissipation_from_PDE` is fully closed, derive
  `IsBoxSolution.totalEnergy_decay` from `interior_eq + robin_bc` rather
  than carry it as an axiom (this is paper eq. (6)).
- Build an `IsBoxSolution → IsSolution` bridge so that
  `IsSolution.energyMeasure_semiDecreasing` becomes unconditional in the
  box case.

## Total estimate

To "truly end-to-end" close Lemma 1 of [MSTW24] in the box case starting
from current branch state: **~600–800 LoC of focused Lean across 4–5
sessions**.

The general smooth-domain case requires additionally building surface
measure on smooth boundaries in Mathlib, which is a separate multi-month
research-grade contribution.

## References

* [MSTW24] Marshall-Stevens, Takada, Tonegawa, Workman, *Gradient flow of
  phase transitions with fixed contact angle* (2024).
* `Mathlib/Analysis/Calculus/ParametricIntegral.lean` —
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
* `Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean` —
  `ContDiffAt.isSymmSndFDerivAt`.
* `Mathlib/Analysis/PhaseField/IntegrationByParts/Box.lean` —
  `green_first_identity_box`, `divergence_smul`,
  `divergence_grad_eq_laplacian`.
