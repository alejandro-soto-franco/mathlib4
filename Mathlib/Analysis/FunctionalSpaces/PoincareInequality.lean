/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Poincaré inequality for compactly supported functions

This file proves the **1D Poincaré inequality**: for a compactly supported C^1 function
f : ℝ → ℝ with support contained in (a, b), the L^2 norm of f is controlled by the
L^2 norm of its derivative:

  ∫ t in [a, b], f t ^ 2 ≤ (b - a)^2 * ∫ t in [a, b], (deriv f t) ^ 2

This is the simplest Poincaré inequality; the n-dimensional version for convex bounded
domains follows from this by integration over coordinate slices (Fubini).

## Main results

* `MeasureTheory.poincare_1d`: 1D Poincaré inequality for compactly supported C^1 functions.

## Proof outline

For x ∈ [a, b]: since f(a) = 0 (a is outside the support), the fundamental theorem of
calculus gives `f(x) = ∫_{a}^{x} f'(t) dt`. The Cauchy-Schwarz inequality then gives
`f(x)^2 ≤ (x-a) * ∫_a^b (f')^2 ≤ (b-a) * ∫_a^b (f')^2`.
Integrating over x ∈ [a, b] gives the result.

## Status

The integral Cauchy-Schwarz step
  `(∫ t in Ioc a x, g t)^2 ≤ (x - a) * ∫ t in Icc a x, g t^2`
is currently marked sorry; it follows from Hölder's inequality
(`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg` with p = q = 2 and constant function 1)
but requires careful measure-theoretic plumbing.
-/

section

open MeasureTheory MeasureTheory.Measure Set intervalIntegral

open scoped ENNReal NNReal

namespace MeasureTheory

variable {a b : ℝ}

/-- **Cauchy-Schwarz for interval integrals**: the square of the integral of a function g
on `(a, x]` is at most `(x - a)` times the integral of `g^2` on `[a, x]`.

This is the key step in the 1D Poincaré proof. The bound follows from Hölder's inequality
with p = q = 2 applied to g and the constant function 1:
  `∫ |g| ≤ ‖g‖_{L^2([a,x])} * ‖1‖_{L^2([a,x])} = √(∫ g^2) * √(x-a)`

Category A: follows from `integral_mul_le_Lp_mul_Lq_of_nonneg` but requires L^2
measurability hypotheses and ENNReal measure arithmetic. -/
theorem sq_integral_Ioc_le_length_mul_integral_sq_Icc {x : ℝ} (hax : a ≤ x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc a x)) :
    (∫ t in Set.Ioc a x, g t) ^ 2 ≤ (x - a) * ∫ t in Set.Icc a x, g t ^ 2 := by
  -- The integrals over Ioc and Icc agree: their symmetric difference {a} has measure 0
  have heq : ∫ t in Set.Ioc a x, g t = ∫ t in Set.Icc a x, g t :=
    setIntegral_congr_set (Ioc_ae_eq_Icc' (by simp))
  rw [heq]
  -- Abbreviate the integrals
  set I := ∫ t in Set.Icc a x, g t
  set I2 := ∫ t in Set.Icc a x, g t ^ 2
  -- Integrability
  have hg_int : IntegrableOn g (Set.Icc a x) :=
    hg.integrableOn_compact isCompact_Icc
  have hg_sq_int : IntegrableOn (fun t => g t ^ 2) (Set.Icc a x) :=
    (hg.pow 2).integrableOn_compact isCompact_Icc
  -- Case x = a: both sides zero
  rcases eq_or_lt_of_le hax with rfl | hxa
  · simp [I, I2]
  have hxa_pos : 0 < x - a := by linarith
  -- For any s : ℝ, expand ∫_Icc (g - s)^2 as a quadratic in s
  have hQ_expand : ∀ s : ℝ,
      ∫ t in Set.Icc a x, (g t - s) ^ 2 =
      I2 - 2 * s * I + s ^ 2 * (x - a) := by
    intro s
    -- Explicit type annotations ensure integral_add/sub match the goal syntactically
    have h2sg : IntegrableOn (fun t => 2 * s * g t) (Set.Icc a x) :=
      hg_int.const_mul (2 * s)
    have hs2 : IntegrableOn (fun _ => s ^ 2) (Set.Icc a x) :=
      integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)
    -- Giving this have an explicit type forces Lean to represent the function as
    -- `fun t => g t ^ 2 - 2 * s * g t` (not as function subtraction Pi.instSub),
    -- which is required for integral_add to pattern-match below.
    have hgsub : IntegrableOn (fun t => g t ^ 2 - 2 * s * g t) (Set.Icc a x) :=
      hg_sq_int.sub h2sg
    -- Rewrite integrand under the binder then split via integral linearity
    conv_lhs => arg 2; ext t; rw [show (g t - s) ^ 2 = (g t ^ 2 - 2 * s * g t) + s ^ 2 from by ring]
    rw [integral_add hgsub hs2,
        integral_sub hg_sq_int h2sg, integral_const_mul, setIntegral_const,
        Real.volume_real_Icc_of_le hax, smul_eq_mul]
    simp [I, I2]; ring
  -- Nonnegativity of the variance: for any s, 0 ≤ ∫ (g - s)^2
  have hQ_nonneg : ∀ s : ℝ, 0 ≤ ∫ t in Set.Icc a x, (g t - s) ^ 2 :=
    fun s => setIntegral_nonneg measurableSet_Icc (fun t _ => sq_nonneg _)
  -- Apply at the optimal s = I / (x - a) to get the discriminant bound
  set s₀ := I / (x - a) with hs₀_def
  have hs₀ : s₀ * (x - a) = I := div_mul_cancel₀ I hxa_pos.ne'
  have hmin : 0 ≤ I2 - 2 * s₀ * I + s₀ ^ 2 * (x - a) := by
    rw [← hQ_expand s₀]; exact hQ_nonneg s₀
  -- Algebraic conclusion: I^2 ≤ (x-a) * I2
  have hs₀I : 2 * s₀ * I = 2 * s₀ ^ 2 * (x - a) := by
    have h : s₀ * I = s₀ ^ 2 * (x - a) := by
      calc s₀ * I = s₀ * (s₀ * (x - a)) := by rw [hs₀]
        _ = s₀ ^ 2 * (x - a) := by ring
    linarith
  have hsd : s₀ ^ 2 * (x - a) ≤ I2 := by nlinarith [hmin, hs₀I]
  calc I ^ 2 = (s₀ * (x - a)) ^ 2 := by rw [hs₀]
    _ = s₀ ^ 2 * (x - a) ^ 2 := by ring
    _ = s₀ ^ 2 * (x - a) * (x - a) := by ring
    _ ≤ I2 * (x - a) := mul_le_mul_of_nonneg_right hsd hxa_pos.le
    _ = (x - a) * I2 := by ring

/-- **1D Poincaré inequality** for compactly supported C^1 functions:
if `f : ℝ → ℝ` satisfies `ContDiff ℝ 1 f` and `f.support ⊆ Set.Ioo a b`, then

  `∫ t in Set.Icc a b, f t ^ 2 ≤ (b - a)^2 * ∫ t in Set.Icc a b, (deriv f t)^2`

Proof:
- `f(a) = 0` since `a ∉ support f`.
- For x ∈ [a, b]: `f(x) = ∫_{a}^{x} f'(t) dt` by FTC.
- Cauchy-Schwarz: `f(x)^2 ≤ (x-a) * ∫_a^x (f')^2 ≤ (b-a) * ∫_a^b (f')^2`.
- Integrate over x ∈ [a, b]: `∫_a^b f^2 ≤ (b-a)^2 * ∫_a^b (f')^2`. -/
theorem poincare_1d (hab : a < b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hsupp : f.support ⊆ Set.Ioo a b) :
    ∫ t in Set.Icc a b, f t ^ 2 ≤
      (b - a) ^ 2 * ∫ t in Set.Icc a b, (deriv f t) ^ 2 := by
  have hab' : a ≤ b := le_of_lt hab
  -- Step 1: f(a) = 0 since a ∉ support f
  have hfa : f a = 0 := by
    by_contra h
    exact absurd (hsupp (Function.mem_support.mpr h)) (by simp)
  -- Step 2: FTC — f(x) = ∫ t in Ioc a x, deriv f t for x ∈ [a, b]
  have hftc : ∀ x ∈ Set.Icc a b, f x = ∫ t in Set.Ioc a x, deriv f t := by
    intro x hx
    have hcontdiff : ContDiffOn ℝ 1 f (Set.Icc a x) :=
      hf.contDiffOn.mono (Set.Icc_subset_Icc_right hx.2)
    -- FTC gives ∫ t in a..x, deriv f t = f x - f a  (interval integral)
    have hiv : ∫ t in a..x, deriv f t = f x - f a :=
      integral_deriv_of_contDiffOn_Icc hcontdiff hx.1
    -- Convert interval integral to set integral over Ioc (since a ≤ x)
    rw [integral_of_le hx.1] at hiv
    -- Conclude f x = ∫ t in Ioc a x, deriv f t  using f a = 0
    linarith [hfa]
  -- Step 3: Pointwise bound — f(x)^2 ≤ (b-a) * ∫ t in Icc a b, (deriv f t)^2
  have hderiv_cont : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hderiv_sq_int : IntegrableOn (fun t => (deriv f t) ^ 2) (Set.Icc a b) :=
    (hderiv_cont.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hpointwise : ∀ x ∈ Set.Icc a b,
      f x ^ 2 ≤ (b - a) * ∫ t in Set.Icc a b, (deriv f t) ^ 2 := by
    intro x hx
    rw [hftc x hx]
    have hderiv_cont_x : ContinuousOn (deriv f) (Set.Icc a x) :=
      hderiv_cont.continuousOn.mono (Set.Icc_subset_Icc_right hx.2)
    have hderiv_sq_int_x : IntegrableOn (fun t => (deriv f t) ^ 2) (Set.Icc a x) :=
      (hderiv_cont.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    -- Monotonicity of the integral over a larger domain
    have hint_mono : ∫ t in Set.Icc a x, (deriv f t) ^ 2 ≤
        ∫ t in Set.Icc a b, (deriv f t) ^ 2 :=
      setIntegral_mono_set hderiv_sq_int
        (Filter.Eventually.of_forall (fun t => sq_nonneg _))
        (Filter.Eventually.of_forall (Set.Icc_subset_Icc_right hx.2))
    calc (∫ t in Set.Ioc a x, deriv f t) ^ 2
        ≤ (x - a) * ∫ t in Set.Icc a x, (deriv f t) ^ 2 :=
          sq_integral_Ioc_le_length_mul_integral_sq_Icc hx.1 hderiv_cont_x
      _ ≤ (b - a) * ∫ t in Set.Icc a b, (deriv f t) ^ 2 :=
          mul_le_mul (by linarith [hx.2]) hint_mono
            (setIntegral_nonneg measurableSet_Icc (fun t _ => sq_nonneg _)) (by linarith)
  -- Step 4: Integrate the pointwise bound
  have hf_sq_int : IntegrableOn (fun t => f t ^ 2) (Set.Icc a b) :=
    (hf.continuous.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hconst_int : IntegrableOn (fun _ => (b - a) * ∫ t in Set.Icc a b, (deriv f t) ^ 2)
      (Set.Icc a b) :=
    integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)
  have hle : ∫ t in Set.Icc a b, f t ^ 2 ≤
      ∫ _ in Set.Icc a b, (b - a) * ∫ t in Set.Icc a b, (deriv f t) ^ 2 :=
    setIntegral_mono_on hf_sq_int hconst_int measurableSet_Icc hpointwise
  calc ∫ t in Set.Icc a b, f t ^ 2
      ≤ ∫ _ in Set.Icc a b, (b - a) * ∫ t in Set.Icc a b, (deriv f t) ^ 2 := hle
    _ = (b - a) ^ 2 * ∫ t in Set.Icc a b, (deriv f t) ^ 2 := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le hab', smul_eq_mul]
        ring

end MeasureTheory

end
