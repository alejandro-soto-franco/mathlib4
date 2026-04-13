/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Poincaré inequality in one dimension

This file proves the 1D Poincaré inequality: for a function `f : ℝ → E` into a real normed
space that is `C¹` on `[a, b]` and vanishes at the endpoints,

  `∫⁻ t in Icc a b, ‖f t‖ₑ ^ 2 ≤ ENNReal.ofReal ((b - a) ^ 2) * ∫⁻ t in Icc a b, ‖deriv f t‖ₑ ^ 2`.

The statement uses Lebesgue integrals of extended-nonneg-real norms, matching the
conventions used elsewhere in Mathlib for analytic estimates (see
`Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`); this keeps the inequality
meaningful without an integrability hypothesis on `deriv f`.

## Main results

* `MeasureTheory.poincare_1d`: the 1D Poincaré inequality stated above.
-/

open MeasureTheory MeasureTheory.Measure Set intervalIntegral

open scoped ENNReal

@[expose] public section

namespace MeasureTheory

variable {a b : ℝ}

/-- Cauchy-Schwarz for the Lebesgue integral of an `ℝ≥0∞`-valued function against the
constant function 1: `(∫⁻ g) ^ 2 ≤ μ s * ∫⁻ g ^ 2`.

This is a packaging of Hölder's inequality (`ENNReal.lintegral_mul_le_Lp_mul_Lq`) with
`p = q = 2` and one factor set to the constant 1. -/
private lemma sq_lintegral_le_measure_mul_lintegral_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (s : Set α) {g : α → ℝ≥0∞}
    (hg : AEMeasurable g (μ.restrict s)) :
    (∫⁻ x in s, g x ∂μ) ^ 2 ≤ μ s * ∫⁻ x in s, g x ^ 2 ∂μ := by
  have hpq : Real.HolderConjugate 2 2 := .two_two
  have hHolder_raw := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict s) hpq
    (f := fun _ => (1 : ℝ≥0∞)) (g := g) aemeasurable_const hg
  -- Rewrite `∫⁻ ((fun _ => 1) * g) a = ∫⁻ g`, `∫⁻ 1 ^ 2 = μ s`, `g^(2:ℝ) = g^2`.
  have hrpow : ∀ x, g x ^ (2 : ℝ) = g x ^ (2 : ℕ) := fun x => by
    rw [← ENNReal.rpow_natCast]; norm_num
  have hint_eq : ∫⁻ x in s, g x ^ (2 : ℝ) ∂μ = ∫⁻ x in s, g x ^ 2 ∂μ :=
    lintegral_congr_ae (.of_forall fun x => hrpow x)
  have hHolder : ∫⁻ x in s, g x ∂μ ≤
      (μ s) ^ ((1 : ℝ) / 2) * (∫⁻ x in s, g x ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
    have := hHolder_raw
    simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, setLIntegral_const] at this
    rwa [hint_eq] at this
  calc (∫⁻ x in s, g x ∂μ) ^ 2
      ≤ ((μ s) ^ ((1 : ℝ) / 2) * (∫⁻ x in s, g x ^ 2 ∂μ) ^ ((1 : ℝ) / 2)) ^ 2 :=
        pow_le_pow_left' hHolder 2
    _ = μ s * ∫⁻ x in s, g x ^ 2 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_natCast _ 2,
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

/-- The 1D Poincaré inequality: for a function `f : ℝ → E` into a real normed space that is
`C¹` on `[a, b]` and vanishes at the left endpoint,

`∫⁻ t in Icc a b, ‖f t‖ₑ ^ 2 ≤ ENNReal.ofReal ((b - a) ^ 2) * ∫⁻ t in Icc a b, ‖deriv f t‖ₑ ^ 2`.

The proof combines the fundamental theorem of calculus (via
`enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc`) with Cauchy-Schwarz against the constant
function `1`. Using Lebesgue integrals of extended-nonneg-real norms avoids any
integrability hypothesis: when `∫⁻ ‖deriv f‖ₑ ^ 2 = ∞` the bound is trivial.

Note that vanishing at only one endpoint suffices for the constant `(b - a) ^ 2`. With
vanishing at both endpoints the optimal constant is `(b - a) ^ 2 / π ^ 2` (Wirtinger);
deriving the tighter version is left to a follow-up. -/
theorem poincare_1d
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hab : a < b)
    (hf : ContDiffOn ℝ 1 f (Icc a b))
    (hfa : f a = 0) :
    ∫⁻ t in Icc a b, ‖f t‖ₑ ^ 2 ≤
      ENNReal.ofReal ((b - a) ^ 2) * ∫⁻ t in Icc a b, ‖deriv f t‖ₑ ^ 2 := by
  -- AE measurability of `‖deriv f‖ₑ` on `Icc a b`, via `derivWithin` (continuous on `Icc a b`)
  -- and the a.e. equality `derivWithin f (Icc a b) = deriv f` on `Ioo a b`.
  have hderivW_cont : ContinuousOn (derivWithin f (Icc a b)) (Icc a b) :=
    hf.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
  have hdW_eq_d : ∀ᵐ t ∂volume.restrict (Icc a b),
      ‖derivWithin f (Icc a b) t‖ₑ = ‖deriv f t‖ₑ := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  have hderiv_aemeas : AEMeasurable (fun t => ‖deriv f t‖ₑ) (volume.restrict (Icc a b)) :=
    ((continuous_enorm.comp_continuousOn hderivW_cont).aestronglyMeasurable
      measurableSet_Icc).aemeasurable.congr hdW_eq_d
  -- Pointwise FTC bound: `‖f x‖ₑ ≤ ∫⁻ t in Icc a x, ‖deriv f t‖ₑ` for `x ∈ Icc a b`.
  have hFTC : ∀ x ∈ Icc a b, ‖f x‖ₑ ≤ ∫⁻ t in Icc a x, ‖deriv f t‖ₑ := fun x hx => by
    have hcd : ContDiffOn ℝ 1 f (Icc a x) := hf.mono (Icc_subset_Icc_right hx.2)
    have h := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hcd hx.1
    rwa [hfa, sub_zero] at h
  -- Pointwise squared bound via Cauchy-Schwarz.
  have hpw_global : ∀ x ∈ Icc a b,
      ‖f x‖ₑ ^ 2 ≤ ENNReal.ofReal (b - a) * ∫⁻ t in Icc a b, ‖deriv f t‖ₑ ^ 2 := fun x hx => by
    have hxa : a ≤ x := hx.1
    have hxb : x ≤ b := hx.2
    have hderiv_aemeas_ax : AEMeasurable (fun t => ‖deriv f t‖ₑ)
        (volume.restrict (Icc a x)) :=
      hderiv_aemeas.mono_measure (Measure.restrict_mono (Icc_subset_Icc_right hxb) le_rfl)
    have hCS : (∫⁻ t in Icc a x, ‖deriv f t‖ₑ) ^ 2 ≤
        volume (Icc a x) * ∫⁻ t in Icc a x, ‖deriv f t‖ₑ ^ 2 :=
      sq_lintegral_le_measure_mul_lintegral_sq _ hderiv_aemeas_ax
    calc ‖f x‖ₑ ^ 2
        ≤ (∫⁻ t in Icc a x, ‖deriv f t‖ₑ) ^ 2 := pow_le_pow_left' (hFTC x hx) 2
      _ ≤ volume (Icc a x) * ∫⁻ t in Icc a x, ‖deriv f t‖ₑ ^ 2 := hCS
      _ ≤ ENNReal.ofReal (b - a) * ∫⁻ t in Icc a b, ‖deriv f t‖ₑ ^ 2 := by
          rw [Real.volume_Icc]
          gcongr ?_ * ?_
          · exact ENNReal.ofReal_le_ofReal (by linarith)
          · exact lintegral_mono_set (Icc_subset_Icc_right hxb)
  -- Integrate over `Icc a b`.
  have hpw_ae : ∀ᵐ t ∂volume.restrict (Icc a b),
      ‖f t‖ₑ ^ 2 ≤ ENNReal.ofReal (b - a) * ∫⁻ s in Icc a b, ‖deriv f s‖ₑ ^ 2 := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht using hpw_global t ht
  calc ∫⁻ t in Icc a b, ‖f t‖ₑ ^ 2
      ≤ ∫⁻ _ in Icc a b, ENNReal.ofReal (b - a) * ∫⁻ s in Icc a b, ‖deriv f s‖ₑ ^ 2 :=
        lintegral_mono_ae hpw_ae
    _ = (ENNReal.ofReal (b - a) * ∫⁻ s in Icc a b, ‖deriv f s‖ₑ ^ 2) * volume (Icc a b) :=
        setLIntegral_const _ _
    _ = ENNReal.ofReal ((b - a) ^ 2) * ∫⁻ s in Icc a b, ‖deriv f s‖ₑ ^ 2 := by
        rw [Real.volume_Icc, mul_assoc, mul_comm (∫⁻ s in Icc a b, _) _, ← mul_assoc,
          ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ b - a), sq]

end MeasureTheory

end
