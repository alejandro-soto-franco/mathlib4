/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Fundamental theorem of calculus for `C^1` functions

We give versions of the second fundamental theorem of calculus under the strong assumption
that the function is `C^1` on the interval. This is restrictive, but satisfied in many situations.
-/

public section

noncomputable section

open MeasureTheory Set Filter Function Asymptotics

open scoped Topology ENNReal Interval NNReal

variable {ι 𝕜 E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E} {a b : ℝ}

namespace intervalIntegral

variable [CompleteSpace E]

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is `C^1` on `[a, b]`,
then `∫ y in a..b, deriv f y` equals `f b - f a`. -/
theorem integral_deriv_of_contDiffOn_Icc (h : ContDiffOn ℝ 1 f (Icc a b)) (hab : a ≤ b) :
    ∫ x in a..b, deriv f x = f b - f a := by
  rcases hab.eq_or_lt with rfl | h'ab
  · simp
  apply integral_eq_sub_of_hasDerivAt_of_le hab h.continuousOn
  · intro x hx
    apply DifferentiableAt.hasDerivAt
    apply ((h x ⟨hx.1.le, hx.2.le⟩).differentiableWithinAt one_ne_zero).differentiableAt
    exact Icc_mem_nhds hx.1 hx.2
  · have := (h.derivWithin (m := 0) (uniqueDiffOn_Icc h'ab) (by simp)).continuousOn
    apply (this.intervalIntegrable_of_Icc (μ := volume) hab).congr_ae
    simp only [hab, uIoc_of_le]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is `C^1` on `[a, b]`,
then `∫ y in a..b, derivWithin f (Icc a b) y` equals `f b - f a`. -/
theorem integral_derivWithin_Icc_of_contDiffOn_Icc (h : ContDiffOn ℝ 1 f (Icc a b)) (hab : a ≤ b) :
    ∫ x in a..b, derivWithin f (Icc a b) x = f b - f a := by
  rw [← integral_deriv_of_contDiffOn_Icc h hab]
  rw [integral_of_le hab, integral_of_le hab]
  apply MeasureTheory.integral_congr_ae
  rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is `C^1` on `[a, b]`,
then `∫ y in a..b, deriv f y` equals `f b - f a`. -/
theorem integral_deriv_of_contDiffOn_uIcc (h : ContDiffOn ℝ 1 f (uIcc a b)) :
    ∫ x in a..b, deriv f x = f b - f a := by
  rcases le_or_gt a b with hab | hab
  · simp only [uIcc_of_le hab] at h
    exact integral_deriv_of_contDiffOn_Icc h hab
  · simp only [uIcc_of_ge hab.le] at h
    rw [integral_symm, integral_deriv_of_contDiffOn_Icc h hab.le]
    abel

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is `C^1` on `[a, b]`,
then `∫ y in a..b, derivWithin f (uIcc a b) y` equals `f b - f a`. -/
theorem integral_derivWithin_uIcc_of_contDiffOn_uIcc (h : ContDiffOn ℝ 1 f (uIcc a b)) :
    ∫ x in a..b, derivWithin f (uIcc a b) x = f b - f a := by
  rcases le_or_gt a b with hab | hab
  · simp only [uIcc_of_le hab] at h ⊢
    exact integral_derivWithin_Icc_of_contDiffOn_Icc h hab
  · simp only [uIcc_of_ge hab.le] at h ⊢
    rw [integral_symm, integral_derivWithin_Icc_of_contDiffOn_Icc h hab.le]
    abel

end intervalIntegral

open intervalIntegral

theorem enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc (h : ContDiffOn ℝ 1 f (Icc a b))
    (hab : a ≤ b) :
    ‖f b - f a‖ₑ ≤ ∫⁻ x in Icc a b, ‖deriv f x‖ₑ := by
  /- We want to write `f b - f a = ∫ x in Icc a b, deriv f x` and use the inequality between
  norm of integral and integral of norm. There is a small difficulty that this formula is not
  true when `E` is not complete, so we need to go first to the completion, and argue there. -/
  let g := UniformSpace.Completion.toComplₗᵢ (𝕜 := ℝ) (E := E)
  have : ‖(g ∘ f) b - (g ∘ f) a‖ₑ = ‖f b - f a‖ₑ := by
    rw [← edist_eq_enorm_sub, Function.comp_def, g.isometry.edist_eq, edist_eq_enorm_sub]
  rw [← this, ← integral_deriv_of_contDiffOn_Icc (g.contDiff.comp_contDiffOn h) hab,
    integral_of_le hab, restrict_Ioc_eq_restrict_Icc]
  apply (enorm_integral_le_lintegral_enorm _).trans
  apply lintegral_mono_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  rw [fderiv_comp_deriv]; rotate_left
  · exact (g.contDiff.differentiable one_ne_zero).differentiableAt
  · exact (h x ⟨hx.1.le, hx.2.le⟩).contDiffAt (Icc_mem_nhds hx.1 hx.2)
      |>.differentiableAt one_ne_zero
  have : fderiv ℝ g (f x) = g.toContinuousLinearMap := g.toContinuousLinearMap.fderiv
  simp [this]

theorem enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc (h : ContDiffOn ℝ 1 f (Icc a b))
    (hab : a ≤ b) :
    ‖f b - f a‖ₑ ≤ ∫⁻ x in Icc a b, ‖derivWithin f (Icc a b) x‖ₑ := by
  apply (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc h hab).trans_eq
  apply lintegral_congr_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]

/-- Variant of `enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc` requiring `f` to be only `C¹` on
the open interval `Ioo a b` and continuous on the closed interval `Icc a b`. This admits
boundary-singular functions such as `x ↦ (x - a) ^ (1/3) * (b - x) ^ (1/3)`. -/
theorem enorm_sub_le_lintegral_deriv_of_contDiffOn_Ioo
    (hf : ContDiffOn ℝ 1 f (Ioo a b)) (hcont : ContinuousOn f (Icc a b)) (hab : a ≤ b) :
    ‖f b - f a‖ₑ ≤ ∫⁻ x in Icc a b, ‖deriv f x‖ₑ := by
  rcases hab.eq_or_lt with rfl | hab_lt
  · simp
  -- Approximate by the interior intervals `Icc (a + δ n) (b - δ n)` with `δ n = (b - a) / (n + 2)`.
  let δ : ℕ → ℝ := fun n => (b - a) / (n + 2)
  have hba_pos : 0 < b - a := by linarith
  have hδ_pos : ∀ n, 0 < δ n := fun n => div_pos hba_pos (by positivity)
  have hδ_le_half : ∀ n, δ n ≤ (b - a) / 2 := fun n => by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith
    exact div_le_div_of_nonneg_left hba_pos.le (by norm_num) h2
  have hδ_bd : ∀ n, a + δ n ≤ b - δ n := fun n => by
    have := hδ_le_half n; linarith
  -- For each `n`, apply the closed-interval lemma to `[a + δ n, b - δ n]`.
  have hbound : ∀ n,
      ‖f (b - δ n) - f (a + δ n)‖ₑ ≤ ∫⁻ x in Icc a b, ‖deriv f x‖ₑ := fun n => by
    have hε := hδ_pos n
    have hsub_oo : Icc (a + δ n) (b - δ n) ⊆ Ioo a b := fun x hx =>
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hsub_cc : Icc (a + δ n) (b - δ n) ⊆ Icc a b := fun x hx =>
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hcd : ContDiffOn ℝ 1 f (Icc (a + δ n) (b - δ n)) := hf.mono hsub_oo
    exact (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hcd (hδ_bd n)).trans
      (lintegral_mono_set hsub_cc)
  -- `δ n → 0` as `n → ∞`.
  have hδ_lim : Tendsto δ atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => (b - a) / ((n : ℝ) + 2)) atTop (𝓝 ((b - a) * 0)) :=
      Tendsto.const_mul (b - a) (by simpa [div_eq_mul_inv] using h1.inv_tendsto_atTop)
    simpa [δ] using h2
  -- Therefore `a + δ n → a` and `b - δ n → b`.
  have ha_lim : Tendsto (fun n => a + δ n) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.add hδ_lim
  have hb_lim : Tendsto (fun n => b - δ n) atTop (𝓝 b) := by
    simpa using tendsto_const_nhds.sub hδ_lim
  -- Hence `f (a + δ n) → f a` and `f (b - δ n) → f b` by continuity of `f` on `Icc a b`.
  have hfa_lim : Tendsto (fun n => f (a + δ n)) atTop (𝓝 (f a)) := by
    have ha_mem : ∀ n, a + δ n ∈ Icc a b := fun n =>
      ⟨by linarith [hδ_pos n], by have := hδ_le_half n; linarith⟩
    exact ((hcont a (left_mem_Icc.mpr hab)).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨ha_lim, .of_forall ha_mem⟩))
  have hfb_lim : Tendsto (fun n => f (b - δ n)) atTop (𝓝 (f b)) := by
    have hb_mem : ∀ n, b - δ n ∈ Icc a b := fun n =>
      ⟨by have := hδ_le_half n; linarith, by linarith [hδ_pos n]⟩
    exact ((hcont b (right_mem_Icc.mpr hab)).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hb_lim, .of_forall hb_mem⟩))
  -- LHS limit: `‖f (b - δ n) - f (a + δ n)‖ₑ → ‖f b - f a‖ₑ`.
  have hLHS_lim : Tendsto (fun n => ‖f (b - δ n) - f (a + δ n)‖ₑ) atTop
      (𝓝 ‖f b - f a‖ₑ) :=
    (continuous_enorm.tendsto _).comp (hfb_lim.sub hfa_lim)
  -- Pass to the limit in the bound.
  exact le_of_tendsto' hLHS_lim hbound
