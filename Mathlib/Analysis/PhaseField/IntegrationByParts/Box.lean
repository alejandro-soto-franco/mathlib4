/-
Copyright (c) 2026 Alejandro Jose Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Jose Soto Franco
-/
module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Divergence Theorem and Green's Identities on Boxes

Specialisation of `Mathlib.MeasureTheory.Integral.DivergenceTheorem` to the
case of a closed box `[a, b] ⊆ Fin n → ℝ`. This is the concrete case in
which `Mathlib.Analysis.PhaseField.IntegrationByParts`'s abstract divergence
theorem is unconditionally provable.

The derivation of the localized Allen–Cahn dissipation inequality
(`IsSolution.localizedDissipation`) reduces to Green's first identity, which
in turn reduces to the box divergence theorem by partition-of-unity in the
general smooth case. The box case is proved here.

## Main definitions

* `MeasureTheory.PhaseField.boxFaces` : the `2n` face boxes of `[a, b]`.
* `MeasureTheory.PhaseField.divergenceBox` : pointwise divergence of a
  vector field on `Fin n → ℝ`.
* `MeasureTheory.PhaseField.gradientBox` : pointwise gradient.
* `MeasureTheory.PhaseField.laplacianBox` : pointwise Laplacian.

## Main results

* `MeasureTheory.PhaseField.divergence_theorem_box` : Gauss–Green for boxes,
  derived from `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`.
* `MeasureTheory.PhaseField.green_first_identity_box` : Green's first identity
  for `f, g ∈ C²([a, b])`.

## References

* [MSTW24] Marshall-Stevens, Takada, Tonegawa, Workman, *Gradient flow of
  phase transitions with fixed contact angle* (2024).
* Evans, *Partial Differential Equations*, Appendix C.2.

## Tags

divergence theorem, Gauss-Green, box, integration by parts, Green's identity
-/

@[expose] public section

namespace MeasureTheory.PhaseField

open Set Finset MeasureTheory Function

variable {n : ℕ}

/-- Pointwise divergence of a vector field `X : (Fin n → ℝ) → (Fin n → ℝ)`. -/
noncomputable def divergenceBox (X : (Fin n → ℝ) → Fin n → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i, fderiv ℝ X x (Pi.single i 1) i

/-- Pointwise gradient of a scalar `f : (Fin n → ℝ) → ℝ`. -/
noncomputable def gradientBox (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => fderiv ℝ f x (Pi.single i 1)

/-- Pointwise Laplacian of `f`. -/
noncomputable def laplacianBox (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single i 1)

/-- The divergence equals `∑ᵢ fderiv X · eᵢ` where `eᵢ = Pi.single i 1`.
Tautological unfolding lemma. -/
theorem divergence_box_def (X : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) :
    divergenceBox X x = ∑ i, fderiv ℝ X x (Pi.single i 1) i := rfl

/-- **Box divergence theorem.** For a `C¹` vector field `X` on `[a, b]`,

`∫_{[a,b]} div X dx = ∑ᵢ (∫_{face i, +} Xᵢ - ∫_{face i, -} Xᵢ)`,

a direct repackaging of `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`
in terms of `divergenceBox`. -/
theorem divergence_theorem_box {a b : Fin (n + 1) → ℝ} (hle : a ≤ b)
    (X : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hX_cont : ContinuousOn X (Icc a b))
    (hX_diff : ∀ x ∈ Set.pi univ (fun i => Set.Ioo (a i) (b i)),
      HasFDerivAt X (fderiv ℝ X x) x)
    (hX_int : IntegrableOn (fun x => divergenceBox X x) (Icc a b)) :
    ∫ x in Icc a b, divergenceBox X x =
      ∑ i : Fin (n + 1),
        ((∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            X (i.insertNth (b i) x) i) -
          ∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            X (i.insertNth (a i) x) i) := by
  -- Direct application of Mathlib's box divergence theorem with the empty
  -- exceptional set.
  have h := MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable
    (a := a) (b := b) hle X (fderiv ℝ X) ∅ countable_empty hX_cont
    (fun x hx => hX_diff x hx.1) hX_int
  -- The Mathlib statement uses `∑ i, f' x (e i) i` with `e := Pi.single`;
  -- this matches our `divergenceBox` definition pointwise.
  simp only [divergenceBox] at *
  exact h

/-- **Box boundary functional applied to a vector field.** Given a vector
field `X : (Fin (n+1) → ℝ) → Fin (n+1) → ℝ`, this is the signed sum over the
`2(n+1)` faces of `[a, b]`, where each face contributes the integral of the
component of `X` parallel to its outward normal. This is the Mathlib
divergence-theorem RHS, packaged under one name. -/
noncomputable def boxBoundaryFlux (a b : Fin (n + 1) → ℝ)
    (X : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n + 1),
    ((∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        X (i.insertNth (b i) x) i) -
      ∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        X (i.insertNth (a i) x) i)

/-- **Box boundary integral of a scalar function.** Sums the integral of `f`
over the `2(n+1)` faces of `[a, b]`, each face equipped with its standard
`n`-dimensional Lebesgue measure. Used to define the surface energy
`∫_{∂Ω} σ(u) dH^{n-1}` for box domains, and the localized variant
`∫_{∂Ω} φ · σ(u) dH^{n-1}`. -/
noncomputable def boxBoundaryScalarIntegral (a b : Fin (n + 1) → ℝ)
    (f : (Fin (n + 1) → ℝ) → ℝ) : ℝ :=
  ∑ i : Fin (n + 1),
    ((∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        f (i.insertNth (b i) x)) +
      ∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        f (i.insertNth (a i) x))

/-- **Box divergence theorem, packaged form.** Wraps `divergence_theorem_box`
in `boxBoundaryFlux`. Fully proved. -/
theorem divergence_theorem_box_flux {a b : Fin (n + 1) → ℝ} (hle : a ≤ b)
    (X : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hX_cont : ContinuousOn X (Icc a b))
    (hX_diff : ∀ x ∈ Set.pi univ (fun i => Set.Ioo (a i) (b i)),
      HasFDerivAt X (fderiv ℝ X x) x)
    (hX_int : IntegrableOn (fun x => divergenceBox X x) (Icc a b)) :
    ∫ x in Icc a b, divergenceBox X x = boxBoundaryFlux a b X :=
  divergence_theorem_box hle X hX_cont hX_diff hX_int

/-- The Euclidean dot product on `Fin n → ℝ`. -/
noncomputable def dotProductBox (v w : Fin n → ℝ) : ℝ := ∑ i, v i * w i

/-- **Pointwise product rule for divergence.** For scalar `f` differentiable
at `x` and vector field `Y` differentiable at `x`,

`div(f · Y)(x) = ⟨∇f(x), Y(x)⟩ + f(x) · div Y(x)`.

Proof: by `fderiv_fun_smul`, `D(f • Y)(x) = f(x) • DY(x) + (Df(x)).smulRight Y(x)`.
Evaluating at `Pi.single i 1` and taking the `i`-th component, the per-component
derivative is `f(x) · ∂ᵢYᵢ(x) + ∂ᵢf(x) · Yᵢ(x)`. Summing over `i` gives the
identity, with the first sum collapsing into `f(x) · div Y(x)` and the second
into `⟨∇f(x), Y(x)⟩`. -/
theorem divergence_smul
    (f : (Fin n → ℝ) → ℝ) (Y : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ)
    (hf : DifferentiableAt ℝ f x) (hY : DifferentiableAt ℝ Y x) :
    divergenceBox (fun y => f y • Y y) x =
      dotProductBox (gradientBox f x) (Y x) + f x * divergenceBox Y x := by
  -- Step 1: derivative of the smul product.
  have hsmul : fderiv ℝ (fun y => f y • Y y) x =
      f x • fderiv ℝ Y x + (fderiv ℝ f x).smulRight (Y x) :=
    fderiv_fun_smul hf hY
  -- Step 2: per-component identity at `Pi.single i 1`.
  have hcomp : ∀ i,
      fderiv ℝ (fun y => f y • Y y) x (Pi.single i 1) i =
        f x * fderiv ℝ Y x (Pi.single i 1) i +
          fderiv ℝ f x (Pi.single i 1) * Y x i := by
    intro i
    rw [hsmul]
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  -- Step 3: assemble the sum.
  simp only [divergenceBox, gradientBox, dotProductBox]
  rw [show (∑ i, fderiv ℝ (fun y => f y • Y y) x (Pi.single i 1) i) =
        ∑ i, (f x * fderiv ℝ Y x (Pi.single i 1) i +
              fderiv ℝ f x (Pi.single i 1) * Y x i)
      from Finset.sum_congr rfl (fun i _ => hcomp i)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- **Divergence of the gradient equals the Laplacian.** Definitional after
commuting the projection-from-pi and `fderiv`. -/
theorem divergence_grad_eq_laplacian (g : (Fin n → ℝ) → ℝ)
    (hg : ContDiff ℝ 2 g) (x : Fin n → ℝ) :
    divergenceBox (gradientBox g) x = laplacianBox g x := by
  -- Both sides are `∑ i, (component derivative)`; we show termwise equality.
  simp only [divergenceBox, laplacianBox]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- For each `i`, the i-th term on each side is a derivative at `x` applied
  -- to `Pi.single i 1`. The LHS is the i-th component of `fderiv (fun y =>
  -- (fderiv g y (Pi.single i 1))_{j}) x (Pi.single i 1)`; the RHS is
  -- directly `fderiv (fun y => fderiv g y (Pi.single i 1)) x (Pi.single i 1)`.
  -- These coincide by `hasFDerivAt_pi'`.
  have hg_grad_diff : Differentiable ℝ (fun y => gradientBox g y) := by
    -- `gradientBox g` is `C¹` because `g ∈ C²`.
    intro z
    -- It suffices that each component `fun y => fderiv g y (Pi.single i 1)`
    -- is differentiable at z.
    change DifferentiableAt ℝ (fun y j => fderiv ℝ g y (Pi.single j 1)) z
    refine differentiableAt_pi.mpr (fun j => ?_)
    have hg1 : ContDiff ℝ 1 (fderiv ℝ g) :=
      ContDiff.fderiv_right (m := 1) (n := 2) hg (by norm_num)
    have h := (hg1.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)) z
    exact (h.clm_apply (differentiableAt_const _))
  -- Apply hasFDerivAt_pi to extract the i-th component of fderiv (gradientBox g).
  have hΦ : HasFDerivAt (gradientBox g) (fderiv ℝ (gradientBox g) x) x :=
    (hg_grad_diff x).hasFDerivAt
  have h_iff := hasFDerivAt_pi'.mp hΦ i
  -- h_iff : HasFDerivAt (fun y => gradientBox g y i) (proj i ∘L fderiv (gradientBox g) x) x
  have hcomp_eq : fderiv ℝ (fun y => gradientBox g y i) x =
      (ContinuousLinearMap.proj i).comp (fderiv ℝ (gradientBox g) x) := h_iff.fderiv
  -- Apply both sides to `Pi.single i 1`.
  have hev := congrArg (fun (φ : (Fin n → ℝ) →L[ℝ] ℝ) => φ (Pi.single i 1)) hcomp_eq
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.proj_apply] at hev
  -- `gradientBox g y i = fderiv g y (Pi.single i 1)` by definition.
  change fderiv ℝ (gradientBox g) x (Pi.single i 1) i =
       fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x (Pi.single i 1)
  rw [← hev]
  rfl

/-- **Green's first identity on a box.** For `f ∈ C¹` and `g ∈ C²` on `[a, b]`,

`∫_{[a,b]} (⟨∇f, ∇g⟩ + f · Δg) dx = boxBoundaryFlux a b (f · ∇g)`.

This is the divergence theorem applied to the vector field `f · ∇g`, using the
product rule `divergence_smul` and the identity `div(∇g) = Δg`. -/
theorem green_first_identity_box {a b : Fin (n + 1) → ℝ} (hle : a ≤ b)
    (f g : (Fin (n + 1) → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g)
    (h_int : IntegrableOn
      (fun x => dotProductBox (gradientBox f x) (gradientBox g x) +
                f x * laplacianBox g x) (Icc a b)) :
    (∫ x in Icc a b, dotProductBox (gradientBox f x) (gradientBox g x)) +
        (∫ x in Icc a b, f x * laplacianBox g x) =
      boxBoundaryFlux a b (fun y => f y • gradientBox g y) := by
  -- Pointwise: div(f · ∇g)(x) = ⟨∇f, ∇g⟩ + f · div(∇g) = ⟨∇f, ∇g⟩ + f · Δg.
  have hf_diff : Differentiable ℝ f :=
    hf.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hg_grad_C1 : ContDiff ℝ 1 (gradientBox g) := by
    change ContDiff ℝ 1 (fun y j => fderiv ℝ g y (Pi.single j 1))
    refine contDiff_pi.mpr (fun j => ?_)
    have : ContDiff ℝ 1 (fderiv ℝ g) :=
      ContDiff.fderiv_right (m := 1) (n := 2) hg (by norm_num)
    exact this.clm_apply contDiff_const
  have hg_grad_diff : Differentiable ℝ (gradientBox g) :=
    hg_grad_C1.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hpt : ∀ x,
      divergenceBox (fun y => f y • gradientBox g y) x =
        dotProductBox (gradientBox f x) (gradientBox g x) + f x * laplacianBox g x := by
    intro x
    rw [divergence_smul f (gradientBox g) x (hf_diff x) (hg_grad_diff x)]
    rw [divergence_grad_eq_laplacian g hg x]
  -- Integrate the pointwise identity, then apply box divergence theorem.
  have hsmul_diff : Differentiable ℝ (fun y => f y • gradientBox g y) :=
    fun y => (hf_diff y).smul (hg_grad_diff y)
  -- The vector field is C¹.
  have hsmul_C1' : ContDiff ℝ 1 (f • gradientBox g) := ContDiff.smul hf hg_grad_C1
  have hsmul_C1 : ContDiff ℝ 1 (fun y => f y • gradientBox g y) := hsmul_C1'
  have hsmul_int : IntegrableOn
      (fun x => divergenceBox (fun y => f y • gradientBox g y) x) (Icc a b) := by
    rw [show (fun x => divergenceBox (fun y => f y • gradientBox g y) x) =
        (fun x => dotProductBox (gradientBox f x) (gradientBox g x) +
                  f x * laplacianBox g x)
      from funext hpt]
    exact h_int
  have hdiv :=
    divergence_theorem_box_flux hle (fun y => f y • gradientBox g y)
      hsmul_C1.continuous.continuousOn
      (fun x _ => hsmul_diff.differentiableAt.hasFDerivAt)
      hsmul_int
  -- Rewrite LHS of hdiv using the pointwise identity.
  have hint_eq :
      ∫ x in Icc a b, divergenceBox (fun y => f y • gradientBox g y) x =
        ∫ x in Icc a b,
          (dotProductBox (gradientBox f x) (gradientBox g x) +
            f x * laplacianBox g x) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro x _
    exact hpt x
  rw [hint_eq] at hdiv
  -- Continuity of the two summands, used for integrability.
  have hf_cont : Continuous f := hf.continuous
  have hf_grad_cont : Continuous (gradientBox f) := by
    change Continuous (fun y j => fderiv ℝ f y (Pi.single j 1))
    refine continuous_pi (fun j => ?_)
    have : Continuous (fderiv ℝ f) :=
      ContDiff.continuous_fderiv hf (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    exact this.clm_apply continuous_const
  have hg_grad_cont : Continuous (gradientBox g) := hg_grad_C1.continuous
  have hg_lap_cont : Continuous (laplacianBox g) := by
    change Continuous (fun x => ∑ i,
      fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x (Pi.single i 1))
    refine continuous_finset_sum _ (fun i _ => ?_)
    have hg_fderiv_C1 : ContDiff ℝ 1 (fderiv ℝ g) :=
      ContDiff.fderiv_right (m := 1) (n := 2) hg (by norm_num)
    have hi_C1 : ContDiff ℝ 1 (fun y => fderiv ℝ g y (Pi.single i 1)) :=
      hg_fderiv_C1.clm_apply contDiff_const
    have : Continuous (fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1))) :=
      ContDiff.continuous_fderiv hi_C1 (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    exact this.clm_apply continuous_const
  have h_dot_cont : Continuous (fun x =>
      dotProductBox (gradientBox f x) (gradientBox g x)) := by
    change Continuous (fun x => ∑ i, gradientBox f x i * gradientBox g x i)
    refine continuous_finset_sum _ (fun i _ => ?_)
    exact ((continuous_apply i).comp hf_grad_cont).mul
      ((continuous_apply i).comp hg_grad_cont)
  have h_fΔ_cont : Continuous (fun x => f x * laplacianBox g x) :=
    hf_cont.mul hg_lap_cont
  -- Integrability of each summand on Icc a b.
  have h_dot_int :
      IntegrableOn (fun x =>
        dotProductBox (gradientBox f x) (gradientBox g x)) (Icc a b) :=
    h_dot_cont.continuousOn.integrableOn_Icc
  have h_fΔ_int :
      IntegrableOn (fun x => f x * laplacianBox g x) (Icc a b) :=
    h_fΔ_cont.continuousOn.integrableOn_Icc
  -- Split the integral of the sum into two integrals.
  rw [MeasureTheory.integral_add h_dot_int h_fΔ_int] at hdiv
  exact hdiv

end MeasureTheory.PhaseField
