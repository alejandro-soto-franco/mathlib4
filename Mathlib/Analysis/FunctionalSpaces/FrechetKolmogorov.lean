/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.FunctionalSpaces.LpTranslation

/-!
# The Fréchet-Kolmogorov precompactness criterion in `L²(ℝⁿ)`

A family of `L²` functions that is uniformly bounded, supported in a fixed ball, and
uniformly Lipschitz under translation is totally bounded in `L²(ℝⁿ)`. This is the
Fréchet-Kolmogorov (Riesz-Kolmogorov) criterion, the precompactness engine behind the
Rellich-Kondrachov compact embedding.

The proof approximates each member of the family by its average over a fixed grid of
axis-aligned cubes of side `η`. The averaging operator lands in the finite-dimensional
span of the cube indicators, so its image is totally bounded; the approximation error is
controlled by the translation modulus through a cube-averaging estimate that reuses the
squared-Tonelli pattern of `MeasureTheory.integral_sq_sub_translation_le`. A finite net of
the averaged family, widened by the uniform approximation error, is a finite net of the
original family.

## Main results

* `MeasureTheory.sq_setIntegral_le`: the finite-measure Cauchy-Schwarz bound
  `(∫_s f)² ≤ μ.real s * ∫_s f²`.
* `MeasureTheory.totallyBounded_of_lipschitz_translation`: the Fréchet-Kolmogorov criterion.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace MeasureTheory

/-! ### A finite-measure Cauchy-Schwarz bound -/

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}

/-- **Finite-measure Cauchy-Schwarz with one constant factor.** For a set of finite measure,
the square of the integral of `f` is at most `μ.real s` times the integral of `f ^ 2`. This is
the general-measure analogue of `MeasureTheory.sq_intervalIntegral_le`. -/
theorem sq_setIntegral_le (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) {f : α → ℝ}
    (hf : IntegrableOn f s μ) (hf2 : IntegrableOn (fun x => (f x) ^ 2) s μ) :
    (∫ x in s, f x ∂μ) ^ 2 ≤ (μ.real s) * ∫ x in s, (f x) ^ 2 ∂μ := by
  have key : ∀ lam : ℝ,
      0 ≤ (μ.real s) * (lam * lam) + (-2 * ∫ x in s, f x ∂μ) * lam + ∫ x in s, (f x) ^ 2 ∂μ := by
    intro lam
    have hnn : 0 ≤ ∫ x in s, (f x - lam) ^ 2 ∂μ :=
      setIntegral_nonneg hs (fun x _ => by positivity)
    have i2 : IntegrableOn (fun x => (-(2 * lam)) * f x) s μ := hf.const_mul _
    have i12 : IntegrableOn (fun x => (f x) ^ 2 + (-(2 * lam)) * f x) s μ := hf2.add i2
    have i3 : IntegrableOn (fun _ : α => lam ^ 2) s μ := integrableOn_const hμs
    have hexp : ∫ x in s, (f x - lam) ^ 2 ∂μ
        = (μ.real s) * (lam * lam) + (-2 * ∫ x in s, f x ∂μ) * lam + ∫ x in s, (f x) ^ 2 ∂μ := by
      calc ∫ x in s, (f x - lam) ^ 2 ∂μ
          = ∫ x in s, ((f x) ^ 2 + (-(2 * lam)) * f x + lam ^ 2) ∂μ := by
            refine integral_congr_ae ?_; filter_upwards with x; ring
        _ = (∫ x in s, ((f x) ^ 2 + (-(2 * lam)) * f x) ∂μ) + (∫ _x in s, lam ^ 2 ∂μ) :=
            integral_add i12 i3
        _ = ((∫ x in s, (f x) ^ 2 ∂μ) + (∫ x in s, (-(2 * lam)) * f x ∂μ))
              + (∫ _x in s, lam ^ 2 ∂μ) := by rw [integral_add hf2 i2]
        _ = (μ.real s) * (lam * lam) + (-2 * ∫ x in s, f x ∂μ) * lam + ∫ x in s, (f x) ^ 2 ∂μ := by
            rw [integral_const_mul, setIntegral_const, smul_eq_mul]; ring
    rw [← hexp]; exact hnn
  have hdisc := discrim_le_zero key
  rw [discrim] at hdisc
  nlinarith [hdisc]

/-! ### The `L²` space, translation, and the squared norm as an integral -/

/-- `L²(ℝⁿ)` with Lebesgue measure. -/
abbrev EucL2 (n : ℕ) := Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))

variable {n : ℕ}

/-- The squared `L²` norm is the integral of the square. -/
theorem norm_sq_eq_integral_sq (g : EucL2 n) : ‖g‖ ^ 2 = ∫ x, (g x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial]
  simp_rw [pow_two]

/-- Translation by `h` as a linear isometry of `L²(ℝⁿ)`. -/
def transL2 (h : EuclideanSpace ℝ (Fin n)) : EucL2 n →ₗᵢ[ℝ] EucL2 n :=
  Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (· + h) (measurePreserving_add_right volume h)

theorem coeFn_transL2 (h : EuclideanSpace ℝ (Fin n)) (g : EucL2 n) :
    (transL2 h g : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] fun x => g (x + h) :=
  Lp.coeFn_compMeasurePreserving _ _

/-- The squared `L²` norm of a translation difference, as an integral. -/
theorem norm_sq_transL2_sub (h : EuclideanSpace ℝ (Fin n)) (g : EucL2 n) :
    ‖transL2 h g - g‖ ^ 2 = ∫ x, (g (x + h) - g x) ^ 2 := by
  have hnorm : ‖transL2 h g - g‖ ^ 2 = ∫ x, ((transL2 h g - g) x) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [RCLike.inner_apply, conj_trivial]
    simp_rw [pow_two]
  rw [hnorm]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (transL2 h g) g, coeFn_transL2 h g] with x hx hx1
  rw [hx]; simp only [Pi.sub_apply]; rw [hx1]

/-! ### The cube grid -/

/-- The half-open cube of side `η` at lattice index `k`, as a subset of `EuclideanSpace ℝ (Fin n)`. -/
def cube (η : ℝ) (k : Fin n → ℤ) : Set (EuclideanSpace ℝ (Fin n)) :=
  WithLp.ofLp ⁻¹' Set.univ.pi (fun i => Set.Ico (η * (k i : ℝ)) (η * ((k i : ℝ) + 1)))

theorem mem_cube {η : ℝ} {k : Fin n → ℤ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ cube η k ↔ ∀ i, x i ∈ Set.Ico (η * (k i : ℝ)) (η * ((k i : ℝ) + 1)) := by
  simp only [cube, mem_preimage, Set.mem_univ_pi]

theorem measurableSet_cube (η : ℝ) (k : Fin n → ℤ) : MeasurableSet (cube η k) :=
  (PiLp.volume_preserving_ofLp (ι := Fin n)).measurable
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico)

theorem volume_cube (η : ℝ) (k : Fin n → ℤ) :
    volume (cube η k) = (ENNReal.ofReal η) ^ n := by
  have hbox : volume (Set.univ.pi (fun i => Set.Ico (η * (k i : ℝ)) (η * ((k i : ℝ) + 1))))
      = (ENNReal.ofReal η) ^ n := by
    rw [volume_pi_pi]
    have hone : ∀ i : Fin n,
        volume (Set.Ico (η * (k i : ℝ)) (η * ((k i : ℝ) + 1))) = ENNReal.ofReal η := by
      intro i; rw [Real.volume_Ico]; congr 1; ring
    rw [Finset.prod_congr rfl (fun i _ => hone i)]; simp
  rw [cube, (PiLp.volume_preserving_ofLp (ι := Fin n)).measure_preimage
        (MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet, hbox]

theorem volume_cube_ne_top (η : ℝ) (k : Fin n → ℤ) :
    volume (cube η k) ≠ ⊤ := by
  rw [volume_cube]; exact (ENNReal.pow_lt_top ENNReal.ofReal_lt_top).ne

theorem volume_real_cube {η : ℝ} (hη : 0 ≤ η) (k : Fin n → ℤ) :
    volume.real (cube η k) = η ^ n := by
  rw [Measure.real, volume_cube, ENNReal.toReal_pow, ENNReal.toReal_ofReal hη]

/-- Cubes at distinct lattice indices are disjoint. -/
theorem cube_disjoint {η : ℝ} (hη : 0 < η) {k k' : Fin n → ℤ} (hk : k ≠ k') :
    Disjoint (cube η k) (cube η k') := by
  rw [Set.disjoint_left]
  rintro x hx hx'
  apply hk
  funext i
  rw [mem_cube] at hx hx'
  obtain ⟨hl, hu⟩ := hx i
  obtain ⟨hl', hu'⟩ := hx' i
  have c1 : η * (k i : ℝ) < η * ((k' i : ℝ) + 1) := lt_of_le_of_lt hl hu'
  have c2 : η * (k' i : ℝ) < η * ((k i : ℝ) + 1) := lt_of_le_of_lt hl' hu
  have d1 : (k i : ℝ) < (k' i : ℝ) + 1 := lt_of_mul_lt_mul_left c1 hη.le
  have d2 : (k' i : ℝ) < (k i : ℝ) + 1 := lt_of_mul_lt_mul_left c2 hη.le
  have e1 : k i < k' i + 1 := by exact_mod_cast d1
  have e2 : k' i < k i + 1 := by exact_mod_cast d2
  omega

/-- Two points of a common cube differ by less than `η` in each coordinate. -/
theorem coord_dist_lt_of_mem_cube {η : ℝ} {k : Fin n → ℤ} {x y : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ cube η k) (hy : y ∈ cube η k) (i : Fin n) : |x i - y i| < η := by
  rw [mem_cube] at hx hy
  obtain ⟨hl, hu⟩ := hx i
  obtain ⟨hl', hu'⟩ := hy i
  rw [abs_lt]; constructor <;> linarith

/-! ### The cube-averaging operator -/

/-- The `L²` class of the indicator of the cube `cube η k`. -/
def cubeIndicator (η : ℝ) (k : Fin n → ℤ) : EucL2 n :=
  indicatorConstLp 2 (measurableSet_cube η k) (volume_cube_ne_top η k) (1 : ℝ)

/-- The average value of `g` over the cube `cube η k`. -/
def cubeCoef (η : ℝ) (k : Fin n → ℤ) (g : EucL2 n) : ℝ :=
  (volume.real (cube η k))⁻¹ * ∫ x in cube η k, g x

/-- The cube-averaging operator: the piecewise-constant approximation of `g` on the grid of
side-`η` cubes indexed by `K`, as an element of `L²`. -/
def avg (η : ℝ) (K : Finset (Fin n → ℤ)) (g : EucL2 n) : EucL2 n :=
  ∑ k ∈ K, cubeCoef η k g • cubeIndicator η k

/-- The averaging operator as an honest piecewise-constant function. -/
def stepFun (η : ℝ) (K : Finset (Fin n → ℤ)) (g : EucL2 n) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => ∑ k ∈ K, cubeCoef η k g * (cube η k).indicator (fun _ => (1 : ℝ)) x

/-- The coercion of a finite `L²` sum is almost everywhere the pointwise sum. -/
theorem coeFn_lp_sum {ι : Type*} (s : Finset ι) (F : ι → EucL2 n) :
    (⇑(∑ i ∈ s, F i) : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] fun x => ∑ i ∈ s, (F i) x := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact Lp.coeFn_zero ℝ 2 volume
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (F i) (∑ j ∈ s, F j), ih] with x hx hx2
    rw [hx]; simp only [Pi.add_apply]; rw [hx2, Finset.sum_insert hi]

/-- The averaging operator agrees almost everywhere with its piecewise-constant representative. -/
theorem coeFn_avg (η : ℝ) (K : Finset (Fin n → ℤ)) (g : EucL2 n) :
    (avg η K g : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] stepFun η K g := by
  refine (coeFn_lp_sum K _).trans ?_
  have hterm : ∀ k ∈ K, (⇑(cubeCoef η k g • cubeIndicator η k) : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[volume] fun x => cubeCoef η k g * (cube η k).indicator (fun _ => (1 : ℝ)) x := by
    intro k _
    filter_upwards [Lp.coeFn_smul (cubeCoef η k g) (cubeIndicator η k),
      indicatorConstLp_coeFn (p := 2) (μ := volume) (hs := measurableSet_cube η k)
        (hμs := volume_cube_ne_top η k) (c := (1 : ℝ))] with x hx hx2
    rw [hx]; simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (cubeIndicator η k) x = (cube η k).indicator (fun _ => (1 : ℝ)) x from hx2]
  filter_upwards [(eventually_all_finset K).mpr hterm] with x hx
  exact Finset.sum_congr rfl (fun k hk => hx k hk)

/-- The averaging operator lands in the finite-dimensional span of the cube indicators. -/
theorem avg_mem_span (η : ℝ) (K : Finset (Fin n → ℤ)) (g : EucL2 n) :
    avg η K g ∈ Submodule.span ℝ (cubeIndicator η '' (K : Set (Fin n → ℤ))) := by
  refine Submodule.sum_mem _ (fun k hk => Submodule.smul_mem _ _ ?_)
  exact Submodule.subset_span ⟨k, hk, rfl⟩

/-- On a cube of the grid, the piecewise-constant representative equals that cube's average. -/
theorem stepFun_eq_on_cube {η : ℝ} (hη : 0 < η) {K : Finset (Fin n → ℤ)} {g : EucL2 n}
    {k₀ : Fin n → ℤ} (hk₀ : k₀ ∈ K) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ cube η k₀) :
    stepFun η K g x = cubeCoef η k₀ g := by
  unfold stepFun
  rw [Finset.sum_eq_single k₀]
  · rw [Set.indicator_of_mem hx]; ring
  · intro k _ hne
    rw [Set.indicator_of_notMem
      (fun hxk => absurd hx (Set.disjoint_left.mp (cube_disjoint hη hne) hxk)), mul_zero]
  · intro h; exact absurd hk₀ h

/-! ### The approximation error as a sum of cube variances -/

/-- On any cube the squared deviation of `g` from a constant is integrable. -/
theorem integrableOn_cube_sq_sub (η : ℝ) (k : Fin n → ℤ) (g : EucL2 n) (c : ℝ) :
    IntegrableOn (fun y => (g y - c) ^ 2) (cube η k) volume := by
  haveI : IsFiniteMeasure (volume.restrict (cube η k)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (volume_cube_ne_top η k).lt_top⟩
  have hg2 : MemLp (fun y => (g : EuclideanSpace ℝ (Fin n) → ℝ) y) 2
      (volume.restrict (cube η k)) := (Lp.memLp g).restrict (cube η k)
  have hc2 : MemLp (fun _ : EuclideanSpace ℝ (Fin n) => c) 2 (volume.restrict (cube η k)) :=
    memLp_const c
  exact (hg2.sub hc2).integrable_sq

/-- **The approximation error decomposes as a sum of cube variances.** When `g` is supported in
the union of the grid cubes, the squared `L²` distance from `g` to its cube-average is the sum
over cubes of the squared deviation of `g` from its average on that cube. -/
theorem norm_sq_sub_avg_eq {η : ℝ} (hη : 0 < η) {K : Finset (Fin n → ℤ)} {g : EucL2 n}
    (hsupp : ∀ᵐ x ∂volume, x ∉ (⋃ k ∈ K, cube η k) → g x = 0) :
    ‖g - avg η K g‖ ^ 2 = ∑ k ∈ K, ∫ x in cube η k, (g x - cubeCoef η k g) ^ 2 := by
  rw [norm_sq_eq_integral_sq]
  have hae : (fun x => ((g - avg η K g) x) ^ 2) =ᵐ[volume]
      fun x => ∑ k ∈ K, (cube η k).indicator (fun y => (g y - cubeCoef η k g) ^ 2) x := by
    filter_upwards [Lp.coeFn_sub g (avg η K g), coeFn_avg η K g, hsupp] with x hsub havg hsup
    rw [hsub]; simp only [Pi.sub_apply]; rw [havg]
    by_cases hmem : x ∈ ⋃ k ∈ K, cube η k
    · obtain ⟨k₀, hk₀K, hk₀⟩ := Set.mem_iUnion₂.mp hmem
      rw [stepFun_eq_on_cube hη hk₀K hk₀,
        Finset.sum_eq_single k₀
          (fun k _ hne => Set.indicator_of_notMem
            (fun hxk => absurd hk₀ (Set.disjoint_left.mp (cube_disjoint hη hne) hxk)) _)
          (fun h => absurd hk₀K h),
        Set.indicator_of_mem hk₀]
    · rw [hsup hmem]
      have hstep0 : stepFun η K g x = 0 :=
        Finset.sum_eq_zero (fun k hk => by
          rw [Set.indicator_of_notMem (fun hxk => hmem (Set.mem_iUnion₂.mpr ⟨k, hk, hxk⟩)),
            mul_zero])
      have hsum0 : (∑ k ∈ K, (cube η k).indicator (fun y => (g y - cubeCoef η k g) ^ 2) x) = 0 :=
        Finset.sum_eq_zero (fun k hk => Set.indicator_of_notMem
          (fun hxk => hmem (Set.mem_iUnion₂.mpr ⟨k, hk, hxk⟩)) _)
      rw [hstep0, hsum0]; norm_num
  rw [integral_congr_ae hae,
    integral_finsetSum K (fun k _ => (integrable_indicator_iff (measurableSet_cube η k)).mpr
      (integrableOn_cube_sq_sub η k g _))]
  exact Finset.sum_congr rfl (fun k _ => integral_indicator (measurableSet_cube η k))

/-! ### The cube-translation estimate -/

/-- The squared difference `(g x - g y) ^ 2` is integrable over a product of finite-measure sets. -/
theorem integrableOn_prod_sq_sub (g : EucL2 n) {s t : Set (EuclideanSpace ℝ (Fin n))}
    (hμs : volume s ≠ ⊤) (hμt : volume t ≠ ⊤) :
    IntegrableOn (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (g p.1 - g p.2) ^ 2) (s ×ˢ t) (volume.prod volume) := by
  haveI : IsFiniteMeasure (volume.restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμs.lt_top⟩
  haveI : IsFiniteMeasure (volume.restrict t) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμt.lt_top⟩
  rw [IntegrableOn, ← Measure.prod_restrict]
  have hgs : AEStronglyMeasurable (g : EuclideanSpace ℝ (Fin n) → ℝ) (volume.restrict s) :=
    (Lp.aestronglyMeasurable g).restrict
  have hgt : AEStronglyMeasurable (g : EuclideanSpace ℝ (Fin n) → ℝ) (volume.restrict t) :=
    (Lp.aestronglyMeasurable g).restrict
  have hmeas : AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (g p.1 - g p.2) ^ 2) ((volume.restrict s).prod (volume.restrict t)) :=
    ((hgs.comp_fst (ν := volume.restrict t)).sub (hgt.comp_snd (μ := volume.restrict s))).pow 2
  have hg2s : Integrable (fun x => (g x) ^ 2) (volume.restrict s) :=
    ((Lp.memLp g).restrict s).integrable_sq
  have hg2t : Integrable (fun y => (g y) ^ 2) (volume.restrict t) :=
    ((Lp.memLp g).restrict t).integrable_sq
  have hdom : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      2 * (g p.1) ^ 2 + 2 * (g p.2) ^ 2) ((volume.restrict s).prod (volume.restrict t)) :=
    ((hg2s.comp_fst (volume.restrict t)).const_mul 2).add ((hg2t.comp_snd (volume.restrict s)).const_mul 2)
  refine hdom.mono' hmeas ?_
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (g p.1 - g p.2), sq_nonneg (g p.1 + g p.2)]

/-- **Per-cube variance bound (Jensen).** The squared deviation of `g` from its average on a cube
is at most the rescaled double integral of the squared difference over that cube. -/
theorem cube_variance_le {η : ℝ} (hη : 0 < η) (k : Fin n → ℤ) (g : EucL2 n) :
    ∫ x in cube η k, (g x - cubeCoef η k g) ^ 2
      ≤ (η ^ n)⁻¹ * ∫ x in cube η k, ∫ y in cube η k, (g x - g y) ^ 2 := by
  have hηn : (0 : ℝ) < η ^ n := pow_pos hη n
  have hne : (η : ℝ) ^ n ≠ 0 := hηn.ne'
  have hμreal : volume.real (cube η k) = η ^ n := volume_real_cube hη.le k
  have hμne : volume (cube η k) ≠ ⊤ := volume_cube_ne_top η k
  have hgint : IntegrableOn (g : EuclideanSpace ℝ (Fin n) → ℝ) (cube η k) volume :=
    integrableOn_Lp_of_measure_ne_top g (by norm_num) hμne
  have hmarg : IntegrableOn (fun x => ∫ y in cube η k, (g x - g y) ^ 2) (cube η k) volume := by
    have hprod : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        (g p.1 - g p.2) ^ 2)
        ((volume.restrict (cube η k)).prod (volume.restrict (cube η k))) := by
      rw [Measure.prod_restrict]; exact integrableOn_prod_sq_sub g hμne hμne
    exact hprod.integral_prod_left
  have hpt_eq : ∀ x, (g x - cubeCoef η k g) = (η ^ n)⁻¹ * ∫ y in cube η k, (g x - g y) := by
    intro x
    have hI : ∫ y in cube η k, (g x - g y) = (η ^ n) * g x - ∫ y in cube η k, g y := by
      rw [integral_sub (integrableOn_const (C := g x) hμne) hgint, setIntegral_const, smul_eq_mul,
        hμreal]
    rw [hI, cubeCoef, hμreal]; field_simp
  have hpt_le : ∀ x ∈ cube η k,
      (g x - cubeCoef η k g) ^ 2 ≤ (η ^ n)⁻¹ * ∫ y in cube η k, (g x - g y) ^ 2 := by
    intro x _
    have hsqint : IntegrableOn (fun y => (g x - g y) ^ 2) (cube η k) volume := by
      have heq : (fun y => (g x - g y) ^ 2)
          = (fun y => ((g : EuclideanSpace ℝ (Fin n) → ℝ) y - g x) ^ 2) := by funext y; ring
      rw [heq]; exact integrableOn_cube_sq_sub η k g (g x)
    have hcs : (∫ y in cube η k, (g x - g y)) ^ 2 ≤ (η ^ n) * ∫ y in cube η k, (g x - g y) ^ 2 := by
      have := sq_setIntegral_le (measurableSet_cube η k) hμne
        ((integrableOn_const (C := g x) hμne).sub hgint) hsqint
      rwa [hμreal] at this
    rw [hpt_eq x, mul_pow]
    calc ((η ^ n)⁻¹) ^ 2 * (∫ y in cube η k, (g x - g y)) ^ 2
        ≤ ((η ^ n)⁻¹) ^ 2 * ((η ^ n) * ∫ y in cube η k, (g x - g y) ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = (η ^ n)⁻¹ * ∫ y in cube η k, (g x - g y) ^ 2 := by rw [sq]; field_simp
  calc ∫ x in cube η k, (g x - cubeCoef η k g) ^ 2
      ≤ ∫ x in cube η k, (η ^ n)⁻¹ * ∫ y in cube η k, (g x - g y) ^ 2 :=
        setIntegral_mono_on (integrableOn_cube_sq_sub η k g _) (hmarg.const_mul _)
          (measurableSet_cube η k) hpt_le
    _ = (η ^ n)⁻¹ * ∫ x in cube η k, ∫ y in cube η k, (g x - g y) ^ 2 := by
        rw [integral_const_mul]

end MeasureTheory
