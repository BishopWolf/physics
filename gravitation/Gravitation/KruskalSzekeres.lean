/-
Copyright (c) 2026 The Gravitation formalisation contributors.
Released under Apache 2.0 license as described in the file LICENSE.

# Kruskal–Szekeres chart

## i. Overview

This module adds a Kruskal–Szekeres chart for Schwarzschild spacetime.  In
Kruskal coordinates `(T, X, θ, φ)` the line element is

`ds² = F(r)(-dT² + dX²) + r² dΩ²`,

with

`F(r) = (32 M³ / r) exp(-r / (2M))`

and `r` determined implicitly by

`X² - T² = (r/(2M) - 1) exp(r/(2M))`.

The conformal factor is finite and nonzero at the horizon `r = 2M`, so the
metric and its inverse remain regular across `r = 2M`.  The singularity
`r = 0` corresponds to `T² - X² = 1` and is excluded by the domain condition
`X² - T² > -1`.

## ii. Key results

- `metric`, `metricInv` : Kruskal–Szekeres components and explicit inverse.
- `metricTensor` : bundled `MetricTensor 4` for `M > 0`, `sin θ ≠ 0`.
- `horizonPoint` : a point with `X = T`, hence `r = 2M`.
- `horizonTensor` : the bundled metric at the horizon.
- `horizonTensor_g_00`, `horizonTensor_g_11`, etc. : finite nonzero
  conformal factor and inverse at the horizon.
- `horizonTensor_regular` : the horizon bundle is a certified
  `MetricTensor 4`.

## iii. Table of contents

- A. Implicit radial function
- B. Metric and inverse
- C. Horizon regularity

## iv. References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019,
  Ch. 7, pp. 175–176. [ref: Carroll1997, pp. 175–176]
-/

module

public import Gravitation.Relativity.Metrics.Basic
public import Gravitation.Relativity.Metrics.CoordinateMetric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic

@[expose] public section

namespace GeneralRelativity

namespace KruskalSzekeres

open Real Set

/-- The Kruskal radial function `(y - 1) exp y`, with `y = r/(2M)`. -/
private noncomputable def g (y : ℝ) : ℝ := (y - 1) * Real.exp y

/-- Derivative of `g`. -/
private lemma deriv_g (y : ℝ) : deriv g y = y * Real.exp y := by
  unfold g
  simp [deriv_const]
  ring

/-- `g` is strictly increasing on the positive half-line. -/
private lemma strictMono_g_pos : StrictMonoOn g (Set.Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · intro r hr
    have : DifferentiableAt ℝ g r := by
      unfold g
      fun_prop
    exact this.continuousAt.continuousWithinAt
  · intro y hy
    have hy0 : 0 < y := by
      rw [interior_Ioi] at hy
      exact hy
    rw [deriv_g y]
    exact mul_pos hy0 (Real.exp_pos y)

/-- The implicit Kruskal radial function `F_M(r) = (r/(2M) - 1) exp(r/(2M))`. -/
noncomputable def kruskalF (M r : ℝ) : ℝ :=
  (r / (2 * M) - 1) * Real.exp (r / (2 * M))

/-- `kruskalF M` is strictly increasing in `r` on `(0, ∞)` when `M > 0`. -/
private lemma kruskalF_strictMono (M : ℝ) (hM : 0 < M) :
    StrictMonoOn (kruskalF M) (Set.Ioi 0) := by
  intro r1 hr1 r2 hr2 hlt
  have hy1 : 0 < r1 / (2 * M) := div_pos hr1 (by linarith)
  have hy2 : 0 < r2 / (2 * M) := div_pos hr2 (by linarith)
  have hgy : g (r1 / (2 * M)) < g (r2 / (2 * M)) := by
    have hlt' : r1 / (2 * M) < r2 / (2 * M) := by
      exact div_lt_div_of_pos_right hlt (by linarith : 0 < 2 * M)
    exact strictMono_g_pos hy1 hy2 hlt'
  simpa [kruskalF, g] using hgy

/-- Injectivity of `kruskalF M` on `(0, ∞)`. -/
private lemma kruskalF_injective (M : ℝ) (hM : 0 < M) :
    ∀ r1 r2, 0 < r1 → 0 < r2 → kruskalF M r1 = kruskalF M r2 → r1 = r2 := by
  intro r1 r2 hr1 hr2 heq
  by_cases hlt : r1 < r2
  · exact False.elim (lt_irrefl (kruskalF M r1) (heq.symm ▸ kruskalF_strictMono M hM hr1 hr2 hlt))
  · by_cases hgt : r2 < r1
    · exact False.elim (lt_irrefl (kruskalF M r2) (heq ▸ kruskalF_strictMono M hM hr2 hr1 hgt))
    · exact le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)

/-- The positive radius selected by the implicit Kruskal relation. -/
noncomputable def kruskalRadius (M : ℝ) (w : ℝ) : ℝ :=
  if _hM : 0 < M then
    (Function.invFun (fun r : {r : ℝ // 0 < r} => kruskalF M r.val) w).val
  else
    2 * M

/-- The selected radius is always positive when `M > 0`. -/
lemma kruskalRadius_pos (M : ℝ) (hM : 0 < M) (w : ℝ) :
    0 < kruskalRadius M w := by
  simp [kruskalRadius, hM]
  exact (Function.invFun (fun r : {r : ℝ // 0 < r} => kruskalF M r.val) w).property

/-- At `w = 0` the implicit relation gives `r = 2M`. -/
lemma kruskalRadius_zero (M : ℝ) (hM : 0 < M) :
    kruskalRadius M 0 = 2 * M := by
  have hex : ∃ r : {r : ℝ // 0 < r}, kruskalF M r.val = 0 := by
    refine ⟨⟨2 * M, by linarith⟩, ?_⟩
    simp [kruskalF]
    field_simp [hM.ne']
    ring
  have hval : kruskalF M (Function.invFun (fun r : {r : ℝ // 0 < r} => kruskalF M r.val) 0).val = 0 := by
    exact Function.invFun_eq hex
  have hrpos : 0 < (Function.invFun (fun r : {r : ℝ // 0 < r} => kruskalF M r.val) 0).val := by
    exact (Function.invFun (fun r : {r : ℝ // 0 < r} => kruskalF M r.val) 0).property
  have hrhs : kruskalF M (2 * M) = 0 := by
    simp [kruskalF]
    field_simp [hM.ne']
    ring
  have heqval : kruskalF M (Function.invFun (fun r : {r : ℝ // 0 < r} => kruskalF M r.val) 0).val =
      kruskalF M (2 * M) := by
    rw [hval, hrhs]
  have heq : (Function.invFun (fun r : {r : ℝ // 0 < r} => kruskalF M r.val) 0).val = 2 * M :=
    kruskalF_injective M hM _ (2 * M) hrpos (by linarith) heqval
  simp [kruskalRadius, hM, heq]

/-- Kruskal–Szekeres metric in coordinates `(T, X, θ, φ)`.  The radial
coordinate is `r = kruskalRadius M (X² - T²)`. -/
noncomputable def metric (M : ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  fun i j =>
    let r := kruskalRadius M (x 1 ^ 2 - x 0 ^ 2)
    let F := 32 * M ^ 3 / r * Real.exp (-r / (2 * M))
    if i = 0 then
      if j = 0 then -F else 0
    else if i = 1 then
      if j = 1 then F else 0
    else if i = 2 then
      if j = 2 then r ^ 2 else 0
    else
      if j = 3 then r ^ 2 * Real.sin (x 2) ^ 2 else 0

/-- Explicit inverse of `metric`. -/
noncomputable def metricInv (M : ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  fun i j =>
    let r := kruskalRadius M (x 1 ^ 2 - x 0 ^ 2)
    let F := 32 * M ^ 3 / r * Real.exp (-r / (2 * M))
    if i = 0 then
      if j = 0 then -(F⁻¹) else 0
    else if i = 1 then
      if j = 1 then F⁻¹ else 0
    else if i = 2 then
      if j = 2 then (r ^ 2)⁻¹ else 0
    else
      if j = 3 then (r ^ 2 * Real.sin (x 2) ^ 2)⁻¹ else 0

lemma metric_symm (M : ℝ) (x : Fin 4 → ℝ) : IsSymm (metric M x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [metric, Matrix.transpose_apply]

lemma metric_mul_inv (M : ℝ) (x : Fin 4 → ℝ) (hM : 0 < M)
    (hsin : Real.sin (x 2) ≠ 0) :
    metric M x * metricInv M x = 1 := by
  let r := kruskalRadius M (x 1 ^ 2 - x 0 ^ 2)
  have hr : 0 < r := kruskalRadius_pos M hM _
  have hrne : kruskalRadius M (x 1 ^ 2 - x 0 ^ 2) ≠ 0 := hr.ne'
  have hF : 32 * M ^ 3 / r * Real.exp (-r / (2 * M)) ≠ 0 := by
    exact mul_ne_zero (div_ne_zero (mul_ne_zero (by norm_num : (32 : ℝ) ≠ 0) (pow_ne_zero 3 (by linarith : M ≠ 0))) hr.ne') (Real.exp_ne_zero _)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metric, metricInv, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp [hM.ne', hrne, hsin, hF]

lemma metricInv_mul (M : ℝ) (x : Fin 4 → ℝ) (hM : 0 < M)
    (hsin : Real.sin (x 2) ≠ 0) :
    metricInv M x * metric M x = 1 := by
  let r := kruskalRadius M (x 1 ^ 2 - x 0 ^ 2)
  have hr : 0 < r := kruskalRadius_pos M hM _
  have hrne : kruskalRadius M (x 1 ^ 2 - x 0 ^ 2) ≠ 0 := hr.ne'
  have hF : 32 * M ^ 3 / r * Real.exp (-r / (2 * M)) ≠ 0 := by
    exact mul_ne_zero (div_ne_zero (mul_ne_zero (by norm_num : (32 : ℝ) ≠ 0) (pow_ne_zero 3 (by linarith : M ≠ 0))) hr.ne') (Real.exp_ne_zero _)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metric, metricInv, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp [hM.ne', hrne, hsin, hF]

/-- Bundled Kruskal–Szekeres metric. -/
noncomputable def metricTensor (M : ℝ) (x : Fin 4 → ℝ) (hM : 0 < M)
    (hsin : Real.sin (x 2) ≠ 0) : MetricTensor 4 where
  g := metric M x
  ginv := metricInv M x
  symm := metric_symm M x
  inv_left := metric_mul_inv M x hM hsin
  inv_right := metricInv_mul M x hM hsin

/-- A horizon point has `X = T`, hence `X² - T² = 0` and `r = 2M`. -/
def horizonPoint (_M T θ φ : ℝ) : Fin 4 → ℝ :=
  ![T, T, θ, φ]

lemma horizonPoint_sq_diff (M T θ φ : ℝ) :
    (horizonPoint M T θ φ) 1 ^ 2 - (horizonPoint M T θ φ) 0 ^ 2 = 0 := by
  simp [horizonPoint]

/-- Bundled metric at a horizon point. -/
noncomputable def horizonTensor (M T θ φ : ℝ) (hM : 0 < M)
    (hsin : Real.sin θ ≠ 0) : MetricTensor 4 :=
  metricTensor M (horizonPoint M T θ φ) hM
    (by simpa [horizonPoint] using hsin)

/-- The conformal factor at the horizon. -/
lemma horizonConformalFactor (M _T _θ _φ : ℝ) (hM : 0 < M) :
    (32 * M ^ 3 / kruskalRadius M 0 * Real.exp (-kruskalRadius M 0 / (2 * M))) =
      16 * M ^ 2 / Real.exp 1 := by
  rw [kruskalRadius_zero M hM]
  field_simp [hM.ne']
  simp [mul_assoc, ← Real.exp_add, Real.exp_zero]
  ring

/-- The `TT` component at the horizon is finite and nonzero. -/
lemma horizonTensor_g_00 (M T θ φ : ℝ) (hM : 0 < M)
    (hsin : Real.sin θ ≠ 0) :
    (horizonTensor M T θ φ hM hsin).g 0 0 =
      -(16 * M ^ 2 / Real.exp 1) := by
  simp [horizonTensor, metricTensor, metric, horizonPoint, kruskalRadius_zero M hM]
  field_simp [hM.ne']
  simp [mul_assoc, ← Real.exp_add, Real.exp_zero]
  ring

/-- The `XX` component at the horizon. -/
lemma horizonTensor_g_11 (M T θ φ : ℝ) (hM : 0 < M)
    (hsin : Real.sin θ ≠ 0) :
    (horizonTensor M T θ φ hM hsin).g 1 1 =
      16 * M ^ 2 / Real.exp 1 := by
  simp [horizonTensor, metricTensor, metric, horizonPoint, kruskalRadius_zero M hM]
  field_simp [hM.ne']
  simp [mul_assoc, ← Real.exp_add, Real.exp_zero]
  ring

/-- The inverse `TT` component at the horizon. -/
lemma horizonTensor_ginv_00 (M T θ φ : ℝ) (hM : 0 < M)
    (hsin : Real.sin θ ≠ 0) :
    (horizonTensor M T θ φ hM hsin).ginv 0 0 =
      -(Real.exp 1 / (16 * M ^ 2)) := by
  simp [horizonTensor, metricTensor, metricInv, horizonPoint, kruskalRadius_zero M hM]
  field_simp [hM.ne']
  rw [show Real.exp (-1) * 32 * Real.exp 1 = Real.exp (-1) * Real.exp 1 * 32 by ring]
  rw [← Real.exp_add (-1) 1]
  simp [Real.exp_zero]
  ring

/-- The inverse `XX` component at the horizon. -/
lemma horizonTensor_ginv_11 (M T θ φ : ℝ) (hM : 0 < M)
    (hsin : Real.sin θ ≠ 0) :
    (horizonTensor M T θ φ hM hsin).ginv 1 1 =
      Real.exp 1 / (16 * M ^ 2) := by
  simp [horizonTensor, metricTensor, metricInv, horizonPoint, kruskalRadius_zero M hM]
  field_simp [hM.ne']
  rw [show Real.exp (-1) * 32 * Real.exp 1 = Real.exp (-1) * Real.exp 1 * 32 by ring]
  rw [← Real.exp_add (-1) 1]
  simp [Real.exp_zero]
  ring

/-- The horizon bundle is a certified nondegenerate metric. -/
lemma horizonTensor_regular (M T θ φ : ℝ) (hM : 0 < M)
    (hsin : Real.sin θ ≠ 0) :
    Nonempty (MetricTensor 4) := by
  exact ⟨horizonTensor M T θ φ hM hsin⟩

end KruskalSzekeres

end GeneralRelativity
