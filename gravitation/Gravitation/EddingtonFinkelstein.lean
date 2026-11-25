/-
Copyright (c) 2026 The Gravitation formalisation contributors.
Released under Apache 2.0 license as described in the file LICENSE.

# Ingoing Eddington–Finkelstein chart

## i. Overview

This module adds the ingoing Eddington–Finkelstein chart for Schwarzschild
spacetime.  In coordinates `(v, r, θ, φ)`, with `v = t + r*` and
`dr*/dr = (1 - 2M/r)⁻¹`, the line element is

`ds² = -(1 - 2M/r) dv² + 2 dv dr + r² dΩ²`.

The cross term makes the metric nondegenerate at the horizon `r = 2M`, where
the Schwarzschild `(t, r, θ, φ)` components have `g_rr = (1 - 2M/r)⁻¹`
divergent.  The chart still excludes the curvature singularity `r = 0` and the
polar axis `sin θ = 0`, but it removes the horizon obstruction.

This is a chart-level metric and inverse.  It is not packaged as a
`ChartSpacetime`, whose `chart` field is a global equivalence to all of
`Fin 4 → ℝ`; the Eddington–Finkelstein domain is the open set
`r ≠ 0 ∧ sin θ ≠ 0`.

## ii. Key results

- `metric`, `metricInv` : the ingoing Eddington–Finkelstein components and
  their explicit inverse.
- `metricTensor` : a bundled `MetricTensor 4` for `r ≠ 0` and `sin θ ≠ 0`,
  with no `1 - 2M/r ≠ 0` hypothesis.
- `horizonTensor` : the same bundle at `r = 2M` when `M ≠ 0`.
- `horizonTensor_ginv_rr`, `horizonTensor_g_vr` : the inverse `rr` component
  vanishes while the cross component remains `1`, so the horizon is regular.

## iii. Table of contents

- A. Metric and inverse
- B. The horizon `r = 2M`

## iv. References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019,
  Ch. 7, pp. 174–175. [ref: Carroll1997, pp. 174–175]
-/

module

public import Gravitation.Relativity.Metrics.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

namespace GeneralRelativity

namespace EddingtonFinkelstein

/-- Ingoing Eddington–Finkelstein metric in `(v, r, θ, φ)` coordinates. -/
noncomputable def metric (M : ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  fun i j =>
    if i = 0 then
      if j = 0 then -(1 - 2 * M / x 1)
      else if j = 1 then 1 else 0
    else if i = 1 then
      if j = 0 then 1 else 0
    else if i = 2 then
      if j = 2 then (x 1) ^ 2 else 0
    else
      if j = 3 then (x 1) ^ 2 * Real.sin (x 2) ^ 2 else 0

/-- Explicit inverse of `metric`.  The `(v,r)` block is
`[[-(1 - 2M/r), 1], [1, 0]]⁻¹ = [[0, 1], [1, 1 - 2M/r]]`. -/
noncomputable def metricInv (M : ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  fun i j =>
    if i = 0 then
      if j = 1 then 1 else 0
    else if i = 1 then
      if j = 0 then 1
      else if j = 1 then 1 - 2 * M / x 1
      else 0
    else if i = 2 then
      if j = 2 then ((x 1) ^ 2)⁻¹ else 0
    else
      if j = 3 then ((x 1) ^ 2 * Real.sin (x 2) ^ 2)⁻¹ else 0

lemma metric_symm (M : ℝ) (x : Fin 4 → ℝ) : IsSymm (metric M x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [metric, Matrix.transpose_apply]

lemma metric_mul_inv (M : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hsin : Real.sin (x 2) ≠ 0) :
    metric M x * metricInv M x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metric, metricInv, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals field_simp [hr, hsin]

lemma metricInv_mul (M : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hsin : Real.sin (x 2) ≠ 0) :
    metricInv M x * metric M x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metric, metricInv, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals field_simp [hr, hsin]

/-- The ingoing Eddington–Finkelstein metric as a bundled `MetricTensor 4`.
The only coordinate exclusions are the curvature singularity `r = 0` and the
polar axis `sin θ = 0`; in particular there is no horizon hypothesis. -/
noncomputable def metricTensor (M : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hsin : Real.sin (x 2) ≠ 0) : MetricTensor 4 where
  g := metric M x
  ginv := metricInv M x
  symm := metric_symm M x
  inv_left := metric_mul_inv M x hr hsin
  inv_right := metricInv_mul M x hr hsin

/-- The horizon point `r = 2M` in Eddington–Finkelstein coordinates. -/
def horizonPoint (M v θ φ : ℝ) : Fin 4 → ℝ :=
  ![v, 2 * M, θ, φ]

lemma horizonPoint_one (M v θ φ : ℝ) : horizonPoint M v θ φ 1 = 2 * M := by
  simp [horizonPoint]

lemma horizonPoint_two (M v θ φ : ℝ) : horizonPoint M v θ φ 2 = θ := by
  simp [horizonPoint]

/-- The Eddington–Finkelstein `MetricTensor 4` at the horizon `r = 2M`. -/
noncomputable def horizonTensor (M v θ φ : ℝ) (hM : M ≠ 0)
    (hsin : Real.sin θ ≠ 0) : MetricTensor 4 :=
  metricTensor M (horizonPoint M v θ φ)
    (by
      simp only [horizonPoint_one]
      exact mul_ne_zero two_ne_zero hM)
    (by
      simpa [horizonPoint] using hsin)

/-- At the horizon the `rr` metric component vanishes, as it must in this
chart. -/
lemma horizonTensor_g_rr (M v θ φ : ℝ) (hM : M ≠ 0)
    (hsin : Real.sin θ ≠ 0) : (horizonTensor M v θ φ hM hsin).g 1 1 = 0 := by
  simp [horizonTensor, metricTensor, metric, horizonPoint]

/-- At the horizon the inverse `rr` component also vanishes: there is no
divergent `(1 - 2M/r)⁻¹` factor. -/
lemma horizonTensor_ginv_rr (M v θ φ : ℝ) (hM : M ≠ 0)
    (hsin : Real.sin θ ≠ 0) : (horizonTensor M v θ φ hM hsin).ginv 1 1 = 0 := by
  simp [horizonTensor, metricTensor, metricInv, horizonPoint]
  field_simp [hM]
  norm_num

/-- The cross component remains `1` at the horizon, so the vanishing `rr`
components do not make the metric degenerate. -/
lemma horizonTensor_g_vr (M v θ φ : ℝ) (hM : M ≠ 0)
    (hsin : Real.sin θ ≠ 0) : (horizonTensor M v θ φ hM hsin).g 0 1 = 1 := by
  simp [horizonTensor, metricTensor, metric, horizonPoint]

end EddingtonFinkelstein

end GeneralRelativity
