/-
Copyright (c) 2026 The Gravitation formalisation contributors.
Released under Apache 2.0 license as described in the file LICENSE.

# Chart-level initial data

## i. Overview

This file provides the chart-level M2 layer by connecting a chart spacetime to
the existing ADM `InitialData` structure.  The induced spatial metric is read
from the `t = 0` slice of the chart metric.  The file packages smooth chart
regularity, the slice embedding and restriction of the metric to it, and the
constraint residual of bundled initial data.

The regularity here is smooth (`ContDiff`) component regularity on a chart, not
manifold Sobolev `H^s` theory: Sobolev spaces, trace/embedding estimates and
constraint solving remain outside this interface.

## ii. Key results

- `ChartSpacetime.spatialMetric`, `ChartSpacetime.spatialMetricField` : the
  spatial metric induced on the `t = 0` chart slice.
- `spatialRiemannTensorOf` : the 3D Riemann tensor derived from a metric field
  and packaged as a `RiemannTensor 3` using the coordinate skew, pair-symmetry
  and Bianchi theorems.
- `extrinsicDerivativeOf` : the momentum-constraint table `dK_μij = ∂_μ K_ij`
  derived from an extrinsic-curvature field.
- `ChartInitialData`, `ChartInitialData.ofDerivedData` : bundled chart initial
  data and the constructor taking the derived curvature and derivative data.
- `ChartInitialData.constraintResidual_eq_zero` : bundled vacuum data have zero
  constraint residual.

## iii. Table of contents

- A. The chart slice and its induced metric
- B. Derived curvature and extrinsic-curvature data
- C. Bundled chart initial data and constraints

## iv. References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019,
  Ch. 4, p. 104. [ref: Carroll1997, p. 104]
* R. Arnowitt, S. Deser, and C. W. Misner, *The Dynamics of General
  Relativity*, arXiv:gr-qc/0405109, p. 1. [ref: ADM1962, p. 1]
-/

module

public import Gravitation.Bianchi
public import Gravitation.ManifoldInterface
public import Gravitation.Relativity.General.InitialData
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

namespace GeneralRelativity

open Filter Topology
open scoped ContDiff

/-- The `t = 0` coordinate slice of a four-dimensional chart. -/
def spacetimeSlice (x : Fin 3 → ℝ) : SpacetimeChart :=
  Fin.cons 0 x

/-- The slice map is injective. -/
lemma spacetimeSlice_injective : Function.Injective spacetimeSlice := by
  change Function.Injective
    (Fin.cons (n := 3) (α := fun _ : Fin 4 => ℝ) (0 : ℝ))
  exact Fin.cons_right_injective 0

/-- The slice map is smooth as a map between chart coordinate spaces. -/
lemma contDiff_spacetimeSlice : ContDiff ℝ ∞ spacetimeSlice := by
  rw [contDiff_pi]
  intro i
  refine Fin.cases ?_ ?_ i
  · simpa [spacetimeSlice] using
      (contDiff_const : ContDiff ℝ ∞ fun _ : Fin 3 → ℝ => (0 : ℝ))
  · intro j
    simpa [spacetimeSlice] using
      (contDiff_apply (𝕜 := ℝ) (n := ∞) (F' := fun _ : Fin 3 => ℝ) j)

/-- Smoothness of the metric components in a chart.  This is the chart-level
regularity input for M2; it is stronger than, and not a substitute for,
manifold Sobolev regularity. -/
def ChartSpacetime.IsSmooth (X : ChartSpacetime) : Prop :=
  ∀ i j : Fin 4, ContDiff ℝ ∞ fun x : SpacetimeChart => X.coordinateMetric x i j

/-- The spatial metric induced on the `t = 0` chart slice. -/
noncomputable def ChartSpacetime.spatialMetric (X : ChartSpacetime) : Tensor2 3 :=
  fun i j => X.coordinateMetric 0 (Fin.succ i) (Fin.succ j)

/-- The spatial metric as a field on the three-dimensional slice. -/
noncomputable def ChartSpacetime.spatialMetricField
    (X : ChartSpacetime) : (Fin 3 → ℝ) → Tensor2 3 :=
  fun y i j => X.coordinateMetric (spacetimeSlice y) (Fin.succ i) (Fin.succ j)

/-- The spatial metric field restricts to the previously defined slice metric at
the origin. -/
lemma ChartSpacetime.spatialMetricField_zero (X : ChartSpacetime) :
    X.spatialMetricField 0 = X.spatialMetric := by
  have hzero : spacetimeSlice (0 : Fin 3 → ℝ) = 0 := by
    funext k
    cases k using Fin.cases <;> simp [spacetimeSlice]
  ext i j
  simp [ChartSpacetime.spatialMetricField, ChartSpacetime.spatialMetric, hzero]

/-- Smooth chart metrics restrict to smooth spatial metric components on the
`t = 0` slice. -/
lemma ChartSpacetime.spatialMetricField_contDiff (X : ChartSpacetime)
    (hX : X.IsSmooth) (i j : Fin 3) :
    ContDiff ℝ ∞ fun y : Fin 3 → ℝ => X.spatialMetricField y i j := by
  change ContDiff ℝ ∞
    ((fun x : SpacetimeChart => X.coordinateMetric x (Fin.succ i) (Fin.succ j)) ∘
      spacetimeSlice)
  exact (hX (Fin.succ i) (Fin.succ j)).comp contDiff_spacetimeSlice

/-- Extensionality for covariant Riemann tensors: equality of all components
implies equality of the bundled tensor. -/
lemma riemannTensor_ext {n : ℕ} {R S : RiemannTensor n}
    (h : ∀ i j k l, R.comp i j k l = S.comp i j k l) : R = S := by
  cases R with
  | mk comp skew pair bianchi =>
    cases S with
    | mk comp' skew' pair' bianchi' =>
      have hcomp : comp = comp' := by
        funext i j k l
        exact h i j k l
      subst hcomp
      simp

/-- The `R3` tensor derived from a 3-metric field: lower the mixed coordinate
Riemann tensor with the metric and use the coordinate skew, pair-symmetry and
Bianchi theorems to fill the `RiemannTensor` fields.
See arXiv:gr-qc/9712019, pp. 72–73. [ref: Carroll1997, pp. 72–73] -/
noncomputable def spatialRiemannTensorOf
    (h hinv : (Fin 3 → ℝ) → Tensor2 3) (x : Fin 3 → ℝ)
    (hgSymm : ∀ᶠ y in 𝓝 x, ∀ i j, h y i j = h y j i)
    (hInv : ∀ᶠ y in 𝓝 x, ∀ m j, ∑ a, hinv y a m * h y a j = if m = j then 1 else 0)
    (hgC2 : ∀ i j, ContDiffAt ℝ 2 (fun y => h y i j) x)
    (hΓD : ∀ k i j,
      DifferentiableAt ℝ (fun y => Pipeline.christoffel h hinv y k i j) x)
    (hΓ : ∀ᶠ y in 𝓝 x, ∀ k i j, Pipeline.christoffel h hinv y k i j =
      Pipeline.christoffel h hinv y k j i) : RiemannTensor 3 where
  comp := fun a b c d => ∑ e, h x a e * Pipeline.riemann h hinv x e b c d
  skew_last := by
    intro a b c d
    calc
      (∑ e, h x a e * Pipeline.riemann h hinv x e b c d)
          = ∑ e, h x a e * (-Pipeline.riemann h hinv x e b d c) := by
            apply Finset.sum_congr rfl
            intro e _
            rw [Bianchi.riemann_skew_last]
      _ = -∑ e, h x a e * Pipeline.riemann h hinv x e b d c := by
            simp_rw [mul_neg, Finset.sum_neg_distrib]
  pair_symm := by
    intro a b c d
    exact Bianchi.riemann_lower_pair_symm h hinv hgSymm hInv hgC2 hΓD hΓ a b c d
  bianchi := by
    intro a b c d
    exact Bianchi.riemann_lower_bianchi h hinv x hΓ a b c d

/-- The derived `R3` of a constant metric is the flat Riemann tensor. -/
theorem spatialRiemannTensorOf_const
    (G : Tensor2 3) (h hinv : (Fin 3 → ℝ) → Tensor2 3) (x : Fin 3 → ℝ)
    (hG : ∀ y, h y = G)
    (hgSymm : ∀ᶠ y in 𝓝 x, ∀ i j, h y i j = h y j i)
    (hInv : ∀ᶠ y in 𝓝 x, ∀ m j, ∑ a, hinv y a m * h y a j = if m = j then 1 else 0)
    (hgC2 : ∀ i j, ContDiffAt ℝ 2 (fun y => h y i j) x)
    (hΓD : ∀ k i j,
      DifferentiableAt ℝ (fun y => Pipeline.christoffel h hinv y k i j) x)
    (hΓ : ∀ᶠ y in 𝓝 x, ∀ k i j, Pipeline.christoffel h hinv y k i j =
      Pipeline.christoffel h hinv y k j i) :
    spatialRiemannTensorOf h hinv x hgSymm hInv hgC2 hΓD hΓ =
      RiemannTensor.flat 3 := by
  apply riemannTensor_ext
  intro a b c d
  change (∑ e, h x a e * Pipeline.riemann h hinv x e b c d) = 0
  apply Finset.sum_eq_zero
  intro e _
  rw [Pipeline.riemann_const h hinv G hG x e b c d]
  ring

/-- The momentum-constraint derivative table `dK_μij = ∂_μ K_ij` derived from
the extrinsic-curvature field. -/
noncomputable def extrinsicDerivativeOf
    (K : (Fin 3 → ℝ) → Tensor2 3) (x : Fin 3 → ℝ) : Fin 3 → Tensor2 3 :=
  fun μ i j => Pipeline.coordDeriv μ (fun y => K y i j) x

/-- A constant extrinsic curvature has vanishing derived derivative table. -/
lemma extrinsicDerivativeOf_const (K : Tensor2 3) (x : Fin 3 → ℝ) (μ : Fin 3) :
    extrinsicDerivativeOf (fun _ => K) x μ = 0 := by
  ext i j
  simp [extrinsicDerivativeOf, Pipeline.coordDeriv_const]

/-- The Minkowski chart induces the Euclidean spatial metric components on the
`t = 0` slice. -/
lemma minkowskiChart_spatialMetric :
    minkowskiChart.spatialMetric = euclid3.g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ChartSpacetime.spatialMetric, ChartSpacetime.coordinateMetric,
      minkowskiChart, minkowski, euclid3, minkowskiMetric4_apply]

/-- ADM data on a chart slice, together with the momentum-constraint derivative
and a proof that the vacuum constraints hold. -/
structure ChartInitialData (X : ChartSpacetime) where
  /-- The ADM metric, spatial curvature and extrinsic curvature. -/
  data : InitialData
  /-- The coordinate derivative `∂K` used by the momentum constraint. -/
  dK : Fin 3 → Tensor2 3
  /-- The vacuum constraint equations. -/
  vacuum : data.IsVacuumData dK

/-- Chart initial data whose curvature and momentum derivative are supplied by
the derived constructors `spatialRiemannTensorOf` and `extrinsicDerivativeOf`.
The vacuum proof is still an input: no constraint-solving theorem is claimed. -/
noncomputable def ChartInitialData.ofDerivedData
    (X : ChartSpacetime) (h : MetricTensor 3) (K : Tensor2 3)
    (Ksymm : IsSymm K) (R3 : RiemannTensor 3) (dK : Fin 3 → Tensor2 3)
    (vacuum : (InitialData.mk h R3 K Ksymm).IsVacuumData dK) :
    ChartInitialData X where
  data := InitialData.mk h R3 K Ksymm
  dK := dK
  vacuum := vacuum

/-- Chart-level regularity of initial data: smooth metric components and smooth
momentum-constraint derivatives.  The ADM tensors themselves are pointwise
matrices, so their regularity is carried by these two fields. -/
structure ChartInitialData.Regular {X : ChartSpacetime} (D : ChartInitialData X) : Prop where
  /-- The chart metric components are smooth. -/
  metric_smooth : X.IsSmooth
  /-- The momentum-constraint derivative is smooth on the slice. -/
  dK_smooth : ∀ (i j k : Fin 3), ContDiff ℝ ∞ fun _ : Fin 3 → ℝ => D.dK i j k

/-- Every bundled chart initial data set satisfies the Hamiltonian constraint. -/
lemma ChartInitialData.ham_zero (D : ChartInitialData X) :
    D.data.hamiltonianConstraint = 0 :=
  D.vacuum.1

/-- Every bundled chart initial data set satisfies the momentum constraint. -/
lemma ChartInitialData.mom_zero (D : ChartInitialData X) (i : Fin 3) :
    D.data.momentumConstraint D.dK i = 0 :=
  D.vacuum.2 i

/-- The bundled vacuum predicate is exactly `InitialData.IsVacuumData`. -/
lemma ChartInitialData.isVacuumData (D : ChartInitialData X) :
    D.data.IsVacuumData D.dK :=
  D.vacuum

/-- The Hamiltonian and momentum constraint residuals of chart initial data. -/
structure ConstraintResidual where
  /-- The Hamiltonian constraint residual. -/
  ham : ℝ
  /-- The momentum constraint residual. -/
  mom : Fin 3 → ℝ

/-- The constraint residual packaged from chart initial data. -/
noncomputable def ChartInitialData.constraintResidual
    (D : ChartInitialData X) : ConstraintResidual where
  ham := D.data.hamiltonianConstraint
  mom := fun i => D.data.momentumConstraint D.dK i

/-- The packaged Hamiltonian residual vanishes. -/
lemma ChartInitialData.constraintResidual_ham (D : ChartInitialData X) :
    D.constraintResidual.ham = 0 := by
  simpa [ChartInitialData.constraintResidual] using D.vacuum.1

/-- Every packaged momentum residual vanishes. -/
lemma ChartInitialData.constraintResidual_mom (D : ChartInitialData X) (i : Fin 3) :
    D.constraintResidual.mom i = 0 := by
  simpa [ChartInitialData.constraintResidual] using D.vacuum.2 i

/-- The whole constraint residual vanishes. -/
lemma ChartInitialData.constraintResidual_eq_zero (D : ChartInitialData X) :
    D.constraintResidual.ham = 0 ∧ ∀ i, D.constraintResidual.mom i = 0 :=
  ⟨D.constraintResidual_ham, D.constraintResidual_mom⟩

/-- Every chart initial data set with a smooth chart metric has regular data. -/
lemma ChartInitialData.regular (D : ChartInitialData X) (hX : X.IsSmooth) :
    D.Regular where
  metric_smooth := hX
  dK_smooth := fun _ _ _ => contDiff_const

/-- The Minkowski chart metric is smooth. -/
lemma minkowskiChart_isSmooth : minkowskiChart.IsSmooth := by
  intro i j
  have h : (fun x : SpacetimeChart => minkowskiChart.coordinateMetric x i j) =
      fun _ => minkowskiMetric4 i j := by
    funext x
    simp [ChartSpacetime.coordinateMetric, minkowskiChart, minkowski]
  rw [h]
  exact contDiff_const

/-- Flat Minkowski initial data on the Minkowski chart. -/
def minkowskiChartInitialData : ChartInitialData minkowskiChart where
  data := flatData
  dK := fun _ => 0
  vacuum := flatData_isVacuum

/-- The induced spatial metric on the Minkowski slice is the metric carried by
the flat chart initial data. -/
lemma minkowskiChartInitialData_metric :
    minkowskiChart.spatialMetric = minkowskiChartInitialData.data.h.g := by
  rw [minkowskiChart_spatialMetric]
  rfl

/-- The flat instance has vanishing Hamiltonian constraint. -/
lemma minkowskiChartInitialData_ham_zero :
    minkowskiChartInitialData.data.hamiltonianConstraint = 0 :=
  flatData_ham_zero

/-- The Minkowski chart initial data are regular. -/
lemma minkowskiChartInitialData_regular :
    minkowskiChartInitialData.Regular :=
  ChartInitialData.regular minkowskiChartInitialData minkowskiChart_isSmooth

/-- The Minkowski chart has vanishing constraint residual. -/
lemma minkowskiChartInitialData_constraintResidual_eq_zero :
    minkowskiChartInitialData.constraintResidual.ham = 0 ∧
      ∀ i, minkowskiChartInitialData.constraintResidual.mom i = 0 :=
  minkowskiChartInitialData.constraintResidual_eq_zero

end GeneralRelativity
