/-
Copyright (c) 2026 The Gravitation formalisation contributors.
Released under Apache 2.0 license as described in the file LICENSE.

# Chart-level initial data

This file provides the chart-level M2 layer by connecting a chart spacetime to
the existing ADM `InitialData` structure.  The induced spatial metric is read
from the `t = 0` slice of the chart metric.  The file packages smooth chart
regularity, the slice embedding and restriction of the metric to it, and the
constraint residual of bundled initial data.

The regularity here is smooth (`ContDiff`) component regularity on a chart, not
manifold Sobolev `H^s` theory: Sobolev spaces, trace/embedding estimates and
constraint solving remain outside this interface.
-/

module

public import Gravitation.ManifoldInterface
public import Gravitation.Relativity.General.InitialData
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

namespace GeneralRelativity

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
