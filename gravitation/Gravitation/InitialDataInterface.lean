/-
Copyright (c) 2026 The Gravitation formalisation contributors.
Released under Apache 2.0 license as described in the file LICENSE.

# Chart-level initial data

This file starts the M2 layer by connecting a chart spacetime to the existing
ADM `InitialData` structure.  The induced spatial metric is read from the
`t = 0` slice of the chart metric.  The bundled `ChartInitialData` carries the
ADM data, the derivative of the extrinsic curvature, and a proof of the vacuum
constraints.

No Sobolev regularity, manifold slice, or constraint-solving theorem is claimed
here; those remain the M2 obligations.
-/

module

public import Gravitation.ManifoldInterface
public import Gravitation.Relativity.General.InitialValue

@[expose] public section

namespace GeneralRelativity

/-- The spatial metric induced on the `t = 0` chart slice. -/
noncomputable def ChartSpacetime.spatialMetric (X : ChartSpacetime) : Tensor2 3 :=
  fun i j => X.coordinateMetric 0 (Fin.succ i) (Fin.succ j)

/-- The Minkowski chart induces the Euclidean spatial metric components on the
`t = 0` slice. -/
lemma minkowskiChart_spatialMetric :
    minkowskiChart.spatialMetric = euclid3.g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ChartSpacetime.spatialMetric, ChartSpacetime.coordinateMetric,
      minkowskiChart, minkowski, euclid3, eta4]

/-- ADM data on a chart slice, together with the momentum-constraint derivative
and a proof that the vacuum constraints hold. -/
structure ChartInitialData (X : ChartSpacetime) where
  /-- The ADM metric, spatial curvature and extrinsic curvature. -/
  data : InitialData
  /-- The coordinate derivative `∂K` used by the momentum constraint. -/
  dK : Fin 3 → Tensor2 3
  /-- The vacuum constraint equations. -/
  vacuum : data.IsVacuumData dK

/-- Flat Minkowski initial data on the Minkowski chart. -/
def minkowskiChartInitialData : ChartInitialData minkowskiChart where
  data := flatData
  dK := fun _ => 0
  vacuum := flatData_isVacuum

/-- The flat instance has vanishing Hamiltonian constraint. -/
lemma minkowskiChartInitialData_ham_zero :
    minkowskiChartInitialData.data.ham = 0 :=
  flatData_ham_zero

end GeneralRelativity
