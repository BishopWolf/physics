/-
Copyright (c) 2026 The Gravitation formalisation contributors.
Released under Apache 2.0 license as described in the file LICENSE.

# Chart-level spacetime interface

This file begins the manifold/Lorentzian layer at the only level supported by the
current component-based development: a spacetime chart domain with a metric
field.  It intentionally does not claim a smooth manifold, a Levi-Civita
connection, curvature from a manifold metric, or causality.  Those are the
remaining M1 obligations.

The point of the interface is to give the later layers a concrete type to extend,
with Minkowski spacetime as its first instance.
-/

module

public import Gravitation.Relativity.General.Minkowski
public import Gravitation.Relativity.General.Pipeline
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

namespace GeneralRelativity

/-- The coordinate model for a four-dimensional chart. -/
abbrev SpacetimeChart : Type := Fin 4 → ℝ

/-- A chart domain with a metric field.  This is the chart-level starting point
for the manifold layer, not a smooth manifold: `chart` is a global equivalence,
and no smoothness of the metric is asserted. -/
structure ChartSpacetime where
  /-- The underlying chart domain. -/
  carrier : Type
  /-- The topology carried by the domain. -/
  topology : TopologicalSpace carrier
  /-- A global chart equivalence to `Fin 4 → ℝ`. -/
  chart : carrier ≃ SpacetimeChart
  /-- The metric components at each point. -/
  metric : carrier → MetricTensor 4

/-- Minkowski spacetime as a chart domain. -/
def minkowskiChart : ChartSpacetime where
  carrier := SpacetimeChart
  topology := inferInstance
  chart := Equiv.refl SpacetimeChart
  metric := fun _ => minkowski

/-- The Minkowski chart carries the Minkowski metric everywhere. -/
lemma minkowskiChart_metric (x : SpacetimeChart) :
    minkowskiChart.metric x = minkowski := rfl

/-- The Minkowski chart is the identity chart. -/
lemma minkowskiChart_chart (x : SpacetimeChart) :
    minkowskiChart.chart x = x := rfl

/-- The metric components read in the chosen chart. -/
noncomputable def ChartSpacetime.coordinateMetric (X : ChartSpacetime) :
    SpacetimeChart → Tensor2 4 :=
  fun x => (X.metric (X.chart.symm x)).g

/-- The inverse metric components read in the chosen chart. -/
noncomputable def ChartSpacetime.coordinateInverseMetric (X : ChartSpacetime) :
    SpacetimeChart → Tensor2 4 :=
  fun x => (X.metric (X.chart.symm x)).ginv

/-- Chart Christoffel symbols computed from the coordinate metric. -/
noncomputable def ChartSpacetime.christoffel (X : ChartSpacetime)
    (x : SpacetimeChart) (k i j : Fin 4) : ℝ :=
  Pipeline.christoffel X.coordinateMetric X.coordinateInverseMetric x k i j

/-- Chart Riemann curvature computed from the coordinate metric. -/
noncomputable def ChartSpacetime.riemann (X : ChartSpacetime)
    (x : SpacetimeChart) (ρ σ μ ν : Fin 4) : ℝ :=
  Pipeline.riemann X.coordinateMetric X.coordinateInverseMetric x ρ σ μ ν

/-- Chart Ricci tensor computed from the coordinate metric. -/
noncomputable def ChartSpacetime.ricci (X : ChartSpacetime)
    (x : SpacetimeChart) (σ ν : Fin 4) : ℝ :=
  Pipeline.ricciOf X.coordinateMetric X.coordinateInverseMetric x σ ν

/-- Chart scalar curvature computed from the coordinate metric. -/
noncomputable def ChartSpacetime.scalarCurvature (X : ChartSpacetime)
    (x : SpacetimeChart) : ℝ :=
  Pipeline.scalarOf X.coordinateMetric X.coordinateInverseMetric x

/-- Chart Einstein tensor computed from the coordinate metric. -/
noncomputable def ChartSpacetime.einstein (X : ChartSpacetime)
    (x : SpacetimeChart) (i j : Fin 4) : ℝ :=
  Pipeline.einsteinOf X.coordinateMetric X.coordinateInverseMetric x i j

lemma minkowskiChart_christoffel_zero (x : SpacetimeChart) (k i j : Fin 4) :
    minkowskiChart.christoffel x k i j = 0 := by
  simpa [ChartSpacetime.christoffel] using
    Pipeline.christoffel_const minkowskiChart.coordinateMetric
      minkowskiChart.coordinateInverseMetric eta4 (fun _ => rfl) x k i j

lemma minkowskiChart_riemann_zero (x : SpacetimeChart)
    (ρ σ μ ν : Fin 4) :
    minkowskiChart.riemann x ρ σ μ ν = 0 := by
  simpa [ChartSpacetime.riemann] using
    Pipeline.riemann_const minkowskiChart.coordinateMetric
      minkowskiChart.coordinateInverseMetric eta4 (fun _ => rfl) x ρ σ μ ν

lemma minkowskiChart_ricci_zero (x : SpacetimeChart) (σ ν : Fin 4) :
    minkowskiChart.ricci x σ ν = 0 := by
  simpa [ChartSpacetime.ricci, ChartSpacetime.coordinateMetric,
    ChartSpacetime.coordinateInverseMetric, minkowskiChart, minkowski] using
    Pipeline.ricciOf_const minkowskiChart.coordinateMetric
      minkowskiChart.coordinateInverseMetric eta4 (fun _ => rfl) x σ ν

lemma minkowskiChart_scalar_zero (x : SpacetimeChart) :
    minkowskiChart.scalarCurvature x = 0 := by
  simpa [ChartSpacetime.scalarCurvature, ChartSpacetime.coordinateMetric,
    ChartSpacetime.coordinateInverseMetric, minkowskiChart, minkowski] using
    Pipeline.scalarOf_const minkowskiChart.coordinateMetric
      minkowskiChart.coordinateInverseMetric eta4 (fun _ => rfl) x

lemma minkowskiChart_einstein_zero (x : SpacetimeChart) (i j : Fin 4) :
    minkowskiChart.einstein x i j = 0 := by
  simpa [ChartSpacetime.einstein] using
    Pipeline.einsteinOf_const minkowskiChart.coordinateMetric
      minkowskiChart.coordinateInverseMetric eta4 (fun _ => rfl) x i j

end GeneralRelativity
