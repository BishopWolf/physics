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

/-- The squared Lorentzian norm of a chart tangent vector. -/
noncomputable def ChartSpacetime.normSq (X : ChartSpacetime)
    (x : SpacetimeChart) (v : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, X.coordinateMetric x i j * v i * v j

/-- A chart vector is timelike when its squared Lorentzian norm is negative. -/
def ChartSpacetime.IsTimelike (X : ChartSpacetime)
    (x : SpacetimeChart) (v : Fin 4 → ℝ) : Prop :=
  X.normSq x v < 0

/-- A chart vector is null when its squared Lorentzian norm vanishes. -/
def ChartSpacetime.IsNull (X : ChartSpacetime)
    (x : SpacetimeChart) (v : Fin 4 → ℝ) : Prop :=
  X.normSq x v = 0

/-- A chart vector is spacelike when its squared Lorentzian norm is positive. -/
def ChartSpacetime.IsSpacelike (X : ChartSpacetime)
    (x : SpacetimeChart) (v : Fin 4 → ℝ) : Prop :=
  0 < X.normSq x v

lemma minkowskiChart_normSq (x : SpacetimeChart) (v : Fin 4 → ℝ) :
    minkowskiChart.normSq x v =
      -(v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2 := by
  simp [ChartSpacetime.normSq, ChartSpacetime.coordinateMetric,
    minkowskiChart, minkowski, eta4, Fin.sum_univ_four]
  ring

/-- The time basis vector is timelike in the Minkowski chart. -/
lemma minkowskiChart_timelike_time (x : SpacetimeChart) :
    minkowskiChart.IsTimelike x (Pi.single 0 1) := by
  rw [ChartSpacetime.IsTimelike, minkowskiChart_normSq]
  simp [Pi.single_eq_same, Pi.single_eq_of_ne]

/-- A spatial basis vector is spacelike in the Minkowski chart. -/
lemma minkowskiChart_spacelike_space (x : SpacetimeChart) :
    minkowskiChart.IsSpacelike x (Pi.single 1 1) := by
  rw [ChartSpacetime.IsSpacelike, minkowskiChart_normSq]
  simp [Pi.single_eq_same, Pi.single_eq_of_ne]

end GeneralRelativity
