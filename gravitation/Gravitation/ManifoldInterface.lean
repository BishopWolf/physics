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

end GeneralRelativity
