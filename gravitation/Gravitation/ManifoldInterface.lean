/-
Copyright (c) 2026 The Gravitation formalisation contributors.
Released under Apache 2.0 license as described in the file LICENSE.

# Chart-level spacetime interface

This file provides the chart-level M1 layer supported by the current
component-based development: a spacetime chart domain, a metric field, the
coordinate connection and curvature, chart causal classification, and a
coordinate covariant derivative.  It proves torsion-freeness and Minkowski
metric compatibility.  It does not claim a smooth manifold, a general
Levi-Civita compatibility theorem, or global causality; those remain outside
this chart interface.

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

/-- The lightlike vector `(1, 1, 0, 0)`. -/
def lightlikeVector : Fin 4 → ℝ :=
  fun i => if i = 0 then 1 else if i = 1 then 1 else 0

/-- `(1, 1, 0, 0)` is null in the Minkowski chart. -/
lemma minkowskiChart_null_lightlike (x : SpacetimeChart) :
    minkowskiChart.IsNull x lightlikeVector := by
  rw [ChartSpacetime.IsNull, minkowskiChart_normSq]
  simp [lightlikeVector]

/-- The three causal characters of a Lorentzian tangent vector. -/
inductive CausalCharacter
  | timelike
  | null
  | spacelike
  deriving DecidableEq, Repr

/-- The causal character of a chart tangent vector. -/
noncomputable def ChartSpacetime.causalCharacter (X : ChartSpacetime)
    (x : SpacetimeChart) (v : Fin 4 → ℝ) : CausalCharacter := by
  classical
  exact if X.IsTimelike x v then .timelike
    else if X.IsNull x v then .null
    else .spacelike

lemma ChartSpacetime.causalCharacter_eq_timelike_of_neg
    (X : ChartSpacetime) (x : SpacetimeChart) (v : Fin 4 → ℝ)
    (h : X.IsTimelike x v) :
    X.causalCharacter x v = .timelike := by
  simp [ChartSpacetime.causalCharacter, h]

lemma ChartSpacetime.causalCharacter_eq_null_of_eq
    (X : ChartSpacetime) (x : SpacetimeChart) (v : Fin 4 → ℝ)
    (h : X.IsNull x v) :
    X.causalCharacter x v = .null := by
  have ht : ¬ X.IsTimelike x v := by
    intro ht
    rw [ChartSpacetime.IsTimelike] at ht
    rw [ChartSpacetime.IsNull] at h
    linarith
  simp [ChartSpacetime.causalCharacter, ht, h]

lemma ChartSpacetime.causalCharacter_eq_spacelike_of_pos
    (X : ChartSpacetime) (x : SpacetimeChart) (v : Fin 4 → ℝ)
    (h : X.IsSpacelike x v) :
    X.causalCharacter x v = .spacelike := by
  have ht : ¬ X.IsTimelike x v := by
    intro ht
    rw [ChartSpacetime.IsTimelike] at ht
    rw [ChartSpacetime.IsSpacelike] at h
    linarith
  have hn : ¬ X.IsNull x v := by
    intro hn
    rw [ChartSpacetime.IsNull] at hn
    rw [ChartSpacetime.IsSpacelike] at h
    linarith
  simp [ChartSpacetime.causalCharacter, ht, hn]

/-- The coordinate covariant derivative of a vector field,
`∇_i v^k = ∂_i v^k + Γ^k_{ij} v^j`. -/
noncomputable def ChartSpacetime.covariantDerivVector
    (X : ChartSpacetime) (v : SpacetimeChart → Fin 4 → ℝ)
    (x : SpacetimeChart) (i k : Fin 4) : ℝ :=
  fderiv ℝ (fun y => v y k) x (Pi.single i 1) +
    ∑ j : Fin 4, X.christoffel x k i j * v x j

/-- A constant vector field has vanishing coordinate covariant derivative in the
Minkowski chart. -/
lemma minkowskiChart_covariantDerivVector_const
    (v : Fin 4 → ℝ) (x : SpacetimeChart) (i k : Fin 4) :
    minkowskiChart.covariantDerivVector (fun _ => v) x i k = 0 := by
  simp [ChartSpacetime.covariantDerivVector, minkowskiChart_christoffel_zero]

/-- The chart Christoffel symbols are torsion-free: `Γ^k_{ij} = Γ^k_{ji}`. -/
lemma ChartSpacetime.christoffel_symm (X : ChartSpacetime)
    (x : SpacetimeChart) (k i j : Fin 4) :
    X.christoffel x k i j = X.christoffel x k j i := by
  simp only [ChartSpacetime.christoffel, Pipeline.christoffel]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  have hsymm : Pipeline.pd l (fun y => X.coordinateMetric y i j) x =
      Pipeline.pd l (fun y => X.coordinateMetric y j i) x := by
    apply Pipeline.pd_congr
    intro y
    exact (X.metric (X.chart.symm y)).symm i j
  rw [hsymm]
  ring

/-- The coordinate covariant derivative of the metric,
`∇_i g_{jk} = ∂_i g_{jk} - Γ^l_{ij} g_{lk} - Γ^l_{ik} g_{jl}`. -/
noncomputable def ChartSpacetime.metricCovariantDeriv
    (X : ChartSpacetime) (x : SpacetimeChart) (i j k : Fin 4) : ℝ :=
  Pipeline.pd i (fun y => X.coordinateMetric y j k) x
    - ∑ l : Fin 4, X.christoffel x l i j * X.coordinateMetric x l k
    - ∑ l : Fin 4, X.christoffel x l i k * X.coordinateMetric x j l

/-- The Minkowski chart is metric compatible: the covariant derivative of the
metric vanishes. -/
lemma minkowskiChart_metricCovariantDeriv_zero
    (x : SpacetimeChart) (i j k : Fin 4) :
    minkowskiChart.metricCovariantDeriv x i j k = 0 := by
  rw [ChartSpacetime.metricCovariantDeriv]
  have hpd : Pipeline.pd i (fun y => minkowskiChart.coordinateMetric y j k) x = 0 := by
    have hconst : ∀ y, minkowskiChart.coordinateMetric y j k = eta4 j k := by
      intro y
      simp [ChartSpacetime.coordinateMetric, minkowskiChart, minkowski]
    rw [Pipeline.pd_congr i x hconst]
    exact Pipeline.pd_const i (eta4 j k) x
  have h1 :
      (∑ l : Fin 4,
        minkowskiChart.christoffel x l i j * minkowskiChart.coordinateMetric x l k) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    rw [minkowskiChart_christoffel_zero]
    ring
  have h2 :
      (∑ l : Fin 4,
        minkowskiChart.christoffel x l i k * minkowskiChart.coordinateMetric x j l) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    rw [minkowskiChart_christoffel_zero]
    ring
  rw [hpd, h1, h2]
  ring

/-- A chart-level Levi-Civita certificate: torsion-freeness together with metric
compatibility. -/
structure ChartSpacetime.IsLeviCivita (X : ChartSpacetime) : Prop where
  /-- The coordinate connection is torsion-free. -/
  torsion_free : ∀ (x : SpacetimeChart) (k i j : Fin 4),
    X.christoffel x k i j = X.christoffel x k j i
  /-- The coordinate covariant derivative of the metric vanishes. -/
  metric_compatible : ∀ (x : SpacetimeChart) (i j k : Fin 4),
    X.metricCovariantDeriv x i j k = 0

/-- The Minkowski chart carries a chart-level Levi-Civita connection. -/
lemma minkowskiChart_isLeviCivita : minkowskiChart.IsLeviCivita where
  torsion_free := minkowskiChart.christoffel_symm
  metric_compatible := minkowskiChart_metricCovariantDeriv_zero

/-- Every chart tangent vector has one of the three causal characters. -/
lemma ChartSpacetime.causalCharacter_cases (X : ChartSpacetime)
    (x : SpacetimeChart) (v : Fin 4 → ℝ) :
    X.causalCharacter x v = .timelike ∨
      X.causalCharacter x v = .null ∨
      X.causalCharacter x v = .spacelike := by
  cases X.causalCharacter x v <;> simp

end GeneralRelativity
