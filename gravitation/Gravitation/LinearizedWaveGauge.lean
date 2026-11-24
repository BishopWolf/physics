/-
Copyright (c) 2026 The Gravitation formalisation contributors.
Released under Apache 2.0 license as described in the file LICENSE.

# Linearized Einstein equations in wave gauge

The vendored linearized-gravity module proves that, in Lorenz gauge, the
linearized Einstein tensor is `-(1/2) □ h̄`.  This file records the resulting
wave-gauge interface explicitly: a perturbation is a linearized vacuum solution
when it is symmetric, `C²`, satisfies the gauge condition near the point, and
solves the component wave equations `□ h̄_{ij} = 0`.

This is the coordinate-level starting point for the linearized Einstein layer;
it is not a manifold-level derivation of the linearized equations.
-/

module

public import Gravitation.Relativity.General.Linearized
public import Gravitation.WaveUniqueness3D

@[expose] public section

open scoped Topology

namespace GeneralRelativity

namespace Linearized

/-- A metric perturbation satisfying the wave-gauge form of the linearized
vacuum equations at a point. -/
structure WaveGaugePerturbation
    (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ) : Prop where
  /-- The perturbation is symmetric. -/
  symm : ∀ y i j, h y i j = h y j i
  /-- Every component is `C²` at the point. -/
  smooth : ∀ i j, ContDiffAt ℝ 2 (fun y => h y i j) x
  /-- The Lorenz gauge condition holds on a neighborhood. -/
  gauge : ∀ᶠ y in nhds x, ∀ k : Fin 4, lorenzGaugeCond h y k
  /-- The trace-reversed perturbation solves the component wave equations. -/
  wave : ∀ i j : Fin 4, boxEta (fun y => traceReversed (h y) i j) x = 0

/-- A wave-gauge perturbation is a linearized vacuum solution:
`G^{(1)}_{ij} = 0`. -/
theorem linEinstein_eq_zero_of_waveGauge
    (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ)
    (S : WaveGaugePerturbation h x) (i j : Fin 4) :
    linEinstein h x i j = 0 := by
  rw [linEinstein_lorenz_gauge h x S.symm S.smooth S.gauge i j]
  simp [S.wave i j]

end Linearized

end GeneralRelativity
