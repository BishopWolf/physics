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

public import Gravitation.Relativity.General.Linearized.LinearizedCurvature
public import Gravitation.Relativity.General.Linearized.LorenzGauge
public import Gravitation.Relativity.General.Linearized.TTWave
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

/-- A component of a plane-wave profile `f(t-z)` is `C²` when `f` is. -/
private lemma contDiffAt_waveProfile
    (c : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x : Fin 4 → ℝ) :
    ContDiffAt ℝ 2 (fun y : Fin 4 → ℝ => c * f (y 0 - y 3)) x := by
  have hlin : ContDiff ℝ 2 (fun y : Fin 4 → ℝ => y 0 - y 3) :=
    (contDiff_pi.mp (contDiff_id (𝕜 := ℝ) (E := Fin 4 → ℝ)) 0).sub
      (contDiff_pi.mp (contDiff_id (𝕜 := ℝ) (E := Fin 4 → ℝ)) 3)
  exact contDiffAt_const.mul ((hf.comp hlin).contDiffAt)

/-- The transverse-traceless plane wave has `C²` components. -/
lemma ttWave_contDiffAt
    (hPlus hCross : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (x : Fin 4 → ℝ) (i j : Fin 4) :
    ContDiffAt ℝ 2 (fun y => ttWave hPlus hCross f y i j) x := by
  fin_cases i <;> fin_cases j <;> simp only [ttWave] <;> norm_num
  all_goals first
    | exact contDiffAt_const
    | exact contDiffAt_waveProfile hPlus f hf x
    | exact (contDiffAt_waveProfile hPlus f hf x).neg
    | exact contDiffAt_waveProfile hCross f hf x

/-- The transverse-traceless plane wave is a wave-gauge perturbation. -/
theorem ttWave_waveGauge
    (hPlus hCross : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x : Fin 4 → ℝ) :
    WaveGaugePerturbation (ttWave hPlus hCross f) x := by
  refine {
    symm := fun y i j => (ttWave_symm hPlus hCross f y).apply j i
    smooth := ttWave_contDiffAt hPlus hCross f hf x
    gauge := Filter.Eventually.of_forall fun y k =>
      ttWave_lorenz_gauge hPlus hCross f y k
    wave := ?_ }
  intro i j
  have hsym : ∀ z a b,
      ttWave hPlus hCross f z a b = ttWave hPlus hCross f z b a :=
    fun z a b => (ttWave_symm hPlus hCross f z).apply b a
  have hc : ∀ a b, ContDiffAt ℝ 2
      (fun z => ttWave hPlus hCross f z a b) x :=
    ttWave_contDiffAt hPlus hCross f hf x
  have hlz : ∀ᶠ y in nhds x, ∀ k,
      lorenzGaugeCond (ttWave hPlus hCross f) y k :=
    Filter.Eventually.of_forall fun y k =>
      ttWave_lorenz_gauge hPlus hCross f y k
  have hG := ttWave_linEinstein_zero hPlus hCross f hf x i j
  rw [linEinstein_lorenz_gauge (ttWave hPlus hCross f) x hsym hc hlz i j] at hG
  nlinarith

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
