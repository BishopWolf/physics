/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Gravitation.Relativity.Metrics.ConformalMetric

/-!
# The Lichnerowicz-York conformal decomposition (interface)

## i. Overview

This module states the conformal decomposition used to solve the Einstein
constraint equations.  It does not solve them.  The seed data are a 3-metric
`hbar`, a transverse-traceless tensor `sigma` and a mean extrinsic curvature
`tau`; the physical data are `h = phi^4 hbar` and `K = phi^{-2} sigma +
(tau/3) h`.  The Hamiltonian and momentum constraints then become the
Lichnerowicz equation for `phi` and the divergence equation for `sigma`.

The residuals below take the seed Laplacian, scalar curvature, divergence and
gradient as explicit arguments.  This repository has coordinate expressions for
those operators but no manifold elliptic theory, so the interface states the
system and leaves existence, regularity and uniqueness to the paper on the
constraint equations.

## ii. Key results

- `ConformalData` : seed metric, conformal factor, TT tensor and mean curvature.
- `ConformalData.physicalMetric` : `h = phi^4 hbar`, packaged with its inverse.
- `ConformalData.extrinsicCurvature` : `K = phi^{-2} sigma + (tau/3) h`.
- `hamiltonianResidual` : `8 lap phi - R phi + |sigma|^2 phi^{-7}`.
- `momentumResidual` : `(div sigma)_i - (2/3) phi^6 (grad tau)_i`.
- `IsLichnerowiczYorkSolution` : both residuals vanish.

## iii. Table of contents

- A. Conformal data
- B. The Lichnerowicz-York residuals

## iv. References

* A. Lichnerowicz, *L'integration des equations de la gravitation relativiste
  et le probleme des n corps*, J. Math. Pures Appl. 23 (1944) 37-63.
* J. W. York, *Gravitational energy and the initial-value problem*,
  Phys. Rev. Lett. 26 (1971) 1656.
* Y. Choquet-Bruhat and J. W. York, *The Cauchy problem*, in *General
  Relativity and Gravitation* (Plenum, 1980).
* R. Bartnik and J. Isenberg, *The constraint equations*, in *The Einstein
  Equations and the Large Scale Behavior of Gravitational Fields* (2004),
  arXiv:gr-qc/0405092.
-/

@[expose] public section

namespace GeneralRelativity

/-! ## A. Conformal data -/

/-- Conformal data for the Lichnerowicz-York decomposition: a seed 3-metric
`hbar`, a positive conformal factor `phi`, a transverse-traceless tensor
`sigma`, and the mean extrinsic curvature `tau`. -/
structure ConformalData where
  /-- The seed 3-metric `hbar`. -/
  seed : MetricTensor 3
  /-- The conformal factor `phi`. -/
  phi : ℝ
  /-- Positivity of the conformal factor. -/
  phi_pos : 0 < phi
  /-- The transverse-traceless tensor `sigma`. -/
  sigma : Tensor2 3
  /-- The mean extrinsic curvature `tau`. -/
  meanCurvature : ℝ

namespace ConformalData

/-- The physical metric `h = phi^4 hbar`, with inverse `phi^{-4} hbar^{-1}`. -/
noncomputable def physicalMetric (D : ConformalData) : MetricTensor 3 :=
  conformalMetric D.seed (D.phi ^ 4) (pow_pos D.phi_pos 4).ne'

/-- The components of the physical metric are `phi^4 hbar_{ij}`. -/
lemma physicalMetric_g (D : ConformalData) :
    D.physicalMetric.g = fun i j => D.phi ^ 4 * D.seed.g i j := by
  rfl

/-! The physical extrinsic curvature `K = phi^{-2} sigma + (tau/3) h`. -/
noncomputable def extrinsicCurvature (D : ConformalData) : Tensor2 3 :=
  fun i j => (D.phi ^ 2)⁻¹ * D.sigma i j
    + (D.meanCurvature / 3) * D.physicalMetric.g i j

/-- The transverse-traceless condition on `sigma` with respect to the seed
metric: `hbar^{ij} sigma_{ij} = 0`. -/
def IsTransverseTraceless (D : ConformalData) : Prop :=
  (∑ i : Fin 3, ∑ j : Fin 3, D.seed.ginv i j * D.sigma i j) = 0

end ConformalData

/-! ## B. The Lichnerowicz-York residuals -/

/-- The Hamiltonian (Lichnerowicz) residual `8 lap phi - R phi + |sigma|^2
phi^{-7}`, with the value of the seed Laplacian at the point supplied
explicitly. -/
noncomputable def hamiltonianResidual (lapPhi R sigmaSq phi : ℝ) : ℝ :=
  8 * lapPhi - R * phi + sigmaSq / phi ^ 7

/-- The momentum residual `(div sigma)_i - (2/3) phi^6 (grad tau)_i`. -/
noncomputable def momentumResidual (divSigma gradTau : Fin 3 → ℝ) (phi : ℝ) :
    Fin 3 → ℝ :=
  fun i => divSigma i - (2 / 3) * phi ^ 6 * gradTau i

/-- Vanishing of both Lichnerowicz-York residuals at a point: the two
constraints are satisfied there.  This states the system; it is not a solution
theorem. -/
structure IsLichnerowiczYorkSolution (D : ConformalData) (lapPhi R sigmaSq : ℝ)
    (divSigma gradTau : Fin 3 → ℝ) : Prop where
  /-- The Hamiltonian constraint vanishes. -/
  hamiltonian : hamiltonianResidual lapPhi R sigmaSq D.phi = 0
  /-- The momentum constraint vanishes. -/
  momentum : ∀ i, momentumResidual divSigma gradTau D.phi i = 0

/-- With constant mean curvature the momentum residual is the divergence of
`sigma`. -/
lemma momentumResidual_zero_gradTau (divSigma : Fin 3 → ℝ) (phi : ℝ) :
    momentumResidual divSigma (fun _ => 0) phi = divSigma := by
  funext i
  simp [momentumResidual]

end GeneralRelativity
