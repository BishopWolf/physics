/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Gravitation.Cosmology.FLRW.Basic
import Mathlib.Tactic.FinCases

/-!
# Linear scalar perturbations of an FLRW background

## i. Overview

This module starts the linear-perturbation layer of the alternatives programme
(T9.4).  It fixes the scalar sector of a metric perturbation on a comoving FLRW
background `S`, in the "supplied gradient" idiom used elsewhere in the
development: the two scalar potentials `phi`, `psi` and the supplied first and
second spatial-gradient data `B`, `E` are given as fields, so no spatial
derivative operator is needed.  The perturbed metric is the background metric
plus the scalar perturbation, and the module proves that the perturbation
vanishes for the zero data (background recovery) and that the perturbation is
symmetric whenever the second-gradient data `E` is symmetric.  The gauge
transformation and the Bardeen potentials are left to a later increment.

## ii. Key results

- `ScalarPerturbation` : the scalar-sector data `(phi, psi, B, E)`.
- `perturbationMetric`, `perturbedMetric` : the scalar perturbation and the
  perturbed FLRW metric.
- `perturbationMetric_zero`, `perturbedMetric_zero` : background recovery.
- `perturbationMetric_symm` : symmetry from a symmetric `E`.
- `bardeenPhi`, `bardeenPsi` : the gauge-invariant Bardeen potentials.
- `bardeenPhi_invariant`, `bardeenPsi_invariant` : gauge invariance.

## iii. Table of contents

- A. The scalar-sector data
- B. The perturbed metric
- C. The gauge transformation and the Bardeen potentials

## iv. References

* V. F. Mukhanov, *Physical Foundations of Cosmology*, Cambridge, 2005, Ch. 6.
* S. Weinberg, *Cosmology*, Oxford, 2008, Ch. 5.
-/

@[expose] public section

open GeneralRelativity

namespace Cosmology

namespace FLRW

/-! ## A. The scalar-sector data -/

/-- The scalar-sector data of a linear metric perturbation on an FLRW
background: the two scalar potentials `phi`, `psi` and the supplied first and
second spatial-gradient fields `B`, `E`. -/
structure ScalarPerturbation where
  /-- The lapse perturbation potential. -/
  phi : (Fin 4 → ℝ) → ℝ
  /-- The curvature perturbation potential. -/
  psi : (Fin 4 → ℝ) → ℝ
  /-- The supplied first spatial gradient of the shift potential. -/
  B : (Fin 4 → ℝ) → (Fin 4 → ℝ)
  /-- The supplied second spatial gradient of the scalar potential. -/
  E : (Fin 4 → ℝ) → (Fin 4 → Fin 4 → ℝ)

/-- The zero scalar perturbation. -/
def ScalarPerturbation.zero : ScalarPerturbation where
  phi := 0
  psi := 0
  B := 0
  E := 0

/-! ## B. The perturbed metric -/

/-- The scalar metric perturbation `delta g` in comoving coordinates, built from
the lapse potential `phi`, the curvature potential `psi`, and the supplied
gradient data `B`, `E`:
`delta g_00 = -2 a^2 phi`, `delta g_0i = a^2 B_i`,
`delta g_ij = a^2 (-2 psi delta_ij + 2 E_ij)`. -/
noncomputable def perturbationMetric (S : FLRWSpacetime) (P : ScalarPerturbation)
    (x : Fin 4 → ℝ) : Tensor2 4 :=
  Matrix.of fun i j =>
    if i = 0 ∧ j = 0 then -2 * (S.a (x 0)) ^ 2 * P.phi x
    else if i = 0 then (S.a (x 0)) ^ 2 * P.B x j
    else if j = 0 then (S.a (x 0)) ^ 2 * P.B x i
    else (S.a (x 0)) ^ 2 * (-2 * P.psi x * (if i = j then 1 else 0) + 2 * P.E x i j)

/-- The perturbed FLRW metric `g + delta g`. -/
noncomputable def perturbedMetric (S : FLRWSpacetime) (P : ScalarPerturbation)
    (x : Fin 4 → ℝ) : Tensor2 4 :=
  S.metric x + perturbationMetric S P x

/-- The scalar perturbation vanishes for the zero data. -/
lemma perturbationMetric_zero (S : FLRWSpacetime) (x : Fin 4 → ℝ) :
    perturbationMetric S ScalarPerturbation.zero x = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [perturbationMetric, ScalarPerturbation.zero]

/-- The perturbed metric reduces to the background for the zero data. -/
lemma perturbedMetric_zero (S : FLRWSpacetime) (x : Fin 4 → ℝ) :
    perturbedMetric S ScalarPerturbation.zero x = S.metric x := by
  rw [perturbedMetric, perturbationMetric_zero]
  simp

/-- The scalar perturbation is symmetric whenever the second-gradient data `E`
is symmetric. -/
lemma perturbationMetric_symm (S : FLRWSpacetime) (P : ScalarPerturbation)
    (hE : ∀ x i j, P.E x i j = P.E x j i) (x : Fin 4 → ℝ) :
    IsSymm (perturbationMetric S P x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [perturbationMetric, hE, Matrix.transpose_apply]

/-! ## C. The gauge transformation and the Bardeen potentials -/

/-- The gauge-transformed lapse potential `phi - xi0' - (a'/a) xi0`. -/
noncomputable def gaugePhi (a a' phi xi0 xi0' : ℝ) : ℝ :=
  phi - xi0' - (a' / a) * xi0

/-- The gauge-transformed curvature potential `psi + (a'/a) xi0`. -/
noncomputable def gaugePsi (a a' psi xi0 : ℝ) : ℝ :=
  psi + (a' / a) * xi0

/-- The gauge-transformed shift gradient `B + xi0 - xi'`. -/
noncomputable def gaugeB (B xi0 xi' : ℝ) : ℝ :=
  B + xi0 - xi'

/-- The gauge-transformed second-gradient scalar `E - xi`. -/
noncomputable def gaugeE (E xi : ℝ) : ℝ :=
  E - xi

/-- The Bardeen lapse potential `Phi = phi + (a'/a)(B - E') + (B' - E'')`. -/
noncomputable def bardeenPhi (a a' phi B E' B' E'' : ℝ) : ℝ :=
  phi + (a' / a) * (B - E') + (B' - E'')

/-- The Bardeen curvature potential `Psi = psi - (a'/a)(B - E')`. -/
noncomputable def bardeenPsi (a a' psi B E' : ℝ) : ℝ :=
  psi - (a' / a) * (B - E')

/-- The Bardeen lapse potential is invariant under the scalar gauge
transformation. -/
lemma bardeenPhi_invariant (a a' phi B E' B' E'' xi0 xi0' xi' xi'') (ha : a ≠ 0) :
    bardeenPhi a a' (gaugePhi a a' phi xi0 xi0') (gaugeB B xi0 xi') (E' - xi')
        (B' + xi0' - xi'') (E'' - xi'') =
      bardeenPhi a a' phi B E' B' E'' := by
  simp only [bardeenPhi, gaugePhi, gaugeB]
  field_simp
  ring

/-- The Bardeen curvature potential is invariant under the scalar gauge
transformation. -/
lemma bardeenPsi_invariant (a a' psi B E' xi0 xi') (ha : a ≠ 0) :
    bardeenPsi a a' (gaugePsi a a' psi xi0) (gaugeB B xi0 xi') (E' - xi') =
      bardeenPsi a a' psi B E' := by
  simp only [bardeenPsi, gaugePsi, gaugeB]
  field_simp
  ring

end FLRW

end Cosmology