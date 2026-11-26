/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith

/-!
# TeVeS as a field theory: action and field equations

## i. Overview

This module states the TeVeS action density and its two field equations at a
point: the aether-projected scalar equation and the modified Einstein equation.
The disformal physical metric, its inverse and its Lorentzian signature are
already formalised in the vendored TeVeS module; this adds the V1 layer of the
alternatives programme.

The projected d'Alembertian and the source (disformal coupling and scalar
potential gradient) are supplied as data, so the scalar equation is a residual
rather than a derivation.

## ii. Key results

- `tevesActionDensity` : the action density at a point.
- `tevesScalarResidual` : the projected scalar equation in one component.
- `tevesEinsteinResidual` : one component of the modified Einstein equation.
- `IsTeVeSSolution` : both field equations hold at a point.

## iii. Table of contents

- A. The action density
- B. The field equations

## iv. References

* J. D. Bekenstein, *Relativistic gravitation theory for the modified Newtonian
  dynamics paradigm*, Phys. Rev. D 70 (2004) 083509, arXiv:astro-ph/0403694.
* C. Skordis, T. Zlosnik, *New relativistic theory for modified Newtonian
  dynamics*, Phys. Rev. Lett. 127 (2021) 161302.
-/

@[expose] public section

namespace GeneralRelativity

/-! ## A. The action density -/

/-- The TeVeS action density at a point:
`R/(16 pi G) - (1/2) (g^{mu nu} - U^mu U^nu) d_mu phi d_nu phi - V`, with the
projected kinetic term and the scalar potential `V` supplied.  The matter
coupling to the disformal metric is not included. -/
noncomputable def tevesActionDensity (G R gradPhiSq V : ℝ) : ℝ :=
  R / (16 * Real.pi * G) - gradPhiSq / 2 - V

/-! ## B. The field equations -/

/-- The TeVeS scalar equation in one frame component: the aether-projected
d'Alembertian of the scalar equals the supplied source. -/
noncomputable def tevesScalarResidual (projBox source : ℝ) : ℝ :=
  projBox - source

/-- The scalar equation holds exactly when the projected d'Alembertian equals
its source. -/
lemma tevesScalarResidual_eq_zero_iff (projBox source : ℝ) :
    tevesScalarResidual projBox source = 0 ↔ projBox = source := by
  unfold tevesScalarResidual
  constructor <;> intro h <;> linarith

/-- One component of the modified Einstein equation
`G_{mu nu} = 8 pi G T_{mu nu}`, with the scalar and vector stress contributions
folded into `Ecouple`. -/
noncomputable def tevesEinsteinResidual (G Ecouple T : ℝ) : ℝ :=
  Ecouple - 8 * Real.pi * G * T

/-- The modified Einstein equation holds exactly when the coupled Einstein
tensor equals `8 pi G` times the source. -/
lemma tevesEinsteinResidual_eq_zero_iff (G Ecouple T : ℝ) :
    tevesEinsteinResidual G Ecouple T = 0 ↔ Ecouple = 8 * Real.pi * G * T := by
  unfold tevesEinsteinResidual
  constructor <;> intro h <;> linarith

/-- A point at which the TeVeS field equations hold. -/
structure IsTeVeSSolution (G Ecouple T projBox source : ℝ) : Prop where
  /-- The modified Einstein equation holds. -/
  einstein_eq : tevesEinsteinResidual G Ecouple T = 0
  /-- The scalar equation holds. -/
  scalar_eq : tevesScalarResidual projBox source = 0

end GeneralRelativity
