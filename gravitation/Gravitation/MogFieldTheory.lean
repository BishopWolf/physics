/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

/-!
# MOG / STVG as a field theory: action and field equations

## i. Overview

This module states the gravitational sector of Moffat's scalar-tensor-vector
gravity at a point - the Einstein term, the Proca mass term and the scalar
potential - together with the Proca field equation for the massive vector.  The
Yukawa-enhanced potential is already formalised in the vendored MOG module; this
adds the V1 layer of the alternatives programme.

The vector and scalar stress-energy are supplied as data, so the modified
Einstein equation is stated as a residual rather than derived, and no
post-Newtonian or stability statement is made.

## ii. Key results

- `stvgActionDensity` : the gravitational action density at a point.
- `procaResidual` : the Proca equation `div B + mu^2 phi = 0` in one component.
- `procaResidual_mu_zero_eq_zero_iff` : at zero mass it is the Maxwell equation.
- `mogEinsteinResidual` : one component of the modified Einstein equation.
- `IsMogSolution` : both field equations hold at a point.
- `procaLagrangian1D`, `procaEulerLagrange1D` : the one-dimensional Proca
  action density and its Euler–Lagrange residual.
- `procaEulerLagrange1D_eq`, `procaStationarity_iff` : the residual is the
  Proca residual, so the field equation is the stationarity condition.

## iii. Table of contents

- A. The action density
- B. The field equations
- C. The one-dimensional Proca variation

## iv. References

* J. W. Moffat, *Scalar-tensor-vector gravity theory*, JCAP 03 (2006) 004,
  arXiv:gr-qc/0506021.
* J. W. Moffat, *A modified gravity and its consequences for the Solar System,
  astrophysics and cosmology*, Int. J. Mod. Phys. D 16 (2007) 2075,
  arXiv:gr-qc/0608074.
-/

@[expose] public section

namespace GeneralRelativity

/-! ## A. The action density -/

/-- The gravitational sector of the STVG action density at a point:
`R/(16 pi G) - B^2/4 + mu^2 phi^2/2 - V`, with `G` the running coupling, `B^2`
the squared field strength, `phi^2 = phi_mu phi^mu` and `V` the scalar
potential.  The matter coupling is not included. -/
noncomputable def stvgActionDensity (G R B2 phiSq mu V : ℝ) : ℝ :=
  R / (16 * Real.pi * G) - B2 / 4 + mu ^ 2 * phiSq / 2 - V

/-! ## B. The field equations -/

/-- The Proca field equation `div B + mu^2 phi = 0` in one frame component,
with the divergence of the field strength and the vector component supplied. -/
noncomputable def procaResidual (divB mu phiComp : ℝ) : ℝ :=
  divB + mu ^ 2 * phiComp

/-- At zero mass the Proca equation is the Maxwell equation `div B = 0`. -/
lemma procaResidual_mu_zero_eq_zero_iff (divB phiComp : ℝ) :
    procaResidual divB 0 phiComp = 0 ↔ divB = 0 := by
  simp [procaResidual]

/-- One component of the modified Einstein equation
`G_{mu nu} = 8 pi G T_{mu nu}`, with the vector and scalar stress contributions
folded into `Ecouple`. -/
noncomputable def mogEinsteinResidual (G Ecouple T : ℝ) : ℝ :=
  Ecouple - 8 * Real.pi * G * T

/-- The modified Einstein equation holds exactly when the coupled Einstein
tensor equals `8 pi G` times the source. -/
lemma mogEinsteinResidual_eq_zero_iff (G Ecouple T : ℝ) :
    mogEinsteinResidual G Ecouple T = 0 ↔ Ecouple = 8 * Real.pi * G * T := by
  unfold mogEinsteinResidual
  constructor <;> intro h <;> linarith

/-- A point at which the STVG field equations hold. -/
structure IsMogSolution (G Ecouple T divB mu phiComp : ℝ) : Prop where
  /-- The modified Einstein equation holds. -/
  einstein_eq : mogEinsteinResidual G Ecouple T = 0
  /-- The Proca equation holds. -/
  proca_eq : procaResidual divB mu phiComp = 0

/-! ## C. The one-dimensional Proca variation -/

/-- The one-dimensional Proca (Klein–Gordon) Lagrangian density
`1/2 (phi')^2 - 1/2 mu^2 phi^2`, the shadow of the STVG Proca sector on a
single component. -/
noncomputable def procaLagrangian1D (mu phi phi' : ℝ) : ℝ :=
  1 / 2 * phi' ^ 2 - 1 / 2 * mu ^ 2 * phi ^ 2

/-- The Euler–Lagrange residual `d/dphi L - d/dx (d/dphi' L)` of the
one-dimensional Proca Lagrangian, `phi'' + mu^2 phi`. -/
noncomputable def procaEulerLagrange1D (mu phi phi'' : ℝ) : ℝ :=
  phi'' + mu ^ 2 * phi

/-- The one-dimensional Proca Euler–Lagrange residual is the Proca residual
with the divergence supplied by `phi''`. -/
lemma procaEulerLagrange1D_eq (mu phi phi'' : ℝ) :
    procaEulerLagrange1D mu phi phi'' = procaResidual phi'' mu phi := by
  simp [procaEulerLagrange1D, procaResidual]

/-- The one-dimensional Proca field equation holds exactly when the
Euler–Lagrange residual of the Proca action vanishes. -/
lemma procaStationarity_iff (mu phi phi'' : ℝ) :
    procaEulerLagrange1D mu phi phi'' = 0 ↔ procaResidual phi'' mu phi = 0 := by
  rw [procaEulerLagrange1D_eq]

/-- The partial derivative of the Proca Lagrangian with respect to the field is
`-mu^2 phi`. -/
lemma procaLagrangian1D_deriv_phi (mu phi phi' : ℝ) :
    deriv (fun p : ℝ => procaLagrangian1D mu p phi') phi = -mu ^ 2 * phi := by
  change deriv ((fun p : ℝ => (1 / 2) * phi' ^ 2) - (fun p => (1 / 2) * mu ^ 2 * p ^ 2)) phi = -mu ^ 2 * phi
  rw [deriv_sub (by fun_prop) (by fun_prop)]
  simp
  ring

/-- The partial derivative of the Proca Lagrangian with respect to the field
derivative is `phi'`. -/
lemma procaLagrangian1D_deriv_phi' (mu phi phi' : ℝ) :
    deriv (fun q : ℝ => procaLagrangian1D mu phi q) phi' = phi' := by
  change deriv ((fun q : ℝ => (1 / 2) * q ^ 2) - (fun _ => (1 / 2) * mu ^ 2 * phi ^ 2)) phi' = phi'
  rw [deriv_sub (by fun_prop) (by fun_prop)]
  simp

end GeneralRelativity
