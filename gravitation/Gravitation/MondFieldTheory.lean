/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Positivity

/-!
# MOND as a field theory: the AQUAL action and its field equation

## i. Overview

This module states the Bekenstein-Milgrom AQUAL action and the modified Poisson
equation it is meant to produce.  It supplies the V1 layer (action and field
equations) for MOND in the alternatives programme.

Deriving the field equation from the action is variational calculus and is not
formalised here: the free function of the action and the interpolating function
of the equation are kept as separate data, related by an explicit hypothesis in
the paper.

## ii. Key results

- `mondMu` : the interpolating function `mu(x) = x / sqrt (1 + x^2)`.
- `aqualActionDensity` : the AQUAL Lagrangian density at a point.
- `aqualFieldResidual` : `div (mu grad phi) - 4 pi G rho`.
- `IsAqualSolution` : the field equation holds at a point.
- `aqualFieldResidual_eq_zero_iff` : with `mu = 1` it is the Poisson equation.

## iii. Table of contents

- A. The interpolating function
- B. Action and field equation

## iv. References

* J. Bekenstein, M. Milgrom, *Does the missing mass problem signal the
  breakdown of Newtonian gravity?*, ApJ 286 (1984) 7.
* M. Milgrom, *A modification of the Newtonian dynamics as a possible
  alternative to the hidden mass hypothesis*, ApJ 270 (1983) 365.
-/

@[expose] public section

namespace GeneralRelativity

/-! ## A. The interpolating function -/

/-- Milgrom's interpolating function `mu(x) = x / sqrt (1 + x^2)`: it is `~ x`
in the deep-MOND regime and tends to `1` in the Newtonian one. -/
noncomputable def mondMu (x : ℝ) : ℝ := x / Real.sqrt (1 + x ^ 2)

/-- The interpolating function vanishes at zero acceleration. -/
lemma mondMu_zero : mondMu 0 = 0 := by
  simp [mondMu]

/-- The interpolating function is positive for positive acceleration. -/
lemma mondMu_pos {x : ℝ} (hx : 0 < x) : 0 < mondMu x := by
  unfold mondMu
  positivity

/-! ## B. Action and field equation -/

/-- The AQUAL action density
`-(a0^2 / (8 pi G)) F(|grad phi|^2 / a0^2) - rho phi` at a point.  The free
function `F` and the field value `phi` are supplied. -/
noncomputable def aqualActionDensity (a0 G : ℝ) (F : ℝ → ℝ) (rho phi : ℝ)
    (gradPhi : Fin 3 → ℝ) : ℝ :=
  -(a0 ^ 2 / (8 * Real.pi * G)) * F ((∑ i : Fin 3, gradPhi i ^ 2) / a0 ^ 2)
    - rho * phi

/-- The AQUAL field equation `div (mu (|grad phi| / a0) grad phi) = 4 pi G rho`
as a residual, with the divergence supplied. -/
noncomputable def aqualFieldResidual (G rho divMuGrad : ℝ) : ℝ :=
  divMuGrad - 4 * Real.pi * G * rho

/-- A point at which the AQUAL field equation holds. -/
structure IsAqualSolution (G rho divMuGrad : ℝ) : Prop where
  /-- The field equation residual vanishes. -/
  field_eq : aqualFieldResidual G rho divMuGrad = 0

/-- At unit interpolating function the AQUAL equation is the Poisson equation
of Newtonian gravity. -/
lemma aqualFieldResidual_eq_zero_iff (G rho divGrad : ℝ) :
    aqualFieldResidual G rho divGrad = 0 ↔ divGrad = 4 * Real.pi * G * rho := by
  unfold aqualFieldResidual
  constructor <;> intro h <;> linarith

end GeneralRelativity
