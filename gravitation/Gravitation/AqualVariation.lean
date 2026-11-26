/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Gravitation.MondFieldTheory
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The Euler-Lagrange residual of the AQUAL action

## i. Overview

This module assembles the Euler-Lagrange residual of the AQUAL action in a
one-dimensional model and proves that its vanishing is exactly the MOND field
equation.  The action density depends on the field and its first derivative;
the residual is `dL/dphi - d/dx (dL/dphi')`, with the conjugate momentum
`-(1/4 pi G) mu (|phi'|/a0) phi'` and its derivative written through the free
function's first two derivatives.

The two partial derivatives of the density are computed, and the algebraic
assembly and the equivalence with `IsAqualSolution` are proved.  The derivative
of the conjugate momentum along the slice, and the functional-analytic step
behind a full derivation (compact-support variations, integration by parts, and
the fundamental lemma of the calculus of variations), are not formalised.  The
free function carries its derivative data and the identification
`F' = mu ∘ sqrt` as hypotheses.

## ii. Key results

- `AqualFreeFunction` : the free function with `F' = mu ∘ sqrt` and its two
  derivative facts.
- `aqualLagrangianDensity1D` : the action density at a point.
- `aqualLagrangianDensity1D_deriv_phi`, `..._deriv_grad` : the two partial
  derivatives, `-rho` and `-(a0^2/8 pi G) F' (2 phi' / a0^2)`.
- `aqualMomentumDensity` : the conjugate momentum.
- `aqualDivergence1D` : `d/dx (mu (|phi'|/a0) phi')` through `F'` and `F''`.
- `aqualEulerLagrangeResidual_eq` : the residual is the AQUAL residual divided
  by `4 pi G`.
- `aqual_euler_lagrange_iff` : stationarity is the MOND field equation.

## iii. Table of contents

- A. The free function and the one-dimensional density
- B. The residual and stationarity

## iv. References

* J. Bekenstein, M. Milgrom, ApJ 286 (1984) 7.
* M. Milgrom, ApJ 270 (1983) 365.
-/

@[expose] public section

namespace GeneralRelativity

/-! ## A. The free function and the one-dimensional density -/

/-- The free function of the AQUAL action with its first two derivatives and the
identification `F' = mu ∘ sqrt` that makes the Euler-Lagrange equation the MOND
equation.  The derivative facts are hypotheses: they express the chain rule for
a specified `F`, not the variation itself. -/
structure AqualFreeFunction where
  /-- The free function `F`. -/
  F : ℝ → ℝ
  /-- Its first derivative. -/
  F' : ℝ → ℝ
  /-- Its second derivative. -/
  F'' : ℝ → ℝ
  /-- The first derivative is `F'` away from zero. -/
  hasDeriv : ∀ y : ℝ, 0 < y → HasDerivAt F (F' y) y
  /-- The second derivative is `F''` away from zero. -/
  hasDeriv' : ∀ y : ℝ, 0 < y → HasDerivAt F' (F'' y) y
  /-- The interpolating identification `F'(y) = mu (sqrt y)`. -/
  interpolating : ∀ y : ℝ, 0 < y → F' y = mondMu (Real.sqrt y)

/-- The AQUAL action density in a one-dimensional model at a point:
`-(a0^2 / (8 pi G)) F(phi'^2 / a0^2) - rho phi`. -/
noncomputable def aqualLagrangianDensity1D (a0 G : ℝ) (F : ℝ → ℝ) (rho phi phi' : ℝ) : ℝ :=
  -(a0 ^ 2 / (8 * Real.pi * G)) * F (phi' ^ 2 / a0 ^ 2) - rho * phi

/-- The conjugate momentum to the field in the one-dimensional model:
`-(1 / (4 pi G)) F'(phi'^2 / a0^2) phi'`, which is `-(1 / (4 pi G)) mu (|phi'|/a0) phi'`. -/
noncomputable def aqualMomentumDensity (a0 G : ℝ) (F' : ℝ → ℝ) (phi' : ℝ) : ℝ :=
  -(1 / (4 * Real.pi * G)) * F' (phi' ^ 2 / a0 ^ 2) * phi'

/-! ## B. The residual and stationarity -/

/-- The one-dimensional divergence `d/dx [mu (|phi'|/a0) phi']`, written through
`F'` and `F''`. -/
noncomputable def aqualDivergence1D (a0 : ℝ) (phi' phi'' : ℝ) (F' F'' : ℝ → ℝ) : ℝ :=
  F' (phi' ^ 2 / a0 ^ 2) * phi'' +
    F'' (phi' ^ 2 / a0 ^ 2) * (2 * phi' * phi'' / a0 ^ 2) * phi'

/-- The Euler-Lagrange residual `dL/dphi - d/dx (dL/dphi')` in the
one-dimensional model, assembled from `dL/dphi = -rho` and the derivative of the
conjugate momentum. -/
noncomputable def aqualEulerLagrangeResidual (a0 G rho phi' phi'' : ℝ)
    (F' F'' : ℝ → ℝ) : ℝ :=
  -rho + aqualDivergence1D a0 phi' phi'' F' F'' / (4 * Real.pi * G)

/-- The Euler-Lagrange residual is the AQUAL residual divided by `4 pi G`. -/
lemma aqualEulerLagrangeResidual_eq (a0 G rho phi' phi'' : ℝ) (F' F'' : ℝ → ℝ)
    (hG : G ≠ 0) :
    aqualEulerLagrangeResidual a0 G rho phi' phi'' F' F'' =
      (aqualDivergence1D a0 phi' phi'' F' F'' - 4 * Real.pi * G * rho) /
        (4 * Real.pi * G) := by
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have h4 : 4 * Real.pi * G ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hpi) hG
  unfold aqualEulerLagrangeResidual
  field_simp
  ring

/-- Stationarity of the one-dimensional AQUAL action is the MOND field equation,
with the one-dimensional divergence playing the role of `div (mu grad phi)`. -/
theorem aqual_euler_lagrange_iff (a0 G rho phi' phi'' : ℝ) (F' F'' : ℝ → ℝ)
    (hG : G ≠ 0) :
    aqualEulerLagrangeResidual a0 G rho phi' phi'' F' F'' = 0 ↔
      IsAqualSolution G rho (aqualDivergence1D a0 phi' phi'' F' F'') := by
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have h4 : 4 * Real.pi * G ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hpi) hG
  constructor
  · intro h
    refine IsAqualSolution.mk ?_
    unfold aqualFieldResidual
    unfold aqualEulerLagrangeResidual at h
    have hd : aqualDivergence1D a0 phi' phi'' F' F'' / (4 * Real.pi * G) = rho := by
      linarith
    have hm : aqualDivergence1D a0 phi' phi'' F' F'' = rho * (4 * Real.pi * G) :=
      (div_eq_iff h4).mp hd
    rw [hm]
    ring
  · intro h
    unfold aqualEulerLagrangeResidual
    have hd : aqualDivergence1D a0 phi' phi'' F' F'' = 4 * Real.pi * G * rho := by
      have := h.field_eq
      unfold aqualFieldResidual at this
      linarith
    rw [hd]
    field_simp
    ring

/-- With the free function's derivative data, stationarity of the
one-dimensional AQUAL action is the MOND field equation. -/
theorem aqualFreeFunction_stationary_iff (A : AqualFreeFunction) (a0 G rho phi' phi'' : ℝ)
    (hG : G ≠ 0) :
    aqualEulerLagrangeResidual a0 G rho phi' phi'' A.F' A.F'' = 0 ↔
      IsAqualSolution G rho (aqualDivergence1D a0 phi' phi'' A.F' A.F'') :=
  aqual_euler_lagrange_iff a0 G rho phi' phi'' A.F' A.F'' hG

/-- The partial derivative of the density with respect to the field is `-rho`. -/
lemma aqualLagrangianDensity1D_deriv_phi (a0 G : ℝ) (F : ℝ → ℝ) (rho phi phi' : ℝ) :
    deriv (fun p : ℝ => aqualLagrangianDensity1D a0 G F rho p phi') phi = -rho := by
  simp [aqualLagrangianDensity1D]

/-- The partial derivative of the density with respect to the field derivative is
`-(a0^2 / (8 pi G)) F'(phi'^2/a0^2) (2 phi' / a0^2)`. -/
lemma aqualLagrangianDensity1D_deriv_grad (a0 G : ℝ) (F F' : ℝ → ℝ) (rho phi phi' : ℝ)
    (hF : HasDerivAt F (F' (phi' ^ 2 / a0 ^ 2)) (phi' ^ 2 / a0 ^ 2)) :
    deriv (fun q : ℝ => aqualLagrangianDensity1D a0 G F rho phi q) phi' =
      -(a0 ^ 2 / (8 * Real.pi * G)) * F' (phi' ^ 2 / a0 ^ 2) * (2 * phi' / a0 ^ 2) := by
  have hd : deriv (fun q : ℝ => aqualLagrangianDensity1D a0 G F rho phi q) phi'
      = -(a0 ^ 2 / (8 * Real.pi * G)) * deriv (fun q : ℝ => F (q ^ 2 / a0 ^ 2)) phi' := by
    simp [aqualLagrangianDensity1D]
  have hg : DifferentiableAt ℝ (fun q : ℝ => q ^ 2 / a0 ^ 2) phi' := by fun_prop
  have hcomp : deriv (fun q : ℝ => F (q ^ 2 / a0 ^ 2)) phi'
      = deriv F (phi' ^ 2 / a0 ^ 2) * deriv (fun q : ℝ => q ^ 2 / a0 ^ 2) phi' := by
    simpa [Function.comp_def] using deriv_comp phi' hF.differentiableAt hg
  have hdg : deriv (fun q : ℝ => q ^ 2 / a0 ^ 2) phi' = 2 * phi' / a0 ^ 2 := by simp
  rw [hd, hcomp, hF.deriv, hdg]
  ring

end GeneralRelativity
