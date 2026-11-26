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

The two partial derivatives of the density and the derivative of the conjugate
momentum along the slice are computed, and the algebraic assembly and the
equivalence with `IsAqualSolution` are proved.  The functional-analytic step
behind a full derivation (compact-support variations, integration by parts, and
the fundamental lemma of the calculus of variations) is not formalised.  The
free function carries its derivative data and the identification
`F' = mu ∘ sqrt` as hypotheses.

## ii. Key results

- `AqualFreeFunction` : the free function with `F' = mu ∘ sqrt` and its two
  derivative facts.
- `aqualLagrangianDensity1D` : the action density at a point.
- `aqualLagrangianDensity1D_deriv_phi`, `..._deriv_phi'` : the two partial
  derivatives, `-rho` and `-(a0^2/8 pi G) F' (2 phi' / a0^2)`.
- `aqualMomentumDensity`, `aqualMomentumDensity_deriv` : the conjugate momentum
  and its derivative along the slice.
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
noncomputable def aqualMomentumDensity (a0 G : ℝ) (F' : ℝ → ℝ) (phi' : ℝ → ℝ) : ℝ → ℝ :=
  fun x => -(1 / (4 * Real.pi * G)) * F' (phi' x ^ 2 / a0 ^ 2) * phi' x

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
lemma aqualLagrangianDensity1D_deriv_phi' (a0 G : ℝ) (F F' : ℝ → ℝ) (rho phi phi' : ℝ)
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

/-- The derivative along the slice of the conjugate momentum, in terms of `F'`
and `F''`. -/
lemma aqualMomentumDensity_deriv (a0 G : ℝ) (F' F'' : ℝ → ℝ) (φ ψ : ℝ → ℝ) (x : ℝ)
    (hφ : HasDerivAt φ (ψ x) x)
    (hF : HasDerivAt F' (F'' (φ x ^ 2 / a0 ^ 2)) (φ x ^ 2 / a0 ^ 2)) :
    deriv (fun y => aqualMomentumDensity a0 G F' φ y) x =
      -(1 / (4 * Real.pi * G)) *
        (F'' (φ x ^ 2 / a0 ^ 2) * (2 * φ x * ψ x / a0 ^ 2) * φ x +
          F' (φ x ^ 2 / a0 ^ 2) * ψ x) := by
  have hφdiff : DifferentiableAt ℝ φ x := hφ.differentiableAt
  have hgdiff : DifferentiableAt ℝ (fun y => φ y ^ 2 / a0 ^ 2) x := by
    have h1 : DifferentiableAt ℝ (fun y => φ y ^ 2) x := hφdiff.pow 2
    exact h1.div_const (a0 ^ 2)
  have hcomp : deriv (fun y => F' (φ y ^ 2 / a0 ^ 2)) x
      = F'' (φ x ^ 2 / a0 ^ 2) * deriv (fun y => φ y ^ 2 / a0 ^ 2) x := by
    have h := deriv_comp x hF.differentiableAt hgdiff
    simpa [Function.comp_def, hF.deriv] using h
  have hdg : deriv (fun y => φ y ^ 2 / a0 ^ 2) x = 2 * φ x * ψ x / a0 ^ 2 := by
    have h2 : deriv (fun y => φ y ^ 2) x = 2 * φ x * ψ x := by
      have h := deriv_comp x (by fun_prop : DifferentiableAt ℝ (fun z : ℝ => z ^ 2) (φ x))
        hφdiff
      simpa [Function.comp_def, hφ.deriv] using h
    have h := deriv_div_const (c := fun y => φ y ^ 2) (d := a0 ^ 2) (x := x)
    rw [h, h2]
  have hf : DifferentiableAt ℝ
      (fun y => -(1 / (4 * Real.pi * G)) * F' (φ y ^ 2 / a0 ^ 2)) x := by
    have h := hF.differentiableAt.comp x hgdiff
    exact h.const_mul _
  have hfun : (fun y => aqualMomentumDensity a0 G F' φ y)
      = (fun y => -(1 / (4 * Real.pi * G)) * F' (φ y ^ 2 / a0 ^ 2)) * φ := rfl
  rw [hfun, deriv_mul hf hφdiff, deriv_const_mul_field, hcomp, hdg, hφ.deriv]
  ring

end GeneralRelativity
