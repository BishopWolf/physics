/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Gravitation.MondFieldTheory
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
equivalence with `IsAqualSolution` are proved.  A finite-graph version of the
variational derivation is also formalised: the action is a sum over links, its
first variation is computed, summation by parts converts it to a site sum, and
stationarity under all variations vanishing on the boundary is proved equivalent
to the discrete Euler-Lagrange equation at every interior site.  The continuum
step (compact-support variations on the line, integration by parts, and the
fundamental lemma of the calculus of variations) is not formalised.  The free
function carries its derivative data and the identification
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
- `sum_link_mul_difference` : summation by parts on a finite graph.
- `discrete_stationary_iff` : stationarity of the discrete action is the
  discrete Euler-Lagrange equation at every interior site.

## iii. Table of contents

- A. The free function and the one-dimensional density
- B. The residual and stationarity
- C. A discrete variational derivation

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

/-! ## C. A discrete variational derivation -/

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- The action of the one-dimensional model on a finite graph with link length
`h`, for the free function `F(s) = s`, whose Euler-Lagrange equation is the
Poisson equation.  The measure `h` multiplies both the gradient and the source
term. -/
noncomputable def discreteAction (a b : E → V) (G h : ℝ) (ρ φ : V → ℝ) : ℝ :=
  -(1 / (8 * Real.pi * G)) * (∑ e : E, (φ (b e) - φ (a e)) ^ 2 / h)
    - h * ∑ x : V, ρ x * φ x

/-- The divergence of a link field: the sum of the incoming links minus the sum
of the outgoing links at a site. -/
noncomputable def discreteDivergence (a b : E → V) (d : E → ℝ) (x : V) : ℝ :=
  (∑ e : E, if b e = x then d e else 0) - ∑ e : E, if a e = x then d e else 0

/-- Summation by parts on a finite graph: the link pairing of a difference with
a link field equals the site pairing of the field with the divergence. -/
lemma sum_link_mul_difference (a b : E → V) (d : E → ℝ) (v : V → ℝ) :
    (∑ e : E, d e * (v (b e) - v (a e)))
      = ∑ x : V, v x * discreteDivergence a b d x := by
  have hb : (∑ x : V, v x * (∑ e : E, if b e = x then d e else 0))
      = ∑ e : E, d e * v (b e) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_eq_single (b e)]
    · simp [mul_comm]
    · intro x _ hx
      simp [Ne.symm hx]
    · intro hmem
      exact absurd (Finset.mem_univ (b e)) hmem
  have ha : (∑ x : V, v x * (∑ e : E, if a e = x then d e else 0))
      = ∑ e : E, d e * v (a e) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_eq_single (a e)]
    · simp [mul_comm]
    · intro x _ hx
      simp [Ne.symm hx]
    · intro hmem
      exact absurd (Finset.mem_univ (a e)) hmem
  simp only [discreteDivergence]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hb, ha]

/-- The link momentum of the discrete model,
`(phi (b e) - phi (a e)) / (4 pi G h)`. -/
noncomputable def discreteMomentum (a b : E → V) (G h : ℝ) (φ : V → ℝ) : E → ℝ :=
  fun e => (φ (b e) - φ (a e)) / (4 * Real.pi * G * h)

/-- The discrete Euler-Lagrange residual at a site. -/
noncomputable def discreteResidual (a b : E → V) (G h : ℝ) (ρ φ : V → ℝ) (x : V) : ℝ :=
  discreteDivergence a b (discreteMomentum a b G h φ) x + h * ρ x

/-- The first variation of the discrete action in the direction `v`. -/
noncomputable def discreteFirstVariation (a b : E → V) (G h : ℝ) (ρ φ v : V → ℝ) : ℝ :=
  -∑ e : E, (1 / (4 * Real.pi * G)) * (φ (b e) - φ (a e)) * (v (b e) - v (a e)) / h
    - h * ∑ x : V, ρ x * v x

/-- The first variation is minus the site sum of the variation against the
discrete residual; this is summation by parts followed by collecting terms. -/
lemma discreteFirstVariation_eq_neg_sum (a b : E → V) (G h : ℝ) (ρ φ v : V → ℝ) :
    discreteFirstVariation a b G h ρ φ v
      = -∑ x : V, v x * discreteResidual a b G h ρ φ x := by
  have hgrad : (∑ e : E, (1 / (4 * Real.pi * G)) *
        (φ (b e) - φ (a e)) * (v (b e) - v (a e)) / h)
      = (1 / (4 * Real.pi * G)) *
        (∑ e : E, (φ (b e) - φ (a e)) * (v (b e) - v (a e)) / h) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun e _ => by ring_nf)
  have hcoef : (1 / (4 * Real.pi * G)) *
        (∑ e : E, (φ (b e) - φ (a e)) * (v (b e) - v (a e)) / h)
      = ∑ e : E, discreteMomentum a b G h φ e * (v (b e) - v (a e)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun e _ => by
      simp only [discreteMomentum]
      ring_nf)
  have hsrc : (∑ x : V, v x * (h * ρ x)) = h * ∑ x : V, ρ x * v x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  simp only [discreteFirstVariation, discreteResidual, hgrad, hcoef,
    sum_link_mul_difference a b (discreteMomentum a b G h φ) v]
  simp only [mul_add, Finset.sum_add_distrib, hsrc]
  ring

omit [DecidableEq V] in
/-- The derivative of the discrete action at `phi` in the direction `v` is the
first variation. -/
lemma hasDerivAt_discreteAction (a b : E → V) (G h : ℝ) (ρ φ v : V → ℝ) :
    HasDerivAt (fun ε : ℝ => discreteAction a b G h ρ (φ + ε • v))
      (discreteFirstVariation a b G h ρ φ v) 0 := by
  have hquad : HasDerivAt
      (fun ε : ℝ => ∑ e : E,
        ((φ (b e) - φ (a e)) + ε * (v (b e) - v (a e))) ^ 2 / h)
      (∑ e : E, 2 * (φ (b e) - φ (a e)) * (v (b e) - v (a e)) / h) 0 := by
    have hterm : ∀ e : E, HasDerivAt
        (fun ε : ℝ => ((φ (b e) - φ (a e)) + ε * (v (b e) - v (a e))) ^ 2 / h)
        (2 * (φ (b e) - φ (a e)) * (v (b e) - v (a e)) / h) 0 := by
      intro e
      have h1 : HasDerivAt
          (fun ε : ℝ => (φ (b e) - φ (a e)) + ε * (v (b e) - v (a e)))
          (v (b e) - v (a e)) 0 := by
        have h := (hasDerivAt_const (c := φ (b e) - φ (a e)) (x := (0 : ℝ))).add
          ((hasDerivAt_id (𝕜 := ℝ) 0).mul_const (v (b e) - v (a e)))
        convert h using 1
        · funext ε
          simp
        · ring
      have h3 := (h1.pow 2).div_const h
      convert h3 using 1
      ring
    convert HasDerivAt.sum (u := Finset.univ) (fun e _ => hterm e) using 1
    funext ε
    rw [Finset.sum_apply]
  have hlin : HasDerivAt
      (fun ε : ℝ => ∑ x : V, ρ x * (φ x + ε * v x))
      (∑ x : V, ρ x * v x) 0 := by
    have hterm : ∀ x : V, HasDerivAt
        (fun ε : ℝ => ρ x * (φ x + ε * v x)) (ρ x * v x) 0 := by
      intro x
      have h1 : HasDerivAt (fun ε : ℝ => φ x + ε * v x) (v x) 0 := by
        have h := (hasDerivAt_const (c := φ x) (x := (0 : ℝ))).add
          ((hasDerivAt_id (𝕜 := ℝ) 0).mul_const (v x))
        convert h using 1
        · funext ε
          simp
        · ring
      simpa using h1.const_mul (ρ x)
    convert HasDerivAt.sum (u := Finset.univ) (fun x _ => hterm x) using 1
    funext ε
    rw [Finset.sum_apply]
  have hfun : (fun ε : ℝ => discreteAction a b G h ρ (φ + ε • v))
      = fun ε : ℝ => -(1 / (8 * Real.pi * G)) *
          (∑ e : E, ((φ (b e) - φ (a e)) + ε * (v (b e) - v (a e))) ^ 2 / h)
          - h * ∑ x : V, ρ x * (φ x + ε * v x) := by
    funext ε
    have hdiff : ∀ e : E, (φ (b e) + ε * v (b e)) - (φ (a e) + ε * v (a e))
        = (φ (b e) - φ (a e)) + ε * (v (b e) - v (a e)) := by
      intro e
      ring
    simp only [discreteAction, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show (∑ e : E,
        ((φ (b e) + ε * v (b e)) - (φ (a e) + ε * v (a e))) ^ 2 / h)
        = ∑ e : E, ((φ (b e) - φ (a e)) + ε * (v (b e) - v (a e))) ^ 2 / h from
      Finset.sum_congr rfl (fun e _ => by rw [hdiff e])]
  have hmoment := (hquad.const_mul (-(1 / (8 * Real.pi * G)))).sub (hlin.const_mul h)
  rw [hfun]
  convert hmoment using 1
  rw [discreteFirstVariation]
  congr 1
  · rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun e _ => by ring_nf)

/-- A site is a boundary site when no link is incident to it. -/
def IsBoundary (a b : E → V) (x : V) : Prop :=
  ∀ e : E, a e ≠ x ∧ b e ≠ x

/-- A variation vanishes on the boundary when it is zero at every boundary
site; this is the discrete analogue of compact support. -/
def VanishesOnBoundary (a b : E → V) (v : V → ℝ) : Prop :=
  ∀ x : V, IsBoundary a b x → v x = 0

/-- Stationarity of the discrete action under every variation that vanishes on
the boundary is the discrete Euler-Lagrange equation at every interior site. -/
theorem discrete_stationary_iff (a b : E → V) (G h : ℝ) (ρ φ : V → ℝ) :
    (∀ v : V → ℝ, VanishesOnBoundary a b v →
        discreteFirstVariation a b G h ρ φ v = 0) ↔
      ∀ x : V, ¬ IsBoundary a b x → discreteResidual a b G h ρ φ x = 0 := by
  classical
  constructor
  · intro hstat x hx
    let v : V → ℝ := fun y => if y = x then 1 else 0
    have hv : VanishesOnBoundary a b v := by
      intro y hy
      by_cases hyx : y = x
      · subst hyx
        exact absurd hy hx
      · simp [v, hyx]
    have h0 := hstat v hv
    rw [discreteFirstVariation_eq_neg_sum] at h0
    have hsum : (∑ y : V, v y * discreteResidual a b G h ρ φ y)
        = discreteResidual a b G h ρ φ x := by
      rw [Finset.sum_eq_single x]
      · simp [v]
      · intro y _ hyx
        simp [v, hyx]
      · intro hmem
        exact absurd (Finset.mem_univ x) hmem
    rw [hsum] at h0
    exact neg_eq_zero.mp h0
  · intro hres v hv
    rw [discreteFirstVariation_eq_neg_sum]
    have hzero : (∑ x : V, v x * discreteResidual a b G h ρ φ x) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      by_cases hx : IsBoundary a b x
      · rw [hv x hx, zero_mul]
      · rw [hres x hx, mul_zero]
    rw [hzero, neg_zero]

end GeneralRelativity
