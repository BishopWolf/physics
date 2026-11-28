/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.NormNum

/-!
# The post-Newtonian (PPN) framework

## i. Overview

This module states the comparison framework V2 of the alternatives programme:
the ten post-Newtonian parameters and the leading terms of the PPN metric
expansion.  It does not derive the parameters of any particular theory nor
compare them with Solar-System bounds; it fixes the language in which that
comparison is to be made.

## ii. Key results

- `PPNParameters` : the parameters `gamma, beta, alpha_1, alpha_2, xi,
  zeta_1, ..., zeta_4`.
- `grParameters` : the general-relativistic values `gamma = beta = 1`, the rest
  zero.
- `ppnG00`, `ppnGij` : the leading metric components `-1 + 2U - 2 beta U^2`
  and `(1 + 2 gamma U) delta_ij`.
- `ppnG00_gr`, `ppnGij_gr` : those components at the GR parameter point.
- `hasDerivAt_ppnG00`, `hasDerivAt_ppnGij` : the Newtonian-limit slopes
  `d g_00 / dU = 2` and `d g_ij / dU = 2 gamma delta_ij` at `U = 0`.
- `lightDeflectionFactor`, `perihelionPrecessionFactor`, `nordtvedtParameter` :
  the Solar-System observables, with their GR-point values `1`, `1`, `0`.
- `bransDickeGamma` : the Brans–Dicke parameter `gamma = (1 + omega)/(2 + omega)`,
  with `bransDickeGamma_lt_one` (`gamma < 1` for `omega > -2`) and
  `bransDickeGamma_zero` (`gamma = 1/2` at `omega = 0`).

## iii. Table of contents

- A. The parameters
- B. The leading metric
- C. The Newtonian limit
- D. Solar-System observables
- E. Theory parameters: Brans–Dicke

## iv. References

* C. M. Will, *Theory and Experiment in Gravitational Physics*, 2nd ed.,
  Cambridge University Press, 2018.
* C. M. Will, *The Confrontation between General Relativity and Experiment*,
  Living Reviews in Relativity 17 (2014) 4.
-/

@[expose] public section

namespace GeneralRelativity

/-! ## A. The parameters -/

/-- The ten post-Newtonian parameters.  `gamma` and `beta` are the classical
PPN parameters; `alpha_1, alpha_2` are the preferred-frame parameters; `xi` is
the Whitehead parameter; `zeta_1, ..., zeta_4` are the conservation
parameters. -/
structure PPNParameters where
  /-- The space-curvature parameter. -/
  gamma : ℝ
  /-- The non-linearity parameter. -/
  beta : ℝ
  /-- The first preferred-frame parameter. -/
  alpha1 : ℝ
  /-- The second preferred-frame parameter. -/
  alpha2 : ℝ
  /-- The Whitehead parameter. -/
  xi : ℝ
  /-- The first conservation parameter. -/
  zeta1 : ℝ
  /-- The second conservation parameter. -/
  zeta2 : ℝ
  /-- The third conservation parameter. -/
  zeta3 : ℝ
  /-- The fourth conservation parameter. -/
  zeta4 : ℝ

/-- The general-relativistic parameter values: `gamma = beta = 1` and all the
others zero. -/
def grParameters : PPNParameters :=
  { gamma := 1, beta := 1, alpha1 := 0, alpha2 := 0, xi := 0
    zeta1 := 0, zeta2 := 0, zeta3 := 0, zeta4 := 0 }

/-- `gamma = 1` for general relativity. -/
lemma grParameters_gamma : grParameters.gamma = 1 := rfl

/-- `beta = 1` for general relativity. -/
lemma grParameters_beta : grParameters.beta = 1 := rfl

/-! ## B. The leading metric -/

/-- The leading `g_00` component of the PPN metric, `-1 + 2U - 2 beta U^2`,
with the Newtonian potential `U`. -/
def ppnG00 (beta U : ℝ) : ℝ := -1 + 2 * U - 2 * beta * U ^ 2

/-- The leading spatial `g_ij` component `(1 + 2 gamma U) delta_ij`. -/
def ppnGij (gamma U : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j => (1 + 2 * gamma * U) * (if i = j then 1 else 0)

/-- The `g_00` expansion is `-1 + 2U - 2 beta U^2` by definition. -/
lemma ppnG00_eq (beta U : ℝ) : ppnG00 beta U = -1 + 2 * U - 2 * beta * U ^ 2 := rfl

/-- The spatial metric is `(1 + 2 gamma U) delta_ij`. -/
lemma ppnGij_eq (gamma U : ℝ) (i j : Fin 3) :
    ppnGij gamma U i j = (1 + 2 * gamma * U) * (if i = j then 1 else 0) := rfl

/-- At the GR point the `g_00` component is `-1 + 2U - 2U^2`. -/
lemma ppnG00_gr (U : ℝ) : ppnG00 grParameters.beta U = -1 + 2 * U - 2 * U ^ 2 := by
  simp [ppnG00, grParameters]

/-- At the GR point the spatial metric is `(1 + 2U) delta_ij`. -/
lemma ppnGij_gr (U : ℝ) (i j : Fin 3) :
    ppnGij grParameters.gamma U i j = (1 + 2 * U) * (if i = j then 1 else 0) := by
  simp [ppnGij, grParameters]

/-! ## C. The Newtonian limit -/

/-- The `g_00` potential has unit Newtonian slope at `U = 0`:
`d g_00 / dU = 2`, independent of `beta`. -/
lemma hasDerivAt_ppnG00 (beta : ℝ) :
    HasDerivAt (fun U => ppnG00 beta U) 2 0 := by
  have hg := HasDerivAt.sub
    (HasDerivAt.add (hasDerivAt_const (0 : ℝ) (-1 : ℝ))
      (HasDerivAt.const_mul (2 : ℝ) (hasDerivAt_id (0 : ℝ))))
    (HasDerivAt.const_mul (2 * beta) (HasDerivAt.pow (hasDerivAt_id (0 : ℝ)) 2))
  have hfun : (fun U => ppnG00 beta U) = (fun U => -1 + 2 * U - 2 * beta * U ^ 2) := by
    funext U; simp [ppnG00]
  rw [hfun]
  convert hg using 1
  · funext U; simp [Pi.add_apply, Pi.sub_apply]
  · simp only [id_eq]; norm_num

/-- The spatial potential has slope `2 gamma delta_ij` at `U = 0`:
`d g_ij / dU = 2 gamma delta_ij`. -/
lemma hasDerivAt_ppnGij (gamma : ℝ) (i j : Fin 3) :
    HasDerivAt (fun U => ppnGij gamma U i j) (2 * gamma * (if i = j then 1 else 0)) 0 := by
  have hg := HasDerivAt.mul_const
    (HasDerivAt.add (hasDerivAt_const (0 : ℝ) (1 : ℝ))
      (HasDerivAt.const_mul (2 * gamma) (hasDerivAt_id (0 : ℝ))))
    (if i = j then 1 else 0)
  have hfun : (fun U => ppnGij gamma U i j) =
      (fun U => (1 + 2 * gamma * U) * (if i = j then 1 else 0)) := by
    funext U; simp [ppnGij]
  rw [hfun]
  convert hg using 1
  · funext U; simp [Pi.add_apply]
  · ring

/-! ## D. Solar-System observables -/

/-- The light-deflection factor `(1 + gamma) / 2`, equal to `1` in general
relativity. -/
noncomputable def lightDeflectionFactor (P : PPNParameters) : ℝ :=
  (1 + P.gamma) / 2

/-- The perihelion-precession factor `(2 + 2 gamma - beta) / 3`, equal to `1` in
general relativity. -/
noncomputable def perihelionPrecessionFactor (P : PPNParameters) : ℝ :=
  (2 + 2 * P.gamma - P.beta) / 3

/-- The Nordtvedt parameter `eta_N = 4 beta - gamma - 3 - (10/3) xi - alpha_1
+ (2/3) alpha_2 - (2/3) zeta_1 - (1/3) zeta_2`, equal to `0` in general
relativity. -/
noncomputable def nordtvedtParameter (P : PPNParameters) : ℝ :=
  4 * P.beta - P.gamma - 3 - (10 / 3) * P.xi - P.alpha1 + (2 / 3) * P.alpha2
    - (2 / 3) * P.zeta1 - (1 / 3) * P.zeta2

/-- In general relativity the light-deflection factor is `1`. -/
lemma lightDeflectionFactor_gr : lightDeflectionFactor grParameters = 1 := by
  norm_num [lightDeflectionFactor, grParameters]

/-- In general relativity the perihelion-precession factor is `1`. -/
lemma perihelionPrecessionFactor_gr : perihelionPrecessionFactor grParameters = 1 := by
  norm_num [perihelionPrecessionFactor, grParameters]

/-- In general relativity the Nordtvedt parameter is `0`. -/
lemma nordtvedtParameter_gr : nordtvedtParameter grParameters = 0 := by
  norm_num [nordtvedtParameter, grParameters]

/-! ## E. Theory parameters: Brans–Dicke -/

/-- The Brans–Dicke post-Newtonian parameter `gamma = (1 + omega)/(2 + omega)`,
with `omega` the Brans–Dicke coupling.  The general-relativistic limit is the
`omega -> infinity` limit, approached from below. -/
noncomputable def bransDickeGamma (omega : ℝ) : ℝ :=
  (1 + omega) / (2 + omega)

/-- `gamma = 1 - 1/(2 + omega)` for `omega != -2`. -/
lemma bransDickeGamma_eq (omega : ℝ) (h : omega ≠ -2) :
    bransDickeGamma omega = 1 - 1 / (2 + omega) := by
  unfold bransDickeGamma
  have h2 : 2 + omega ≠ 0 := by intro hz; apply h; linarith
  field_simp [h2]
  ring

/-- The Brans–Dicke `gamma` is strictly below the general-relativistic value
`1` for every `omega > -2`. -/
lemma bransDickeGamma_lt_one (omega : ℝ) (h : -2 < omega) :
    bransDickeGamma omega < 1 := by
  rw [bransDickeGamma_eq omega (by linarith)]
  have h2 : 0 < 2 + omega := by linarith
  have hpos : 0 < 1 / (2 + omega) := by positivity
  linarith

/-- At `omega = 0` the Brans–Dicke parameter is `gamma = 1/2`. -/
lemma bransDickeGamma_zero : bransDickeGamma 0 = 1 / 2 := by
  norm_num [bransDickeGamma]

end GeneralRelativity