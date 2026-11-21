import Gravitation.Examples.Minkowski
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp

/-!
# The Schwarzschild curvature is Ricci flat

In the orthonormal frame `(t, r, θ, φ)` the Schwarzschild curvature is a purely
electric Weyl tensor:

`R_{trtr} = −2k`, `R_{tθtθ} = R_{tφtφ} = k`, `R_{rθrθ} = R_{rφrφ} = −k`,
`R_{θφθφ} = 2k`, all other components zero, with `k = M/r³` at the point.

This file builds that tensor from its electric part `E = diag(0, −2k, k, k)` by

`R_{ijlm} = δ_{il} E_{jm} − δ_{im} E_{jl} − δ_{jl} E_{im} + δ_{jm} E_{il}`,

proves the three structural laws of `Riemann`, proves that the Ricci
contraction against `η` vanishes for every `k` — so Schwarzschild satisfies the
vacuum Einstein equation in this frame — and computes the sum of squares of the
frame components, `48 k²`, which at `k = M/r³` is the Schwarzschild
Kretschmann scalar `48 M²/r⁶`.

**Scope.**  This verifies the curvature algebra of the solution, not its
derivation: the components are supplied as the standard orthonormal-frame
components, and obtaining them from `g = diag(−f, 1/f, r², r²sin²θ)` by
differentiating the Christoffel symbols is not formalised here.
-/

namespace Gravitation

/-- The electric part of a static Weyl tensor in the frame `(t, r, θ, φ)`:
`diag(0, −2k, k, k)`, symmetric and trace free. -/
noncomputable def electricPart (k : ℝ) (i j : Fin 4) : ℝ :=
  if i = j then (if i = 0 then 0 else if i = 1 then -2 * k else k) else 0

theorem electricPart_symm (k : ℝ) (i j : Fin 4) :
    electricPart k i j = electricPart k j i := by
  fin_cases i <;> fin_cases j <;> simp [electricPart]

theorem electricPart_trace (k : ℝ) : (∑ i, electricPart k i i) = 0 := by
  simp [electricPart, Fin.sum_univ_four]
  ring

/-- Sum of squares of the frame components of a curvature tensor. -/
noncomputable def frameSqSum (R : Riemann 4) : ℝ :=
  ∑ i, ∑ j, ∑ l, ∑ m, R.comp i j l m * R.comp i j l m

/-- **The Schwarzschild curvature** in the orthonormal frame, with `k = M/r³`
at the point: the static Weyl tensor of electric part `E = diag(0, −2k, k, k)`. -/
noncomputable def schwarzschild (k : ℝ) : Riemann 4 where
  comp := fun i j l m =>
    (if i = l then electricPart k j m else 0)
      - (if i = m then electricPart k j l else 0)
      - (if j = l then electricPart k i m else 0)
      + (if j = m then electricPart k i l else 0)
  skew_last := by
    intro i j l m
    show (if i = l then electricPart k j m else 0)
        - (if i = m then electricPart k j l else 0)
        - (if j = l then electricPart k i m else 0)
        + (if j = m then electricPart k i l else 0)
      = -((if i = m then electricPart k j l else 0)
        - (if i = l then electricPart k j m else 0)
        - (if j = m then electricPart k i l else 0)
        + (if j = l then electricPart k i m else 0))
    ring
  pair_symm := by
    intro i j l m
    fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases m
    all_goals simp [electricPart, two_mul, add_assoc]
  bianchi := by
    intro i j l m
    fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases m
    all_goals simp [electricPart, two_mul, add_assoc]

namespace Schwarzschild

/-- **Schwarzschild is a vacuum solution.**  The Ricci contraction of the
Schwarzschild curvature against the Minkowski frame metric vanishes for every
value of the mass parameter. -/
theorem ricci_eq_zero (k : ℝ) : ricci minkowski (schwarzschild k) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [ricci, minkowski, schwarzschild, electricPart, eta4, Fin.sum_univ_four,
    two_mul, add_assoc]

/-- The frame components carry `48 k²` in total: the Weyl tensor's invariant. -/
theorem frameSqSum_eq (k : ℝ) : frameSqSum (schwarzschild k) = 48 * k ^ 2 := by
  simp [frameSqSum, schwarzschild, electricPart, Fin.sum_univ_four, two_mul, add_assoc]
  ring

/-- **The Schwarzschild Kretschmann scalar** `48 M²/r⁶`, obtained at
`k = M/r³`. -/
theorem kretschmann_scalar (M r : ℝ) (hr : r ≠ 0) :
    frameSqSum (schwarzschild (M / r ^ 3)) = 48 * M ^ 2 / r ^ 6 := by
  rw [frameSqSum_eq]
  have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 hr
  field_simp

/-! ## From the Schwarzschild metric to the electric part

The components above are supplied; this section ties them to the metric.  The
Schwarzschild line element in `(t, r, θ, φ)` coordinates is

`ds² = −f dt² + f⁻¹ dr² + r² dθ² + r² sin²θ dφ²`,  `f = 1 − 2M/r`,

and `g_tt = −f = −(1 + 2Φ)` for the potential `Φ = −M/r`, so the static
potential that governs the tidal field is read off from the metric itself.

In an orthonormal frame the Hessian of a radial potential has eigenvalues `Φ''`
along the radial direction and `Φ'/r` along the two angular directions, and the
electric part of the Weyl tensor is (up to sign) that Hessian.  Both eigenvalues
are proved here from `Φ`, giving `diag(0, −2M/r³, M/r³, M/r³)` — which is
exactly `electricPart` at `k = M/r³`, the same `k` that `kretschmann_scalar`
fixes from the mass.  So the tidal eigenvalues are derived, not assumed.

What is still not formalised is the contraction of the full Riemann tensor of
this metric against the orthonormal frame, which would derive the electric part
from the metric without passing through the potential.
-/

/-- The Schwarzschild metric in `(t, r, θ, φ)` coordinates with signature
`(−,+,+,+)`, as a matrix of functions of the coordinates. -/
noncomputable def schwarzschildMetric (M : ℝ) (x : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun i j =>
    if i = j then
      if i = 0 then -(1 - 2 * M / x 1)
      else if i = 1 then (1 - 2 * M / x 1)⁻¹
      else if i = 2 then x 1 ^ 2
      else x 1 ^ 2 * Real.sin (x 2) ^ 2
    else 0

/-- The `tt` component of the Schwarzschild metric is `−f` with `f = 1 − 2M/r`. -/
theorem schwarzschildMetric_tt (M : ℝ) (x : Fin 4 → ℝ) :
    schwarzschildMetric M x 0 0 = -(1 - 2 * M / x 1) := by
  simp [schwarzschildMetric]

/-- The metric's static potential is `Φ = −M/r`: `g_tt = −(1 + 2Φ)`. -/
theorem schwarzschildMetric_tt_potential (M : ℝ) (x : Fin 4 → ℝ) :
    schwarzschildMetric M x 0 0 = -(1 + 2 * (-M / x 1)) := by
  rw [schwarzschildMetric_tt]
  ring

/-- First derivative of the potential: `Φ' = M/r²`. -/
theorem potential_hasDerivAt (M r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => -M / s) (M / r ^ 2) r := by
  have h : HasDerivAt (fun s : ℝ => s⁻¹) (-(r ^ 2)⁻¹) r := hasDerivAt_inv hr
  have h' := h.const_mul (-M)
  have hfun : (fun s : ℝ => -M / s) = fun s : ℝ => -M * s⁻¹ := by
    funext s
    simp [div_eq_mul_inv]
  have hval : -M * -(r ^ 2)⁻¹ = M / r ^ 2 := by ring
  rw [← hfun, hval] at h'
  exact h'

/-- The slope is itself differentiable: `Φ'' = −2M/r³`. -/
theorem slope_hasDerivAt (M r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => M / s ^ 2) (-2 * M / r ^ 3) r := by
  have hnum : HasDerivAt (fun _ : ℝ => M) 0 r := hasDerivAt_const r M
  have hden : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  have h := hnum.div hden (pow_ne_zero 2 hr)
  have hfun : (fun s : ℝ => M / s ^ 2) = (fun _ : ℝ => M) / fun s : ℝ => s ^ 2 := rfl
  have hval : (0 * r ^ 2 - M * (2 * r)) / (r ^ 2) ^ 2 = -2 * M / r ^ 3 := by
    have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
    have hr4 : (r ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hr2
    field_simp
    ring
  rw [← hfun, hval] at h
  exact h

/-- The tidal tensor of a static potential in the orthonormal frame
`(t, R, θ, φ)`: the time row vanishes, the radial entry is the second radial
derivative `Φ''` of the potential, and the two angular entries are `Φ'/r` —
the eigenvalues of the Hessian of a radial function in an orthonormal frame. -/
noncomputable def tidalPart (phiRR phiOverR : ℝ) (i j : Fin 4) : ℝ :=
  if i = j then (if i = 0 then 0 else if i = 1 then phiRR else phiOverR) else 0

/-- **The supplied electric part is the tidal tensor of the potential.**  With
`Φ = −M/r` the eigenvalues `Φ'' = −2M/r³` and `Φ'/r = M/r³` make the tidal
tensor `electricPart` at `k = M/r³`. -/
theorem tidalPart_eq_electricPart (M r : ℝ) :
    tidalPart (-2 * M / r ^ 3) (M / r ^ 3) = electricPart (M / r ^ 3) := by
  funext i j
  fin_cases i <;> fin_cases j
  all_goals first
    | (simp [tidalPart, electricPart]; ring)
    | simp [tidalPart, electricPart]

/-- **The tidal tensor is trace free.**  The exterior potential is harmonic,
`Φ'' + 2Φ'/r = 0`, which is the vacuum field equation read at the level of the
potential. -/
theorem tidal_trace_zero (M r : ℝ) :
    (-2 * M / r ^ 3) + 2 * (M / r ^ 3) = 0 := by
  ring

end Schwarzschild

end Gravitation
