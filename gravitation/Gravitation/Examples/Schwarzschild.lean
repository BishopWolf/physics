import Gravitation.Examples.Minkowski
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

end Schwarzschild

end Gravitation
