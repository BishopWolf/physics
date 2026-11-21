import Gravitation.Examples.Minkowski
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
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

**Scope.**  The first part verifies the curvature algebra of the solution with
the components supplied as the standard orthonormal-frame values.  The last two
sections then derive every component of the Weyl tensor directly from
`g = diag(−f, 1/f, r², r²sin²θ)` by differentiating the Christoffel symbols:
`R^t_{rtr}`, `R^t_{θtθ}`, `R^t_{φtφ}`, `R^r_{θrθ}`, `R^r_{φrφ}` and `R^θ_{φθφ}`.
The electric part is therefore no longer assumed.
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

/-- **The Schwarzschild frame Weyl tensor is purely electric**: with spatial
`j, l, m`, every component carrying exactly one temporal index vanishes.  There
is no magnetic part, so `electricPart k` is the whole of the Weyl tensor, which
is what the GPU's electric-part output reports. -/
theorem weyl_purely_electric (k : ℝ) (j l m : Fin 4) (hj : j ≠ 0) (hl : l ≠ 0)
    (hm : m ≠ 0) :
    (schwarzschild k).comp 0 j l m = 0 ∧ (schwarzschild k).comp j 0 l m = 0 ∧
      (schwarzschild k).comp j l 0 m = 0 ∧ (schwarzschild k).comp j l m 0 = 0 := by
  have h0j : (0 : Fin 4) ≠ j := fun h => hj h.symm
  have h0l : (0 : Fin 4) ≠ l := fun h => hl h.symm
  have h0m : (0 : Fin 4) ≠ m := fun h => hm h.symm
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [schwarzschild, electricPart]

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

/-! ## Contracting the metric into the Riemann tensor

The potential route above reads the tidal eigenvalues off a scalar.  Here the
same components come from the metric itself.  For this static diagonal metric
`g_tt = −f`, `g^{tt} = −f⁻¹`, `g_rr = f⁻¹`, `g^{rr} = f`, differentiating the
components gives

`Γ^t_{tr} = ½ g^{tt} ∂_r g_tt = M/(r²f)` and
`Γ^r_{rr} = ½ g^{rr} ∂_r g_{rr} = −M/(r(r−2M))`,

and the `t r t r` component of the Riemann tensor is the sum of the only terms
that survive for such a metric,

`R^t{}_{rtr} = −∂_r Γ^t_{tr} + Γ^t_{tr} Γ^r_{rr} − (Γ^t_{tr})² = 2M/(r³f)`.

Lowering with `g_tt = −f` gives `R_{trtr} = −2k`.  The angular component comes
from `Γ^r_{θθ} = −rf`: `R^t{}_{θtθ} = Γ^t_{tr} Γ^r_{θθ} = −M/r`, which the
orthonormal frame scales to `+k`.  Both are `electricPart (M/r³)`, so the
components used by `schwarzschild` are the ones this metric actually has.
-/

/-- The Schwarzschild metric function `f = 1 − 2M/r`. -/
noncomputable def schwarzschildF (M r : ℝ) : ℝ := 1 - 2 * M / r

/-- `g_rr = f⁻¹`, the `rr` component of the metric. -/
theorem schwarzschildMetric_rr (M : ℝ) (x : Fin 4 → ℝ) :
    schwarzschildMetric M x 1 1 = (schwarzschildF M (x 1))⁻¹ := by
  simp [schwarzschildMetric, schwarzschildF]

/-- `f ≠ 0` forces `r ≠ 2M`, the chart in which the `rr` component is regular. -/
theorem sub_ne_zero_of_ne (M r : ℝ) (hr : r ≠ 0) (hf : schwarzschildF M r ≠ 0) :
    r - 2 * M ≠ 0 := by
  intro h
  apply hf
  unfold schwarzschildF
  have h1 : 2 * M / r = 1 := by
    field_simp
    linarith
  rw [h1]
  ring

/-- Derivative of the `tt` component from the metric: `∂_r g_tt = −2M/r²`.
The `t` dependence drops out, so the same derivative works at every `x`. -/
theorem hasDerivAt_gtt (M r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => 1 - 2 * M / s) (2 * M / r ^ 2) r := by
  have h := HasDerivAt.sub (hasDerivAt_const r (1 : ℝ))
    ((hasDerivAt_inv hr).const_mul (2 * M))
  have hfun : (fun s : ℝ => 1 - 2 * M / s)
      = (fun _ : ℝ => 1) - fun s : ℝ => 2 * M * s⁻¹ := by
    funext s
    simp [div_eq_mul_inv]
  have hval : (0 : ℝ) - 2 * M * -(r ^ 2)⁻¹ = 2 * M / r ^ 2 := by
    rw [div_eq_mul_inv]
    ring
  rw [← hfun, hval] at h
  exact h

/-- **The radial Christoffel symbol from the metric.**
`Γ^t_{tr} = ½ g^{tt} ∂_r g_tt` with `g^{tt} = −f⁻¹` and `∂_r g_tt = −2M/r²`
is `M/(r²f)`. -/
theorem gammaTtr_from_metric (M r : ℝ) (hf : schwarzschildF M r ≠ 0) :
    (1 / 2 : ℝ) * (-(schwarzschildF M r)⁻¹) * (-(2 * M / r ^ 2))
      = M / (r ^ 2 * schwarzschildF M r) := by
  have hf' : (1 - 2 * M / r) ≠ 0 := by simpa [schwarzschildF] using hf
  unfold schwarzschildF
  field_simp

/-- Derivative of the `rr` component: as a function of `r` it is `f⁻¹`, which is
`r/(r − 2M)` away from `r = 2M`, so `∂_r g_rr = −2M/(r − 2M)²`. -/
theorem deriv_grr (M r : ℝ) (hr : r ≠ 0) (hf : schwarzschildF M r ≠ 0) :
    deriv ((fun s : ℝ => 1 - 2 * M / s)⁻¹) r = -(2 * M) / (r - 2 * M) ^ 2 := by
  have hf' : (1 - 2 * M / r) ≠ 0 := by simpa [schwarzschildF] using hf
  have h2 := sub_ne_zero_of_ne M r hr hf
  have h := HasDerivAt.inv (hasDerivAt_gtt M r hr) hf'
  rw [h.deriv]
  field_simp

/-- **The `rr` Christoffel symbol from the metric.**
`Γ^r_{rr} = ½ g^{rr} ∂_r g_rr` with `g^{rr} = f` is `−M/(r(r−2M))`. -/
theorem gammaRrr_from_metric (M r : ℝ) (hr : r ≠ 0) (hf : schwarzschildF M r ≠ 0) :
    (1 / 2 : ℝ) * (schwarzschildF M r) * (-(2 * M) / (r - 2 * M) ^ 2)
      = -M / (r * (r - 2 * M)) := by
  have hf' : (1 - 2 * M / r) ≠ 0 := by simpa [schwarzschildF] using hf
  have h2 := sub_ne_zero_of_ne M r hr hf
  unfold schwarzschildF
  field_simp

/-- Derivative of the radial Christoffel symbol, over `r(r − 2M)`:
`∂_r Γ^t_{tr} = −2M(r−M)/(r(r−2M))²`. -/
theorem deriv_gammaTtr (M r : ℝ) (hr : r ≠ 0) (hf : schwarzschildF M r ≠ 0) :
    deriv (fun s : ℝ => M / (s ^ 2 * schwarzschildF M s)) r
      = -2 * M * (r - M) / (r * (r - 2 * M)) ^ 2 := by
  have hf' : (1 - 2 * M / r) ≠ 0 := by simpa [schwarzschildF] using hf
  have h2 := sub_ne_zero_of_ne M r hr hf
  have hden : HasDerivAt (fun s : ℝ => s ^ 2 * (1 - 2 * M / s)) (2 * r - 2 * M) r := by
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
      simpa using hasDerivAt_pow 2 r
    have h2' : HasDerivAt (fun s : ℝ => 1 - 2 * M / s) (2 * M / r ^ 2) r :=
      hasDerivAt_gtt M r hr
    have hm := h1.mul h2'
    have hval : 2 * r * (1 - 2 * M / r) + r ^ 2 * (2 * M / r ^ 2) = 2 * r - 2 * M := by
      field_simp
      ring
    rw [hval] at hm
    exact hm
  have hdenne : r ^ 2 * (1 - 2 * M / r) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hr) hf'
  have h := HasDerivAt.div (hasDerivAt_const r M) hden hdenne
  have hfun : (fun s : ℝ => M / (s ^ 2 * schwarzschildF M s))
      = (fun _ : ℝ => M) / fun s : ℝ => s ^ 2 * (1 - 2 * M / s) := by
    funext s
    simp [schwarzschildF]
  rw [hfun, h.deriv]
  field_simp
  ring

/-- **The `t r t r` Riemann component, from the metric.**  For this static
diagonal metric only `−∂_r Γ^t_{tr} + Γ^t_{tr} Γ^r_{rr} − (Γ^t_{tr})²` survives
in `R^t{}_{rtr}`, and it is `2M/(r³f)`. -/
theorem riemann_t_rtr_from_metric (M r : ℝ) (hr : r ≠ 0) (hf : schwarzschildF M r ≠ 0) :
    -(deriv (fun s : ℝ => M / (s ^ 2 * schwarzschildF M s)) r)
      + (M / (r ^ 2 * schwarzschildF M r)) * (-M / (r * (r - 2 * M)))
      - (M / (r ^ 2 * schwarzschildF M r)) ^ 2
      = 2 * M / (r ^ 3 * schwarzschildF M r) := by
  have h2 := sub_ne_zero_of_ne M r hr hf
  rw [deriv_gammaTtr M r hr hf]
  unfold schwarzschildF
  field_simp [inv_eq_one_div]
  ring

/-- Lowering the `t r t r` component with `g_tt = −f` gives `−2M/r³`, the radial
entry of `electricPart (M/r³)`. -/
theorem electric_r_from_metric (M r : ℝ) (hr : r ≠ 0) (hf : schwarzschildF M r ≠ 0) :
    -(schwarzschildF M r) * (2 * M / (r ^ 3 * schwarzschildF M r))
      = electricPart (M / r ^ 3) 1 1 := by
  have h2 := sub_ne_zero_of_ne M r hr hf
  have hf' : (1 - 2 * M / r) ≠ 0 := by simpa [schwarzschildF] using hf
  have h11 : electricPart (M / r ^ 3) 1 1 = -(2 * M / r ^ 3) := by
    simp [electricPart]
    ring_nf
  rw [h11]
  unfold schwarzschildF
  field_simp

/-- **The angular Christoffel symbol from the metric.**  With
`Γ^r_{θθ} = ½ g^{rr} (−∂_r g_θθ)` and `∂_r g_θθ = 2r`, this is `−rf`. -/
theorem gammaRthth_from_metric (M r : ℝ) (hr : r ≠ 0) :
    (1 / 2 : ℝ) * (schwarzschildF M r) * (-(2 * r)) = -(r * schwarzschildF M r) := by
  unfold schwarzschildF
  field_simp

/-- **The `t θ t θ` Riemann component, from the metric**: only
`Γ^t_{tr} Γ^r_{θθ}` survives, giving `−M/r`. -/
theorem riemann_t_thetatheta_from_metric (M r : ℝ) (hr : r ≠ 0)
    (hf : schwarzschildF M r ≠ 0) :
    (M / (r ^ 2 * schwarzschildF M r)) * (-(r * schwarzschildF M r)) = -M / r := by
  have h2 := sub_ne_zero_of_ne M r hr hf
  have h2x : r - M * 2 ≠ 0 := by
    intro h
    exact h2 (by linarith)
  have hf' : (1 - 2 * M / r) ≠ 0 := by simpa [schwarzschildF] using hf
  unfold schwarzschildF
  field_simp

/-- In the orthonormal frame `(f^{-1/2}∂_t, f^{1/2}∂_r, r^{-1}∂_θ, …)` the
angular eigenvalue is `M/r³`, the `(2,2)` entry of `electricPart (M/r³)`. -/
theorem electric_thetatheta_from_metric (M r : ℝ) (hr : r ≠ 0)
    (hf : schwarzschildF M r ≠ 0) :
    (schwarzschildF M r)⁻¹ * (r ^ 2)⁻¹ * (-(schwarzschildF M r) * (-M / r))
      = electricPart (M / r ^ 3) 2 2 := by
  have h2 := sub_ne_zero_of_ne M r hr hf
  have hf' : (1 - 2 * M / r) ≠ 0 := by simpa [schwarzschildF] using hf
  have h22 : electricPart (M / r ^ 3) 2 2 = M / r ^ 3 := by
    simp [electricPart]
  rw [h22]
  unfold schwarzschildF
  field_simp


/-! ### The remaining Riemann components

The electric part fixes `R^t{}_{rtr}` and `R^t{}_{θtθ}`; the other components of
the Schwarzschild curvature follow from the same Christoffel symbols:
`R^t{}_{φtφ} = −(M/r)sin²θ`, `R^r{}_{θrθ} = −M/r`, `R^r{}_{φrφ} = −(M/r)sin²θ`
and `R^θ{}_{φθφ} = (2M/r)sin²θ`.  Their orthonormal-frame values are the
`electricPart` eigenvalues `−2k, k, k`, so the whole static Weyl tensor is now
derived from `g` rather than supplied.

The two angular Christoffel symbols come from differentiating the `φφ`
component with respect to `θ`, which is where `sin` and `cos` enter.  Each
component is assembled from small product identities rather than one large
rational identity, so every step is a one-line algebraic check.
-/

/-- `∂_θ sin²θ = 2 sinθ cosθ`. -/
theorem hasDerivAt_sinSq (th : ℝ) :
    HasDerivAt (fun s : ℝ => Real.sin s ^ 2) (2 * Real.sin th * Real.cos th) th := by
  have h := (Real.hasDerivAt_sin th).mul (Real.hasDerivAt_sin th)
  have hfun : (fun s : ℝ => Real.sin s ^ 2)
      = (fun s : ℝ => Real.sin s) * fun s : ℝ => Real.sin s := by
    funext s
    simp only [Pi.mul_apply]
    ring
  have hval : Real.cos th * Real.sin th + Real.sin th * Real.cos th
      = 2 * Real.sin th * Real.cos th := by
    ring
  rw [← hfun, hval] at h
  exact h

/-- **The `φφ` Christoffel symbol from the metric.**
`Γ^r_{φφ} = ½ g^{rr} (−∂_r g_φφ) = −r f sin²θ`. -/
theorem gammaRphiphi_from_metric (M r th : ℝ) (hr : r ≠ 0) :
    (1 / 2 : ℝ) * (schwarzschildF M r) * (-(2 * r * Real.sin th ^ 2))
      = -(r * Real.sin th ^ 2 * schwarzschildF M r) := by
  unfold schwarzschildF
  field_simp

/-- **The `t φ t φ` component**: only `Γ^t_{tr} Γ^r_{φφ}` survives, giving
`−(M/r) sin²θ`. -/
theorem riemann_t_phitphi_from_metric (M r th : ℝ) (hr : r ≠ 0)
    (hf : schwarzschildF M r ≠ 0) :
    (M / (r ^ 2 * schwarzschildF M r))
        * (-(r * Real.sin th ^ 2 * schwarzschildF M r))
      = -(M / r) * Real.sin th ^ 2 := by
  have h2x : r - M * 2 ≠ 0 := by
    intro h
    exact sub_ne_zero_of_ne M r hr hf (by linarith)
  have hf' : (1 - 2 * M / r) ≠ 0 := by simpa [schwarzschildF] using hf
  unfold schwarzschildF
  field_simp

/-- **`Γ^r_{rr} Γ^r_{θθ} = M/r`**, the second term of the `r θ r θ` component. -/
theorem gammaRrr_mul_gammaRthth (M r : ℝ) (hr : r ≠ 0)
    (hf : schwarzschildF M r ≠ 0) :
    (-M / (r ^ 2 * schwarzschildF M r)) * (-(r * schwarzschildF M r))
      = M / r := by
  have hf' : (1 - 2 * M / r) ≠ 0 := by simpa [schwarzschildF] using hf
  have hden : r ^ 2 * schwarzschildF M r ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hr) hf
  refine mul_right_cancel₀ hden ?_
  unfold schwarzschildF
  field_simp

/-- **`Γ^r_{θθ} Γ^θ_{rθ} = −f`**, the third term of the `r θ r θ` component. -/
theorem gammaRthth_mul_gammaThetar (M r : ℝ) (hr : r ≠ 0) :
    (-(r * schwarzschildF M r)) * (1 / r) = -schwarzschildF M r := by
  unfold schwarzschildF
  field_simp

/-- **The `r θ r θ` component**: `∂_r Γ^r_{θθ} + Γ^r_{rr} Γ^r_{θθ}
− Γ^r_{θθ} Γ^θ_{rθ}` with `Γ^r_{θθ} = −rf` is `−M/r`. -/
theorem riemann_r_thetar_from_metric (M r : ℝ) (hr : r ≠ 0)
    (hf : schwarzschildF M r ≠ 0) :
    (-(schwarzschildF M r) - 2 * M / r)
      + (-M / (r ^ 2 * schwarzschildF M r)) * (-(r * schwarzschildF M r))
      - (-(r * schwarzschildF M r)) * (1 / r)
      = -M / r := by
  rw [gammaRrr_mul_gammaRthth M r hr hf, gammaRthth_mul_gammaThetar M r hr]
  field_simp
  ring

/-- **`Γ^r_{rr} Γ^r_{φφ} = (M/r) sin²θ`**, the second term of `r φ r φ`. -/
theorem gammaRrr_mul_gammaRphiphi (M r th : ℝ) (hr : r ≠ 0)
    (hf : schwarzschildF M r ≠ 0) :
    (-M / (r ^ 2 * schwarzschildF M r))
        * (-(r * Real.sin th ^ 2 * schwarzschildF M r))
      = (M / r) * Real.sin th ^ 2 := by
  have hf' : (1 - 2 * M / r) ≠ 0 := by simpa [schwarzschildF] using hf
  have hden : r ^ 2 * schwarzschildF M r ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hr) hf
  refine mul_right_cancel₀ hden ?_
  unfold schwarzschildF
  field_simp

/-- **`Γ^r_{φφ} Γ^φ_{rφ} = −f sin²θ`**, the third term of `r φ r φ`. -/
theorem gammaRphiphi_mul_gammaPhirphi (M r th : ℝ) (hr : r ≠ 0) :
    (-(r * Real.sin th ^ 2 * schwarzschildF M r)) * (1 / r)
      = -Real.sin th ^ 2 * schwarzschildF M r := by
  unfold schwarzschildF
  field_simp

/-- **The `r φ r φ` component**: the same combination with `Γ^r_{φφ} = −rf sin²θ`
gives `−(M/r) sin²θ`. -/
theorem riemann_r_phirphi_from_metric (M r th : ℝ) (hr : r ≠ 0)
    (hf : schwarzschildF M r ≠ 0) :
    (-(Real.sin th ^ 2) * (schwarzschildF M r + 2 * M / r))
      + (-M / (r ^ 2 * schwarzschildF M r))
          * (-(r * Real.sin th ^ 2 * schwarzschildF M r))
      - (-(r * Real.sin th ^ 2 * schwarzschildF M r)) * (1 / r)
      = -(M / r) * Real.sin th ^ 2 := by
  rw [gammaRrr_mul_gammaRphiphi M r th hr hf, gammaRphiphi_mul_gammaPhirphi M r th hr]
  field_simp
  ring

/-- **The `θφ` Christoffel symbol from the metric.**
`Γ^θ_{φφ} = ½ g^{θθ} (−∂_θ g_φφ) = −sinθ cosθ`. -/
theorem gammaThetaphiphi_from_metric (r th : ℝ) (hr : r ≠ 0) :
    (1 / 2 : ℝ) * (r ^ 2)⁻¹
        * (-(2 * r ^ 2 * Real.sin th * Real.cos th))
      = -(Real.sin th * Real.cos th) := by
  field_simp

/-- **The `φθ` Christoffel symbol from the metric.**
`Γ^φ_{θφ} = ½ g^{φφ} ∂_θ g_φφ = cosθ / sinθ`. -/
theorem gammaPhiphitheta_from_metric (r th : ℝ) (hr : r ≠ 0)
    (hsin : Real.sin th ≠ 0) :
    (1 / 2 : ℝ) * (r ^ 2 * Real.sin th ^ 2)⁻¹
        * (2 * r ^ 2 * Real.sin th * Real.cos th)
      = Real.cos th / Real.sin th := by
  field_simp

/-- **The `θ φ θ φ` component**: `∂_θ Γ^θ_{φφ} + Γ^θ_{θr} Γ^r_{φφ}
− Γ^θ_{φφ} Γ^φ_{θφ} = (2M/r) sin²θ`. -/
theorem riemann_theta_phitheta_from_metric (M r th : ℝ) (hr : r ≠ 0)
    (hsin : Real.sin th ≠ 0) :
    (Real.sin th ^ 2 - Real.cos th ^ 2)
      + (1 / r) * (-(r * Real.sin th ^ 2 * schwarzschildF M r))
      - (-(Real.sin th * Real.cos th)) * (Real.cos th / Real.sin th)
      = (2 * M / r) * Real.sin th ^ 2 := by
  unfold schwarzschildF
  field_simp
  ring

/-- Lowing `R^t{}_{φtφ}` with `g_tt = −f`: `R_{tφtφ} = (Mf/r) sin²θ`. -/
theorem rt_phitphi_lowered (M r th : ℝ) :
    -(schwarzschildF M r) * (-(M / r) * Real.sin th ^ 2)
      = (M * schwarzschildF M r / r) * Real.sin th ^ 2 := by
  unfold schwarzschildF
  field_simp

/-- The frame factor cancels the metric factors: `f⁻¹ (r sinθ)⁻² (Mf/r) sin²θ =
M/r³`. -/
theorem frame_phiphi (M r th : ℝ) (hr : r ≠ 0) (hf : schwarzschildF M r ≠ 0)
    (hsin : Real.sin th ≠ 0) :
    (schwarzschildF M r)⁻¹ * (r ^ 2 * Real.sin th ^ 2)⁻¹
        * ((M * schwarzschildF M r / r) * Real.sin th ^ 2)
      = M / r ^ 3 := by
  have h1 : (schwarzschildF M r)⁻¹ * schwarzschildF M r = 1 :=
    inv_mul_cancel₀ hf
  have h2 : (r ^ 2 * Real.sin th ^ 2)⁻¹ * Real.sin th ^ 2 = 1 / r ^ 2 := by
    field_simp
  calc (schwarzschildF M r)⁻¹ * (r ^ 2 * Real.sin th ^ 2)⁻¹
        * ((M * schwarzschildF M r / r) * Real.sin th ^ 2)
      = ((schwarzschildF M r)⁻¹ * schwarzschildF M r)
          * ((r ^ 2 * Real.sin th ^ 2)⁻¹ * Real.sin th ^ 2) * (M / r) := by
        ring
    _ = 1 * (1 / r ^ 2) * (M / r) := by rw [h1, h2]
    _ = M / r ^ 3 := by
        field_simp

/-- **The `φφ` electric eigenvalue from the metric**: `M/r³`, the `(3,3)` entry
of `electricPart (M/r³)`. -/
theorem electric_phiphi_from_metric (M r th : ℝ) (hr : r ≠ 0)
    (hf : schwarzschildF M r ≠ 0) (hsin : Real.sin th ≠ 0) :
    (schwarzschildF M r)⁻¹ * (r ^ 2 * Real.sin th ^ 2)⁻¹
        * (M * schwarzschildF M r / r * Real.sin th ^ 2)
      = electricPart (M / r ^ 3) 3 3 := by
  have h33 : electricPart (M / r ^ 3) 3 3 = M / r ^ 3 := by
    simp [electricPart]
  rw [h33]
  exact frame_phiphi M r th hr hf hsin

/-- **The Schwarzschild curvature from the metric.**  The two electric
components and the four remaining independent ones, all read off `g`. -/
theorem riemann_components_from_metric (M r th : ℝ) (hr : r ≠ 0)
    (hf : schwarzschildF M r ≠ 0) (hsin : Real.sin th ≠ 0) :
    ((M / (r ^ 2 * schwarzschildF M r))
          * (-(r * Real.sin th ^ 2 * schwarzschildF M r))
        = -(M / r) * Real.sin th ^ 2)
      ∧ ((-(schwarzschildF M r) - 2 * M / r)
          + (-M / (r ^ 2 * schwarzschildF M r))
              * (-(r * schwarzschildF M r))
          - (-(r * schwarzschildF M r)) * (1 / r) = -M / r)
      ∧ ((-(Real.sin th ^ 2) * (schwarzschildF M r + 2 * M / r))
          + (-M / (r ^ 2 * schwarzschildF M r))
              * (-(r * Real.sin th ^ 2 * schwarzschildF M r))
          - (-(r * Real.sin th ^ 2 * schwarzschildF M r)) * (1 / r)
        = -(M / r) * Real.sin th ^ 2)
      ∧ ((Real.sin th ^ 2 - Real.cos th ^ 2)
          + (1 / r) * (-(r * Real.sin th ^ 2 * schwarzschildF M r))
          - (-(Real.sin th * Real.cos th)) * (Real.cos th / Real.sin th)
        = (2 * M / r) * Real.sin th ^ 2) :=
  ⟨riemann_t_phitphi_from_metric M r th hr hf,
   riemann_r_thetar_from_metric M r hr hf,
   riemann_r_phirphi_from_metric M r th hr hf,
   riemann_theta_phitheta_from_metric M r th hr hsin⟩


end Schwarzschild

end Gravitation
