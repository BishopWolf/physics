import Gravitation.Einstein
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.Basic

/-!
# Scalar–tensor and higher-order gravity

Three families that dominate the space of viable alternatives to general
relativity, each reduced to the structure that can actually be proved:

* **Brans–Dicke**: the PPN parameter `γ` and the effective coupling as functions
  of `ω`, their bounds, the `ω = 0` limit that reproduces `f(R)`, and the
  `ω = -3/2` pole where the scalar's kinetic term degenerates.
* **f(R)**: the linear case `R - 2Λ` is exactly general relativity with a
  cosmological constant; Starobinsky's `R + αR²` has the Legendre potential
  `(φ-1)²/(8α)`, a scalar mass `1/(6α)`, and is *not* GR because `f'` is not
  constant.
* **Horndeski / Galileon**: the one-dimensional shadow of the second-order
  property — the cubic Galileon `(φ')²φ''` is a total derivative, a constant
  shift changes it by a total derivative, and an exactly shift-symmetric
  potential must be constant.

What is **not** formalised here: the variational calculus behind Horndeski's
theorem (that the `G₂…G₅` Lagrangian gives second-order field equations), the
Ostrogradsky instability of generic higher-derivative theories, and the
four-dimensional Galileon total-derivative identities.  The four-dimensional
field equations are also not derived: the modules work at the level of the
algebraic statements that make each theory's phenomenology calculable.
-/

namespace Gravitation

/-! ## Brans–Dicke theory -/

namespace BransDicke

/-- The Brans–Dicke PPN parameter `γ = (1 + ω)/(2 + ω)`. -/
noncomputable def gamma (ω : ℝ) : ℝ := (1 + ω) / (2 + ω)

/-- `γ = 1 − 1/(2+ω)`: the deviation from GR is the reciprocal of the coupling. -/
theorem gamma_eq_one_sub (ω : ℝ) (h : 2 + ω ≠ 0) : gamma ω = 1 - 1 / (2 + ω) := by
  simp only [gamma]
  field_simp
  ring

/-- **Brans–Dicke always deviates from GR, but never by as much as `f(R)`.**
For every `ω > 0`, `1/2 < γ < 1`. -/
theorem gamma_bounds (ω : ℝ) (hω : 0 < ω) : 1 / 2 < gamma ω ∧ gamma ω < 1 := by
  have h2 : (2 : ℝ) < 2 + ω := by linarith
  have hinv_lt : 1 / (2 + ω) < 1 / 2 :=
    one_div_lt_one_div_of_lt (by norm_num) h2
  have hinv_pos : (0 : ℝ) < 1 / (2 + ω) := by positivity
  rw [gamma_eq_one_sub ω (by linarith)]
  constructor <;> linarith

/-- **Cassini.**  `ω > 40000` forces `|1 − γ| < 1/40000 ≈ 2.5 × 10⁻⁵`, the
solar-system bound on the Brans–Dicke coupling. -/
theorem cassini_deviation (ω : ℝ) (h : 40000 < ω) : 1 - gamma ω < 1 / 40000 := by
  rw [gamma_eq_one_sub ω (by linarith)]
  have h2 : (40000 : ℝ) < 2 + ω := by linarith
  have hinv : 1 / (2 + ω) < 1 / 40000 :=
    one_div_lt_one_div_of_lt (by norm_num) h2
  linarith

/-- **The general-relativity limit.**  As `ω → ∞` the PPN parameter tends to
`1`, so Brans–Dicke becomes indistinguishable from GR. -/
theorem gamma_tendsto_atTop :
    Filter.Tendsto (fun ω : ℝ => gamma ω) Filter.atTop (nhds 1) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    rw [Filter.eventually_atTop]
    refine ⟨1 / (1 - a) - 1, fun ω hω => ?_⟩
    have ha1 : 0 < 1 - a := by linarith
    have hpos : 0 < 1 / (1 - a) := one_div_pos.mpr ha1
    have hden : 0 < 2 + ω := by linarith
    have hlt : 1 / (1 - a) < 2 + ω := by linarith
    have hone : 1 < (1 - a) * (2 + ω) := by
      have hm := mul_lt_mul_of_pos_left hlt ha1
      have h1 : (1 - a) * (1 / (1 - a)) = 1 := by field_simp
      rwa [h1] at hm
    have hinv : 1 / (2 + ω) < 1 - a := by
      rw [div_lt_iff₀ hden]
      exact hone
    rw [gamma_eq_one_sub ω (by linarith)]
    linarith
  · intro b hb
    rw [Filter.eventually_atTop]
    refine ⟨1 / (b - 1) - 1, fun ω hω => ?_⟩
    have hb1 : 0 < b - 1 := by linarith
    have hpos : 0 < 1 / (b - 1) := one_div_pos.mpr hb1
    have hden : 0 < 2 + ω := by linarith
    have hlt : 1 / (b - 1) < 2 + ω := by linarith
    have hone : 1 < (b - 1) * (2 + ω) := by
      have hm := mul_lt_mul_of_pos_left hlt hb1
      have h1 : (b - 1) * (1 / (b - 1)) = 1 := by field_simp
      rwa [h1] at hm
    have hinv : 1 / (2 + ω) < b - 1 := by
      rw [div_lt_iff₀ hden]
      exact hone
    have hxpos : 0 < 1 / (2 + ω) := one_div_pos.mpr hden
    rw [gamma_eq_one_sub ω (by linarith)]
    linarith

/-- **`f(R)` gravity is Brans–Dicke with `ω = 0`**, and then `γ = 1/2` — the PPN
value that solar-system tests exclude for pure `f(R)` without screening. -/
theorem fR_gamma : gamma 0 = 1 / 2 := by
  norm_num [gamma]

/-- The Brans–Dicke effective coupling `G_eff ∝ (4 + 2ω)/(3 + 2ω)`. -/
noncomputable def coupling (ω : ℝ) : ℝ := (4 + 2 * ω) / (3 + 2 * ω)

/-- `(4+2ω)/(3+2ω) = 1 + 1/(3+2ω)`. -/
theorem coupling_eq_one_add (ω : ℝ) (h : 3 + 2 * ω ≠ 0) :
    coupling ω = 1 + 1 / (3 + 2 * ω) := by
  simp only [coupling]
  field_simp
  ring

/-- For `ω ≥ 0` the effective coupling lies in `[1, 4/3]`: the scalar can only
*strengthen* gravity, and at most by a factor `4/3` (at `ω = 0`). -/
theorem coupling_bounds (ω : ℝ) (hω : 0 ≤ ω) : 1 ≤ coupling ω ∧ coupling ω ≤ 4 / 3 := by
  have hden : (0 : ℝ) < 3 + 2 * ω := by linarith
  have hinv_le : 1 / (3 + 2 * ω) ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hinv_pos : (0 : ℝ) < 1 / (3 + 2 * ω) := by positivity
  rw [coupling_eq_one_add ω (by linarith)]
  constructor <;> linarith

/-- `ω = -3/2` is a pole of the effective coupling: the scalar's kinetic term
changes sign there, so Brans–Dicke is not a healthy gravity theory at that
point. -/
theorem coupling_pole : 3 + 2 * (-(3 / 2) : ℝ) = 0 := by norm_num

end BransDicke

/-! ## f(R) gravity -/

namespace fR

/-- The algebraic part of the metric-formalism `f(R)` field equations,
`f'(S) Ric_ij − ½ f(S) g_ij`.  The derivative terms `−∇_i∇_j f' + g_ij □f'` are
not represented; the identity below is exact when they vanish, i.e. when `f'` is
constant. -/
noncomputable def fieldEqn (f df : ℝ → ℝ) {n : ℕ} (M : Metric n) (R : Riemann n) :
    Tensor2 n :=
  fun i j => df (scalarCurv M R) * ricci M R i j - (1 / 2) * f (scalarCurv M R) * M.g i j

/-- **`f(R) = R − 2Λ` is exactly general relativity with a cosmological
constant**: with `f' = 1` the field equations reduce to `G + Λg = 0`. -/
theorem linear_is_einstein {n : ℕ} (M : Metric n) (R : Riemann n) (Λ : ℝ) :
    fieldEqn (fun S => S - 2 * Λ) (fun _ => 1) M R
      = fun i j => einstein M R i j + Λ * M.g i j := by
  funext i j
  simp only [fieldEqn, einstein]
  ring

/-! ### Starobinsky's `R + αR²` -/

/-- The Starobinsky potential `V(φ) = (φR(φ) − f(R(φ)))/2` with
`φ = f'(R) = 1 + 2αR` and `f(R) = R + αR²`. -/
noncomputable def V (α φ : ℝ) : ℝ := (φ - 1) ^ 2 / (8 * α)

/-- `φ = 1 + 2αR` inverts to `R = (φ−1)/(2α)`. -/
theorem phi_inverse (α φ : ℝ) (hα : α ≠ 0) :
    1 + 2 * α * ((φ - 1) / (2 * α)) = φ := by
  have h2 : (2 : ℝ) * α ≠ 0 := mul_ne_zero (by norm_num) hα
  field_simp
  ring

/-- **The Starobinsky potential is exactly quadratic**,
`V(φ) = (φ−1)²/(8α)`: the extra scalar is massive, with no higher powers, and
`φ = 1` (equivalently `R = 0`) is its GR minimum. -/
theorem potential_eq (α φ : ℝ) (hα : α ≠ 0) :
    (φ * ((φ - 1) / (2 * α))
        - (((φ - 1) / (2 * α)) + α * ((φ - 1) / (2 * α)) ^ 2)) / 2 = V α φ := by
  have h2 : (2 : ℝ) * α ≠ 0 := mul_ne_zero (by norm_num) hα
  have h8 : (8 : ℝ) * α ≠ 0 := mul_ne_zero (by norm_num) hα
  simp only [V]
  field_simp
  ring

/-- The scalar mass from `f'' = 2α`: `m² = 1/(3f'') = 1/(6α)`. -/
theorem mass_sq (α : ℝ) (hα : α ≠ 0) : 3 * (2 * α) * (1 / (6 * α)) = 1 := by
  have h6 : (6 : ℝ) * α ≠ 0 := mul_ne_zero (by norm_num) hα
  field_simp
  ring

/-- **`R + αR²` is not GR.**  For `α ≠ 0` the derivative `f'` is not constant,
so the trace of the field equations is not algebraic: a scalar degree of freedom
propagates, with the mass above. -/
theorem not_gr (α : ℝ) (hα : α ≠ 0) : ∃ S : ℝ, 1 + 2 * α * S ≠ 1 := by
  refine ⟨1 / (2 * α), ?_⟩
  have h : 2 * α * (1 / (2 * α)) = 1 := by
    have h2 : (2 : ℝ) * α ≠ 0 := mul_ne_zero (by norm_num) hα
    field_simp
  intro heq
  rw [h] at heq
  norm_num at heq

/-! ### The trace equation -/

/-- **The trace of the `f(R)` field equation.**  The metric-formalism equation is
`f'(S) Ric_ij − ½ f(S) g_ij − ∇_i∇_j f' + g_ij □f' = 0`; tracing with `g^{ij}`
gives `f'(S) S − (n/2) f(S) + (n − 1) □f' = 0`, because `g^{ij} g_ij = n` while the
two second-derivative terms contribute `−1 + n`. -/
theorem trace_fieldEqn {n : ℕ} (M : Metric n) (R : Riemann n) (f df : ℝ → ℝ)
    (box : ℝ) (d2 : Tensor2 n) (hbox : metricTrace M d2 = box) :
    metricTrace M (fun i j => df (scalarCurv M R) * ricci M R i j
        - (1 / 2) * f (scalarCurv M R) * M.g i j + (M.g i j * box - d2 i j))
      = df (scalarCurv M R) * scalarCurv M R
        - (1 / 2) * f (scalarCurv M R) * (n : ℝ) + ((n : ℝ) - 1) * box := by
  have hcomm : (fun i j => M.g i j * box) = fun i j => box * M.g i j := by
    funext i j
    ring
  have h1 := metricTrace_add_fun M
    (fun i j => df (scalarCurv M R) * ricci M R i j - (1 / 2) * f (scalarCurv M R) * M.g i j)
    (fun i j => M.g i j * box - d2 i j)
  have h2 := metricTrace_sub_fun M
    (fun i j => df (scalarCurv M R) * ricci M R i j)
    (fun i j => (1 / 2) * f (scalarCurv M R) * M.g i j)
  have h3 := metricTrace_sub_fun M (fun i j => M.g i j * box) d2
  have h4 := metricTrace_smul M (df (scalarCurv M R)) (ricci M R)
  have h5 := metricTrace_mul_g M box
  have h6 := metricTrace_mul_g M ((1 / 2) * f (scalarCurv M R))
  rw [h1, h2, h3, hcomm, h5, h6, h4, ← scalarCurv_eq_metricTrace, hbox]
  ring

/-- **In four dimensions the trace equation is `f'(S) S − 2 f(S) + 3 □f' = 0`.**
The coefficient `3` is `n − 1`, and it is why the scalar mode is massive rather
than an auxiliary field. -/
theorem trace_fieldEqn_four (M : Metric 4) (R : Riemann 4) (f df : ℝ → ℝ)
    (box : ℝ) (d2 : Tensor2 4) (hbox : metricTrace M d2 = box) :
    metricTrace M (fun i j => df (scalarCurv M R) * ricci M R i j
        - (1 / 2) * f (scalarCurv M R) * M.g i j + (M.g i j * box - d2 i j))
      = df (scalarCurv M R) * scalarCurv M R - 2 * f (scalarCurv M R) + 3 * box := by
  rw [trace_fieldEqn M R f df box d2 hbox]
  push_cast
  ring

/-! ### The Einstein frame -/

/-- The Einstein-frame potential of a scalar–tensor theory, `U = V/(2φ²)`. -/
noncomputable def einsteinFrameV (V : ℝ → ℝ) (φ : ℝ) : ℝ := V φ / (2 * φ ^ 2)

/-- **The Starobinsky potential in the Einstein frame.**  The conformal
rescaling `g̃ = φ g` turns `V(φ) = (φ−1)²/(8α)` into
`U(φ) = (φ−1)²/(16αφ²)`. -/
theorem starobinsky_einsteinFrame (α φ : ℝ) (hα : α ≠ 0) (hφ : φ ≠ 0) :
    einsteinFrameV (V α) φ = (φ - 1) ^ 2 / (16 * α * φ ^ 2) := by
  have h8 : (8 : ℝ) * α ≠ 0 := mul_ne_zero (by norm_num) hα
  have h2 : (2 : ℝ) * φ ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hφ)
  simp only [einsteinFrameV, V]
  field_simp; ring

/-- `U(φ) = 1/(16α) · (1 − 1/φ)²`, the form in which the plateau is visible. -/
theorem starobinsky_einsteinFrame_form (α φ : ℝ) (hα : α ≠ 0) (hφ : φ ≠ 0) :
    einsteinFrameV (V α) φ = (1 / (16 * α)) * (1 - 1 / φ) ^ 2 := by
  rw [starobinsky_einsteinFrame α φ hα hφ]
  have h16 : (16 : ℝ) * α * φ ^ 2 ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) hα) (pow_ne_zero 2 hφ)
  field_simp

/-- **The slow-roll plateau.**  As `φ → ∞` the Einstein-frame potential tends to
its asymptote `1/(16α)`; that flat region is what makes Starobinsky inflation
slow roll. -/
theorem starobinsky_plateau (α : ℝ) (hα : α ≠ 0) :
    Filter.Tendsto (fun φ : ℝ => einsteinFrameV (V α) φ) Filter.atTop
      (nhds (1 / (16 * α))) := by
  have hinv : Filter.Tendsto (fun φ : ℝ => 1 / φ) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  have h1 : Filter.Tendsto (fun φ : ℝ => 1 - 1 / φ) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hinv
  have hsq : Filter.Tendsto (fun φ : ℝ => (1 - 1 / φ) ^ 2) Filter.atTop (nhds 1) := by
    simpa using h1.pow 2
  have hmul : Filter.Tendsto (fun φ : ℝ => (1 / (16 * α)) * (1 - 1 / φ) ^ 2)
      Filter.atTop (nhds ((1 / (16 * α)) * 1)) := tendsto_const_nhds.mul hsq
  have heq : (fun φ : ℝ => einsteinFrameV (V α) φ)
      =ᶠ[Filter.atTop] fun φ : ℝ => (1 / (16 * α)) * (1 - 1 / φ) ^ 2 := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun b hb => hb⟩] with φ hφ
    exact starobinsky_einsteinFrame_form α φ hα (by linarith)
  refine Filter.Tendsto.congr' heq.symm ?_
  simpa using hmul

end fR

/-! ## Horndeski and Galileon: the second-order structure -/

namespace Galileon

/-- **The cubic Galileon is a total derivative.**  In one dimension the density
`(φ')²φ''` is the derivative of `(φ')³/3`.  This is the shadow of the
field-theory statement that `□φ (∂φ)²` differs from a total derivative only by
terms proportional to the equations of motion — which is why the Galileon
equations stay second order and carry no Ostrogradsky ghost. -/
theorem cubic_total_derivative (v a : ℝ → ℝ) (t : ℝ) (hv : HasDerivAt v (a t) t) :
    HasDerivAt (fun s => v s ^ 3 / 3) (v t ^ 2 * a t) t := by
  have h := (hv.pow 3).div_const 3
  convert h using 1; ring

/-- **Shift symmetry is an invariance up to a total derivative.**  Shifting the
velocity by a constant changes the cubic Galileon density by the derivative of
`((v+c)³ − v³)/3`, so the action is unchanged for fields vanishing at the
boundary. -/
theorem shift_total_derivative (v a : ℝ → ℝ) (t c : ℝ) (hv : HasDerivAt v (a t) t) :
    HasDerivAt (fun s => (v s + c) ^ 3 / 3) ((v t + c) ^ 2 * a t) t :=
  cubic_total_derivative (fun s => v s + c) a t (hv.add_const c)

/-- **Shift symmetry forbids a potential.**  A potential invariant under
`φ ↦ φ + c` for every constant `c` is constant — the reason the Galileon scalar
is protected from a mass term, exactly as a Goldstone boson is. -/
theorem shift_forbids_potential (V : ℝ → ℝ) (h : ∀ φ c, V (φ + c) = V φ)
    (φ₁ φ₂ : ℝ) : V φ₁ = V φ₂ := by
  have h' := h φ₁ (φ₂ - φ₁)
  have hsub : φ₁ + (φ₂ - φ₁) = φ₂ := by ring
  rw [hsub] at h'
  exact h'.symm

end Galileon

end Gravitation
