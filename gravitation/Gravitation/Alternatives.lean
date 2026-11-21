import Gravitation.Basic
import Gravitation.Einstein
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Alternative gravity: MOND, MOG and TeVeS

Contrasting theories of the galactic-scale anomalies that general relativity
attributes to dark matter.  Each model is stated in the form in which it is
actually used, and its *mathematical* properties are proved: the Newtonian
limit, the deep-MOND/flat-rotation regime, the bounded enhancement of MOG, and
the preservation of Lorentzian signature by the TeVeS physical metric.

Empirical strengths and weaknesses are **not** theorems and are not claimed as
such — they are recorded in `README.md` with references.  What is proved here is
the internal structure that makes those claims testable:

* MOND: `newtonian_limit`, `flat_rotation` (v⁴ = G M a₀ in the deep regime) and
  `newtonian_velocity_ne` (Newtonian orbits with fixed mass cannot be flat).
* MOG: `factor_bounds` — the enhancement factor lies in `[1, 1 + α]`, so the
  model has a hard ceiling on the mass discrepancy it can absorb.
* TeVeS: `metric_lorentzian` — the physical (Jordan) metric stays Lorentzian for
  every scalar field value, so causal structure survives the disformal
  transformation.
-/

namespace Gravitation

/-! ## MOND (Milgrom 1983) -/

namespace MOND

/-- Newtonian acceleration of a point mass. -/
noncomputable def newtonAccel (G M r : ℝ) : ℝ := G * M / r ^ 2

/-- Deep-MOND acceleration: the solution of `μ(a/a₀) · a = g_N` with `μ(x) = x`. -/
noncomputable def deepAccel (a₀ gN : ℝ) : ℝ := Real.sqrt (a₀ * gN)

/-- The MOND relation `μ(a/a₀) · a = g_N` with interpolating function `μ`. -/
def Relation (μ : ℝ → ℝ) (a₀ a gN : ℝ) : Prop := μ (a / a₀) * a = gN

/-- Newtonian limit: where the interpolating function saturates at `1`, MOND is
indistinguishable from Newton. -/
theorem newtonian_limit (μ : ℝ → ℝ) {a₀ a gN : ℝ} (hμ : μ (a / a₀) = 1)
    (h : Relation μ a₀ a gN) : a = gN := by
  simpa [Relation, hμ] using h

/-- Deep-MOND acceleration squared. -/
theorem deep_accel_sq {a₀ gN : ℝ} (h : 0 ≤ a₀ * gN) :
    deepAccel a₀ gN ^ 2 = a₀ * gN := by
  simp [deepAccel, Real.sq_sqrt h]

/-- **Flat rotation curves from MOND.**  With `v² = a r` and the deep-MOND
acceleration, `v⁴ = G M a₀`: the circular speed is independent of the radius. -/
theorem flat_rotation (G M a₀ r : ℝ) (hr : r ≠ 0)
    (h : 0 ≤ a₀ * (G * M / r ^ 2)) :
    (deepAccel a₀ (newtonAccel G M r) * r) ^ 2 = G * M * a₀ := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  simp only [newtonAccel] at h ⊢
  rw [mul_pow, deep_accel_sq h]
  rw [mul_assoc, div_mul_cancel₀ _ hr2]
  ring

/-- **Why MOND is needed.**  In Newtonian gravity with a fixed enclosed mass the
circular speed falls with radius, so the same two radii cannot share a speed. -/
theorem newtonian_velocity_ne (G M r₁ r₂ : ℝ) (hGM : G * M ≠ 0)
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0) (h : r₁ ≠ r₂) :
    (G * M) / r₁ ≠ (G * M) / r₂ := by
  intro heq
  rw [div_eq_div_iff hr₁ hr₂] at heq
  exact h (mul_left_cancel₀ hGM heq).symm

end MOND

/-! ## MOG (Moffat 2006) -/

namespace MOG

/-- MOG enhancement factor `1 + α(1 − e^{−μ r})`. -/
noncomputable def factor (α μ r : ℝ) : ℝ := 1 + α * (1 - Real.exp (-(μ * r)))

/-- The MOG potential `−G M/r · factor`. -/
noncomputable def potential (G M α μ r : ℝ) : ℝ := -((G * M) / r) * factor α μ r

theorem factor_zero (α μ : ℝ) : factor α μ 0 = 1 := by
  simp [factor]

/-- **The structural weakness of MOG.**  For positive `α` and `μ r ≥ 0` the
enhancement lies in `[1, 1 + α]`: the model cannot absorb a mass discrepancy
larger than `1 + α`, and raising `α` to fit one galaxy changes every other fit. -/
theorem factor_bounds (α μ r : ℝ) (hα : 0 < α) (hμr : 0 ≤ μ * r) :
    1 ≤ factor α μ r ∧ factor α μ r < 1 + α := by
  have hpos : 0 < Real.exp (-(μ * r)) := Real.exp_pos _
  have hle : Real.exp (-(μ * r)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  constructor
  · simp only [factor]
    nlinarith
  · simp only [factor]
    nlinarith

end MOG

/-! ## TeVeS (Bekenstein 2004) -/

namespace TeVeS

/-- The TeVeS physical (Jordan) metric in a frame where the unit timelike vector
is `∂_t` and the Einstein metric is `η`:

`g̃ = e^{−2φ}(g + U ⊗ U) − e^{2φ} U ⊗ U = diag(−e^{2φ}, e^{−2φ}, e^{−2φ}, e^{−2φ})`.
-/
noncomputable def metric (φ : ℝ) : Tensor2 4 :=
  !![(-Real.exp (2 * φ)), 0, 0, 0;
     0, Real.exp (-2 * φ), 0, 0;
     0, 0, Real.exp (-2 * φ), 0;
     0, 0, 0, Real.exp (-2 * φ)]

theorem metric_symm (φ : ℝ) : IsSymm (metric φ) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [metric]

/-- **Causal structure survives.**  The TeVeS physical metric is Lorentzian for
every value of the scalar field: one negative and three positive eigenvalues. -/
theorem metric_lorentzian (φ : ℝ) :
    metric φ 0 0 < 0 ∧ 0 < metric φ 1 1 ∧ 0 < metric φ 2 2 ∧
      0 < metric φ 3 3 := by
  have h1 : 0 < Real.exp (2 * φ) := Real.exp_pos _
  have h2 : 0 < Real.exp (-(2 * φ)) := Real.exp_pos _
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [metric] <;> linarith

/-- The spatial part is the conformal rescaling `e^{−2φ} δ`, which is how TeVeS
produces gravitational lensing without dark matter. -/
theorem metric_spatial (φ : ℝ) :
    metric φ 1 1 = Real.exp (-2 * φ) ∧ metric φ 2 2 = Real.exp (-2 * φ) ∧
      metric φ 3 3 = Real.exp (-2 * φ) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [metric]

end TeVeS

end Gravitation
