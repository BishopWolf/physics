import Mathlib.Analysis.ODE.ExistUnique

/-!
# The geodesic Cauchy problem

Given Christoffel symbols on a chart, the geodesic equation

`γ'' = -Γ(γ)(γ', γ')`

is a second-order ODE.  Writing `z = (γ, γ')` turns it into the first-order
system

`z' = (z.2, -Γ z.1 z.2 z.2)`,

to which Mathlib's Picard–Lindelöf theorem applies.

Proved here:

* `geodesic_ivp_exists` — every initial position and velocity is the initial
  data of a solution on some open interval around `0`, for `C¹` Christoffel
  symbols;
* `geodesic_ivp_exists_curve` — the same statement with the solution split into
  a curve and its velocity;
* `geodesic_ivp_unique` — two solutions that agree at one time and stay in a
  ball where the field is Lipschitz coincide;
* `geodesicField_zero`, `flat_geodesic` — in flat space the solutions are the
  straight lines `t ↦ x₀ + t • v₀`.

The existence statement is local in time and inside the chart, because the
field is only `C¹` at a point.  Nothing here is assumed: `Picard–Lindelöf` is
proved in Mathlib, and no axiom is added by this file.
-/

open Set Metric

namespace Gravitation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Christoffel symbols on a chart, as a field of bilinear maps. -/
abbrev Christoffel (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E → E →L[ℝ] E →L[ℝ] E

/-- Geodesic acceleration `-Γ(x)(v, v)`. -/
def geodesicAccel (Γ : Christoffel E) (x v : E) : E := - Γ x v v

/-- The first-order form of the geodesic equation, with state `(position, velocity)`. -/
def geodesicField (Γ : Christoffel E) : E × E → E × E :=
  fun z => (z.2, geodesicAccel Γ z.1 z.2)

@[simp] theorem geodesicField_apply (Γ : Christoffel E) (x v : E) :
    geodesicField Γ (x, v) = (v, geodesicAccel Γ x v) := rfl

/-- The geodesic field inherits `C¹` regularity from the Christoffel symbols. -/
theorem contDiffAt_geodesicField (Γ : E → E →L[ℝ] E →L[ℝ] E) {x₀ v₀ : E}
    (hΓ : ContDiffAt ℝ 1 Γ x₀) :
    ContDiffAt ℝ 1 (geodesicField Γ) (x₀, v₀) := by
  unfold geodesicField geodesicAccel
  fun_prop

/-- Projections of a differentiable curve into a product are differentiable. -/
theorem hasDerivAt_fst {f : ℝ → E × E} {f' : E × E} {t : ℝ}
    (h : HasDerivAt f f' t) : HasDerivAt (fun s => (f s).1) f'.1 t := by
  simpa [Function.comp_def] using
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t h

/-- Second projection of a differentiable curve into a product. -/
theorem hasDerivAt_snd {f : ℝ → E × E} {f' : E × E} {t : ℝ}
    (h : HasDerivAt f f' t) : HasDerivAt (fun s => (f s).2) f'.2 t := by
  simpa [Function.comp_def] using
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t h

/-- **Local existence for the geodesic Cauchy problem.**  Given `C¹` Christoffel
symbols, every pair of initial position and velocity is the initial data of a
geodesic defined on an open interval around `0`. -/
theorem geodesic_ivp_exists [CompleteSpace E] (Γ : Christoffel E) (hΓ : ContDiff ℝ 1 Γ)
    (x₀ v₀ : E) :
    ∃ ε > 0, ∃ z : ℝ → E × E, z 0 = (x₀, v₀) ∧
      ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (fun s => (z s).1) (z t).2 t ∧
        HasDerivAt (fun s => (z s).2) (geodesicAccel Γ (z t).1 (z t).2) t := by
  have hf : ContDiffAt ℝ 1 (geodesicField Γ) (x₀, v₀) :=
    contDiffAt_geodesicField Γ hΓ.contDiffAt
  obtain ⟨r, hr, ε, hε, H⟩ :=
    hf.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt 0
  obtain ⟨z, hz0, hz⟩ := H (x₀, v₀) (mem_closedBall_self (le_of_lt hr))
  refine ⟨ε, hε, z, hz0, fun t ht => ?_⟩
  have h := hz t (by simpa using ht)
  exact ⟨hasDerivAt_fst h, hasDerivAt_snd h⟩

/-- The same existence result split into a curve and its velocity. -/
theorem geodesic_ivp_exists_curve [CompleteSpace E] (Γ : Christoffel E) (hΓ : ContDiff ℝ 1 Γ)
    (x₀ v₀ : E) :
    ∃ ε > 0, ∃ γ w : ℝ → E, γ 0 = x₀ ∧ w 0 = v₀ ∧
      ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt γ (w t) t ∧
        HasDerivAt w (geodesicAccel Γ (γ t) (w t)) t := by
  obtain ⟨ε, hε, z, hz0, hz⟩ := geodesic_ivp_exists Γ hΓ x₀ v₀
  refine ⟨ε, hε, fun t => (z t).1, fun t => (z t).2, ?_, ?_, fun t ht => hz t ht⟩
  · simpa using congrArg Prod.fst hz0
  · simpa using congrArg Prod.snd hz0

/-- **Uniqueness for the geodesic Cauchy problem.**  Two solutions of the same
geodesic system that agree at one time, and stay in a ball on which the field is
`K`-Lipschitz, agree on the whole interval. -/
theorem geodesic_ivp_unique (Γ : Christoffel E) {K : NNReal} {a b t₀ : ℝ}
    {c : E × E} {R : ℝ}
    (hLip : ∀ t ∈ Ioo a b, LipschitzOnWith K (geodesicField Γ) (closedBall c R))
    (ht : t₀ ∈ Ioo a b) {z₁ z₂ : ℝ → E × E}
    (h₁ : ContinuousOn z₁ (Icc a b))
    (h₁' : ∀ t ∈ Ioo a b, HasDerivAt z₁ (geodesicField Γ (z₁ t)) t)
    (h₁s : ∀ t ∈ Ioo a b, z₁ t ∈ closedBall c R)
    (h₂ : ContinuousOn z₂ (Icc a b))
    (h₂' : ∀ t ∈ Ioo a b, HasDerivAt z₂ (geodesicField Γ (z₂ t)) t)
    (h₂s : ∀ t ∈ Ioo a b, z₂ t ∈ closedBall c R)
    (h₀ : z₁ t₀ = z₂ t₀) : EqOn z₁ z₂ (Icc a b) :=
  ODE_solution_unique_of_mem_Icc (v := fun _ => geodesicField Γ)
    (s := fun _ => closedBall c R) hLip ht h₁ h₁' h₁s h₂ h₂' h₂s h₀

/-! ### Flat space: geodesics are straight lines -/

theorem geodesicField_zero (x v : E) :
    geodesicField (fun _ : E => 0) (x, v) = (v, 0) := by
  simp [geodesicField, geodesicAccel]

/-- In flat space `t ↦ x₀ + t • v₀` has constant velocity, so it solves the
geodesic equation `γ'' = 0`. -/
theorem flat_geodesic (x₀ v₀ : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x₀ + s • v₀) v₀ t ∧
      HasDerivAt (fun _ : ℝ => v₀) 0 t := by
  refine ⟨?_, hasDerivAt_const t v₀⟩
  have hid : HasDerivAt (fun s : ℝ => s) (1 : ℝ) t := hasDerivAt_id t
  simpa using (hid.smul_const v₀).const_add x₀

end Gravitation
