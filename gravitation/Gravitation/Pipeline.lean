import Gravitation.Curvature
import Gravitation.Examples.Schwarzschild
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.LinearCombination

/-!
# The metric → Christoffel → Riemann pipeline

The hand-derived components in `Examples/Schwarzschild.lean` and
`Examples/SchwarzschildDeSitter.lean` are six separate computations.  This
module replaces the pattern with one construction.  Given a metric as a
function of the coordinates and its inverse in the same way, it *defines*

`g` → `∂ g` → `Γ` → `∂ Γ` → `R^ρ_{σμν}` → `Ric_{σν}` → `S` → `G_{ij}`,

so a component is a value of a formula rather than the conclusion of a
bespoke proof.  The derivative is the coordinate partial derivative: the
derivative of a component along the line through `x` in the direction `μ`, with
the other coordinates held fixed.

What remains to be proved for a particular metric is only that the partial
derivatives evaluate as expected — differentiation of one-variable functions,
not tensor algebra.  Two checks are included: a constant metric gives `Γ = 0`,
`R = 0`, `Ric = 0`, `S = 0`, `G = 0` (so Minkowski is a *computed* vacuum
solution), and the `Γ^t_{tr}` of the Schwarzschild metric computed by the
pipeline is the value `M/(r²f)` derived by hand in `Examples/Schwarzschild.lean`.
-/

namespace Gravitation

namespace Pipeline

/-- The partial derivative of a scalar field along the coordinate `μ`: the
derivative of `s ↦ f (x` with `x μ` replaced by `s)` at `x μ`. -/
noncomputable def pd {n : ℕ} (μ : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  deriv (fun s : ℝ => f (Function.update x μ s)) (x μ)

/-- The derivative of a constant field vanishes. -/
theorem pd_const {n : ℕ} (μ : Fin n) (c : ℝ) (x : Fin n → ℝ) :
    pd μ (fun _ => c) x = 0 := by
  simp [pd]

/-- `pd` only sees the values of the field. -/
theorem pd_congr {n : ℕ} (μ : Fin n) {f g : (Fin n → ℝ) → ℝ} (x : Fin n → ℝ)
    (h : ∀ y, f y = g y) : pd μ f x = pd μ g x := by
  simp only [pd]
  exact congrArg (fun F => deriv F (x μ)) (funext fun s => h _)

/-- Christoffel symbols of the second kind,
`Γ^k_{ij} = ½ g^{kl}(∂_i g_{jl} + ∂_j g_{il} − ∂_l g_{ij})`, at the point `x`. -/
noncomputable def christoffel {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (k i j : Fin n) : ℝ :=
  (1 / 2) * ∑ l, ginv x k l *
    (pd i (fun y => g y j l) x + pd j (fun y => g y i l) x
      - pd l (fun y => g y i j) x)

/-- The Riemann tensor
`R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} − ∂_ν Γ^ρ_{μσ} + Γ^ρ_{μλ}Γ^λ_{νσ} − Γ^ρ_{νλ}Γ^λ_{μσ}`. -/
noncomputable def riemann {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n) : ℝ :=
  pd μ (fun y => christoffel g ginv y ρ ν σ) x
    - pd ν (fun y => christoffel g ginv y ρ μ σ) x
    + ∑ l, (christoffel g ginv x ρ μ l * christoffel g ginv x l ν σ
          - christoffel g ginv x ρ ν l * christoffel g ginv x l μ σ)

/-- The Ricci tensor `Ric_{σν} = Σ_ρ R^ρ_{σρν}`. -/
noncomputable def ricciOf {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (σ ν : Fin n) : ℝ :=
  ∑ ρ, riemann g ginv x ρ σ ρ ν

/-- The scalar curvature `S = g^{σν} Ric_{σν}`. -/
noncomputable def scalarOf {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) : ℝ :=
  ∑ σ, ∑ ν, ginv x σ ν * ricciOf g ginv x σ ν

/-- The Einstein tensor `G_{ij} = Ric_{ij} − ½ S g_{ij}`. -/
noncomputable def einsteinOf {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (i j : Fin n) : ℝ :=
  ricciOf g ginv x i j - (1 / 2) * scalarOf g ginv x * g x i j

/-! ## Constant metrics: flatness is computed, not assumed -/

/-- **A constant metric has no Christoffel symbols.**  Only derivatives of the
metric appear in `Γ`, so the pipeline returns zero at every point. -/
theorem christoffel_const {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (G : Tensor2 n)
    (hg : ∀ x, g x = G) (x : Fin n → ℝ) (k i j : Fin n) :
    christoffel g ginv x k i j = 0 := by
  have hpd : ∀ (μ a b : Fin n), pd μ (fun y => g y a b) x = 0 := by
    intro μ a b
    rw [pd_congr μ x (fun y => by rw [hg y])]
    exact pd_const μ (G a b) x
  simp only [christoffel]
  rw [Finset.sum_eq_zero (fun l _ => by rw [hpd i j l, hpd j i l, hpd l i j]; ring)]
  ring

/-- **A constant metric has no curvature.**  `Γ = 0` at every point, so its
derivatives vanish and every product of Christoffel symbols does too. -/
theorem riemann_const {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (G : Tensor2 n)
    (hg : ∀ x, g x = G) (x : Fin n → ℝ) (ρ σ μ ν : Fin n) :
    riemann g ginv x ρ σ μ ν = 0 := by
  have hc := fun y => christoffel_const g ginv G hg y
  have h1 : pd μ (fun y => christoffel g ginv y ρ ν σ) x = 0 := by
    rw [pd_congr μ x (fun y => hc y ρ ν σ)]
    exact pd_const μ 0 x
  have h2 : pd ν (fun y => christoffel g ginv y ρ μ σ) x = 0 := by
    rw [pd_congr ν x (fun y => hc y ρ μ σ)]
    exact pd_const ν 0 x
  have h3 : (∑ l, (christoffel g ginv x ρ μ l * christoffel g ginv x l ν σ
              - christoffel g ginv x ρ ν l * christoffel g ginv x l μ σ)) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    rw [hc x ρ μ l, hc x ρ ν l, hc x l ν σ, hc x l μ σ]
    ring
  rw [riemann, h1, h2, h3]
  ring

/-- A constant metric is Ricci flat, as computed by the pipeline. -/
theorem ricciOf_const {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (G : Tensor2 n)
    (hg : ∀ x, g x = G) (x : Fin n → ℝ) (σ ν : Fin n) :
    ricciOf g ginv x σ ν = 0 := by
  simp only [ricciOf]
  apply Finset.sum_eq_zero
  intro ρ _
  exact riemann_const g ginv G hg x ρ σ ρ ν

/-- A constant metric has zero scalar curvature. -/
theorem scalarOf_const {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (G : Tensor2 n)
    (hg : ∀ x, g x = G) (x : Fin n → ℝ) : scalarOf g ginv x = 0 := by
  simp only [scalarOf]
  apply Finset.sum_eq_zero
  intro σ _
  apply Finset.sum_eq_zero
  intro ν _
  rw [ricciOf_const g ginv G hg x σ ν]
  ring

/-- **A constant metric is a vacuum solution, as computed**: `G_{ij} = 0`. -/
theorem einsteinOf_const {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (G : Tensor2 n)
    (hg : ∀ x, g x = G) (x : Fin n → ℝ) (i j : Fin n) :
    einsteinOf g ginv x i j = 0 := by
  simp only [einsteinOf]
  rw [ricciOf_const g ginv G hg x i j, scalarOf_const g ginv G hg x]
  ring

/-! ## Minkowski as a computed vacuum solution -/

/-- The Minkowski metric as a field of components. -/
noncomputable def minkowskiG : (Fin 4 → ℝ) → Tensor2 4 := fun _ => eta4

/-- The pipeline gives no Christoffel symbols for Minkowski spacetime. -/
theorem minkowski_christoffel (x : Fin 4 → ℝ) (k i j : Fin 4) :
    christoffel minkowskiG minkowskiG x k i j = 0 :=
  christoffel_const minkowskiG minkowskiG eta4 (fun _ => rfl) x k i j

/-- The pipeline gives no curvature for Minkowski spacetime. -/
theorem minkowski_riemann (x : Fin 4 → ℝ) (ρ σ μ ν : Fin 4) :
    riemann minkowskiG minkowskiG x ρ σ μ ν = 0 :=
  riemann_const minkowskiG minkowskiG eta4 (fun _ => rfl) x ρ σ μ ν

/-- **Minkowski is a vacuum solution of the Einstein equations, computed from
the metric rather than assumed.** -/
theorem minkowski_einstein (x : Fin 4 → ℝ) (i j : Fin 4) :
    einsteinOf minkowskiG minkowskiG x i j = 0 :=
  einsteinOf_const minkowskiG minkowskiG eta4 (fun _ => rfl) x i j


/-- The Schwarzschild metric as a field of components. -/
noncomputable def schwarzschildG (M : ℝ) : (Fin 4 → ℝ) → Tensor2 4 :=
  fun x => Schwarzschild.schwarzschildMetric M x

/-- The Schwarzschild inverse metric as a field of components. -/
noncomputable def schwarzschildGinv (M : ℝ) : (Fin 4 → ℝ) → Tensor2 4 :=
  fun x i j =>
    if i = j then
      if i = 0 then -(Schwarzschild.schwarzschildF M (x 1))⁻¹
      else if i = 1 then Schwarzschild.schwarzschildF M (x 1)
      else if i = 2 then (x 1 ^ 2)⁻¹
      else (x 1 ^ 2 * Real.sin (x 2) ^ 2)⁻¹
    else 0

/-- The `tt` entry of the inverse metric. -/
theorem schwarzschildGinv_00 (M : ℝ) (x : Fin 4 → ℝ) :
    schwarzschildGinv M x 0 0 = -(Schwarzschild.schwarzschildF M (x 1))⁻¹ := by
  simp [schwarzschildGinv]

/-- The inverse metric is diagonal. -/
theorem schwarzschildGinv_off (M : ℝ) (x : Fin 4 → ℝ) {k l : Fin 4} (h : k ≠ l) :
    schwarzschildGinv M x k l = 0 := by
  simp [schwarzschildGinv, h]

/-- The `tt` component of the metric does not depend on `t`, so its `t`
derivative is zero. -/
theorem pd_zero_of_schwarzschild_offdiag (M : ℝ) (x : Fin 4 → ℝ) :
    pd 0 (fun y => Schwarzschild.schwarzschildMetric M y 1 0) x = 0 := by
  have h : (fun s : ℝ => Schwarzschild.schwarzschildMetric M (Function.update x 0 s) 1 0)
      = fun _ => 0 := by
    funext s
    simp [Schwarzschild.schwarzschildMetric]
  rw [pd, h]
  simp

/-- The `r` derivative of `g_tt = −f` is `−2M/r²`. -/
theorem pd_schwarzschild_tt (M : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0) :
    pd 1 (fun y => Schwarzschild.schwarzschildMetric M y 0 0) x
      = -(2 * M / (x 1) ^ 2) := by
  have hfun : (fun s : ℝ => Schwarzschild.schwarzschildMetric M (Function.update x 1 s) 0 0)
      = fun s : ℝ => -(1 - 2 * M / s) := by
    funext s
    simp [Schwarzschild.schwarzschildMetric]
  have hmul : HasDerivAt (fun s : ℝ => -1 * (1 - 2 * M / s))
      (-1 * (2 * M / (x 1) ^ 2)) (x 1) :=
    (Schwarzschild.hasDerivAt_gtt M (x 1) hr).const_mul (-1)
  have hfun2 : (fun s : ℝ => -(1 - 2 * M / s)) = fun s : ℝ => -1 * (1 - 2 * M / s) := by
    funext s
    ring
  rw [pd, hfun, hfun2, hmul.deriv]
  ring

/-- **`Γ^t_{tr}` of the Schwarzschild metric, computed by the pipeline**, is
the value `M/(r²f)` proved by hand in `Examples/Schwarzschild.lean`.  Only the
`l = 0` term of the sum survives: the inverse is diagonal and the metric is
static. -/
theorem schwarzschild_christoffel_tr (M : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : Schwarzschild.schwarzschildF M (x 1) ≠ 0) :
    christoffel (schwarzschildG M) (schwarzschildGinv M) x 0 1 0
      = M / ((x 1) ^ 2 * Schwarzschild.schwarzschildF M (x 1)) := by
  have hoff := pd_zero_of_schwarzschild_offdiag M x
  have htt := pd_schwarzschild_tt M x hr
  have hr2 : (x 1) ^ 2 ≠ 0 := pow_ne_zero 2 hr
  simp only [christoffel, schwarzschildG, Fin.sum_univ_four]
  rw [schwarzschildGinv_00 M x,
      schwarzschildGinv_off M x (by decide : (0 : Fin 4) ≠ 1),
      schwarzschildGinv_off M x (by decide : (0 : Fin 4) ≠ 2),
      schwarzschildGinv_off M x (by decide : (0 : Fin 4) ≠ 3),
      hoff, htt]
  field_simp [hf, hr, hr2]
  ring


/-! ## Curvature from Christoffel data

The metric pipeline differentiates inside `riemann`.  This variant takes the
Christoffel symbols and their partial derivatives as *parameters*, which is what
lets a metric with a known derivative table be evaluated by algebra; the two are
the same definition, as `riemann_eq_riemannFromData` shows.
-/

/-- The Riemann tensor from Christoffel symbols and their partial derivatives as
data: `R^ρ_{σμν} = ∂_μΓ^ρ_{νσ} − ∂_νΓ^ρ_{μσ}
+ Γ^ρ_{μλ}Γ^λ_{νσ} − Γ^ρ_{νλ}Γ^λ_{μσ}`. -/
noncomputable def riemannFromData {n : ℕ}
    (G : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ)
    (dG : Fin n → (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n) : ℝ :=
  dG μ x ρ ν σ - dG ν x ρ μ σ
    + ∑ l, (G x ρ μ l * G x l ν σ - G x ρ ν l * G x l μ σ)

/-- **The data form is the pipeline**: feeding `riemannFromData` the metric's
actual partial derivatives of the Christoffel symbols reproduces `riemann`
definitionally, so nothing is assumed in passing to derivatives as data. -/
theorem riemann_eq_riemannFromData {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n) :
    riemann g ginv x ρ σ μ ν =
      riemannFromData (christoffel g ginv)
        (fun μ y a b c => pd μ (fun z => christoffel g ginv z a b c) y)
        x ρ σ μ ν :=
  rfl

/-- The data form gives Minkowski's vanishing curvature, matching
`minkowski_riemann` through the same definition. -/
theorem minkowski_riemannFromData (x : Fin 4 → ℝ) (ρ σ μ ν : Fin 4) :
    riemannFromData (christoffel minkowskiG minkowskiG)
      (fun μ y a b c => pd μ (fun z => christoffel minkowskiG minkowskiG z a b c) y)
      x ρ σ μ ν = 0 := by
  rw [← riemann_eq_riemannFromData]
  exact minkowski_riemann x ρ σ μ ν

/-! ## The Schwarzschild curvature from one evaluation of the data pipeline

`schG` is the Christoffel table of `g = diag(−f, 1/f, r², r²sin²θ)` in closed
form, and `schDG` its partial derivatives.  Feeding the pair to
`riemannFromData` gives all six independent components at once, which is
`riemann_components_pipeline`; the entries are the ones the hand computations in
`Examples/Schwarzschild.lean` differentiate term by term.
-/

/-- The Schwarzschild Christoffel symbols in `(t, r, θ, φ)` coordinates:
`Γ^t_{tr} = M/(r²f)`, `Γ^r_{tt} = Mf/r²`, `Γ^r_{rr} = −M/(r²f)`, `Γ^r_{θθ} = −rf`,
`Γ^r_{φφ} = −rf sin²θ`, `Γ^θ_{rθ} = Γ^φ_{rφ} = 1/r`,
`Γ^θ_{φφ} = −sinθ cosθ` and `Γ^φ_{θφ} = cosθ/sinθ`. -/
noncomputable def schG (M : ℝ) (x : Fin 4 → ℝ) (k i j : Fin 4) : ℝ :=
  if k = 0 then
    (if (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 1) then
      M / ((x 1) ^ 2 * Schwarzschild.schwarzschildF M (x 1)) else 0)
  else if k = 1 then
    (if i = 0 ∧ j = 0 then M * Schwarzschild.schwarzschildF M (x 1) / (x 1) ^ 2
     else if i = 1 ∧ j = 1 then (-M) / ((x 1) ^ 2 * Schwarzschild.schwarzschildF M (x 1))
     else if i = 2 ∧ j = 2 then -(x 1 * Schwarzschild.schwarzschildF M (x 1))
     else if i = 3 ∧ j = 3 then
       -(x 1 * Real.sin (x 2) ^ 2 * Schwarzschild.schwarzschildF M (x 1))
     else 0)
  else if k = 2 then
    (if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then 1 / (x 1)
     else if i = 3 ∧ j = 3 then -(Real.sin (x 2) * Real.cos (x 2)) else 0)
  else
    (if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then 1 / (x 1)
     else if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then
       Real.cos (x 2) / Real.sin (x 2) else 0)

/-- The partial derivatives of the Schwarzschild Christoffel table, in closed
form: `∂_r Γ^t_{tr} = −2M(r−M)/(r(r−2M))²`, `∂_r Γ^r_{θθ} = −f − 2M/r`,
`∂_r Γ^r_{φφ} = −(f + 2M/r) sin²θ` and `∂_θ Γ^θ_{φφ} = sin²θ − cos²θ`, with
all other partial derivatives zero.  The `r t` entry is the value
`deriv_gammaTtr` computes, so the table is the differentiation already done by
hand rather than a derivative expression. -/
noncomputable def schDG (M : ℝ) (μ : Fin 4) (x : Fin 4 → ℝ)
    (ρ ν σ : Fin 4) : ℝ :=
  if μ = 1 ∧ ρ = 0 ∧ ν = 0 ∧ σ = 1 then
    -2 * M * (x 1 - M) / (x 1 * (x 1 - 2 * M)) ^ 2
  else if μ = 1 ∧ ρ = 1 ∧ ν = 2 ∧ σ = 2 then
    -(Schwarzschild.schwarzschildF M (x 1)) - 2 * M / (x 1)
  else if μ = 1 ∧ ρ = 1 ∧ ν = 3 ∧ σ = 3 then
    -(Real.sin (x 2) ^ 2) * (Schwarzschild.schwarzschildF M (x 1) + 2 * M / (x 1))
  else if μ = 2 ∧ ρ = 2 ∧ ν = 3 ∧ σ = 3 then
    Real.sin (x 2) ^ 2 - Real.cos (x 2) ^ 2
  else 0

/-- **One evaluation of the pipeline yields all six Schwarzschild components.**
The closed-form table `schG` and its derivative table `schDG`, fed to
`riemannFromData`, give the six independent curvature components of §4.4 — the
same `2M/(r³f)`, `−M/r`, `−(M/r)sin²θ`, `−M/r`, `−(M/r)sin²θ` and
`(2M/r)sin²θ` that the per-component derivations establish, now read off a
single evaluation rather than one proof each. -/
theorem riemann_components_pipeline (M : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : Schwarzschild.schwarzschildF M (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    (riemannFromData (schG M) (schDG M) x 0 1 0 1
        = 2 * M / ((x 1) ^ 3 * Schwarzschild.schwarzschildF M (x 1)))
      ∧ (riemannFromData (schG M) (schDG M) x 0 2 0 2 = -M / (x 1))
      ∧ (riemannFromData (schG M) (schDG M) x 0 3 0 3
          = -(M / (x 1)) * Real.sin (x 2) ^ 2)
      ∧ (riemannFromData (schG M) (schDG M) x 1 2 1 2 = -M / (x 1))
      ∧ (riemannFromData (schG M) (schDG M) x 1 3 1 3
          = -(M / (x 1)) * Real.sin (x 2) ^ 2)
      ∧ (riemannFromData (schG M) (schDG M) x 2 3 2 3
          = (2 * M / (x 1)) * Real.sin (x 2) ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hden : x 1 * x 1 * Schwarzschild.schwarzschildF M (x 1)
        = x 1 * (x 1 - 2 * M) := by
      unfold Schwarzschild.schwarzschildF
      field_simp
    have hd : deriv (fun s : ℝ => M / (s * s * Schwarzschild.schwarzschildF M s)) (x 1)
        = -2 * M * (x 1 - M) / (x 1 * (x 1 - 2 * M)) ^ 2 := by
      simpa [pow_two] using Schwarzschild.deriv_gammaTtr M (x 1) hr hf
    have h := Schwarzschild.riemann_t_rtr_from_metric M (x 1) hr hf
    simp [riemannFromData, schG, schDG, Fin.sum_univ_four, hden, hd, add_assoc,
      sub_eq_add_neg, pow_two] at h ⊢
    linear_combination h
  · simpa [riemannFromData, schG, schDG, Fin.sum_univ_four] using
      Schwarzschild.riemann_t_thetatheta_from_metric M (x 1) hr hf
  · simpa [riemannFromData, schG, schDG, Fin.sum_univ_four] using
      Schwarzschild.riemann_t_phitphi_from_metric M (x 1) (x 2) hr hf
  · simpa [riemannFromData, schG, schDG, Fin.sum_univ_four, add_assoc,
      sub_eq_add_neg, pow_two] using
      Schwarzschild.riemann_r_thetar_from_metric M (x 1) hr hf
  · simpa [riemannFromData, schG, schDG, Fin.sum_univ_four, add_assoc,
      sub_eq_add_neg, pow_two] using
      Schwarzschild.riemann_r_phirphi_from_metric M (x 1) (x 2) hr hf
  · simpa [riemannFromData, schG, schDG, Fin.sum_univ_four, add_assoc,
      sub_eq_add_neg, pow_two] using
      Schwarzschild.riemann_theta_phitheta_from_metric M (x 1) (x 2) hr hsin


/-! ### The metric's Christoffel symbols are the closed-form table

`christoffel` evaluated on the metric's own components and their inverse is
`schG`, so the six-component theorem speaks about the metric rather than about a
transcribed table.  The metric is static in `t` and axisymmetric in `φ`, so only
`r` and `θ` derivatives appear; `pd_schwarzschild_r` and `pd_schwarzschild_theta`
tabulate them.
-/

/-- The metric does not depend on `t`: every `t` derivative vanishes. -/
@[simp] theorem pd_schwarzschild_t (M : ℝ) (x : Fin 4 → ℝ) (a b : Fin 4) :
    pd 0 (fun y => Schwarzschild.schwarzschildMetric M y a b) x = 0 := by
  fin_cases a <;> fin_cases b <;> simp [pd, Schwarzschild.schwarzschildMetric]

/-- The metric does not depend on `φ`: every `φ` derivative vanishes. -/
@[simp] theorem pd_schwarzschild_phi (M : ℝ) (x : Fin 4 → ℝ) (a b : Fin 4) :
    pd 3 (fun y => Schwarzschild.schwarzschildMetric M y a b) x = 0 := by
  fin_cases a <;> fin_cases b <;> simp [pd, Schwarzschild.schwarzschildMetric]

/-- `∂_r g_rr = −(2M/r²) f⁻²`, from `∂_r f = 2M/r²` and `g_rr = f⁻¹`. -/
theorem pd_schwarzschild_rr (M : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : Schwarzschild.schwarzschildF M (x 1) ≠ 0) :
    pd 1 (fun y => Schwarzschild.schwarzschildMetric M y 1 1) x
      = -(2 * M / (x 1) ^ 2) * (Schwarzschild.schwarzschildF M (x 1))⁻¹ ^ 2 := by
  have hf' : (1 - 2 * M / (x 1)) ≠ 0 := by
    simpa [Schwarzschild.schwarzschildF] using hf
  have hfun : (fun s : ℝ => Schwarzschild.schwarzschildMetric M (Function.update x 1 s) 1 1)
      = (fun s : ℝ => 1 - 2 * M / s)⁻¹ := by
    funext s
    simp [Schwarzschild.schwarzschildMetric]
  have h := HasDerivAt.inv (Schwarzschild.hasDerivAt_gtt M (x 1) hr) hf'
  rw [pd, hfun, h.deriv, Schwarzschild.schwarzschildF]
  field_simp

/-- `∂_r g_θθ = 2r`. -/
theorem pd_schwarzschild_thetatheta (M : ℝ) (x : Fin 4 → ℝ) :
    pd 1 (fun y => Schwarzschild.schwarzschildMetric M y 2 2) x = 2 * (x 1) := by
  have hfun : (fun s : ℝ => Schwarzschild.schwarzschildMetric M (Function.update x 1 s) 2 2)
      = fun s : ℝ => s ^ 2 := by
    funext s
    simp [Schwarzschild.schwarzschildMetric]
  rw [pd, hfun]
  simp

/-- `∂_r g_φφ = 2r sin²θ`. -/
theorem pd_schwarzschild_phiphi_r (M : ℝ) (x : Fin 4 → ℝ) :
    pd 1 (fun y => Schwarzschild.schwarzschildMetric M y 3 3) x
      = 2 * (x 1) * Real.sin (x 2) ^ 2 := by
  have hfun : (fun s : ℝ => Schwarzschild.schwarzschildMetric M (Function.update x 1 s) 3 3)
      = fun s : ℝ => s ^ 2 * Real.sin (x 2) ^ 2 := by
    funext s
    simp [Schwarzschild.schwarzschildMetric]
  have h := (hasDerivAt_pow 2 (x 1)).mul_const (Real.sin (x 2) ^ 2)
  rw [pd, hfun, h.deriv]
  ring

/-- `∂_θ g_φφ = 2r² sinθ cosθ`. -/
theorem pd_schwarzschild_phiphi_theta (M : ℝ) (x : Fin 4 → ℝ) :
    pd 2 (fun y => Schwarzschild.schwarzschildMetric M y 3 3) x
      = 2 * (x 1) ^ 2 * Real.sin (x 2) * Real.cos (x 2) := by
  have hfun : (fun s : ℝ => Schwarzschild.schwarzschildMetric M (Function.update x 2 s) 3 3)
      = fun s : ℝ => (x 1) ^ 2 * Real.sin s ^ 2 := by
    funext s
    simp [Schwarzschild.schwarzschildMetric]
  have h := (Schwarzschild.hasDerivAt_sinSq (x 2)).const_mul ((x 1) ^ 2)
  rw [pd, hfun, h.deriv]
  ring

/-- The `θ` derivatives of the metric components: only `g_φφ` contributes. -/
@[simp] theorem pd_schwarzschild_theta (M : ℝ) (x : Fin 4 → ℝ) (a b : Fin 4) :
    pd 2 (fun y => Schwarzschild.schwarzschildMetric M y a b) x
      = if a = 3 ∧ b = 3 then 2 * (x 1) ^ 2 * Real.sin (x 2) * Real.cos (x 2)
        else 0 := by
  fin_cases a <;> fin_cases b <;>
    first
    | exact pd_schwarzschild_phiphi_theta M x
    | simp [pd, Schwarzschild.schwarzschildMetric]

/-- The `r` derivatives of the metric components. -/
theorem pd_schwarzschild_r (M : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : Schwarzschild.schwarzschildF M (x 1) ≠ 0) (a b : Fin 4) :
    pd 1 (fun y => Schwarzschild.schwarzschildMetric M y a b) x
      = if a = 0 ∧ b = 0 then -(2 * M / (x 1) ^ 2)
        else if a = 1 ∧ b = 1 then
          -(2 * M / (x 1) ^ 2) * (Schwarzschild.schwarzschildF M (x 1))⁻¹ ^ 2
        else if a = 2 ∧ b = 2 then 2 * (x 1)
        else if a = 3 ∧ b = 3 then 2 * (x 1) * Real.sin (x 2) ^ 2
        else 0 := by
  fin_cases a <;> fin_cases b <;>
    first
    | exact pd_schwarzschild_tt M x hr
    | exact pd_schwarzschild_rr M x hr hf
    | exact pd_schwarzschild_thetatheta M x
    | exact pd_schwarzschild_phiphi_r M x
    | simp [pd, Schwarzschild.schwarzschildMetric]

/-- **The metric's Christoffel symbols are the closed-form table.**  Evaluating
`christoffel` on `schwarzschildG` and `schwarzschildGinv` gives `schG`, so the
table is the pipeline's own output; with `riemann_components_pipeline` the six
Schwarzschild components are then a statement about the metric itself. -/
theorem christoffel_eq_schG (M : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : Schwarzschild.schwarzschildF M (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    ∀ k i j, christoffel (schwarzschildG M) (schwarzschildGinv M) x k i j
      = schG M x k i j := by
  intro k i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [christoffel, schG, schwarzschildG, schwarzschildGinv,
      pd_schwarzschild_r M x hr hf]
  all_goals field_simp

end Pipeline

end Gravitation
