import Gravitation.Einstein
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Chameleon screening

`f(R)` and chameleon models couple the scalar to matter, so it should mediate a
fifth force — yet the same theories pass solar-system tests.  The mechanism is
chameleon screening: the scalar's mass grows with the ambient density, its range
shrinks in the solar system, and the force is exponentially suppressed before it
can be measured.

This file proves the chain

`density ↑ → mass ↑ → range ↓ → Yukawa suppression`,

plus the thin-shell factor that caps the external force of a screened body.

Three inputs are modelling assumptions, stated as definitions rather than
derived: the mass–density law `m² = cρ`, the Yukawa factor `e^{−x}` with
`x = r/λ`, and the thin-shell fraction `min Δ 1`.  What is proved is the
structure those assumptions imply — the same structure that lets `f(R)` evade
the `γ = 1/2` bound proved in `Gravitation.ScalarTensor`.
-/

namespace Gravitation

namespace Screening

/-- Scalar mass-squared proportional to ambient density: `m² = cρ`. -/
noncomputable def chameleonMassSq (ρ c : ℝ) : ℝ := ρ * c

/-- The chameleon scalar mass, `m = √(cρ)`. -/
noncomputable def chameleonMass (ρ c : ℝ) : ℝ := Real.sqrt (ρ * c)

/-- **Denser environment, heavier scalar.** -/
theorem chameleonMass_mono {ρ₁ ρ₂ c : ℝ} (hc : 0 ≤ c) (h : ρ₁ ≤ ρ₂) :
    chameleonMass ρ₁ c ≤ chameleonMass ρ₂ c :=
  Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right h hc)

/-- Compton wavelength `λ = 1/m` of a scalar of mass `m`. -/
noncomputable def range (m : ℝ) : ℝ := 1 / m

/-- **Heavier scalar, shorter range.** -/
theorem range_antitone {m₁ m₂ : ℝ} (h₁ : 0 < m₁) (h : m₁ ≤ m₂) :
    range m₂ ≤ range m₁ :=
  one_div_le_one_div_of_le h₁ h

/-- **Denser environment, shorter range** — the first half of the mechanism. -/
theorem chameleon_range_shrinks {ρ₁ ρ₂ c : ℝ} (hpos : 0 < chameleonMass ρ₁ c)
    (hc : 0 ≤ c) (h : ρ₁ ≤ ρ₂) :
    range (chameleonMass ρ₂ c) ≤ range (chameleonMass ρ₁ c) :=
  range_antitone hpos (chameleonMass_mono hc h)

/-- Yukawa factor `e^{−x}` in the dimensionless distance `x = r/λ`. -/
noncomputable def yukawaRatio (x : ℝ) : ℝ := Real.exp (-x)

/-- `e^{−1} < 1/2`: at one Compton wavelength the force is already down by more
than a factor of two. -/
theorem exp_neg_one_lt_half : Real.exp (-1) < 1 / 2 := by
  rw [Real.exp_neg]
  simpa using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2)
    (by linarith [Real.exp_one_gt_d9])

/-- **Beyond its range the scalar force is negligible**: for `r ≥ λ` the Yukawa
factor is below `1/2`. -/
theorem yukawaRatio_lt_half {x : ℝ} (h : 1 ≤ x) : yukawaRatio x < 1 / 2 := by
  have h1 : yukawaRatio x ≤ Real.exp (-1) := by
    simp only [yukawaRatio]
    exact Real.exp_le_exp.mpr (by linarith)
  linarith [exp_neg_one_lt_half]

/-- Thin-shell parameter `Δ = |δφ| / (2 β M_pl |Φ_N|)`. -/
noncomputable def thinShell (dphi β Mpl Phi : ℝ) : ℝ :=
  |dphi| / (2 * β * Mpl * |Phi|)

/-- The fraction of the unscreened fifth force that survives: `min Δ 1`. -/
noncomputable def screeningFactor (Δ : ℝ) : ℝ := min Δ 1

theorem thinShell_nonneg {dphi β Mpl Phi : ℝ} (h : 0 ≤ 2 * β * Mpl * |Phi|) :
    0 ≤ thinShell dphi β Mpl Phi :=
  div_nonneg (abs_nonneg dphi) h

theorem screeningFactor_le (Δ : ℝ) : screeningFactor Δ ≤ Δ := min_le_left _ _

theorem screeningFactor_le_one (Δ : ℝ) : screeningFactor Δ ≤ 1 := min_le_right _ _

/-- **A thin shell is screened.**  A body with thin-shell parameter `Δ ≤ ε`
exerts a fifth force reduced at least to `ε`, so `Δ ≪ 1` makes the scalar
invisible. -/
theorem thin_shell_suppressed {Δ ε : ℝ} (h : Δ ≤ ε) : screeningFactor Δ ≤ ε :=
  (screeningFactor_le Δ).trans h

/-- The external force saturates at one — the unscreened value — only for
`Δ ≥ 1`. -/
theorem screeningFactor_eq_one_iff (Δ : ℝ) : screeningFactor Δ = 1 ↔ 1 ≤ Δ :=
  min_eq_right_iff

end Screening

/-! ## The thin-shell profile -/

namespace ThinShell

/-- The exterior scalar profile of a screened spherical body,
`φ(r) = φ∞ − Q/r`. -/
noncomputable def profile (φinf Q r : ℝ) : ℝ := φinf - Q / r

/-- The exterior gradient is `Q/r²`. -/
theorem hasDerivAt_profile (φinf Q r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (profile φinf Q) (Q / r ^ 2) r := by
  change HasDerivAt (fun s : ℝ => φinf - Q / s) (Q / r ^ 2) r
  have hinv : HasDerivAt (fun s : ℝ => s⁻¹) (-1 / r ^ 2) r :=
    HasDerivAt.inv (hasDerivAt_id r) hr
  have hQ : HasDerivAt (fun s : ℝ => Q * s⁻¹) (Q * (-1 / r ^ 2)) r :=
    HasDerivAt.const_mul Q hinv
  have hsub : HasDerivAt (fun s : ℝ => φinf - Q * s⁻¹) (0 - Q * (-1 / r ^ 2)) r :=
    (hasDerivAt_const r φinf).sub hQ
  have hval : (0 - Q * (-1 / r ^ 2)) = Q / r ^ 2 := by
    field_simp; ring
  rw [hval] at hsub
  exact hsub

/-- The fifth-force ratio: scalar acceleration over the Newtonian acceleration
`Φ R/r²`. -/
noncomputable def forceRatio (Q Phi R r : ℝ) : ℝ := (Q / r ^ 2) / (Phi * R / r ^ 2)

theorem forceRatio_eq (Q Phi R r : ℝ) (_h : Phi * R ≠ 0) (hr : r ≠ 0) :
    forceRatio Q Phi R r = Q / (Phi * R) := by
  simp only [forceRatio]
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  field_simp

/-- **The thin-shell charge.**  With `Q = Δ Φ R` the exterior fifth force is
`Δ` times gravity. -/
theorem forceRatio_thin_shell (Δ Phi R r : ℝ) (h : Phi * R ≠ 0) (hr : r ≠ 0) :
    forceRatio (Δ * Phi * R) Phi R r = Δ := by
  have hPhi : Phi ≠ 0 := (mul_ne_zero_iff.mp h).1
  have hR : R ≠ 0 := (mul_ne_zero_iff.mp h).2
  rw [forceRatio_eq _ Phi R r h hr]
  field_simp

/-- The profile at the surface: `φ(R) = φ∞ − Δ Φ`. -/
theorem profile_surface (φinf Δ Phi R : ℝ) (hR : R ≠ 0) :
    profile φinf (Δ * Phi * R) R = φinf - Δ * Phi := by
  simp only [profile]
  field_simp

/-- **Thin shell, weak force.**  `Δ ≤ ε` caps the fifth force at `ε` times
gravity. -/
theorem thin_shell_weak (Δ ε Phi R r : ℝ) (hPR : Phi * R ≠ 0) (hr : r ≠ 0)
    (h : Δ ≤ ε) : forceRatio (Δ * Phi * R) Phi R r ≤ ε := by
  rw [forceRatio_thin_shell Δ Phi R r hPR hr]
  exact h

/-- **Thick shell, order-one force.**  `Δ ≥ 1` leaves an unscreened fifth force
of the same order as gravity — the `γ = 1/2` problem. -/
theorem thick_shell_strong (Δ Phi R r : ℝ) (hPR : Phi * R ≠ 0) (hr : r ≠ 0)
    (h : 1 ≤ Δ) : 1 ≤ forceRatio (Δ * Phi * R) Phi R r := by
  rw [forceRatio_thin_shell Δ Phi R r hPR hr]
  exact h

end ThinShell

end Gravitation
