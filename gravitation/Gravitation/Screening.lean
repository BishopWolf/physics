import Gravitation.Einstein
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

end Gravitation
