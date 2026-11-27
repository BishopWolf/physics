/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Gravitation.Relativity.General.Schwarzschild.ElectricWeyl
public import Gravitation.Relativity.General.SchwarzschildDeSitter.DeSitterFrame

/-!

# Hypothesis-free Kretschmann scalars

The frame theorems `SchwarzschildSpacetime.kretschmann_scalar` and
`SchwarzschildDeSitter.kretschmann` assume `r ≠ 0` only to clear denominators.
Division by zero is total in Lean (`a / 0 = 0`), and at `r = 0` both sides of each
identity are zero, so the hypothesis is not needed. These corollaries remove it,
leaving the frame Kretschmann statements with no hypotheses at all.

## i. Main results

- `Schwarzschild.kretschmann_scalar_total` : `∑ R_{ijlm}² = 48 M² / r⁶` for every `r`.
- `SchwarzschildDeSitter.kretschmann_sds_total` : `∑ R_{ijlm}² = 48 M² / r⁶ + 8 Λ² / 3`
  for every `r`.

-/

@[expose] public section

namespace GeneralRelativity

namespace Schwarzschild

/-- The Schwarzschild frame Kretschmann scalar, with the `r ≠ 0` hypothesis removed. -/
lemma kretschmann_scalar_total (M r : ℝ) :
    ((SchwarzschildSpacetime.mk M).frameRiemann r).frameKretschmannScalar
      = 48 * M ^ 2 / r ^ 6 := by
  by_cases hr : r = 0
  · subst r
    simp [SchwarzschildSpacetime.frameRiemann, electricWeyl_frameKretschmannScalar_eq]
  · exact (SchwarzschildSpacetime.mk M).kretschmann_scalar r hr

end Schwarzschild

namespace SchwarzschildDeSitter

/-- The Schwarzschild–de Sitter frame Kretschmann scalar, with the `r ≠ 0`
hypothesis removed. -/
lemma kretschmann_sds_total (M Λ r : ℝ) :
    (SchwarzschildDeSitterSpacetime.mk M Λ).frameSumOfSquares r
      = 48 * M ^ 2 / r ^ 6 + 8 * Λ ^ 2 / 3 := by
  by_cases hr : r = 0
  · subst r
    rw [SchwarzschildDeSitterSpacetime.frameSumOfSquares_eq]
    norm_num
  · exact (SchwarzschildDeSitterSpacetime.mk M Λ).kretschmann r hr

end SchwarzschildDeSitter

end GeneralRelativity