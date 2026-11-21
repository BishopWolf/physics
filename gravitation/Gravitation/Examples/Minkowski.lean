import Gravitation.Einstein

/-!
# Minkowski spacetime as a vacuum solution

The flat metric `η = diag(-1,1,1,1)` with vanishing curvature solves `G = 0`.
This is the smallest nontrivial consistency check of the definitions: a real
spacetime, a real curvature tensor, and a proved vacuum Einstein equation.
-/

namespace Gravitation

/-- Four-dimensional Minkowski spacetime in inertial coordinates. -/
def minkowski : Metric 4 :=
  { g := eta4, ginv := eta4, symm := eta4_symm,
    inv_left := eta4_mul_self, inv_right := eta4_mul_self }

namespace Minkowski

theorem ricci_eq_zero : ricci (Riemann.flat 4) = 0 := ricci_flat 4

theorem scalarCurv_eq_zero : scalarCurv minkowski (Riemann.flat 4) = 0 := by
  simp [scalarCurv]

/-- Minkowski spacetime is a vacuum solution of the Einstein equations. -/
theorem einstein_eq_zero : einstein minkowski (Riemann.flat 4) = 0 := by
  ext i j
  simp [einstein, scalarCurv_eq_zero]

/-- `G = 0` and `Ric = 0` agree here, as the four-dimensional theorem predicts. -/
theorem vacuum_iff_ricci_flat :
    einstein minkowski (Riemann.flat 4) = 0 ↔ ricci (Riemann.flat 4) = 0 :=
  Gravitation.vacuum_iff_ricci_flat minkowski (Riemann.flat 4)

end Minkowski

end Gravitation
