import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Component tensors, metrics and the Minkowski metric

Foundational layer of a coordinate (component) formalisation of general
relativity.  A rank-2 covariant tensor is a real matrix of components; the
metric is carried together with an explicit two-sided inverse, which is what a
nondegenerate symmetric bilinear form is in coordinates.

The choice of coordinates is deliberate: it keeps every statement elementary
and every proof checkable by `ring`/`linarith`, at the price of a separate
coordinate-invariance layer that this development does not attempt.
-/

namespace Gravitation

/-- A rank-2 covariant tensor in a fixed basis: a real matrix of components. -/
abbrev Tensor2 (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℝ

/-- Symmetry of a rank-2 tensor. -/
def IsSymm {n : ℕ} (T : Tensor2 n) : Prop := ∀ i j, T i j = T j i

theorem isSymm_zero {n : ℕ} : IsSymm (0 : Tensor2 n) := fun _ _ => rfl

theorem IsSymm.transpose {n : ℕ} {T : Tensor2 n} (h : IsSymm T) :
    Matrix.transpose T = T := by
  ext i j
  exact (h i j).symm

/-- The Minkowski metric of signature `(-,+,+,+)` in inertial coordinates. -/
def eta4 : Tensor2 4 := !![(-1 : ℝ), 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem eta4_symm : IsSymm eta4 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [eta4]

/-- `η` is its own inverse: `η * η = 1`. -/
theorem eta4_mul_self : eta4 * eta4 = (1 : Tensor2 4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eta4, Matrix.mul_apply, Fin.sum_univ_four]

/-- A nondegenerate metric, carried together with an explicit two-sided inverse. -/
structure Metric (n : ℕ) where
  g : Tensor2 n
  ginv : Tensor2 n
  symm : IsSymm g
  inv_left : g * ginv = 1
  inv_right : ginv * g = 1

/-- The inverse of a symmetric metric is itself symmetric. -/
theorem Metric.ginv_symm {n : ℕ} (M : Metric n) : IsSymm M.ginv := by
  have htrans : Matrix.transpose M.ginv * M.g = 1 := by
    have h := congrArg Matrix.transpose M.inv_left
    rwa [Matrix.transpose_mul, Matrix.transpose_one, IsSymm.transpose M.symm] at h
  have hsq : Matrix.transpose M.ginv * M.g = M.ginv * M.g := by
    rw [htrans, M.inv_right]
  have hEq : Matrix.transpose M.ginv = M.ginv := by
    have h := congrArg (fun X : Tensor2 n => X * M.ginv) hsq
    simpa [Matrix.mul_assoc, M.inv_left, M.inv_right] using h
  intro i j
  exact (congrFun (congrFun hEq i) j).symm

end Gravitation
