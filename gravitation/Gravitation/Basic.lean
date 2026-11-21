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

/-- Componentwise conformal rescaling of a metric, `g̃ = φ g`. -/
def conformalG {n : ℕ} (g : Tensor2 n) (φ : ℝ) : Tensor2 n := fun i j => φ * g i j

/-- The corresponding inverse components, `g̃⁻¹ = φ⁻¹ g⁻¹`. -/
noncomputable def conformalGinv {n : ℕ} (ginv : Tensor2 n) (φ : ℝ) : Tensor2 n :=
  fun i j => φ⁻¹ * ginv i j

/-- The rescaled inverse is the inverse of the rescaled metric. -/
theorem conformalG_mul {n : ℕ} (M : Metric n) (φ : ℝ) (hφ : φ ≠ 0) :
    conformalG M.g φ * conformalGinv M.ginv φ = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have hterm : ∀ k,
      conformalG M.g φ i k * conformalGinv M.ginv φ k j = M.g i k * M.ginv k j := by
    intro k
    simp only [conformalG, conformalGinv]
    calc (φ * M.g i k) * (φ⁻¹ * M.ginv k j)
        = (φ * φ⁻¹) * (M.g i k * M.ginv k j) := by ring
      _ = M.g i k * M.ginv k j := by rw [mul_inv_cancel₀ hφ, one_mul]
  have h1 : (∑ k, M.g i k * M.ginv k j) = (1 : Tensor2 n) i j := by
    have hinv := congrFun (congrFun M.inv_left i) j
    simpa only [Matrix.mul_apply] using hinv
  have hsum : (∑ k, conformalG M.g φ i k * conformalGinv M.ginv φ k j)
      = ∑ k, M.g i k * M.ginv k j := Finset.sum_congr rfl (fun k _ => hterm k)
  rw [hsum]
  exact h1

theorem conformalGinv_mul {n : ℕ} (M : Metric n) (φ : ℝ) (hφ : φ ≠ 0) :
    conformalGinv M.ginv φ * conformalG M.g φ = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have hterm : ∀ k,
      conformalGinv M.ginv φ i k * conformalG M.g φ k j = M.ginv i k * M.g k j := by
    intro k
    simp only [conformalG, conformalGinv]
    calc (φ⁻¹ * M.ginv i k) * (φ * M.g k j)
        = (φ⁻¹ * φ) * (M.ginv i k * M.g k j) := by ring
      _ = M.ginv i k * M.g k j := by rw [inv_mul_cancel₀ hφ, one_mul]
  have h1 : (∑ k, M.ginv i k * M.g k j) = (1 : Tensor2 n) i j := by
    have hinv := congrFun (congrFun M.inv_right i) j
    simpa only [Matrix.mul_apply] using hinv
  have hsum : (∑ k, conformalGinv M.ginv φ i k * conformalG M.g φ k j)
      = ∑ k, M.ginv i k * M.g k j := Finset.sum_congr rfl (fun k _ => hterm k)
  rw [hsum]
  exact h1

/-- A conformal rescaling `g̃ = φ g` of a metric, with inverse `φ⁻¹ g⁻¹` — the
metric-level transformation underlying the Jordan-to-Einstein frame change. -/
noncomputable def conformalMetric {n : ℕ} (M : Metric n) (φ : ℝ) (hφ : φ ≠ 0) :
    Metric n where
  g := conformalG M.g φ
  ginv := conformalGinv M.ginv φ
  symm := by
    intro i j
    show φ * M.g i j = φ * M.g j i
    rw [M.symm i j]
  inv_left := conformalG_mul M φ hφ
  inv_right := conformalGinv_mul M φ hφ

end Gravitation
