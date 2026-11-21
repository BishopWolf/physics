import Gravitation.Basic

/-!
# Curvature: Riemann, Ricci and scalar curvature

The Riemann tensor is introduced with its four algebraic symmetries as
structure fields (the standard characterisation of the curvature of a
metric-compatible connection).  Ricci contraction and scalar curvature are then
defined from it, and the symmetry of Ricci is *proved* from pair symmetry.
-/

namespace Gravitation

/-- Components of the Riemann curvature tensor with the algebraic symmetries of
a curvature tensor.  `bianchi` is the first (algebraic) Bianchi identity

`R_{ijkl} + R_{iklj} + R_{iljk} = 0`.
-/
structure Riemann (n : ℕ) where
  comp : Fin n → Fin n → Fin n → Fin n → ℝ
  skew_first : ∀ i j k l, comp i j k l = -comp j i k l
  skew_last : ∀ i j k l, comp i j k l = -comp i j l k
  pair_symm : ∀ i j k l, comp i j k l = comp k l i j
  bianchi : ∀ i j k l, comp i j k l + comp i k l j + comp i l j k = 0

namespace Riemann

variable {n : ℕ} (R : Riemann n)

/-- A component with a repeated first index vanishes. -/
theorem zero_of_repeated_first (i k l : Fin n) : R.comp i i k l = 0 := by
  have h := R.skew_first i i k l
  linarith

/-- A component with a repeated last index vanishes. -/
theorem zero_of_repeated_last (i j k : Fin n) : R.comp i j k k = 0 := by
  have h := R.skew_last i j k k
  linarith

/-- Swapping one index in each antisymmetric pair preserves the component. -/
theorem swap_mixed (i j k l : Fin n) : R.comp i j k l = R.comp j i l k := by
  rw [R.skew_first i j k l, R.skew_last j i k l]
  ring

/-- The flat curvature tensor: every component vanishes. -/
def flat (n : ℕ) : Riemann n where
  comp := fun _ _ _ _ => 0
  skew_first := by intro i j k l; ring
  skew_last := by intro i j k l; ring
  pair_symm := by intro i j k l; rfl
  bianchi := by intro i j k l; ring

@[simp] theorem flat_comp (i j k l : Fin n) : (flat n).comp i j k l = 0 := rfl

end Riemann

/-- The Ricci tensor, `Ric_{ij} = R^k{}_{ikj}`. -/
def ricci {n : ℕ} (R : Riemann n) : Tensor2 n := fun i j => ∑ k, R.comp k i k j

/-- Ricci is symmetric.  This is a real consequence of the symmetries: the
contraction pairs the antisymmetric indices with each other. -/
theorem ricci_symm {n : ℕ} (R : Riemann n) : IsSymm (ricci R) := by
  intro i j
  exact Finset.sum_congr rfl (fun k _ => R.pair_symm k i k j)

/-- The flat curvature tensor is Ricci flat. -/
@[simp] theorem ricci_flat (n : ℕ) : ricci (Riemann.flat n) = 0 := by
  ext i j
  simp [ricci]

/-- Scalar curvature, `S = g^{ij} Ric_{ij}`. -/
def scalarCurv {n : ℕ} (M : Metric n) (R : Riemann n) : ℝ :=
  ∑ i, ∑ j, M.ginv i j * ricci R i j

end Gravitation
