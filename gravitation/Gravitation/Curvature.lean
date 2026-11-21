import Gravitation.Basic

/-!
# Curvature: Riemann, Ricci and scalar curvature

The Riemann tensor carries its algebraic symmetries.  Antisymmetry in the last
pair, pair symmetry and the first Bianchi identity are structure fields;
antisymmetry in the *first* pair is proved from the other two
(`Riemann.skew_first`), so it is a theorem, not an assumption.

The Ricci contraction uses the inverse metric, `Ric_{ij} = Σ_k g^{kk} R_{kikj}`.
The chart is assumed to have a diagonal inverse metric, which holds for
Minkowski, Schwarzschild and FLRW in their standard coordinates; the fully
general `g^{kl} R_{kilj}` contraction is the next refinement.
-/

namespace Gravitation

/-- Components of the Riemann tensor with the algebraic symmetries of a
curvature tensor.  `bianchi` is the first (algebraic) Bianchi identity
`R_{ijkl} + R_{iklj} + R_{iljk} = 0`. -/
structure Riemann (n : ℕ) where
  comp : Fin n → Fin n → Fin n → Fin n → ℝ
  skew_last : ∀ i j k l, comp i j k l = -comp i j l k
  pair_symm : ∀ i j k l, comp i j k l = comp k l i j
  bianchi : ∀ i j k l, comp i j k l + comp i k l j + comp i l j k = 0

namespace Riemann

variable {n : ℕ} (R : Riemann n)

/-- Antisymmetry in the first pair follows from pair symmetry and antisymmetry
in the second pair, so it need not be assumed. -/
theorem skew_first (i j k l : Fin n) : R.comp i j k l = -R.comp j i k l := by
  have h1 : R.comp j i k l = R.comp k l j i := R.pair_symm j i k l
  have h2 : R.comp k l j i = -R.comp k l i j := R.skew_last k l j i
  have h3 : R.comp k l i j = R.comp i j k l := R.pair_symm k l i j
  rw [h1, h2, h3]
  ring

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
  skew_last := by intro i j k l; ring
  pair_symm := by intro i j k l; rfl
  bianchi := by intro i j k l; ring

@[simp] theorem flat_comp (i j k l : Fin n) : (flat n).comp i j k l = 0 := rfl

end Riemann

/-- The Ricci tensor `Ric_{ij} = Σ_k g^{kk} R_{kikj}`, contracting with the
inverse metric of a chart with diagonal `g^{ij}`. -/
noncomputable def ricci {n : ℕ} (M : Metric n) (R : Riemann n) : Tensor2 n :=
  fun i j => ∑ k, M.ginv k k * R.comp k i k j

/-- Ricci is symmetric.  With the metric weight outside the pair, this is
termwise pair symmetry of the Riemann tensor. -/
theorem ricci_symm {n : ℕ} (M : Metric n) (R : Riemann n) : IsSymm (ricci M R) := by
  intro i j
  exact Finset.sum_congr rfl (fun k _ => by rw [R.pair_symm k i k j])

/-- The flat curvature tensor is Ricci flat. -/
@[simp] theorem ricci_flat (n : ℕ) (M : Metric n) : ricci M (Riemann.flat n) = 0 := by
  ext i j
  simp [ricci]

/-- Scalar curvature, `S = g^{ij} Ric_{ij}`. -/
noncomputable def scalarCurv {n : ℕ} (M : Metric n) (R : Riemann n) : ℝ :=
  ∑ i, ∑ j, M.ginv i j * ricci M R i j

end Gravitation
