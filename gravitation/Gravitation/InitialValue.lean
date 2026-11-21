import Gravitation.Curvature
import Gravitation.Einstein

/-!
# The initial value problem: constraint equations

The initial value (Cauchy) problem for the vacuum Einstein equations asks for a
spacetime whose induced data on a spatial slice `Σ` are a Riemannian metric `h`
and a symmetric extrinsic curvature `K`.  Not every pair `(h, K)` is admissible:
the normal components of `G = 0` are equations *on the slice*, not evolution
equations.  In a chart where the slice is `t = 0` and the induced metric is
Euclidean, these are

* Hamiltonian (energy) constraint  `H = ³R + (tr K)² − K_ij K^ij = 0`
* momentum constraint             `M_i = ∂_j K_ij − ∂_i (tr K) = 0`

where `³R` is the scalar curvature of `h`.

What is formalised here:

* the two constraint functions and the fact that `H` is *not* automatically
  zero, so the theory has content (`squeezedData_ham_ne_zero`);
* the moment-of-time-symmetry reduction `K = 0`: then `M ≡ 0` and `H = ³R`, so
  vacuum data are exactly the scalar-flat `h`
  (`ham_zero_iff_scalarCurv_zero_of_K_zero`);
* the maximal-slicing form `tr K = 0`: `H = ³R − K_ij K^ij`;
* the consequence `(tr K)² = K_ij K^ij` on scalar-flat slices;
* flat `ℝ³` with `K = 0` as a concrete vacuum data set.

What is *not* formalised, and is not axiomatised either: the existence and
uniqueness of a maximal globally hyperbolic development of given data
(Choquet–Bruhat–Geroch).  That is a theorem about quasilinear hyperbolic PDEs,
not available in Mathlib, and this development adds no axiom to paper over the
gap.  Everything below is proved from Lean's three standard axioms.
-/

namespace Gravitation

/-- Vacuum initial data on a spatial slice: the induced metric `h`, its Riemann
tensor `R3`, and the extrinsic curvature `K`. -/
structure InitialData where
  h : Metric 3
  R3 : Riemann 3
  K : Tensor2 3
  Ksymm : IsSymm K

/-- The momentum constraint `M_i = ∂_j K_ij − ∂_i (tr K)`, with the chart
derivatives of the extrinsic curvature supplied as `dK μ i j = ∂_μ K_ij`.  The
induced metric is flat in this chart, so partial derivatives are the covariant
ones. -/
noncomputable def momConstraint (dK : Fin 3 → Tensor2 3) (i : Fin 3) : ℝ :=
  (∑ j, dK j i j) - ∑ j, dK i j j

namespace InitialData

/-- The Hamiltonian (energy) constraint `H = ³R + (tr K)² − K_ij K^ij`. -/
noncomputable def ham (D : InitialData) : ℝ :=
  scalarCurv D.h D.R3 + (∑ i, D.K i i) ^ 2 - ∑ i, ∑ j, D.K i j * D.K i j

/-- The two vacuum constraints together. -/
def IsVacuumData (D : InitialData) (dK : Fin 3 → Tensor2 3) : Prop :=
  D.ham = 0 ∧ ∀ i, momConstraint dK i = 0

/-! ### Moment of time symmetry -/

/-- `K = 0` (a moment of time symmetry): the Hamiltonian constraint reduces to
scalar flatness of the induced metric. -/
theorem ham_eq_scalarCurv_of_K_zero (D : InitialData) (hK : D.K = 0) :
    D.ham = scalarCurv D.h D.R3 := by
  simp [ham, hK]

/-- In a moment of time symmetry, vacuum data are exactly scalar-flat data. -/
theorem ham_zero_iff_scalarCurv_zero_of_K_zero (D : InitialData)
    (hK : D.K = 0) : D.ham = 0 ↔ scalarCurv D.h D.R3 = 0 := by
  rw [ham_eq_scalarCurv_of_K_zero D hK]

/-! ### Maximal slicing -/

/-- Maximal slicing, `tr K = 0`: the Hamiltonian constraint becomes
`³R = K_ij K^ij`. -/
theorem ham_eq_of_trace_zero (D : InitialData) (htr : (∑ i, D.K i i) = 0) :
    D.ham = scalarCurv D.h D.R3 - ∑ i, ∑ j, D.K i j * D.K i j := by
  simp [ham, htr]

/-- On a scalar-flat slice, the Hamiltonian constraint forces
`(tr K)² = K_ij K^ij`. -/
theorem trace_sq_eq_of_ham_zero (D : InitialData) (hH : D.ham = 0)
    (hR : scalarCurv D.h D.R3 = 0) :
    (∑ i, D.K i i) ^ 2 = ∑ i, ∑ j, D.K i j * D.K i j := by
  simp only [ham] at hH
  linarith

end InitialData

/-- Constant extrinsic curvature gives a vanishing momentum constraint. -/
theorem momConstraint_zero_of_dK_zero (dK : Fin 3 → Tensor2 3)
    (hdK : ∀ μ, dK μ = 0) : ∀ i, momConstraint dK i = 0 := by
  intro i
  simp [momConstraint, hdK]

/-! ### Concrete data: flat `ℝ³` at a moment of time symmetry -/

theorem one_symm {n : ℕ} : IsSymm (1 : Tensor2 n) := by
  intro i j
  simp only [Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · have h' : j ≠ i := fun hji => h hji.symm
    simp [h, h']

/-- The Euclidean metric on `Fin 3`. -/
def euclid3 : Metric 3 where
  g := 1
  ginv := 1
  symm := one_symm
  inv_left := one_mul 1
  inv_right := one_mul 1

/-- Flat space with vanishing extrinsic curvature: the initial slice of Minkowski
spacetime. -/
def flatData : InitialData where
  h := euclid3
  R3 := Riemann.flat 3
  K := 0
  Ksymm := isSymm_zero

theorem flatData_ham_zero : flatData.ham = 0 := by
  rw [InitialData.ham_eq_scalarCurv_of_K_zero flatData rfl]
  show scalarCurv euclid3 (Riemann.flat 3) = 0
  simp [scalarCurv]

theorem flatData_mom_zero : ∀ i, momConstraint (fun _ => 0) i = 0 :=
  momConstraint_zero_of_dK_zero (fun _ => 0) (fun _ => rfl)

/-- Minkowski's initial slice satisfies both vacuum constraints. -/
theorem flatData_isVacuum : flatData.IsVacuumData (fun _ => 0) :=
  ⟨flatData_ham_zero, flatData_mom_zero⟩

/-! ### The constraints have content: a non-vacuum data set -/

/-- Extrinsic curvature `diag(1, 1, 0)` on flat space. -/
def squeezedK : Tensor2 3 := !![(1 : ℝ), 0, 0; 0, 1, 0; 0, 0, 0]

theorem squeezedK_symm : IsSymm squeezedK := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [squeezedK]

/-- Flat space with `K = diag(1,1,0)`. -/
def squeezedData : InitialData where
  h := euclid3
  R3 := Riemann.flat 3
  K := squeezedK
  Ksymm := squeezedK_symm

/-- Its Hamiltonian constraint is `(tr K)² − K_ij K^ij = 4 − 2 = 2`. -/
theorem squeezedData_ham : squeezedData.ham = 2 := by
  simp [InitialData.ham, squeezedData, euclid3, squeezedK, scalarCurv,
    Fin.sum_univ_three]
  norm_num

/-- So the vacuum constraints are not automatic. -/
theorem squeezedData_ham_ne_zero : squeezedData.ham ≠ 0 := by
  rw [squeezedData_ham]
  norm_num

end Gravitation
