import Gravitation.Basic
import Mathlib.Tactic.FieldSimp

/-!
# The Ostrogradsky instability

A Lagrangian that depends non-degenerately on accelerations defines *two*
canonical pairs instead of one: the conjugate momentum of `q̇` is computed from
`∂L/∂q̈`, and the Hamiltonian obtained from it is affine in that momentum, hence
unbounded below.  That negative-energy degree of freedom is the Ostrogradsky
ghost (Ostrogradsky 1850), and it is why higher-derivative gravity must either
be reduced to a healthy scalar–tensor theory (`f(R)` in the metric formalism) or
protected by construction (Horndeski).

This file formalises the algebraic core for the model `L = ½ q̈² + V(q)`:

* `kineticMatrix_degenerate` : the kinetic matrix in `(q̇, q̈)` is singular, so the
  system is constrained and `q̇` is not a genuine canonical coordinate;
* `hamiltonian_add` : the Hamiltonian is affine in the conjugate momentum `p₁`,
  with slope equal to the velocity;
* `unbounded_below` : for any non-zero velocity it is unbounded below — the ghost;
* `kinetic_bounded` / `kinetic_zero_iff` : a standard quadratic kinetic term is
  bounded below and vanishes only at zero velocity, so no ghost.

Not formalised: the Dirac reduction that isolates the ghost, and the derivation
of the Euler–Lagrange equation from the action.
-/

namespace Gravitation

namespace Ostrogradsky

/-- The kinetic matrix of `L = ½ q̈² + V(q)` in the variables `(q̇, q̈)`, i.e.
`diag(0, 1)`: the Hessian in the velocities. -/
def kineticMatrix : Tensor2 2 :=
  fun i j => if i = 1 ∧ j = 1 then 1 else 0

/-- **The kinetic matrix is degenerate.**  Its determinant vanishes, so `q̇` does
not enter quadratically: the system carries a constraint, and after reduction one
of the remaining canonical pairs has negative energy. -/
theorem kineticMatrix_degenerate :
    kineticMatrix 0 0 * kineticMatrix 1 1 - kineticMatrix 0 1 * kineticMatrix 1 0 = 0 := by
  simp [kineticMatrix]

/-- The Ostrogradsky Hamiltonian for `L = ½ q̈² + V(q)`, with `p₁` conjugate to
`q̇` and `p₂ = q̈`. -/
noncomputable def hamiltonian (v a p₁ p₂ q m : ℝ) : ℝ :=
  p₁ * v + p₂ * a - a ^ 2 / 2 + m ^ 2 * q ^ 2 / 2

/-- The Hamiltonian is affine in the momentum `p₁`, with slope equal to the
velocity `v`: shifting `p₁` by `t` shifts `H` by `t v`. -/
theorem hamiltonian_add (v a p₁ p₂ q m t : ℝ) :
    hamiltonian v a (p₁ + t) p₂ q m = hamiltonian v a p₁ p₂ q m + t * v := by
  simp only [hamiltonian]
  ring

/-- **The Ostrogradsky ghost.**  For any non-zero velocity the Hamiltonian is a
non-constant affine function of `p₁`, hence unbounded below: the extra degree of
freedom carries arbitrarily negative energy. -/
theorem unbounded_below (v a p₂ q m : ℝ) (hv : v ≠ 0) :
    ∀ B : ℝ, ∃ p₁ : ℝ, hamiltonian v a p₁ p₂ q m < B := by
  intro B
  have h : (B - 1 - (p₂ * a - a ^ 2 / 2 + m ^ 2 * q ^ 2 / 2)) / v * v
      = B - 1 - (p₂ * a - a ^ 2 / 2 + m ^ 2 * q ^ 2 / 2) := by
    field_simp
  refine ⟨(B - 1 - (p₂ * a - a ^ 2 / 2 + m ^ 2 * q ^ 2 / 2)) / v, ?_⟩
  simp only [hamiltonian]
  linarith

/-- A standard quadratic kinetic term is non-negative: no ghost. -/
theorem kinetic_bounded (m x : ℝ) (hm : 0 < m) : 0 ≤ m * x ^ 2 / 2 := by
  positivity

/-- A standard quadratic kinetic term vanishes only at zero velocity, so the
kinetic matrix is nondegenerate. -/
theorem kinetic_zero_iff (m x : ℝ) (hm : 0 < m) : m * x ^ 2 / 2 = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h2 : m * x ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp h3
  · rintro rfl
    ring

end Ostrogradsky

end Gravitation
