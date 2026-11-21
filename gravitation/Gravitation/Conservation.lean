import Gravitation.Einstein

/-!
# Conservation of the Einstein tensor

The contracted Bianchi identity

`∇^a Ric_ab = (1/2) ∇_b S`

is a consequence of the second Bianchi identity together with metric
compatibility.  Taking it as a hypothesis (the differential identity itself is
not formalised here), this file proves:

* `divergence_combination` : for any `α, β`,
  `∇^a (α Ric + β S g)_b = (α/2 + β) ∇_b S`;
* `divergence_einstein_eq_zero` : the Einstein tensor is conserved,
  `∇^a G_ab = 0`;
* `combination_conserved_iff` : if `∇S` does not vanish, then `α Ric + β S g`
  is conserved **only if** `α = -2β`, so `G` is the unique conserved
  combination of `Ric` and `S g` up to scale.

The chart is Lorentzian and orthonormal, `g = ginv = η`, so indices are raised
and lowered with `η` and `η^{aa} η_ab = δ_ab`.  This is the same chart
convention as `Gravitation.Curvature`.
-/

namespace Gravitation

/-- Derivatives of the Ricci tensor and of the scalar curvature in an
orthonormal chart: `dRic e i j = ∂_e Ric_ij`, `dS e = ∂_e S`. -/
structure CurvDeriv where
  dRic : Fin 4 → Tensor2 4
  dS : Fin 4 → ℝ

/-- The derivative of the Einstein tensor, `∂_e G_ij = ∂_e Ric_ij − ½ ∂_e S η_ij`
(the metric is constant in an orthonormal chart, so `∂η = 0`). -/
noncomputable def CurvDeriv.dEinstein (D : CurvDeriv) (e : Fin 4) : Tensor2 4 :=
  fun i j => D.dRic e i j - (1 / 2) * D.dS e * eta4 i j

/-- Divergence of a family of rank-2 tensors in an orthonormal chart:
`∇^a T_ab = Σ_a η^{aa} ∂_a T_ab`. -/
noncomputable def divergence (T : Fin 4 → Tensor2 4) (b : Fin 4) : ℝ :=
  ∑ a, eta4 a a * T a a b

/-- `Σ_a f a · η^{aa} η_ab = f b`: raising and lowering with `η` is an inverse
operation. -/
theorem sum_eta_mul (f : Fin 4 → ℝ) (b : Fin 4) :
    (∑ a, f a * (eta4 a a * eta4 a b)) = f b := by
  fin_cases b <;> simp [Fin.sum_univ_four, eta4]

/-- **The divergence of a combination of `Ric` and `S g`.**  The contracted
Bianchi identity collapses `∇Ric` to `½∇S`, and `η^{aa} η_ab = δ_ab` collapses
the second term, leaving `(α/2 + β) ∇_b S`. -/
theorem divergence_combination (D : CurvDeriv)
    (hB : ∀ b, (∑ a, eta4 a a * D.dRic a a b) = (1 / 2) * D.dS b)
    (α β : ℝ) (b : Fin 4) :
    divergence (fun e i j => α * D.dRic e i j + β * D.dS e * eta4 i j) b
      = (α / 2 + β) * D.dS b := by
  have hterm : ∀ a,
      eta4 a a * (α * D.dRic a a b + β * D.dS a * eta4 a b)
        = α * (eta4 a a * D.dRic a a b)
          + β * (D.dS a * (eta4 a a * eta4 a b)) := by
    intro a
    ring
  simp only [divergence]
  rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hB b, sum_eta_mul (fun a => D.dS a) b]
  ring

/-- **The Einstein tensor is conserved**: the contracted Bianchi identity gives
`∇^a G_ab = 0`. -/
theorem divergence_einstein_eq_zero (D : CurvDeriv)
    (hB : ∀ b, (∑ a, eta4 a a * D.dRic a a b) = (1 / 2) * D.dS b) (b : Fin 4) :
    divergence D.dEinstein b = 0 := by
  have h := divergence_combination D hB 1 (-(1 / 2)) b
  have heq : D.dEinstein
      = fun e i j => 1 * D.dRic e i j + (-(1 / 2)) * D.dS e * eta4 i j := by
    funext e i j
    simp only [CurvDeriv.dEinstein]
    ring
  rw [heq, h]
  ring

/-- **Uniqueness of the Einstein combination.**  If `∇_b S ≠ 0` somewhere, then
`α Ric + β S g` is divergence free only when `α = -2β`, i.e. only for a multiple
of `G = Ric − ½ S g`. -/
theorem combination_conserved_iff (D : CurvDeriv)
    (hB : ∀ b, (∑ a, eta4 a a * D.dRic a a b) = (1 / 2) * D.dS b)
    (α β : ℝ) (hne : ∃ b, D.dS b ≠ 0)
    (h : ∀ b, divergence (fun e i j => α * D.dRic e i j + β * D.dS e * eta4 i j) b = 0) :
    α = -2 * β := by
  obtain ⟨b, hb⟩ := hne
  have h0 : (α / 2 + β) * D.dS b = 0 := by
    rw [← divergence_combination D hB α β b]
    exact h b
  have hc : α / 2 + β = 0 := by
    rcases mul_eq_zero.mp h0 with h1 | h2
    · exact h1
    · exact absurd h2 hb
  linarith

end Gravitation
