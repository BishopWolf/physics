/-
Copyright (c) 2026 The Gravitation formalisation contributors.
Released under Apache 2.0 license as described in the file LICENSE.

# Energy conservation for the 3D linear wave equation

This file instantiates the conditional 3D energy theorem with the physical flux
`F = u_t ∇u`.  The divergence identity

  div F = u_t Δu + ∇u · ∇u_t

is proved from the coordinate derivatives, the wave equation `u_tt = Δu`, and
the mixed-partial symmetry `∇u_t = (∇u)_t`.  Homogeneous Dirichlet data makes
the normal flux vanish on every face.
-/

module

public import Gravitation.WaveEnergy3DConservation

@[expose] public section

open MeasureTheory BoxIntegral
open scoped Topology

namespace GeneralRelativity

/-- The energy flux `F = u_t ∇u`. -/
noncomputable def waveFlux3D
    (ut : ℝ → Space3 → ℝ) (grad : ℝ → Space3 → Space3)
    (t : ℝ) (x : Space3) : Space3 :=
  ut t x • grad t x

/-- A derivative of the energy flux, built from the spatial derivatives of
`u_t` and `∇u`. -/
noncomputable def waveFlux3DDeriv
    (ut : ℝ → Space3 → ℝ) (grad : ℝ → Space3 → Space3)
    (Dut : ℝ → Space3 → Space3 →L[ℝ] ℝ)
    (Dgrad : ℝ → Space3 → Space3 →L[ℝ] Space3)
    (t : ℝ) (x : Space3) : Space3 →L[ℝ] Space3 :=
  (ut t x) • Dgrad t x + (Dut t x).smulRight (grad t x)

lemma hasFDerivAt_waveFlux3D
    (ut : ℝ → Space3 → ℝ) (grad : ℝ → Space3 → Space3)
    (Dut : ℝ → Space3 → Space3 →L[ℝ] ℝ)
    (Dgrad : ℝ → Space3 → Space3 →L[ℝ] Space3)
    (t : ℝ) (x : Space3)
    (hut : HasFDerivAt (ut t) (Dut t x) x)
    (hgrad : HasFDerivAt (grad t) (Dgrad t x) x) :
    HasFDerivAt (waveFlux3D ut grad t) (waveFlux3DDeriv ut grad Dut Dgrad t x) x := by
  simpa [waveFlux3D, waveFlux3DDeriv] using hut.smul hgrad

/-- **3D wave energy conservation.**  Under the wave equation
`u_tt = Δu`, mixed-partial symmetry, homogeneous Dirichlet data and the stated
regularity, the box energy is constant in time. -/
theorem waveEnergy3D_eq_initial_of_wave
    (ut utt : ℝ → Space3 → ℝ) (grad gradt : ℝ → Space3 → Space3)
    (Dut : ℝ → Space3 → Space3 →L[ℝ] ℝ)
    (Dgrad : ℝ → Space3 → Space3 →L[ℝ] Space3)
    (lap : ℝ → Space3 → ℝ) (I : Box (Fin 3)) (M : ℝ)
    (hut : ∀ s x, HasDerivAt (fun s : ℝ => ut s x) (utt s x) s)
    (hgrad : ∀ s x, HasDerivAt (fun s : ℝ => grad s x) (gradt s x) s)
    (hut_cont : Continuous (Function.uncurry ut))
    (hgrad_cont : Continuous (Function.uncurry grad))
    (hutt_cont : Continuous (Function.uncurry utt))
    (hgradt_cont : Continuous (Function.uncurry gradt))
    (hbound : ∀ s x, ‖waveEnergy3DDerivIntegrand ut utt grad gradt s x‖ ≤ M)
    (hut_spatial : ∀ t x, HasFDerivAt (ut t) (Dut t x) x)
    (hgrad_spatial : ∀ t x, HasFDerivAt (grad t) (Dgrad t x) x)
    (hlap : ∀ t x, (∑ i : Fin 3, Dgrad t x (Pi.single i 1) i) = lap t x)
    (hgradut : ∀ (t : ℝ) (x : Space3) (i : Fin 3),
      Dut t x (Pi.single i 1) = gradt t x i)
    (hwave : ∀ t x, utt t x = lap t x)
    (hdiv_int : ∀ s, IntegrableOn
      (fun x => ∑ i, waveFlux3DDeriv ut grad Dut Dgrad s x (Pi.single i 1) i)
      (Box.Icc I))
    (hut_face_upper : ∀ (s : ℝ) (i : Fin 3) (y : Fin 2 → ℝ),
      ut s (i.insertNth (I.upper i) y) = 0)
    (hut_face_lower : ∀ (s : ℝ) (i : Fin 3) (y : Fin 2 → ℝ),
      ut s (i.insertNth (I.lower i) y) = 0) :
    ∀ t, waveEnergy3D ut grad I t = waveEnergy3D ut grad I 0 := by
  have hF_cont : ∀ s, ContinuousOn (waveFlux3D ut grad s) (Box.Icc I) := by
    intro s
    have h1 : Continuous (fun x : Space3 => ut s x) :=
      hut_cont.comp (continuous_const.prodMk continuous_id)
    have h2 : Continuous (fun x : Space3 => grad s x) :=
      hgrad_cont.comp (continuous_const.prodMk continuous_id)
    exact (h1.smul h2).continuousOn
  have hF_deriv : ∀ s, ∀ x ∈ Box.Ioo I,
      HasFDerivAt (waveFlux3D ut grad s) (waveFlux3DDeriv ut grad Dut Dgrad s x) x := by
    intro s x hx
    exact hasFDerivAt_waveFlux3D ut grad Dut Dgrad s x
      (hut_spatial s x) (hgrad_spatial s x)
  have hface_upper : ∀ (s : ℝ) (i : Fin 3),
      (∫ y in Box.Icc (I.face i), waveFlux3D ut grad s (i.insertNth (I.upper i) y) i) = 0 := by
    intro s i
    simp [waveFlux3D, hut_face_upper s i]
  have hface_lower : ∀ (s : ℝ) (i : Fin 3),
      (∫ y in Box.Icc (I.face i), waveFlux3D ut grad s (i.insertNth (I.lower i) y) i) = 0 := by
    intro s i
    simp [waveFlux3D, hut_face_lower s i]
  have hdiv : ∀ s x,
      (∑ i : Fin 3, waveFlux3DDeriv ut grad Dut Dgrad s x (Pi.single i 1) i) =
        (1 / 2) * waveEnergy3DDerivIntegrand ut utt grad gradt s x := by
    intro s x
    have hleft : (∑ i : Fin 3, ut s x * (Dgrad s x (Pi.single i 1) i)) =
        ut s x * lap s x := by
      rw [← Finset.mul_sum, hlap s x]
    have hsum1 : (∑ i : Fin 3, gradt s x i * grad s x i) =
        ∑ i : Fin 3, grad s x i * gradt s x i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hsum3 : (∑ i : Fin 3, 2 * (grad s x i * gradt s x i)) =
        2 * ∑ i : Fin 3, grad s x i * gradt s x i := by
      rw [Finset.mul_sum]
    simp [waveFlux3DDeriv, waveEnergy3DDerivIntegrand, hgradut s x,
      Finset.sum_add_distrib, hleft, hwave s x, hsum1]
    rw [hsum3]
    ring
  exact waveEnergy3D_eq_initial_of_divergence ut utt grad gradt
    (waveFlux3D ut grad) (waveFlux3DDeriv ut grad Dut Dgrad) I M
    hut hgrad hut_cont hgrad_cont hutt_cont hgradt_cont hbound
    hF_cont hF_deriv hdiv_int hface_upper hface_lower hdiv

end GeneralRelativity
