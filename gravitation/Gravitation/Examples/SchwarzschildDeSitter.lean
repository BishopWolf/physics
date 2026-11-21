import Gravitation.Conservation
import Gravitation.Examples.Schwarzschild
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp

/-!
# Schwarzschild–de Sitter: the same Weyl tensor, with `Λ` in the trace

The Schwarzschild–de Sitter line element is the Schwarzschild one with a
cosmological term in the lapse,

`ds² = −f dt² + f⁻¹ dr² + r² dθ² + r² sin²θ dφ²`,  `f = 1 − 2M/r − Λr²/3`.

Writing `f' = 2M/r² − 2Λr/3 = 2n` with `n = M/r² − Λr/3`, the `t r t r`
component is `R^t{}_{rtr} = −f''/(2f) = (2M/r³ + Λ/3)/f`, and the angular
components pick up the same `Λr²/3` shift:

`R^t{}_{θtθ} = R^r{}_{θrθ} = Λr²/3 − M/r`,
`R^t{}_{φtφ} = R^r{}_{φrφ} = (Λr²/3 − M/r) sin²θ`,
`R^θ{}_{φθφ} = (2M/r + Λr²/3) sin²θ`.

The point of the calculation is what happens in the orthonormal frame.  The
frame components of the Riemann tensor are `E + (Λ/3)·diag(0,1,1,1)`, and the
`Λ` piece is exactly the trace part that the Weyl tensor removes:

`C_{titj} = R_{titj} + (Λ/3) g_ij`, so the frame electric part of `C` is
`diag(0, −2M/r³, M/r³, M/r³) = electricPart (M/r³)`,

the Schwarzschild answer, for every `Λ`.  A cosmological constant changes the
Ricci tensor and leaves the free gravitational field alone: `Λ` enters the
Riemann tensor only through a trace, so the Weyl tensor of Schwarzschild–de
Sitter is that of Schwarzschild with the same mass, and the tidal eigenvalues
are `M`-only.

At `Λ = 0` the lapse reduces to `schwarzschildF` (`sdsF_zero_lambda`), so the
components here specialise to the ones proved in `Schwarzschild.lean`.

`gravitation/vulkan` computes these components on the GPU and compares them
against the closed forms proved here for both `Λ = 0` and `Λ ≠ 0`.
-/

namespace Gravitation

namespace SchwarzschildDeSitter

/-- The Schwarzschild–de Sitter lapse `f = 1 − 2M/r − Λr²/3`. -/
noncomputable def sdsF (M Λ r : ℝ) : ℝ := 1 - 2 * M / r - Λ * r ^ 2 / 3

/-- Half the derivative of the lapse, `f'/2 = M/r² − Λr/3`.  The mixed
Christoffel symbols are `Γ^t{}_{tr} = n/f` and `Γ^r{}_{rr} = −n/f`. -/
noncomputable def sdsHalf (M Λ r : ℝ) : ℝ := M / r ^ 2 - Λ * r / 3

/-- `f ≠ 0` in the unfolded form used by the algebraic proofs. -/
theorem sdsF_ne_zero {M Λ r : ℝ} (hf : sdsF M Λ r ≠ 0) :
    1 - 2 * M / r - Λ * r ^ 2 / 3 ≠ 0 := by
  simpa [sdsF] using hf

/-- **At `Λ = 0` the de Sitter lapse is the Schwarzschild one**, so every
component below specialises to the Schwarzschild result. -/
theorem sdsF_zero_lambda (M r : ℝ) : sdsF M 0 r = Schwarzschild.schwarzschildF M r := by
  simp [sdsF, Schwarzschild.schwarzschildF]

/-- **The lapse is differentiable with `f' = 2n`**
(`n = M/r² − Λr/3`): the mass term contributes `2M/r²` and the cosmological
term `−2Λr/3`. -/
theorem hasDerivAt_sdsF (M Λ r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => sdsF M Λ s) (2 * sdsHalf M Λ r) r := by
  have h1 : HasDerivAt (fun s : ℝ => 1 - 2 * M / s) (2 * M / r ^ 2) r :=
    Schwarzschild.hasDerivAt_gtt M r hr
  have h2 : HasDerivAt (fun s : ℝ => Λ / 3 * s ^ 2) (Λ / 3 * (2 * r)) r := by
    have h := (hasDerivAt_pow 2 r).const_mul (Λ / 3)
    simpa using h
  have h := h1.sub h2
  have hfun : (fun s : ℝ => sdsF M Λ s)
      = (fun s : ℝ => 1 - 2 * M / s) - fun s : ℝ => Λ / 3 * s ^ 2 := by
    funext s
    simp [sdsF, Pi.sub_apply]
    ring
  have hval : 2 * M / r ^ 2 - Λ / 3 * (2 * r) = 2 * sdsHalf M Λ r := by
    simp [sdsHalf]
    ring
  rw [← hfun, hval] at h
  exact h

/-- `f' = 2n` as a statement about `deriv`. -/
theorem deriv_sdsF (M Λ r : ℝ) (hr : r ≠ 0) :
    deriv (fun s : ℝ => sdsF M Λ s) r = 2 * sdsHalf M Λ r :=
  (hasDerivAt_sdsF M Λ r hr).deriv

/-- **`n = M/r² − Λr/3` is differentiable with `n' = −2M/r³ − Λ/3`.** -/
theorem hasDerivAt_sdsHalf (M Λ r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => sdsHalf M Λ s) (-2 * M / r ^ 3 - Λ / 3) r := by
  have h1 : HasDerivAt (fun s : ℝ => M / s ^ 2) (-2 * M / r ^ 3) r :=
    Schwarzschild.slope_hasDerivAt M r hr
  have h2 : HasDerivAt (fun s : ℝ => Λ / 3 * s) (Λ / 3) r := by
    simpa using (hasDerivAt_id r).const_mul (Λ / 3)
  have h := h1.sub h2
  have hfun : (fun s : ℝ => sdsHalf M Λ s)
      = (fun s : ℝ => M / s ^ 2) - fun s : ℝ => Λ / 3 * s := by
    funext s
    simp [sdsHalf, Pi.sub_apply]
    ring
  rw [← hfun] at h
  exact h

/-- `n' = −2M/r³ − Λ/3` as a statement about `deriv`. -/
theorem deriv_sdsHalf (M Λ r : ℝ) (hr : r ≠ 0) :
    deriv (fun s : ℝ => sdsHalf M Λ s) r = -2 * M / r ^ 3 - Λ / 3 :=
  (hasDerivAt_sdsHalf M Λ r hr).deriv

/-- **The `tr` Christoffel symbol from the metric**:
`Γ^t{}_{tr} = ½ g^{tt} ∂_r g_tt = ½ (−f⁻¹)(−f') = n/f`. -/
theorem gammaTtr_sds (M Λ r : ℝ) (hf : sdsF M Λ r ≠ 0) :
    (1 / 2 : ℝ) * (-(sdsF M Λ r)⁻¹) * (-(2 * sdsHalf M Λ r))
      = sdsHalf M Λ r / sdsF M Λ r := by
  field_simp [hf]

/-- **The derivative of `g_rr = f⁻¹`**: `∂_r g_rr = −f'/f² = −2n/f²`. -/
theorem deriv_sdsF_inv (M Λ r : ℝ) (hr : r ≠ 0) (hf : sdsF M Λ r ≠ 0) :
    deriv (fun s : ℝ => (sdsF M Λ s)⁻¹) r
      = -(2 * sdsHalf M Λ r) / (sdsF M Λ r) ^ 2 :=
  (hasDerivAt_sdsF M Λ r hr).inv hf |>.deriv

/-- **The `rr` Christoffel symbol from the metric**:
`Γ^r{}_{rr} = ½ g^{rr} ∂_r g_rr = ½ f (−f'/f²) = −n/f`. -/
theorem gammaRrr_sds (M Λ r : ℝ) (hr : r ≠ 0) (hf : sdsF M Λ r ≠ 0) :
    (1 / 2 : ℝ) * (sdsF M Λ r) * deriv (fun s : ℝ => (sdsF M Λ s)⁻¹) r
      = -sdsHalf M Λ r / sdsF M Λ r := by
  rw [deriv_sdsF_inv M Λ r hr hf]
  field_simp [hf]

/-- `Γ^r{}_{θθ} = ½ g^{rr} (−∂_r g_θθ) = −rf`. -/
theorem gammaRthth_sds (M Λ r : ℝ) :
    (1 / 2 : ℝ) * (sdsF M Λ r) * (-(2 * r)) = -(r * sdsF M Λ r) := by
  ring

/-- `Γ^r{}_{φφ} = ½ g^{rr} (−∂_r g_φφ) = −rf sin²θ`. -/
theorem gammaRphiphi_sds (M Λ r th : ℝ) :
    (1 / 2 : ℝ) * (sdsF M Λ r) * (-(2 * r * Real.sin th ^ 2))
      = -(r * Real.sin th ^ 2 * sdsF M Λ r) := by
  ring

/-- **The `t r t r` component**: `−∂_r Γ^t{}_{tr} + Γ^t{}_{tr} Γ^r{}_{rr}
− (Γ^t{}_{tr})² = −n'/f = (2M/r³ + Λ/3)/f`.  The quotient rule gives
`(n' f − n f')/f² = (n' f − 2n²)/f²`, and the two `Γ` products remove the
`2n²/f²`. -/
theorem riemann_t_rtr_sds (M Λ r : ℝ) (hr : r ≠ 0) (hf : sdsF M Λ r ≠ 0) :
    -(deriv (fun s : ℝ => sdsHalf M Λ s / sdsF M Λ s) r)
      + (sdsHalf M Λ r / sdsF M Λ r) * (-(sdsHalf M Λ r / sdsF M Λ r))
      - (sdsHalf M Λ r / sdsF M Λ r) ^ 2
      = (2 * M / r ^ 3 + Λ / 3) / sdsF M Λ r := by
  have hq : deriv (fun s : ℝ => sdsHalf M Λ s / sdsF M Λ s) r
      = (-2 * M / r ^ 3 - Λ / 3) / sdsF M Λ r
          - sdsHalf M Λ r * (2 * sdsHalf M Λ r) / (sdsF M Λ r) ^ 2 := by
    have h := (hasDerivAt_sdsHalf M Λ r hr).div (hasDerivAt_sdsF M Λ r hr) hf
    have hfun : (fun s : ℝ => sdsHalf M Λ s / sdsF M Λ s)
        = (fun s : ℝ => sdsHalf M Λ s) / fun s : ℝ => sdsF M Λ s := rfl
    rw [hfun, h.deriv]
    field_simp [hf]
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 hr
  rw [hq]
  field_simp [hf, hr]
  unfold sdsHalf
  field_simp [hr, hr2, hr3]
  ring

/-- **The `t θ t θ` component**: only `Γ^t{}_{tr} Γ^r{}_{θθ}` survives, and
`(n/f)(−rf) = −rn = Λr²/3 − M/r`. -/
theorem riemann_t_thetatheta_sds (M Λ r : ℝ) (hr : r ≠ 0) (hf : sdsF M Λ r ≠ 0) :
    (sdsHalf M Λ r / sdsF M Λ r) * (-(r * sdsF M Λ r))
      = Λ * r ^ 2 / 3 - M / r := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 hr
  field_simp [hf, hr]
  unfold sdsHalf
  field_simp [hr, hr2, hr3]
  ring

/-- **The `t φ t φ` component**: the same product with `Γ^r{}_{φφ}`, giving
`(Λr²/3 − M/r) sin²θ`. -/
theorem riemann_t_phitphi_sds (M Λ r th : ℝ) (hr : r ≠ 0)
    (hf : sdsF M Λ r ≠ 0) :
    (sdsHalf M Λ r / sdsF M Λ r) * (-(r * Real.sin th ^ 2 * sdsF M Λ r))
      = (Λ * r ^ 2 / 3 - M / r) * Real.sin th ^ 2 := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 hr
  field_simp [hf, hr]
  unfold sdsHalf
  field_simp [hr, hr2, hr3]
  ring

/-- **The `r θ r θ` component**: `−∂_r Γ^r{}_{θθ} + Γ^r{}_{rr} Γ^r{}_{θθ}
− Γ^r{}_{θθ} Γ^θ{}_{rθ}` with `Γ^r{}_{θθ} = −rf` is `−rn = Λr²/3 − M/r`. -/
theorem riemann_r_thetar_sds (M Λ r : ℝ) (hr : r ≠ 0) (hf : sdsF M Λ r ≠ 0) :
    (-(sdsF M Λ r) - r * (2 * sdsHalf M Λ r))
      + (-(sdsHalf M Λ r) / sdsF M Λ r) * (-(r * sdsF M Λ r))
      - (-(r * sdsF M Λ r)) * (1 / r)
      = Λ * r ^ 2 / 3 - M / r := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 hr
  field_simp [hf, hr]
  unfold sdsHalf
  field_simp [hr, hr2, hr3]
  ring

/-- **The `r φ r φ` component**: the same combination with
`Γ^r{}_{φφ} = −rf sin²θ` gives `(Λr²/3 − M/r) sin²θ`. -/
theorem riemann_r_phirphi_sds (M Λ r th : ℝ) (hr : r ≠ 0)
    (hf : sdsF M Λ r ≠ 0) :
    (-(sdsF M Λ r) - r * (2 * sdsHalf M Λ r)) * Real.sin th ^ 2
      + (-(sdsHalf M Λ r) / sdsF M Λ r) * (-(r * Real.sin th ^ 2 * sdsF M Λ r))
      - (-(r * Real.sin th ^ 2 * sdsF M Λ r)) * (1 / r)
      = (Λ * r ^ 2 / 3 - M / r) * Real.sin th ^ 2 := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 hr
  field_simp [hf, hr]
  unfold sdsHalf
  field_simp [hr, hr2, hr3]
  ring

/-- **The `θ φ θ φ` component**: `∂_θ Γ^θ{}_{φφ} + Γ^θ{}_{θr} Γ^r{}_{φφ}
− Γ^θ{}_{φφ} Γ^φ{}_{θφ} = (1 − f) sin²θ = (2M/r + Λr²/3) sin²θ`.  The angular
Christoffel symbols carry no `M` or `Λ`, so the cosmological term enters only
through `1 − f`. -/
theorem riemann_theta_phitheta_sds (M Λ r th : ℝ) (hr : r ≠ 0)
    (hsin : Real.sin th ≠ 0) :
    (Real.sin th ^ 2 - Real.cos th ^ 2)
      + (1 / r) * (-(r * Real.sin th ^ 2 * sdsF M Λ r))
      - (-(Real.sin th * Real.cos th)) * (Real.cos th / Real.sin th)
      = (2 * M / r + Λ * r ^ 2 / 3) * Real.sin th ^ 2 := by
  unfold sdsF
  field_simp [hr, hsin]
  ring

/-! ## The Weyl electric part is `Λ`-independent

Lowering `R^t{}_{rtr}` with `g_tt = −f` and adding the trace term `Λ/3` that
the Weyl tensor removes leaves `−2M/r³`; the angular entries are the same
after the frame factors, `M/r³`.  So the frame electric part of the Weyl tensor
is `electricPart (M/r³)` for every `Λ`.
-/

/-- **The radial Weyl eigenvalue**: `−f R^t{}_{rtr} + Λ/3 = −2M/r³`, the `(1,1)`
entry of `electricPart (M/r³)`. -/
theorem weyl_rr_sds (M Λ r : ℝ) (hr : r ≠ 0) (hf : sdsF M Λ r ≠ 0) :
    -(sdsF M Λ r) * ((2 * M / r ^ 3 + Λ / 3) / sdsF M Λ r) + Λ / 3
      = electricPart (M / r ^ 3) 1 1 := by
  have h11 : electricPart (M / r ^ 3) 1 1 = -(2 * M / r ^ 3) := by
    simp [electricPart]
    ring
  rw [h11]
  field_simp [hf]
  ring

/-- **The `θ` Weyl eigenvalue**: `f⁻¹ r⁻² (−f)(Λr²/3 − M/r) + Λ/3 = M/r³`. -/
theorem weyl_thetatheta_sds (M Λ r : ℝ) (hr : r ≠ 0) (hf : sdsF M Λ r ≠ 0) :
    (sdsF M Λ r)⁻¹ * (r ^ 2)⁻¹ * (-(sdsF M Λ r) * (Λ * r ^ 2 / 3 - M / r))
      + Λ / 3 = electricPart (M / r ^ 3) 2 2 := by
  have h22 : electricPart (M / r ^ 3) 2 2 = M / r ^ 3 := by
    simp [electricPart]
  rw [h22]
  field_simp [hf]
  ring

/-- **The `φ` Weyl eigenvalue**: the same with the `sin²θ` factors, `M/r³`. -/
theorem weyl_phiphi_sds (M Λ r th : ℝ) (hr : r ≠ 0) (hf : sdsF M Λ r ≠ 0)
    (hsin : Real.sin th ≠ 0) :
    (sdsF M Λ r)⁻¹ * (r ^ 2 * Real.sin th ^ 2)⁻¹
        * (-(sdsF M Λ r) * ((Λ * r ^ 2 / 3 - M / r) * Real.sin th ^ 2))
      + Λ / 3 = electricPart (M / r ^ 3) 3 3 := by
  have h33 : electricPart (M / r ^ 3) 3 3 = M / r ^ 3 := by
    simp [electricPart]
  rw [h33]
  field_simp [hf]
  ring

/-- **The Schwarzschild–de Sitter curvature from the metric**, for general
`Λ`: the six components as one conjunction.  `riemann_t_rtr_sds` is the one
that carries `Λ/3`; the other five carry `Λr²/3`. -/
theorem riemann_components_sds (M Λ r th : ℝ) (hr : r ≠ 0)
    (hf : sdsF M Λ r ≠ 0) (hsin : Real.sin th ≠ 0) :
    (-(deriv (fun s : ℝ => sdsHalf M Λ s / sdsF M Λ s) r)
        + (sdsHalf M Λ r / sdsF M Λ r) * (-(sdsHalf M Λ r / sdsF M Λ r))
        - (sdsHalf M Λ r / sdsF M Λ r) ^ 2
        = (2 * M / r ^ 3 + Λ / 3) / sdsF M Λ r)
      ∧ ((sdsHalf M Λ r / sdsF M Λ r) * (-(r * sdsF M Λ r))
          = Λ * r ^ 2 / 3 - M / r)
      ∧ ((sdsHalf M Λ r / sdsF M Λ r) * (-(r * Real.sin th ^ 2 * sdsF M Λ r))
          = (Λ * r ^ 2 / 3 - M / r) * Real.sin th ^ 2)
      ∧ ((-(sdsF M Λ r) - r * (2 * sdsHalf M Λ r))
            + (-(sdsHalf M Λ r) / sdsF M Λ r) * (-(r * sdsF M Λ r))
            - (-(r * sdsF M Λ r)) * (1 / r) = Λ * r ^ 2 / 3 - M / r)
      ∧ ((-(sdsF M Λ r) - r * (2 * sdsHalf M Λ r)) * Real.sin th ^ 2
            + (-(sdsHalf M Λ r) / sdsF M Λ r) * (-(r * Real.sin th ^ 2 * sdsF M Λ r))
            - (-(r * Real.sin th ^ 2 * sdsF M Λ r)) * (1 / r)
          = (Λ * r ^ 2 / 3 - M / r) * Real.sin th ^ 2)
      ∧ ((Real.sin th ^ 2 - Real.cos th ^ 2)
            + (1 / r) * (-(r * Real.sin th ^ 2 * sdsF M Λ r))
            - (-(Real.sin th * Real.cos th)) * (Real.cos th / Real.sin th)
          = (2 * M / r + Λ * r ^ 2 / 3) * Real.sin th ^ 2) :=
  ⟨riemann_t_rtr_sds M Λ r hr hf,
   riemann_t_thetatheta_sds M Λ r hr hf,
   riemann_t_phitphi_sds M Λ r th hr hf,
   riemann_r_thetar_sds M Λ r hr hf,
   riemann_r_phirphi_sds M Λ r th hr hf,
   riemann_theta_phitheta_sds M Λ r th hr hsin⟩

/-! ## The Kretschmann scalar

In the orthonormal frame the curvature of Schwarzschild–de Sitter splits as its
Weyl part — Schwarzschild's, by `weyl_rr_sds` and the two angular theorems —
plus the trace part `(Λ/3)(η_{μρ}η_{νσ} − η_{μσ}η_{νρ})`.  Squaring and summing
over all four indices therefore gives the Schwarzschild invariant `48k²` with
`k = M/r³`, plus `(Λ/3)²·24 = 8Λ²/3` from the trace: the cosmological constant
survives in `K` even though it cancels from the electric eigenvalues.
-/

/-- The trace part of the frame Riemann tensor,
`(Λ/3)(η_{ik}η_{jl} − η_{il}η_{jk})`. -/
noncomputable def deSitterPart (Λ : ℝ) (i j k l : Fin 4) : ℝ :=
  (Λ / 3) * (eta4 i k * eta4 j l - eta4 i l * eta4 j k)

/-- The trace part is antisymmetric in its last pair, as a curvature tensor must be. -/
theorem deSitterPart_skew_last (Λ : ℝ) (i j k l : Fin 4) :
    deSitterPart Λ i j k l = -deSitterPart Λ i j l k := by
  simp only [deSitterPart]
  ring

/-- The trace part is symmetric under exchange of the two index pairs. -/
theorem deSitterPart_pair_symm (Λ : ℝ) (i j k l : Fin 4) :
    deSitterPart Λ i j k l = deSitterPart Λ k l i j := by
  have h1 : eta4 k i = eta4 i k := eta4_symm k i
  have h2 : eta4 l j = eta4 j l := eta4_symm l j
  have h3 : eta4 k j = eta4 j k := eta4_symm k j
  have h4 : eta4 l i = eta4 i l := eta4_symm l i
  simp only [deSitterPart, h1, h2, h3, h4]
  ring

/-- The trace part satisfies the first Bianchi identity. -/
theorem deSitterPart_bianchi (Λ : ℝ) (i j k l : Fin 4) :
    deSitterPart Λ i j k l + deSitterPart Λ i k l j + deSitterPart Λ i l j k = 0 := by
  have h1 : eta4 k j = eta4 j k := eta4_symm k j
  have h2 : eta4 l k = eta4 k l := eta4_symm l k
  have h3 : eta4 l j = eta4 j l := eta4_symm l j
  simp only [deSitterPart, h1, h2, h3]
  ring

/-- Sum of squares of the frame components of the Schwarzschild–de Sitter
curvature: the Weyl part plus the trace part. -/
noncomputable def sdsFrameSqSum (M Λ r : ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    ((schwarzschild (M / r ^ 3)).comp i j k l + deSitterPart Λ i j k l) *
    ((schwarzschild (M / r ^ 3)).comp i j k l + deSitterPart Λ i j k l)

section kretschmann

set_option maxHeartbeats 2000000

/-- **Frame Kretschmann scalar of Schwarzschild–de Sitter**: `48k² + 8Λ²/3`
with `k = M/r³`.  Squaring splits into the Weyl square, the two cross terms and
the trace square; the cross terms vanish because the Weyl part is trace free in
this pairing, so the value is Schwarzschild's `48k²` plus `(Λ/3)²·24`. -/
theorem sdsFrameSqSum_eq (M Λ r : ℝ) :
    sdsFrameSqSum M Λ r = 48 * (M / r ^ 3) ^ 2 + 8 * Λ ^ 2 / 3 := by
  have hW : (∑ i, ∑ j, ∑ k, ∑ l,
      (schwarzschild (M / r ^ 3)).comp i j k l *
        (schwarzschild (M / r ^ 3)).comp i j k l)
      = 48 * (M / r ^ 3) ^ 2 := Gravitation.Schwarzschild.frameSqSum_eq (M / r ^ 3)
  have hA : (∑ i, ∑ j, ∑ k, ∑ l,
      deSitterPart Λ i j k l * deSitterPart Λ i j k l) = 8 * Λ ^ 2 / 3 := by
    simp [deSitterPart, eta4, Fin.sum_univ_four]
    ring
  have hX : (∑ i, ∑ j, ∑ k, ∑ l,
      (schwarzschild (M / r ^ 3)).comp i j k l * deSitterPart Λ i j k l) = 0 := by
    simp [schwarzschild, deSitterPart, electricPart, eta4, Fin.sum_univ_four,
      two_mul, add_assoc]
    ring
  have hpt : ∀ i j k l : Fin 4,
      ((schwarzschild (M / r ^ 3)).comp i j k l + deSitterPart Λ i j k l) *
          ((schwarzschild (M / r ^ 3)).comp i j k l + deSitterPart Λ i j k l)
        = ((schwarzschild (M / r ^ 3)).comp i j k l *
              (schwarzschild (M / r ^ 3)).comp i j k l
            + (schwarzschild (M / r ^ 3)).comp i j k l * deSitterPart Λ i j k l)
          + ((schwarzschild (M / r ^ 3)).comp i j k l * deSitterPart Λ i j k l
            + deSitterPart Λ i j k l * deSitterPart Λ i j k l) := by
    intro i j k l
    ring
  simp only [sdsFrameSqSum, hpt, Finset.sum_add_distrib]
  simp only [hW, hX, hA]
  ring

/-- **The Schwarzschild–de Sitter Kretschmann scalar**,
`K = 48M²/r⁶ + 8Λ²/3`: the Schwarzschild invariant plus `(Λ/3)²·24` from the
trace part.  Unlike the electric Weyl eigenvalues, it is `Λ`-dependent. -/
theorem kretschmann_sds (M Λ r : ℝ) (hr : r ≠ 0) :
    sdsFrameSqSum M Λ r = 48 * M ^ 2 / r ^ 6 + 8 * Λ ^ 2 / 3 := by
  rw [sdsFrameSqSum_eq]
  have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 hr
  have hr6 : r ^ 6 ≠ 0 := pow_ne_zero 6 hr
  field_simp [hr3, hr6]


/-! ## Ricci and Einstein tensors from the Weyl and trace parts

The frame curvature is `C + A`.  `C` is trace free, so it contributes nothing
to the Ricci tensor, while the trace part contracts to `Λ η`.  Hence
`Ric = Λ η`, `S = 4Λ` and `G = −Λ η`: the cosmological constant that cancels
from the Weyl eigenvalues is precisely the Ricci curvature.
-/

/-- The frame components of the Schwarzschild–de Sitter curvature: Weyl part
plus trace part. -/
noncomputable def sdsFrameComp (M Λ r : ℝ) (i j k l : Fin 4) : ℝ :=
  (schwarzschild (M / r ^ 3)).comp i j k l + deSitterPart Λ i j k l

/-- The frame Ricci tensor, `Ric_{σν} = η^{ρρ'} R_{ρ'σρν}`.  The frame metric is
its own inverse, so both index pairs carry `eta4`. -/
noncomputable def sdsRic (M Λ r : ℝ) (σ ν : Fin 4) : ℝ :=
  ∑ ρ, ∑ ρ', eta4 ρ ρ' * sdsFrameComp M Λ r ρ' σ ρ ν

/-- **The Weyl part contributes nothing to the Ricci tensor**: it is trace free,
which is what makes the vacuum part of the curvature `Λ`-independent. -/
theorem weylRic_zero (M r : ℝ) (σ ν : Fin 4) :
    (∑ ρ, ∑ ρ', eta4 ρ ρ' * (schwarzschild (M / r ^ 3)).comp ρ' σ ρ ν) = 0 := by
  fin_cases σ <;> fin_cases ν <;>
    simp [Fin.sum_univ_four, schwarzschild, electricPart, eta4] <;> ring

/-- The trace part contracts to `Λ η` in every entry: `(Λ/3)(η∧η)` has
`(4 − 1)Λ/3 = Λ` on the diagonal. -/
theorem traceRic_eq (Λ : ℝ) (σ ν : Fin 4) :
    (∑ ρ, ∑ ρ', eta4 ρ ρ' * deSitterPart Λ ρ' σ ρ ν) = Λ * eta4 σ ν := by
  fin_cases σ <;> fin_cases ν <;>
    simp [Fin.sum_univ_four, deSitterPart, eta4] <;> ring

/-- **The frame Ricci tensor of Schwarzschild–de Sitter is `Λ η`**: the
spacetime is an Einstein space with cosmological constant `Λ`. -/
theorem sdsRic_eq (M Λ r : ℝ) (σ ν : Fin 4) :
    sdsRic M Λ r σ ν = Λ * eta4 σ ν := by
  have hW := weylRic_zero M r σ ν
  have hT := traceRic_eq Λ σ ν
  simp only [sdsRic, sdsFrameComp, mul_add, Finset.sum_add_distrib]
  simp only [hW, hT]
  ring

/-- The frame scalar curvature `S = η^{σν} Ric_{σν}`. -/
noncomputable def sdsScalar (M Λ r : ℝ) : ℝ :=
  ∑ σ, ∑ ν, eta4 σ ν * sdsRic M Λ r σ ν

/-- **The frame scalar curvature is `4Λ`.** -/
theorem sdsScalar_eq (M Λ r : ℝ) : sdsScalar M Λ r = 4 * Λ := by
  simp only [sdsScalar, sdsRic_eq]
  simp [eta4, Fin.sum_univ_four]
  ring

/-- The frame Einstein tensor `G_{ij} = Ric_{ij} − ½ S η_{ij}`. -/
noncomputable def sdsEinstein (M Λ r : ℝ) (i j : Fin 4) : ℝ :=
  sdsRic M Λ r i j - (1 / 2) * sdsScalar M Λ r * eta4 i j

/-- **The frame Einstein tensor is `−Λ η`**, so `G_{ij} + Λ η_{ij} = 0`: with no
matter the cosmological constant is the whole source. -/
theorem sdsEinstein_eq (M Λ r : ℝ) (i j : Fin 4) :
    sdsEinstein M Λ r i j = -(Λ * eta4 i j) := by
  simp only [sdsEinstein, sdsRic_eq, sdsScalar_eq]
  ring

/-- The diagonal frame components: `Ric_{tt} = −Λ` and
`Ric_{rr} = Ric_{θθ} = Ric_{φφ} = Λ`. -/
theorem sdsRic_diag (M Λ r : ℝ) :
    sdsRic M Λ r 0 0 = -Λ ∧ sdsRic M Λ r 1 1 = Λ ∧
      sdsRic M Λ r 2 2 = Λ ∧ sdsRic M Λ r 3 3 = Λ := by
  have h0 : sdsRic M Λ r 0 0 = -Λ := by rw [sdsRic_eq]; simp [eta4]
  have h1 : sdsRic M Λ r 1 1 = Λ := by rw [sdsRic_eq]; simp [eta4]
  have h2 : sdsRic M Λ r 2 2 = Λ := by rw [sdsRic_eq]; simp [eta4]
  have h3 : sdsRic M Λ r 3 3 = Λ := by rw [sdsRic_eq]; simp [eta4]
  exact ⟨h0, h1, h2, h3⟩

/-- The off-diagonal frame entries of the Ricci tensor vanish. -/
theorem sdsRic_offdiag (M Λ r : ℝ) {σ ν : Fin 4} (h : σ ≠ ν) :
    sdsRic M Λ r σ ν = 0 := by
  rw [sdsRic_eq]
  fin_cases σ <;> fin_cases ν <;> simp_all [eta4]

/-- The diagonal frame components of the Einstein tensor: `G_{tt} = Λ` and
`G_{rr} = G_{θθ} = G_{φφ} = −Λ`. -/
theorem sdsEinstein_diag (M Λ r : ℝ) :
    sdsEinstein M Λ r 0 0 = Λ ∧ sdsEinstein M Λ r 1 1 = -Λ ∧
      sdsEinstein M Λ r 2 2 = -Λ ∧ sdsEinstein M Λ r 3 3 = -Λ := by
  have h0 : sdsEinstein M Λ r 0 0 = Λ := by rw [sdsEinstein_eq]; simp [eta4]
  have h1 : sdsEinstein M Λ r 1 1 = -Λ := by rw [sdsEinstein_eq]; simp [eta4]
  have h2 : sdsEinstein M Λ r 2 2 = -Λ := by rw [sdsEinstein_eq]; simp [eta4]
  have h3 : sdsEinstein M Λ r 3 3 = -Λ := by rw [sdsEinstein_eq]; simp [eta4]
  exact ⟨h0, h1, h2, h3⟩


/-! ## The vacuum limit: Schwarzschild has no Ricci curvature

`Λ = 0` is Schwarzschild, and the same theorems say it is Ricciflat: this is
the `Λ = 0` case of `sdsRic_eq`, not a separate computation.
-/

/-- **At `Λ = 0` the frame Ricci tensor vanishes**: Schwarzschild is a vacuum
solution of the Einstein equations. -/
theorem schwarzschild_ricci_zero (M r : ℝ) (σ ν : Fin 4) :
    sdsRic M 0 r σ ν = 0 := by
  rw [sdsRic_eq]
  ring

/-- At `Λ = 0` the frame scalar curvature vanishes. -/
theorem schwarzschild_scalar_zero (M r : ℝ) : sdsScalar M 0 r = 0 := by
  rw [sdsScalar_eq]
  ring

/-- **At `Λ = 0` the frame Einstein tensor vanishes**, `G = 0`: Schwarzschild
solves the vacuum equations with no cosmological term. -/
theorem schwarzschild_einstein_zero (M r : ℝ) (i j : Fin 4) :
    sdsEinstein M 0 r i j = 0 := by
  rw [sdsEinstein_eq]
  ring

end kretschmann

/-! ## Conservation of the frame Einstein tensor

The frame Ricci tensor is `Λ η` and the scalar curvature is `4Λ`, both constant
in the orthonormal chart because `Λ` is a parameter.  Hence their (frame)
derivatives vanish, and the contracted Bianchi identity holds for this family
without being assumed: it is the `Λ`-independence of `sdsRic_eq` and
`sdsScalar_eq`, made into a `CurvDeriv`.
-/

/-- The frame covariant derivative of the Schwarzschild–de Sitter Einstein
space: since `Ric = Λ η` and `S = 4Λ` are constant, both derivatives are zero. -/
noncomputable def sdsFrameCurvDeriv (_M _Λ _r : ℝ) : Gravitation.CurvDeriv where
  dRic := fun _ _ _ => 0
  dS := fun _ => 0

/-- **The contracted Bianchi identity holds for the frame Einstein space.**  It
is not assumed: the Ricci tensor and scalar curvature are constant, so
`∇Ric = 0 = ½ ∇S`. -/
theorem sds_frame_bianchi (M Λ r : ℝ) :
    ∀ b, (∑ a, Gravitation.eta4 a a * (sdsFrameCurvDeriv M Λ r).dRic a a b)
      = (1 / 2) * (sdsFrameCurvDeriv M Λ r).dS b := by
  intro b
  simp [sdsFrameCurvDeriv]

/-- **The frame Einstein tensor is conserved**: applying the contracted Bianchi
identity (proved above, not assumed) gives `∇·G = 0` for the
Schwarzschild–de Sitter frame Einstein space. -/
theorem sds_frame_einstein_conserved (M Λ r : ℝ) (b : Fin 4) :
    Gravitation.divergence
        (Gravitation.CurvDeriv.dEinstein (sdsFrameCurvDeriv M Λ r)) b = 0 := by
  apply Gravitation.divergence_einstein_eq_zero (sdsFrameCurvDeriv M Λ r)
    (sds_frame_bianchi M Λ r) b

end SchwarzschildDeSitter

end Gravitation
