/-
Copyright (c) 2026 The Gravitation formalisation contributors.
Released under Apache 2.0 license as described in the file LICENSE.

# M6: Explicit-solution cross-checks and inhabited explicit development certificate

This module instantiates `ExplicitDevelopmentObligations` with non-vacuous
4D Einstein field-equation + `t = 0` spatial-slice / initial-data statements and
proves **`explicitSolutions_certificate : ExplicitDevelopmentCertificate explicitSolutionObligations`**,
recovering all four explicit spacetimes directly from the vendored metric-pipeline
theorems and the curved 3D initial-data theorems in `SobolevInitialData`:

1. **Schwarzschild (`schwarzschild_explicit_development`)**:
   4D vacuum Einstein equation `einsteinOf (schwarzschildG M) (schwarzschildGinv M) = 0`
   together with `t = 0` spatial-metric agreement with `sdsSpatialMetric M 0`
   and vanishing nonlinear 3D Hamiltonian constraint.
2. **Schwarzschild–de Sitter (`sds_explicit_development`)**:
   4D cosmological Einstein equation `einsteinOf (sdsMetric M Λ) (sdsMetricInv M Λ) + Λ g = 0`
   together with `t = 0` spatial-metric agreement with `sdsSpatialMetric M Λ`
   and 3D spatial scalar curvature `³R = 2 Λ`.
3. **Kerr (`kerr_explicit_development`)**:
   4D rotating vacuum Einstein equation `einsteinOf (kerrMetric M a) (kerrMetricInv M a) = 0`
   together with symmetry and `t = 0` spatial/shift slice components.
4. **FLRW (`flrw_explicit_development`)**:
   4D Einstein–Friedmann equivalence `G_{ij} + Λ g_{ij} = 8 π G T_{ij}`
   together with the flat (`k = 0`) `t = 0` spatial scale-factor metric components.
-/

module

public import Gravitation.CauchyInterfaces
public import Gravitation.SobolevInitialData
public import Gravitation.Relativity.General.SchwarzschildDeSitter.Pipeline
public import Gravitation.Relativity.General.Kerr.Vacuum
public import Gravitation.Relativity.General.FLRW.Pipeline

@[expose] public section

namespace GeneralRelativity

/-- Non-vacuous M6 explicit-solution obligations pairing the full 4D Einstein
equations with `t = 0` spatial-slice restrictions and initial-data checks for
Schwarzschild, Schwarzschild–de Sitter, Kerr, and FLRW. -/
def explicitSolutionObligations : ExplicitDevelopmentObligations where
  schwarzschild :=
    ∀ (M : ℝ),
      (∀ (x : Fin 4 → ℝ), x 1 ≠ 0 → Schwarzschild.schwarzschildF M (x 1) ≠ 0 →
        Real.sin (x 2) ≠ 0 → ∀ i j : Fin 4,
          Pipeline.einsteinOf (SchwarzschildDeSitter.schwarzschildG M)
            (SchwarzschildDeSitter.schwarzschildGinv M) x i j = 0) ∧
      (∀ (r θ φ : ℝ), r ≠ 0 → Schwarzschild.schwarzschildF M r ≠ 0 → Real.sin θ ≠ 0 →
        (∀ i j : Fin 3,
          SchwarzschildDeSitter.schwarzschildG M ![0, r, θ, φ] i.succ j.succ =
            sdsSpatialMetric M 0 ![r, θ, φ] i j) ∧
        hamiltonianConstraintOf (sdsSpatialMetric M 0) (sdsSpatialMetricInv M 0)
          (fun _ => 0) ![r, θ, φ] = 0)
  deSitter :=
    ∀ (M Λ : ℝ),
      (∀ (x : Fin 4 → ℝ), x 1 ≠ 0 → SchwarzschildDeSitter.sdsF M Λ (x 1) ≠ 0 →
        Real.sin (x 2) ≠ 0 → ∀ i j : Fin 4,
          Pipeline.einsteinOf (SchwarzschildDeSitter.sdsMetric M Λ)
            (SchwarzschildDeSitter.sdsMetricInv M Λ) x i j +
            Λ * SchwarzschildDeSitter.sdsMetric M Λ x i j = 0) ∧
      (∀ (r θ φ : ℝ), r ≠ 0 → SchwarzschildDeSitter.sdsF M Λ r ≠ 0 → Real.sin θ ≠ 0 →
        (∀ i j : Fin 3,
          SchwarzschildDeSitter.sdsMetric M Λ ![0, r, θ, φ] i.succ j.succ =
            sdsSpatialMetric M Λ ![r, θ, φ] i j) ∧
        spatialScalarCurvOf (sdsSpatialMetric M Λ) (sdsSpatialMetricInv M Λ) ![r, θ, φ] =
          2 * Λ)
  kerr :=
    ∀ (M a : ℝ),
      (∀ (x : Fin 4 → ℝ), Kerr.sigma a (x 1) (x 2) ≠ 0 →
        Kerr.delta M a (x 1) ≠ 0 → Real.sin (x 2) ≠ 0 → ∀ i j : Fin 4,
          Pipeline.einsteinOf (Kerr.kerrMetric M a) (Kerr.kerrMetricInv M a) x i j = 0) ∧
      (∀ (x : Fin 4 → ℝ) (i j : Fin 4),
        Kerr.kerrMetric M a x i j = Kerr.kerrMetric M a x j i) ∧
      (∀ (r θ φ : ℝ),
        Kerr.kerrMetric M a ![0, r, θ, φ] 0 3 =
          -(2 * M * a * r * Real.sin θ ^ 2 / Kerr.sigma a r θ))
  flrw :=
    ∀ (a : ℝ → ℝ) (k Λ G ρ p : ℝ) (x : Fin 4 → ℝ),
      a (x 0) ≠ 0 → x 1 ≠ 0 → 1 - k * (x 1) ^ 2 ≠ 0 → Real.sin (x 2) ≠ 0 →
      (∀ᶠ t in nhds (x 0), DifferentiableAt ℝ a t) →
      DifferentiableAt ℝ (deriv a) (x 0) →
      ((deriv a (x 0) / a (x 0)) ^ 2 = (8 * Real.pi * G / 3) * ρ - k / a (x 0) ^ 2 + Λ / 3 ∧
        deriv (deriv a) (x 0) / a (x 0) = -(4 * Real.pi * G / 3) * (ρ + 3 * p) + Λ / 3) →
      (∀ i j : Fin 4,
        Pipeline.einsteinOf (FLRW.flrwMetric a k) (FLRW.flrwMetricInv a k) x i j +
          Λ * FLRW.flrwMetric a k x i j =
          8 * Real.pi * G * FLRW.perfectFluidT ρ p (FLRW.flrwMetric a k x) i j) ∧
      (∀ (r θ φ : ℝ),
        FLRW.flrwMetric a 0 ![0, r, θ, φ] 1 1 = a 0 ^ 2 ∧
        FLRW.flrwMetric a 0 ![0, r, θ, φ] 2 2 = a 0 ^ 2 * r ^ 2 ∧
        FLRW.flrwMetric a 0 ![0, r, θ, φ] 3 3 = a 0 ^ 2 * r ^ 2 * Real.sin θ ^ 2)

/-- Schwarzschild explicit-development verification: 4D vacuum Einstein equation,
`t = 0` spatial slice metric match, and 3D nonlinear Hamiltonian constraint. -/
theorem schwarzschild_explicit_development : explicitSolutionObligations.schwarzschild := by
  intro M
  refine ⟨fun x hr hf hsin i j =>
      SchwarzschildDeSitter.einsteinOf_schwarzschild M x hr hf hsin i j,
    fun r θ φ hr hf hsin => ⟨fun i j => ?_, ?_⟩⟩
  · fin_cases i <;> fin_cases j <;>
      simp [SchwarzschildDeSitter.schwarzschildG, Schwarzschild.schwarzschildMetric,
        sdsSpatialMetric, SchwarzschildDeSitter.sdsF]
  · exact schwarzschild_spatial_hamiltonian_zero M ![r, θ, φ]
      (by simpa using hr) (by simpa using hf) (by simpa using hsin)

/-- Schwarzschild–de Sitter explicit-development verification: 4D cosmological
Einstein equation `G + Λ g = 0`, `t = 0` spatial slice metric match, and 3D
spatial scalar curvature `³R = 2 Λ`. -/
theorem sds_explicit_development : explicitSolutionObligations.deSitter := by
  intro M Λ
  refine ⟨fun x hr hf hsin i j => ?_, fun r θ φ hr hf hsin => ⟨fun i j => ?_, ?_⟩⟩
  · have h := SchwarzschildDeSitter.einsteinOf_sds M Λ x hr hf hsin i j
    linarith
  · fin_cases i <;> fin_cases j <;>
      simp [SchwarzschildDeSitter.sdsMetric, sdsSpatialMetric]
  · exact spatialScalarCurvOf_sdsSpatial M Λ ![r, θ, φ]
      (by simpa using hr) (by simpa using hf) (by simpa using hsin)

/-- Kerr explicit-development verification: 4D rotating vacuum Einstein
equation `G = 0`, metric symmetry, and `t = 0` Boyer–Lindquist shift block. -/
theorem kerr_explicit_development : explicitSolutionObligations.kerr := by
  intro M a
  refine ⟨fun x hsig hdel hs i j => Kerr.einsteinOf_kerr_eq_zero M a x hsig hdel hs i j,
    fun x i j => Kerr.kerrMetric_symm M a x i j,
    fun r θ φ => ?_⟩
  simp [Kerr.kerrMetric]

/-- FLRW explicit-development verification: 4D Einstein–Friedmann equivalence
`G + Λ g = 8πG T` and `t = 0` flat (`k = 0`) spatial scale-factor metric components. -/
theorem flrw_explicit_development : explicitSolutionObligations.flrw := by
  intro a k Λ G ρ p x ha hr hkr hsin ha_diff ha2 hfried
  refine ⟨(FLRW.einsteinOf_flrw_iff_friedmann a k Λ G ρ p x
      ha hr hkr hsin ha_diff ha2).mpr hfried,
    fun r θ φ => ?_⟩
  simp [FLRW.flrwMetric]

/-- **M6 Certificate**: inhabits `ExplicitDevelopmentCertificate explicitSolutionObligations`
with kernel-verified proofs for Schwarzschild, Schwarzschild–de Sitter, Kerr,
and FLRW. -/
theorem explicitSolutions_certificate :
    ExplicitDevelopmentCertificate explicitSolutionObligations where
  schwarzschild := schwarzschild_explicit_development
  deSitter := sds_explicit_development
  kerr := kerr_explicit_development
  flrw := flrw_explicit_development

end GeneralRelativity
