/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Gravitation.KretschmannTotal
public import Gravitation.WaveCauchy
public import Gravitation.WaveEnergy
public import Gravitation.WaveUniqueness
public import Gravitation.Divergence3D
public import Gravitation.WaveEnergy3D
public import Gravitation.WaveEnergy3DConservation
public import Gravitation.WaveEnergy3DWave
public import Gravitation.WaveUniqueness3D
public import Gravitation.LinearizedWaveGauge
public import Gravitation.ManifoldInterface
public import Gravitation.EddingtonFinkelstein
public import Gravitation.KruskalSzekeres
public import Gravitation.Bianchi
public import Gravitation.InitialDataInterface
public import Gravitation.SobolevInitialData
public import Gravitation.ConformalDecomposition
public import Gravitation.MondFieldTheory
public import Gravitation.PPNParameters
public import Gravitation.ManifoldSobolev
public import Gravitation.MogFieldTheory
public import Gravitation.TeVeSFieldTheory
public import Gravitation.AqualVariation
public import Gravitation.DiracCounting
public import Gravitation.SchwarzschildManifold
public import Gravitation.CauchyInterfaces
public import Gravitation.ReducedWave3D
public import Gravitation.ReducedCauchy
public import Gravitation.GaugeRecovery
public import Gravitation.MaximalDevelopment
public import Gravitation.ExplicitDevelopments
public import Gravitation.ClassicalMechanics.OrbitalMechanics.NewtonianGravity
public import Gravitation.Cosmology.FLRW.Basic
public import Gravitation.Cosmology.FLRW.Christoffel
public import Gravitation.Cosmology.FLRW.Curvature
public import Gravitation.Cosmology.FLRW.FriedmannEquations
public import Gravitation.Mathematics.Calculus.CoordDeriv
public import Gravitation.Mathematics.FinSum
public import Gravitation.Mathematics.GeneralizedKronecker
public import Gravitation.Relativity.General.FrameSumOfSquares
public import Gravitation.Relativity.General.GeodesicSystem
public import Gravitation.Relativity.General.GravitationalConstant
public import Gravitation.Relativity.General.InitialData.AnisotropicSlice
public import Gravitation.Relativity.General.InitialData.Basic
public import Gravitation.Relativity.General.InitialData.FlatSlice
public import Gravitation.Relativity.General.Kerr.Basic
public import Gravitation.Relativity.General.Kerr.Christoffel
public import Gravitation.Relativity.General.Kerr.MetricDeriv
public import Gravitation.Relativity.General.Kerr.RicciCurvature
public import Gravitation.Relativity.General.Linearized.Basic
public import Gravitation.Relativity.General.Linearized.GaugeTransform
public import Gravitation.Relativity.General.Linearized.Laplacian3
public import Gravitation.Relativity.General.Linearized.LinearizedChristoffel
public import Gravitation.Relativity.General.Linearized.LinearizedEinstein
public import Gravitation.Relativity.General.Linearized.LinearizedRicci
public import Gravitation.Relativity.General.Linearized.LinearizedRiemann
public import Gravitation.Relativity.General.Linearized.LorenzGauge
public import Gravitation.Relativity.General.Linearized.MinkowskiDalembertian
public import Gravitation.Relativity.General.Linearized.NewtonianPerturbation
public import Gravitation.Relativity.General.Linearized.TTWave
public import Gravitation.Relativity.General.Linearized.TraceReversed
public import Gravitation.Relativity.General.MinkowskiCoordinateMetric
public import Gravitation.Relativity.General.ReissnerNordstrom.Basic
public import Gravitation.Relativity.General.Schwarzschild.Basic
public import Gravitation.Relativity.General.Schwarzschild.CoordinateCurvature
public import Gravitation.Relativity.General.Schwarzschild.ElectricWeyl
public import PhyslibAlpha.Relativity.General.Schwarzschild.IncompressibleSphere
public import Gravitation.Relativity.General.SchwarzschildDeSitter.Basic
public import Gravitation.Relativity.General.SchwarzschildDeSitter.CoordinateCurvature
public import Gravitation.Relativity.General.SchwarzschildDeSitter.DeSitterFrame
public import Gravitation.Relativity.Metrics.Basic
public import Gravitation.Relativity.Metrics.Christoffel
public import Gravitation.Relativity.Metrics.ConformalMetric
public import Gravitation.Relativity.Metrics.SpaceTimeDerivBridge
public import Gravitation.Relativity.Metrics.CoordinateMetric
public import Gravitation.Relativity.General.InitialData.CovariantDerivTensor2
public import Gravitation.Relativity.Metrics.CurvatureBridge
public import Gravitation.Relativity.Metrics.CurvatureDerivatives
public import Gravitation.Relativity.Metrics.Einstein
public import Gravitation.Relativity.Metrics.MetricTrace
public import Gravitation.Relativity.Metrics.Minkowski
public import Gravitation.Relativity.Metrics.NullVector
public import Gravitation.Relativity.Metrics.Ricci
public import Gravitation.Relativity.Metrics.RicciScalar
public import Gravitation.Relativity.Metrics.Riemann
public import Gravitation.Relativity.Metrics.RiemannFromData
public import Gravitation.Relativity.Metrics.StaticSphericalMetric.Basic
public import Gravitation.Relativity.Metrics.StaticSphericalMetric.Christoffel
public import Gravitation.Relativity.Modified.BransDicke
public import Gravitation.Relativity.Modified.ChameleonScreening
public import Gravitation.Relativity.Modified.EinsteinAether
public import Gravitation.Relativity.Modified.EinsteinCartan.Basic
public import Gravitation.Relativity.Modified.EinsteinCartan.Contorsion
public import Gravitation.Relativity.Modified.EinsteinCartan.ModifiedTorsion
public import Gravitation.Relativity.Modified.FRGravity
public import Gravitation.Relativity.Modified.Galileon
public import Gravitation.Relativity.Modified.KaluzaKlein.Basic
public import Gravitation.Relativity.Modified.KaluzaKlein.GaugeTransform
public import Gravitation.Relativity.Modified.KaluzaKlein.KaluzaMiracle
public import Gravitation.Relativity.Modified.KaluzaKlein.TriangularFactorization
public import Gravitation.Relativity.Modified.Lovelock.Basic
public import Gravitation.Relativity.Modified.Lovelock.ConstantCurvature
public import Gravitation.Relativity.Modified.Lovelock.Contract5
public import Gravitation.Relativity.Modified.MOND
public import Gravitation.Relativity.Modified.MassiveGravity.Basic
public import Gravitation.Relativity.Modified.MassiveGravity.DRGT
public import Gravitation.Relativity.Modified.MassiveGravity.FierzPauli
public import Gravitation.Relativity.Modified.MassiveGravity.VDVZ
public import Gravitation.Perturbation
public import Gravitation.Relativity.Modified.Nordstrom
public import Gravitation.Relativity.Modified.Ostrogradsky
public import Gravitation.Relativity.Modified.TeVeS
public import Gravitation.Relativity.Modified.Teleparallel.Basic
public import Gravitation.Relativity.Modified.Teleparallel.FLRWTorsion
public import Gravitation.Relativity.Modified.Teleparallel.FTGravity
public import Gravitation.Relativity.Tensors.EMFieldStrength
public import Gravitation.Relativity.Tensors.EinsteinTensor
public import Gravitation.Relativity.Tensors.MaxwellStressEnergy
public import Gravitation.Relativity.Tensors.PerfectFluidStressEnergy
public import Gravitation.Relativity.Tensors.RicciTensor
public import Gravitation.Relativity.Tensors.RiemannTensor
public import Gravitation.Relativity.Tensors.Tensor2
public import Gravitation.Relativity.General.SchwarzschildDeSitter.Embedding
/-!

# General relativity: the Physlib development

Umbrella module for the general-relativity development maintained in Physlib
(`PhyslibAlpha/Relativity/General`, branch `gravity`).  Until that branch is
merged, its modules are vendored under `vendor/Gravitation/Relativity/{General,Metrics,
Modified,Tensors}/`, `vendor/Gravitation/Cosmology/FLRW/`, and the shared
helpers under `vendor/Gravitation/{Mathematics,ClassicalMechanics}/` at commit
`61505fa6` as `Gravitation.Relativity.*`, `Gravitation.Cosmology.*`,
`Gravitation.Mathematics.*` and `Gravitation.ClassicalMechanics.*`; the namespace
is still `GeneralRelativity` and the proofs are unchanged, so migrating consists
of switching these imports back to the corresponding `PhyslibAlpha.*` paths.  The
repository adds the numerical verification and the written account.

## i. Overview

General relativity is a metric theory of gravitation: a four-dimensional
Lorentzian metric `g` determines the Levi-Civita connection `Γ`, its curvature
`R^ρ_{σμν}`, the Ricci tensor `Ric` and scalar `S`, and the Einstein tensor
`G = Ric - ½ S g`.  Matter curves spacetime through `G = 8π T`, and test
particles fall along the geodesics of `g`.  The formalisation is coordinate
(component) based: a metric is a field of `4 × 4` component matrices with a
certified inverse, and every curvature tensor is computed from it by
differentiation and contraction.

The modules below cover the full pipeline from a metric to the field equations,
the initial-value constraints, the geodesic Cauchy problem, the exact black-hole
and cosmological solutions, linearized gravity, and the standard alternatives to
general relativity.

## ii. Key results

- `GeneralRelativity.Pipeline.coordDeriv`, `christoffel`, `riemann`,
  `ricciTensorOf`, `ricciScalarOf`, `einsteinTensorOf` : the coordinate chain
  `g ↦ ∂g ↦ Γ ↦ ∂Γ ↦ R ↦ Ric ↦ S ↦ G`.
- `GeneralRelativity.Riemann.skew_first`, `ricci_symm`, `vacuum_iff_ricci_flat` :
  the algebraic symmetries of curvature and `G = 0 ↔ Ric = 0` in four dimensions.
- `GeneralRelativity.Bianchi.riemann_bianchi`, `riemann_lower_bianchi`,
  `riemann_lower_pair_symm` : the coordinate first Bianchi identity and pair
  symmetry of the lowered Riemann tensor.
- `GeneralRelativity.InitialData.hamiltonianConstraint`, `momentumConstraint` :
  the ADM Hamiltonian and momentum constraints.
- `GeneralRelativity.spatialRiemannTensorOf`,
  `spatialRiemannTensorOfConstMetric`, `extrinsicDerivativeOf`,
  `ChartInitialData.ofFields`, `ChartInitialData.ofChartData`,
  `minkowskiChartInitialDataDerived` :
  the 3D Riemann tensor and momentum-constraint derivative derived from the
  spatial metric and extrinsic-curvature fields, exercised on Minkowski.
- `GeneralRelativity.warpedSpatialMetric`, `warpedSpatialRiemann`,
  `spatialRiemannTensorOf_warped_nonconstant` :
  a nonconstant warped metric whose derived `R_{0101}` is `-1`.
- `GeneralRelativity.ManifoldSpacetime`, `ManifoldInitialData`,
  `minkowskiManifoldInitialData` :
  global-chart manifold packaging of the derived chart curvature and momentum
  data.
- `GeneralRelativity.ManifoldTransition`, `ManifoldInitialData.IsCompatible` :
  isometric chart transitions preserve the coordinate metric, inverse metric and
  induced spatial metric, and induced manifold initial data are compatible
  across them.
- `GeneralRelativity.ManifoldInitialData.ham_zero`, `mom_zero`, `isVacuumData` :
  direct wrapper accessors for the vacuum-constraint facts.
- `GeneralRelativity.Schwarzschild.manifoldInitialData` :
  the exterior Schwarzschild manifold-level time-symmetric initial-data
  instance.
- `GeneralRelativity.ChartSpacetime.Isometry`, `ChartSpacetime.Embedding` :
  chart-level isometry and embedding API, with identity, inverse and composition.
- `GeneralRelativity.Geodesics.geodesic_ivp_exists` : local existence for the
  geodesic equation from position and velocity.
- `GeneralRelativity.Schwarzschild.ricciTensorOf_schwarzschild`,
  `SchwarzschildDeSitter.ricciTensorOf_sds` : Schwarzschild's vacuum and
  Schwarzschild–de Sitter's `Ric = Λ g`, proved from the metric.
- `GeneralRelativity.Kerr.ricciTensorOf_kerr_eq_zero` : the rotating Kerr metric
  is Ricci flat.
- `GeneralRelativity.ReissnerNordstrom.einsteinTensorOf_rn_eq_maxwell` : the charged
  Reissner–Nordström metric solves the Einstein–Maxwell equations.
- `GeneralRelativity.FLRW.einsteinTensorOf_flrw_iff_friedmann` : the FLRW
  metric satisfies the Einstein equations exactly when the Friedmann equations
  hold.
- `GeneralRelativity.Linearized.linEinstein_lorenz_gauge` : in Lorenz gauge the
  linearized Einstein tensor is `-½ □ h̄`.

## iii. Table of contents

- `Basic`, `Curvature`, `Einstein`, `Conservation` : tensors, curvature,
  field equations, and the conservation of `G`.
- `Metrics/CoordinateMetric`, `Metrics/StaticSphericalMetric`, `Metrics/Minkowski` :
  the metric-to-curvature pipeline and the flat reference spacetime.
- `Schwarzschild/*`, `SchwarzschildDeSitter/*`, `ReissnerNordstrom/Basic`,
  `Kerr/*`, `Cosmology/FLRW/Metric` : the exact solutions.
- `InitialData`, `GeodesicSystem`, `Linearized`, `GravitationalConstant` : the
  Cauchy problem, linearized gravity, and Newton's constant.
- `Modified/*` : Brans–Dicke, `f(R)`, chameleon screening, Galileons,
  Ostrogradsky, MOND, MOG, TeVeS, Nordström, Einstein–Aether, Einstein–Cartan,
  Kaluza–Klein, Lovelock, massive gravity, teleparallel gravity, and the PPN
  parameterisation.

## iv. References

* R. M. Wald, *General Relativity*, University of Chicago Press, 1984, chapters 2–4 (curvature, field equations, conservation). [ref: wald_gr]
* C. W. Misner, K. S. Thorne, J. A. Wheeler, *Gravitation*, Freeman, 1973, chapters 8–10 and 21–22 (curvature, initial value, exact solutions). [ref: mtw]
* S. Chandrasekhar, *The Mathematical Theory of Black Holes*, Oxford, 1983, chapters 2–3 and 6 (Schwarzschild and Kerr). [ref: chandrasekhar_bh]
* R. P. Kerr, *Gravitational field of a spinning mass as an example of algebraically special metrics*, Phys. Rev. Lett. 11 (1963) 237. [ref: kerr_1963]
* H. Reissner, *Über die Eigengravitation des elektrischen Feldes nach der Einsteinschen Theorie*, Ann. Phys. 50 (1916) 106. [ref: reissner_1916]
* A. Friedmann, *Über die Krümmung des Raumes*, Z. Phys. 10 (1922) 377. [ref: friedmann_1922]
* R. Arnowitt, S. Deser, C. W. Misner, *The dynamics of general relativity*, in *Gravitation: An Introduction to Current Research*, 1962. [ref: arnowitt_deser_misner_1962]
* C. M. Will, *Theory and Experiment in Gravitational Physics*, 2nd ed., Cambridge, 2018, chapters 4–5 (PPN parameters and solar-system tests). [ref: will_ppn]
* The bibliography with full entries is `docs/references.bib`.

-/
