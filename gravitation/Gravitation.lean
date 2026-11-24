/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Gravitation.Relativity.General.Basic
public import Gravitation.Relativity.General.Conservation
public import Gravitation.Relativity.General.Curvature
public import Gravitation.Relativity.General.Einstein
public import Gravitation.Relativity.General.FLRW.Pipeline
public import Gravitation.Relativity.General.Geodesics
public import Gravitation.Relativity.General.GravitationalConstant
public import Gravitation.Relativity.General.InitialValue
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
public import Gravitation.Relativity.General.Kerr.Basic
public import Gravitation.Relativity.General.Kerr.Christoffel
public import Gravitation.Relativity.General.Kerr.Vacuum
public import Gravitation.Relativity.General.Linearized
public import Gravitation.Relativity.General.Minkowski
public import Gravitation.Relativity.General.Modified.BransDicke
public import Gravitation.Relativity.General.Modified.ChameleonScreening
public import Gravitation.Relativity.General.Modified.EinsteinAether
public import Gravitation.Relativity.General.Modified.EinsteinCartan
public import Gravitation.Relativity.General.Modified.FRGravity
public import Gravitation.Relativity.General.Modified.Galileon
public import Gravitation.Relativity.General.Modified.KaluzaKlein
public import Gravitation.Relativity.General.Modified.Lovelock
public import Gravitation.Relativity.General.Modified.MOG
public import Gravitation.Relativity.General.Modified.MOND
public import Gravitation.Relativity.General.Modified.MassiveGravity
public import Gravitation.Relativity.General.Modified.Nordstrom
public import Gravitation.Relativity.General.Modified.Ostrogradsky
public import Gravitation.Relativity.General.Modified.PPN
public import Gravitation.Relativity.General.Modified.TeVeS
public import Gravitation.Relativity.General.Modified.Teleparallel
public import Gravitation.Relativity.General.Pipeline
public import Gravitation.Relativity.General.ReissnerNordstrom.Basic
public import Gravitation.Relativity.General.Schwarzschild.Frame
public import PhyslibAlpha.Relativity.General.Schwarzschild.IncompressibleSphere
public import Gravitation.Relativity.General.Schwarzschild.Metric
public import Gravitation.Relativity.General.SchwarzschildDeSitter.Frame
public import Gravitation.Relativity.General.SchwarzschildDeSitter.Metric
public import Gravitation.Relativity.General.SchwarzschildDeSitter.Pipeline
public import Gravitation.Relativity.General.StaticSpherical

/-!

# General relativity: the Physlib development

Umbrella module for the general-relativity development maintained in Physlib
(`PhyslibAlpha/Relativity/General`, branch `gravity`).  Until that branch is
merged, its modules are vendored under `vendor/Gravitation/Relativity/General/`
at commit `41abde06` as `Gravitation.Relativity.General.*`; the namespace is
still `GeneralRelativity` and the proofs are unchanged, so migrating consists of
switching these imports back to `PhyslibAlpha.Relativity.General.*`.  The
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

- `GeneralRelativity.Pipeline.christoffel`, `riemann`, `ricciOf`, `scalarOf`,
  `einsteinOf` : the coordinate chain `g ↦ ∂g ↦ Γ ↦ ∂Γ ↦ R ↦ Ric ↦ S ↦ G`.
- `GeneralRelativity.Riemann.skew_first`, `ricci_symm`, `vacuum_iff_ricci_flat` :
  the algebraic symmetries of curvature and `G = 0 ↔ Ric = 0` in four dimensions.
- `GeneralRelativity.InitialValue.ham`, `momConstraint` : the ADM Hamiltonian and
  momentum constraints.
- `GeneralRelativity.Geodesics.geodesic_ivp_exists` : local existence for the
  geodesic equation from position and velocity.
- `GeneralRelativity.Pipeline.ricciOf_schwarzschild`,
  `SchwarzschildDeSitter.Pipeline.ricciOf_sds` : Schwarzschild's vacuum and
  Schwarzschild–de Sitter's `Ric = Λ g`, proved from the metric.
- `GeneralRelativity.Kerr.Vacuum.ricciOf_kerr_eq_zero` : the rotating Kerr metric
  is Ricci flat.
- `GeneralRelativity.ReissnerNordstrom.einsteinOf_rn_eq_maxwell` : the charged
  Reissner–Nordström metric solves the Einstein–Maxwell equations.
- `GeneralRelativity.FLRW.Pipeline.einsteinOf_flrw_iff_friedmann` : the FLRW
  metric satisfies the Einstein equations exactly when the Friedmann equations
  hold.
- `GeneralRelativity.Linearized.linEinstein_lorenz_gauge` : in Lorenz gauge the
  linearized Einstein tensor is `-½ □ h̄`.

## iii. Table of contents

- `Basic`, `Curvature`, `Einstein`, `Conservation` : tensors, curvature,
  field equations, and the conservation of `G`.
- `Pipeline`, `StaticSpherical`, `Minkowski` : the metric-to-curvature pipeline
  and the flat reference spacetime.
- `Schwarzschild/*`, `SchwarzschildDeSitter/*`, `ReissnerNordstrom/Basic`,
  `Kerr/*`, `FLRW/Pipeline` : the exact solutions.
- `InitialValue`, `Geodesics`, `Linearized`, `GravitationalConstant` : the
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
