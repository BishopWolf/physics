# Survey: Lean formalisation of physics and mathematics (Nov 2026)

Context gathered for this repository: what the Anthropic and OpenAI Lean
repositories contain, what the physics-Lean community has done, and where
general relativity currently stands as *formalised theorems*.

Repositories were inspected through the GitHub contents API and their
published documentation on 2026-11-21.

## Anthropic

| Repository | Contents | Physics / GR |
| --- | --- | --- |
| [`anthropics/formal-math`](https://github.com/anthropics/formal-math) | Self-contained Lake projects, Apache-2.0: `zeta23` (Riemann zeta zeros), `3sum-apsp` (fine-grained complexity), `eth` (2^o(n) 3-SAT) | None |
| [`anthropics/fermats-last-theorem`](https://github.com/anthropics/fermats-last-theorem) | Complete Lean 4 formalisation of Fermat's Last Theorem (Frey–Serre–Ribet–Wiles), Lean 4.33.1 / Mathlib v4.33.0, `#print axioms` restricted to the three standard axioms | None |

Both are pure mathematics/TCS. Neither contains a physics library, a metric, or
a curvature tensor.

## OpenAI

| Repository | Contents | Physics / GR |
| --- | --- | --- |
| [`openai/ten-proofs`](https://github.com/openai/ten-proofs) | Lean 4 certificates for ten results (sphere packing, binary/spherical codes, permanent, Ramsey, non-sofic groups, quantum parallel repetition, Ehrhart, GapCVP, Connes rigidity, compactness/degeneracy) | None (quantum parallel repetition is information-theoretic, not field theory) |
| [`openai/math`](https://github.com/openai/math) | 722 manuscripts in 372 families; `lean/` catalogue lists 162 papers whose main result has a Lean formalisation (snapshot 2026-10-07) | None found; the collection is mathematics |

## Community physics formalisation

* [`leanprover-community/physlib`](https://github.com/leanprover-community/physlib)
  (`Physlib`, `PhyslibAlpha`). Top-level areas: `ClassicalMechanics`,
  `ClassicalFieldTheory`, `Electromagnetism`, `QFT`, `QuantumMechanics`,
  `StatisticalMechanics`, `Cosmology`, `Relativity`, `SpaceAndTime`, …
  `Physlib/Relativity/` contains `MinkowskiMatrix.lean`, `LorentzGroup/`,
  `LorentzAlgebra/`, `Tensors/`, `Special/`, `Causality/`, `Poincare/`,
  `Bispinors/`, `Fermions/`, `SL2C/`, `PauliMatrices/`. That is
  special-relativistic kinematics and Lorentz/Poincaré representation theory.
  As of November 2026 its **`gravity` branch** additionally contains the full
  development surveyed below — curvature, the coordinate pipeline, the exact
  solutions, the Cauchy problem and the modified theories — but that branch is
  not yet merged into `master`.
* HepLean (Tooby-Smith) — high-energy physics: particles, gauge theory,
  spinors; not gravitation.
* `TataSatyaPratheek/mathematical-physics-lean` — a from-scratch,
  Mathlib-free dimension-parametric development reaching the Einstein tensor and
  Einstein equations (`Relativity/EinsteinN.lean`). Its own README states
  0 `sorry` but 365 axioms; trust surface is the axioms, not the kernel alone.
* QIQT / Zenodo 20837810 — an audited human-AI loop whose case study proves a
  *conditional* statement: the Einstein field equations follow from a
  finite-information capacity bound plus a Jacobson-style equation of state,
  with the physics inputs as explicit hypotheses
  (`QIQTH.QiqtToGR.qiqt_bekenstein_gives_gr`). The authors stress the result is
  conditional, not a derivation of GR from first principles.

## Has general relativity been formalised as theorems?

**No, not end to end.** As of the surveyed state:

1. **Curvature algebra** is formalised in places: metric components,
   Christoffel symbols, Riemann/Ricci/scalar curvature, the Einstein tensor and
   its divergence-free property.
2. **The field equations** have been *stated* and derived only conditionally
   from extra physical premises.
3. **Solution theory** — the initial value formulation, local existence and
   uniqueness for the Einstein equations, singularity theorems (Penrose–
   Hawking), black-hole uniqueness/no-hair, energy conditions, global
   hyperbolicity — is not formalised in any of these projects.
4. **No Lean theorem** in the surveyed repositories states that a specific
   black-hole metric solves the vacuum equations; the Schwarzschild solution
   appears, if at all, as an unproved claim.

So the meaningful gap is not "definitions of curvature" but "theorems about
solutions". This repository is a small, kernel-checked step into that gap, plus
a GPU numerical check of the solutions the Lean side cannot yet reach. The
survey above records the state before the unmerged `gravity` branch existed; the
branch, and the vendored copy of it here, now prove the solution-theory results
listed at the end of this document.

## What this repository adds

The general-relativity development lives in Physlib on the `gravity` branch
(`PhyslibAlpha/Relativity/General` plus the branch-only `Metrics`, `Tensors` and
`Cosmology` trees, 67 Lean modules on the branch, namespace `GeneralRelativity`),
which is not yet merged upstream. Since 25 November 2026 the 57 vendored modules
are **vendored** here under `gravitation/vendor/Gravitation/Relativity/{General,
Metrics,Tensors}/` and `gravitation/vendor/Gravitation/Cosmology/FLRW/Metric.lean`
(module paths `Gravitation.Relativity.*` and `Gravitation.Cosmology.*`, namespace
`GeneralRelativity` unchanged) at branch commit `b81c896a`, while the `physlib`
requirement points at merged master `7910f51f`
— the merge base the branch was written against, which also supplies the
already-merged `Schwarzschild.IncompressibleSphere` and the base library. The 1194 audited declarations are those sources plus the local
`Gravitation.WaveCauchy`, `Gravitation.WaveEnergy`, `Gravitation.WaveUniqueness`,
`Gravitation.Divergence3D`, `Gravitation.WaveEnergy3D`,
`Gravitation.WaveEnergy3DConservation`, `Gravitation.WaveEnergy3DWave`,
`Gravitation.WaveUniqueness3D`, `Gravitation.LinearizedWaveGauge`,
`Gravitation.ManifoldInterface`, `Gravitation.EddingtonFinkelstein`, `Gravitation.Bianchi`, `Gravitation.KretschmannTotal`,
`Gravitation.InitialDataInterface`, `Gravitation.SobolevInitialData`,
`Gravitation.CauchyInterfaces`, `Gravitation.ReducedWave3D`,
`Gravitation.ReducedCauchy`, `Gravitation.GaugeRecovery`,
`Gravitation.MaximalDevelopment` and `Gravitation.ExplicitDevelopments` modules,
imported through
`gravitation/Gravitation.lean`; deleting `vendor/` is the migration once the
branch lands.

* Core development — metric with a certified inverse, Riemann/Ricci/scalar
  curvature and the Einstein tensor, the coordinate pipeline
  `g ↦ ∂g ↦ Γ ↦ ∂Γ ↦ R ↦ Ric ↦ S ↦ G`, the Einstein-tensor trace identity and
  `G = 0 ↔ Ric = 0` in four dimensions, conservation of the Einstein tensor
  (the contracted Bianchi identity is proved for the frame Einstein space,
  `sds_frame_bianchi`, rather than assumed), the ADM constraints, the geodesic Cauchy problem, the d'Alembert one-dimensional wave Cauchy theorem
  (`dAlembert_wave_equation`), the wave energy conservation theorem
  (`waveEnergy_eq_initial`), zero-data uniqueness (`wave_zero_of_zero_data`, `wave_zero_of_zero_data_Icc`), closed-interval general-data uniqueness (`wave_unique_of_same_data`), the 3D box divergence theorem (`integral_divergence_box_eq_zero`), the 3D energy derivative (`hasDerivAt_waveEnergy3D`), conditional 3D energy conservation (`waveEnergy3D_eq_initial_of_divergence`), 3D wave energy conservation (`waveEnergy3D_eq_initial_of_wave`), 3D zero-energy data (`eq_zero_of_waveEnergy3D_eq_zero`), 3D wave uniqueness on the closed box (`wave_zero_of_zero_data3D`, `wave_unique3D_of_same_data`) and the linearized wave-gauge interface (`WaveGaugePerturbation`, `linEinstein_eq_zero_of_waveGauge`, with the TT-wave instantiation `ttWave_waveGauge`) and the M1 global-chart interface (`SmoothChartSpacetime`, general `ChartSpacetime.isLeviCivita`, `ChartSpacetime.IsCauchySurface`, `minkowskiChart_globallyHyperbolic`, the coordinate first Bianchi identity and pair symmetry (`Bianchi.riemann_lower_bianchi`, `Bianchi.riemann_lower_pair_symm`), the derived chart curvature and momentum data (`spatialRiemannTensorOf`, `spatialRiemannTensorOfConstMetric`, `spatialRiemannTensorOf_warped_nonconstant`, `extrinsicDerivativeOf`, `ChartInitialData.ofFields`, `ChartInitialData.ofChartData`, `ManifoldInitialData`, `minkowskiManifoldInitialData`, `minkowskiChartInitialDataDerived`), and the general `Bianchi.second_bianchi` / `contracted_bianchi` / `covDiv_einstein_eq_zero`), the M2 Sobolev and curved-slice initial-data layer (`ChartInitialData`, `sobolev_embedding_1D`, `trace_estimate_1D`, `sobolevH1NormSq3D`, `hamiltonianConstraintOf`, `momentumConstraintOf`, `flrw_initial_constraints`), the M3–M6 certificates and their inhabited scopes (`CauchyInterfaces`, `ReducedCauchy`, `GaugeRecovery`, `MaximalDevelopment`, `ExplicitDevelopments`: linearized 3D box, nonlinear flat FLRW, abstract Zorn/open-domain maximality, and explicit Schwarzschild–de Sitter/Kerr/FLRW recovery), the scoped 3D linear wave model (`ReducedWave3D`), linearized gravity, and Newton's gravitational constant with its natural-unit systems.
* Multi-chart transition layer — isometric transitions between global-chart
  spacetimes preserve the full coordinate metric and inverse metric, the induced
  spatial metric, and induced manifold initial data, with reflexivity, symmetry
  and transitivity. The wrapper also exposes direct Hamiltonian, momentum and
  vacuum-data accessors. Arbitrary multi-chart atlas gluing remains outside. A
  regular exterior Schwarzschild chart supplies a concrete manifold-level
  instance (`Schwarzschild.manifoldInitialData`) with its curved time-symmetric
  slice.
* Exact solutions — Minkowski; Schwarzschild with its orthonormal frame, all six
  Riemann components and the Kretschmann scalar `48M²/r⁶`; the interior
  incompressible sphere (TOV profile, Buchdahl bound); Schwarzschild–de Sitter
  for general `Λ`, with `Ric = Λg`, `S = 4Λ`, `G = −Λg` and the `Λ`-independent
  Weyl part; Reissner–Nordström, where `G = 8πT^{EM}` is proved from the metric;
  Kerr in Boyer–Lindquist coordinates, proved Ricci flat together with its
  horizons, ergosphere and ZAMO frame dragging; and FLRW, where the metric-level
  Einstein equations are proved equivalent to the Friedmann equations and
  bridged to `Physlib.Cosmology.FLRW`.
* Alternative and modified theories — machine-checked cores of sixteen theories:
  Einstein–Cartan (torsion, contorsion uniqueness, Cartan spin–torsion
  inversion), teleparallel/TEGR (`R = −T + B` and `f(T)` Friedmann), Kaluza–Klein
  (5D inverse, `R⁵ = R⁴ − ¼F²`), Lovelock/Gauss–Bonnet (vanishing variation for
  `n ≤ 4`), Einstein–Aether (mode speeds, GW170817), massive gravity (Fierz–Pauli,
  vDVZ, dRGT), the full Will–Nordtvedt PPN parameterisation, Brans–Dicke,
  `f(R)`/Starobinsky, chameleon screening, MOND, MOG, TeVeS, Nordström,
  Galileon and Ostrogradsky. Depth varies by theory and is stated per module.
* Axiom policy — no `axiom`, `constant`, `opaque`, `sorry`, `admit` or
  `native_decide` in the audited surface; `scripts/audit_axioms.sh` now covers
  both the local module and the Physlib GR subtree, prints `#print axioms` for
  all 1194 declarations (741 theorem-like) and rejects anything outside
  `{propext, Classical.choice, Quot.sound}`. `Proof-Status.md` is regenerated
  from that audit and CI fails if it is stale.
* Silent build — `lake build` emits no messages; `scripts/check_messages.sh`
  fails if one reappears.
* Numerical check — the Vulkan tensor pass now covers seven metrics. Besides
  Minkowski, Schwarzschild and Schwarzschild–de Sitter (Kretschmann, Weyl part
  and four Riemann components), it verifies the Kerr vacuum (`2.10e-7` on
  `|Ric|` and `1.42e-7` on `|G|` at `a = 0.5`), the Reissner–Nordström
  Einstein–Maxwell equation (`1.085e-7` on `|G − 8πT|` at `Q = 0.5`), the FLRW
  closed forms for `a = 1 + Ht + t²` (`1.27e-6` on `Ric`, `R` and `G`, so the
  `a''` term is exercised), and the interior Schwarzschild constant-density
  Einstein tensor (`8.90e-8` at `Rc = 5`, `Ra = 4`). CI runs it on the lavapipe
  software driver.
* Vendor drift guard — `scripts/check_vendor_sync.sh` fetches the `gravity`
  branch, fails if its tip has moved from `vendor/REVISION`, and diffs every
  vendored module against the branch after the import rewrite. CI runs it
  before the build, so the temporary copy cannot go stale silently.
* References — `docs/references.bib` collects the standards texts, original
  solution papers and modified-gravity literature; each Physlib module cites its
  sources in its own references section as `[ref: key]`.

## Sources

* https://github.com/anthropics/formal-math
* https://github.com/anthropics/fermats-last-theorem
* https://github.com/openai/ten-proofs
* https://github.com/openai/math
* https://github.com/leanprover-community/physlib
* https://arxiv.org/abs/2405.08863 (HepLean)
* https://zenodo.org/records/20837810 (conditional EFE derivation)
* https://github.com/TataSatyaPratheek/mathematical-physics-lean
