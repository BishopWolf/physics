# The Einstein Constraint Equations on Compact Three-Manifolds: A Formalisation Plan

**Alex Vergara Gil**

26 November 2026

> **Companion paper.** This is the third of the programme's papers. Paper I
> (`Gravitation-Formalisation.md`) proves that the explicit metrics have the
> curvature and solve the field equations claimed for them. Paper II
> (`Cauchy-Problem.md`) isolates the initial-value problem and identifies
> constraint solving as the layer it consumes but does not supply. This paper
> takes that layer: solving the Hamiltonian and momentum constraints on an
> arbitrary compact three-manifold. It is a plan with a machine-checked
> interface, not a solution theorem.

---

## Abstract

The initial-value problem of general relativity starts with data that satisfy
the Hamiltonian and momentum constraints. The conformal method of Lichnerowicz
and York reduces those four equations to an elliptic system for a conformal
factor and a transverse-traceless tensor. This paper records what the
development already has — derived spatial curvature and the nonlinear ADM
constraint functionals, 1D and 3D-box Sobolev $H^1$ estimates, the
Brill–Lindquist conformal factor, the curved Schwarzschild–de Sitter spatial
slice, and flat FLRW data — states the conformal decomposition as a Lean
interface (`Gravitation.ConformalDecomposition`), and orders the layers still
missing: function spaces on the manifold, the linearised operator and its
Fredholm property, a nonlinear fixed point, and regularity and uniqueness.
None of those layers is claimed here.

**Keywords:** Einstein constraints · Lichnerowicz–York · conformal method ·
elliptic PDE · formal verification

---

## 1. Why a third paper

Paper II's §6 lists four layers between the present development and the
Choquet–Bruhat–Geroch theorem. The second — Sobolev spaces and the constraint
problem — is not a corollary of any curvature computation. It is a quasilinear
elliptic system on a three-manifold, and it is the input Paper II needs before
hyperbolic existence can even be stated for arbitrary data.

Treating it inside Paper II would conflate two different bodies of analysis.
This paper owns the elliptic layer; Paper II takes its result as a black box.

## 2. The conformal system

Let $\bar h$ be a seed Riemannian metric on a compact three-manifold $\Sigma$,
$\phi>0$ a conformal factor, $\sigma$ a symmetric tensor, and $\tau$ the mean
extrinsic curvature. The physical data are

$$h_{ij}=\phi^4\bar h_{ij},\qquad
K_{ij}=\phi^{-2}\sigma_{ij}+\tfrac13\tau\,h_{ij},$$

with $\sigma$ transverse-traceless with respect to $\bar h$:
$\bar h^{ij}\sigma_{ij}=0$ and $\bar\nabla^j\sigma_{ij}=0$. In this split the
constraints become

$$8\bar\Delta\phi-\bar R\phi+|\sigma|^2_{\bar h}\,\phi^{-7}=0,
\qquad
\bar\nabla^j\sigma_{ij}=\tfrac23\phi^6\bar\nabla_i\tau .$$

The first is the Lichnerowicz equation; the second is the momentum constraint,
linear in $\sigma$ for fixed $\phi$ and $\tau$. The system is elliptic, and its
solvability depends on $\bar R$, on $\tau$, and on whether $\Sigma$ is compact
with or without boundary.

## 3. What is already formalised

| Layer | Module | Content |
| --- | --- | --- |
| Derived spatial curvature | `Gravitation.SobolevInitialData` | `spatialRiemannOf`, `spatialRicciOf`, `spatialScalarCurvOf` from a 3-metric field |
| Constraint functionals | `Gravitation.SobolevInitialData` | `hamiltonianConstraintOf`, `momentumConstraintOf`, and `minkowskiChart_spatial_constraints_zero` |
| Sobolev estimates | `Gravitation.SobolevInitialData` | `sobolevH1NormSq3D`, `l2_le_sobolevH1_3D`, `grad_le_sobolevH1_3D` on a box; `sobolev_embedding_1D`, `trace_estimate_1D` in 1D |
| Conformal factor | `Gravitation.SobolevInitialData` | `brillLindquistPhi`, `spatialLaplacian3D_brillLindquistPhi` |
| Curved slice | `Gravitation.SobolevInitialData` | `sdsSpatialMetric`, `spatialScalarCurvOf_sdsSpatial` |
| FLRW data | `Gravitation.SobolevInitialData` | `flrw_initial_constraints` |
| Packaging | `Gravitation.InitialDataInterface` | `ChartInitialData.ofChartData`, `ConstraintResidual`, `constraintResidual_eq_zero` |
| Conformal metrics | `Gravitation.Relativity.Metrics.ConformalMetric` | `conformalRescaleMetric`, `conformalMetric` with a proved inverse |
| This paper's interface | `Gravitation.ConformalDecomposition` | `ConformalData`, `physicalMetric`, `extrinsicCurvature`, the two residuals |

Every row is a statement at a point or on a chart. None of them solves a
boundary-value problem, and none constructs a global solution.

## 4. The interface

`ConformalData` carries the seed metric, the conformal factor with its
positivity proof, the transverse-traceless tensor and the mean curvature. From
it the module defines the physical metric $\phi^4\bar h$ (packaged as a
`MetricTensor` with inverse $\phi^{-4}\bar h^{-1}$, so the existing conformal
machinery is reused rather than duplicated) and the physical extrinsic
curvature.

The equations are stated as residuals with the operators taken as explicit
arguments:

- `hamiltonianResidual lapPhi R sigmaSq phi = 8 * lapPhi - R * phi + sigmaSq / phi^7`,
- `momentumResidual divSigma gradTau phi = fun i => divSigma i - (2/3) * phi^6 * gradTau i`.

`IsLichnerowiczYorkSolution` is the predicate that both residuals vanish at a
point. That is deliberately all it is: the module supplies the shape of the
system, not an existence theorem. The only derived result is
`momentumResidual_zero_gradTau`, which records that constant mean curvature
reduces the momentum residual to the divergence of $\sigma$.

Supplying $\bar\Delta\phi$, $\bar R$, $|\sigma|^2$ and $\bar\nabla\sigma$ as
arguments is honest about the current boundary: the repository has coordinate
expressions for these quantities, but no manifold operators to feed them.

## 5. The layers still missing

| Layer | Content | Status |
| --- | --- | --- |
| L0 | The conformal decomposition as a Lean interface | **Done** in `Gravitation.ConformalDecomposition` |
| L1 | Manifold Sobolev spaces $H^s(\Sigma)$ with trace and multiplication estimates on a compact 3-manifold | open; only $\mathbb{R}$/box $H^1$ exists |
| L2 | The linearised Lichnerowicz operator: invertibility or Fredholm alternative, maximum principle and Schauder/`H^s` estimates | open; no elliptic theory in the repository or its dependencies |
| L3 | Nonlinear existence by a fixed point, with small-data or near-flat hypotheses explicit | open |
| L4 | Regularity and uniqueness of the solution; comparison with the constant, warped and Brill–Lindquist instances | open |
| L5 | Handing the solved constraints to Paper II's hyperbolic layer | open; depends on L1–L4 |

## 6. What is not claimed

- No existence theorem for the constraint equations on any manifold.
- No manifold Sobolev spaces. The formalised estimates are 1D $H^1$ and a 3D
  box $H^1$ norm; there is no $H^s(\Sigma)$ for $s$ large.
- No elliptic regularity, Fredholm property, maximum principle or a priori
  estimate.
- No statement about boundary conditions, asymptotically flat ends, or
  non-compact $\Sigma$.
- No numerical constraint solver. The Vulkan pass computes the curvature of
  metrics it is given; it does not solve for data.
- `IsLichnerowiczYorkSolution` is a predicate on supplied operators, not a
  construction of them.

## 7. Relation to Papers I and II

Paper I supplies the tensor calculus and the exact solutions; Paper II supplies
the ADM constraints, the chart data packaging and the hyperbolic roadmap. This
paper adds the conformal split and nothing else. A solution of the system here
would enter Paper II as its layer 2 and would not by itself prove
Choquet–Bruhat–Geroch: hyperbolic existence and geometric maximality remain
separate layers.

## 8. Reproducibility and trust

The build is silent, no declaration uses `sorry`, `admit` or an axiom of its
own, and every axiom report stays inside
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$. The
commands are the repository's standard ones:

```sh
cd gravitation
lake build
bash ../scripts/check_messages.sh
bash ../scripts/audit_axioms.sh
bash ../scripts/proof_status.sh --check
```

The new module adds nine declarations, two of them theorem-like; the audit and
`Proof-Status.md` carry the exact totals.

## References

1. A. Lichnerowicz. *L'intégration des équations de la gravitation relativiste et le problème des n corps.* J. Math. Pures Appl. 23 (1944) 37–63.
2. J. W. York. *Gravitational energy and the initial-value problem.* Phys. Rev. Lett. 26 (1971) 1656.
3. Y. Choquet-Bruhat, J. W. York. *The Cauchy problem.* In *General Relativity and Gravitation* (Plenum, 1980).
4. R. Bartnik, J. Isenberg. *The constraint equations.* In *The Einstein Equations and the Large Scale Behavior of Gravitational Fields* (Birkhäuser, 2004). arXiv:gr-qc/0405092.
5. Y. Choquet-Bruhat. *General Relativity and the Einstein Equations.* Oxford University Press, 2009.
6. R. M. Wald. *General Relativity.* University of Chicago Press, 1984.
7. A. Vergara Gil. *A Machine-Checked Solution Theory of General Relativity and Its Alternatives.* `docs/Gravitation-Formalisation.md`, 2026.
8. A. Vergara Gil. *The Cauchy Problem for the Einstein Equations: Formalised Constraints, a Wave Model, and a Roadmap.* `docs/Cauchy-Problem.md`, 2026.
