# The Einstein Constraint Equations on Compact Three-Manifolds: A Formalisation Plan

**Alex Vergara Gil**

26 November 2026

> **Companion paper.** This is the third of four accounts. The first
> (`Gravitation-Formalisation.md`) proves that the explicit metrics have the
> curvature and solve the field equations claimed for them. The second
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
factor, a shift and a transverse-traceless tensor. This paper records what the
development already has — derived spatial curvature and the nonlinear constraint
functionals, Sobolev $H^1$ estimates on a box and in one dimension, the
Brill–Lindquist conformal factor, the curved Schwarzschild–de Sitter spatial
slice, flat FLRW data — states the conformal decomposition as a mathematical
interface, and orders the layers still missing: function spaces on the manifold,
the linearised operator and its Fredholm property, a nonlinear fixed point, and
regularity and uniqueness. None of those layers is claimed here.

**Keywords:** Einstein constraints · Lichnerowicz–York · conformal method ·
elliptic PDE · formal verification

---

## 1. Why a third paper

The Cauchy paper lists four layers between the present development and the
Choquet–Bruhat–Geroch theorem. The second — Sobolev spaces and the constraint
problem — is not a corollary of any curvature computation. It is a quasilinear
elliptic system on a three-manifold, and it is the input the hyperbolic layer
needs before existence can even be stated for arbitrary data.

Treating it inside the Cauchy paper would conflate two different bodies of
analysis. This paper owns the elliptic layer; the Cauchy paper takes its result
as a black box.

## 2. The conformal system

Let $\bar h$ be a seed Riemannian metric on a compact three-manifold $\Sigma$,
$\phi>0$ a conformal factor, $\beta$ a shift, $\sigma$ a symmetric tensor, and
$\tau$ the mean extrinsic curvature. The physical data are

$$h_{ij}=\phi^4\bar h_{ij},\qquad
K_{ij}=\phi^{-2}\big((\bar L\beta)_{ij}+\sigma_{ij}\big)+\tfrac13\tau\,h_{ij},$$

where $(\bar L\beta)_{ij}=\bar\nabla_i\beta_j+\bar\nabla_j\beta_i
-\tfrac23\bar h_{ij}\bar\nabla_k\beta^k$ is the conformal Killing operator and
$\sigma$ is transverse-traceless with respect to $\bar h$:
$\bar h^{ij}\sigma_{ij}=0$, $\bar\nabla^j\sigma_{ij}=0$. In this split the
constraints become

$$8\bar\Delta\phi-\bar R\phi+|\sigma+\bar L\beta|^2_{\bar h}\,\phi^{-7}=0,
\qquad
\bar\nabla_j(\bar L\beta)^{ij}+\bar\nabla^j\sigma_{ij}
=\tfrac23\phi^6\bar\nabla^i\tau .$$

The first is the Lichnerowicz equation; the second is the momentum constraint,
linear in $\beta$ for fixed $\phi$ and $\tau$. For constant mean curvature with
a transverse $\sigma$ and no shift it reduces to the divergence equation of the
shift-free form.

## 3. What the development already contains

| Content | Depth |
| --- | --- |
| Spatial Riemann, Ricci and scalar curvature derived from a 3-metric field | pointwise, chart coordinates |
| Hamiltonian and momentum constraint functionals, with the flat case shown to vanish | pointwise |
| Sobolev $H^1$ norm on a 3D box, with coercivity | constant-coefficient box |
| 1D $H^1$ embedding and boundary trace inequality | interval |
| Brill–Lindquist conformal factor, with $\bar\Delta\phi=0$ proved | $\mathbb{R}^3\setminus\{0\}$ |
| Schwarzschild–de Sitter spatial slice, with $^3R=2\Lambda$ | curved slice |
| Flat FLRW data: momentum constraint identically, Hamiltonian $6H^2$ | flat slice |
| Chart initial data packaged with a vanishing constraint residual | pointwise |
| Conformal rescaling $h\mapsto\phi^4h$ with its inverse | pointwise |
| Conformal decomposition interface: $\phi$, $\beta$, $\sigma$, $\tau$ and both residual equations | stated, not solved |
| $H^s$ interface on a compact manifold: norm, completeness, point evaluation and product bounds | hypotheses, not constructed |

Every row is a statement at a point, on a chart, or an interface. None solves a
boundary-value problem, and none constructs a global solution.

## 4. The interface

The conformal data are a seed metric, a positive conformal factor, a shift
field, a transverse-traceless tensor and the mean curvature. The physical
metric is $\phi^4\bar h$, packaged so that its inverse $\phi^{-4}\bar h^{-1}$ is
available; the physical extrinsic curvature is the expression of §2, with and
without the conformal Killing term.

The two constraints are stated as residuals rather than as existence problems:

$$8\Delta\phi-\bar R\phi+|\sigma|^2\phi^{-7},
\qquad
(\bar\nabla_j(\bar L\beta)^{ij}+\bar\nabla^j\sigma_{ij})
-\tfrac23\phi^6\bar\nabla^i\tau .$$

A solution is the predicate that both vanish at a point. The covariant
derivatives and the conformal Killing term are inputs: the development has
coordinate expressions for them but no manifold connection with which to build
them from the shift. The shift's regularity is recorded separately (it is
$C^2$ on the slice); seed-metric regularity stays with the chart data, since
the seed is stored pointwise.

The one derived statement is that constant mean curvature with a transverse
$\sigma$ reduces the momentum residual to the divergence of the conformal
Killing term — the shift-free form of the equation.

## 5. The layers still missing

| Layer | Content | Status |
| --- | --- | --- |
| L0 | The conformal decomposition as an interface | **Done** — conformal factor, shift, transverse-traceless tensor, both residual systems |
| L1 | Manifold Sobolev spaces $H^s(\Sigma)$ with embedding, trace and product estimates | **Interface stated**; the space is not constructed |
| L2 | The linearised Lichnerowicz operator: invertibility or Fredholm alternative, maximum principle and Schauder/$H^s$ estimates | open; no elliptic theory in the development or its dependencies |
| L3 | Nonlinear existence by a fixed point, with small-data or near-flat hypotheses explicit | open |
| L4 | Regularity and uniqueness of the solution; comparison with the constant, warped and Brill–Lindquist instances | open |
| L5 | Handing the solved constraints to the hyperbolic layer | open; depends on L1–L4 |

## 6. What is not claimed

- No existence theorem for the constraint equations on any manifold.
- No constructed Sobolev space. The $H^s$ interface records the estimates a
  solver would use; it does not prove them.
- No elliptic regularity, Fredholm property, maximum principle or a priori
  estimate.
- No statement about boundary conditions, asymptotically flat ends, or
  non-compact $\Sigma$.
- No derivation of the field equation from the action for the alternatives
  (that is the fourth paper), and no numerical constraint solver.
- No construction of the conformal Killing operator or of covariant
  derivatives; they are supplied as data.
- The solution predicate is a condition on supplied operators, not a
  construction of them.

## 7. Relation to the other papers

The first paper supplies the tensor calculus and the exact solutions; the
Cauchy paper supplies the constraint functionals, the chart data packaging and
the hyperbolic roadmap. This paper adds the conformal split and the $H^s$
interface. A solution of the system here would enter the Cauchy paper as its
second layer and would not by itself prove Choquet–Bruhat–Geroch: hyperbolic
existence and geometric maximality remain separate layers.

## 8. Reproducibility and trust

The build is silent, every statement in the development is fully proved, and no
proof introduces an axiom beyond the three standard ones of the base libraries.
The audit covers the whole development, and the generated proof-status table is
checked against it in continuous integration.

## References

1. A. Lichnerowicz. *L'intégration des équations de la gravitation relativiste et le problème des n corps.* J. Math. Pures Appl. 23 (1944) 37–63.
2. J. W. York. *Gravitational energy and the initial-value problem.* Phys. Rev. Lett. 26 (1971) 1656.
3. Y. Choquet-Bruhat, J. W. York. *The Cauchy problem.* In *General Relativity and Gravitation* (Plenum, 1980).
4. R. Bartnik, J. Isenberg. *The constraint equations.* In *The Einstein Equations and the Large Scale Behavior of Gravitational Fields* (Birkhäuser, 2004). arXiv:gr-qc/0405092.
5. Y. Choquet-Bruhat. *General Relativity and the Einstein Equations.* Oxford University Press, 2009.
6. R. M. Wald. *General Relativity.* University of Chicago Press, 1984.
7. R. A. Adams, J. J. F. Fournier. *Sobolev Spaces.* 2nd ed., Academic Press, 2003.
8. A. Vergara Gil. *A Machine-Checked Solution Theory of General Relativity and Its Alternatives.* `docs/Gravitation-Formalisation.md`, 2026.
9. A. Vergara Gil. *The Cauchy Problem for the Einstein Equations: Formalised Constraints, a Wave Model, and a Roadmap.* `docs/Cauchy-Problem.md`, 2026.
