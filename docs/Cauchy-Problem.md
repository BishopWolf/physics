# The Cauchy Problem for the Einstein Equations: Formalised Constraints, a Wave Model, and a Roadmap

**Alex Vergara Gil**

24 November 2026

> **Companion paper.** This is the second of two accounts. Paper I
> (`Gravitation-Formalisation.md`) is the solution-theory paper: it proves that
> explicit metrics — Schwarzschild, Schwarzschild–de Sitter, Kerr,
> Reissner–Nordström, FLRW and the interior sphere — have the curvature and
> satisfy the field equations claimed for them. This paper isolates the other
> half of the subject: the initial-value problem. It records what is already
> formalised, states the Choquet–Bruhat–Geroch theorem precisely, and sets out
> the layers that are still missing. It does **not** claim a formalisation of
> that theorem.

---

## Abstract

The initial-value formulation of general relativity rests on two independent
layers: the ADM constraint equations on a Cauchy slice, and local
well-posedness of the evolution equations. This paper reports the first layer
as formalised in Lean 4 — the Hamiltonian and momentum constraints, their
moment-of-time-symmetry and maximal-slicing reductions, flat vacuum data, and a
non-vacuum data set showing that the constraints are not automatic — together
with local existence and uniqueness for the geodesic Cauchy problem via
Picard–Lindelöf.

It then formalises a genuine PDE Cauchy theorem: the d'Alembert formula solves
the one-dimensional wave equation with prescribed initial position and
velocity, including the proof that $\partial_t^2u=\partial_x^2u$. This is a
linear model, not the Einstein equations. The energy method gives zero-data
uniqueness on a closed interval and, by applying it to the difference of two
solutions, general-data uniqueness under explicit regularity and boundary
hypotheses. A three-dimensional box version, including energy conservation and
uniqueness for the constant-coefficient wave equation, is also formalised.

The paper states the Choquet–Bruhat–Geroch theorem, which produces the unique
maximal globally hyperbolic development of arbitrary constraint-satisfying
data, and explains why that theorem cannot yet be stated, let alone proved, in
the present pointwise framework. The missing layers are identified and ordered
into a concrete roadmap: manifold Lorentzian geometry, Sobolev and elliptic
theory for the constraints, quasilinear hyperbolic existence in a suitable
gauge, and gauge/constraint propagation together with geometric maximality.
The Cauchy-programme modules contribute 356 of the 1306 audited declarations
in Paper I's development.

**Keywords:** general relativity · Cauchy problem · ADM constraints ·
Choquet–Bruhat–Geroch · wave equation · energy method · formal verification

---

## 1. Why a separate paper

Paper I answers questions of the form: *given this metric, what is its
curvature, and does it solve this field equation?* That is solution theory. It
is not existence theory. The statement that *arbitrary* constraint-satisfying
initial data have a development is a theorem of quasilinear hyperbolic PDE
theory, not a corollary of any curvature computation.

Keeping the two apart has three advantages. Paper I no longer carries an
open-ended PDE limitation that its results do not need. The Cauchy programme
gets a precise statement of its target and of its current frontier. And the
constraint and geodesic layers are recorded where a reader looking for the
initial-value problem will find them, rather than as a short section in a paper
about exact solutions.

The division is also honest about dependencies. The constraint layer is
pointwise: it checks the constraint *expressions* once the metric, its spatial
curvature and the derivative of the extrinsic curvature are supplied. It does
not construct a manifold, derive the spatial curvature from the metric, or
solve the constraints. The geodesic layer proves local existence in a Banach
chart. Neither is a substitute for the PDE layer, and this paper does not
present them as one.

## 2. Initial data and the constraint equations

In the ADM 3+1 decomposition, a spacetime is foliated by spacelike slices
$\Sigma_t$. On a slice $\Sigma$, the initial data consist of a Riemannian
3-metric $h_{ij}$, a symmetric extrinsic curvature $K_{ij}$, and the
3-dimensional scalar curvature ${}^{3}R$ determined by $h$. The vacuum
constraints are

$$
H={}^{3}R+(\operatorname{tr}K)^2-K_{ij}K^{ij}=0,
\qquad
M_i=\nabla_j K^i{}_j-\nabla_i\operatorname{tr}K=0.
$$

The Hamiltonian constraint fixes the scalar curvature of the slice in terms of
the extrinsic curvature; the momentum constraint fixes the divergence of
$K$. They are four equations for the twelve components of $(h,K)$, so the
initial data are not arbitrary: four degrees of freedom are constrained, and
the remaining freedom is the physical gravitational data.

The simplest reduction is a moment of time symmetry, $K=0$, where
$H={}^{3}R$. A scalar-flat slice is therefore vacuum data. Under maximal
slicing, $\operatorname{tr}K=0$, the Hamiltonian constraint becomes
${}^{3}R=K_{ij}K^{ij}$. Constant extrinsic curvature satisfies the momentum
constraint, but not every constant $K$ satisfies the Hamiltonian constraint:
flat space with $K=0$ is vacuum, while flat space with
$K=\mathrm{diag}(1,1,0)$ has $H=2$. The constraints are therefore not
automatic, and the non-vacuum example is included precisely to make that point.

The development checks these equations once $h$, $K$, ${}^{3}R$ and the
derivative of $K$ are supplied. A chart layer computes the spatial Riemann
tensor from a metric field and the derivative of $K$ from the extrinsic
curvature field, and rebuilds the Minkowski data end to end. A nonconstant
warped metric,
$$
h=dx_0^2+(1+x_0^2)\left(dx_1^2+dx_2^2\right),
$$
gives $R_{0101}=-1$, so the derived curvature is not merely the flat
constant case. At the field level, the construction leaves the metric
regularity, Christoffel and vacuum-constraint hypotheses explicit. The result
is a global-chart wrapping with isometric chart-transition compatibility, not
arbitrary multi-chart gluing.

Two restrictions matter for what follows. First, ${}^{3}R$ remains an input to
the constraint check: the module verifies the constraint equation rather than
constructing ${}^{3}R$ intrinsically on a manifold. Second, $h$ and $K$ are
matrix fields in a chart, not geometric tensors on an arbitrary 3-manifold.
The development therefore formalises the *algebra* of the constraints, which
is exactly what a pointwise development can do, and stops short of the
geometric data a Cauchy theorem needs.

## 3. The geodesic Cauchy problem

A geodesic $x^\mu(\lambda)$ obeys

$$
\frac{d^2x^\mu}{d\lambda^2}
+\Gamma^\mu{}_{\rho\sigma}
\frac{dx^\rho}{d\lambda}
\frac{dx^\sigma}{d\lambda}=0.
$$

Writing $z=(x,\dot x)$, this becomes the first-order autonomous system

$$
\dot z=F(z),
\qquad
F(x,v)=\left(v,-\Gamma(x)(v,v)\right).
$$

For $C^1$ Christoffel symbols, Picard–Lindelöf gives a solution on some
interval $(-\varepsilon,\varepsilon)$ for every initial position and
velocity, and uniqueness on any interval where $F$ is Lipschitz. In flat
space the solution is the straight line
$x^\mu(\lambda)=x^\mu_0+\lambda v^\mu_0$.

This is local existence for test particles. It is stated for a Christoffel
field on a Banach space, not for a connection on a manifold, and it proves no
global continuation or maximal-interval theorem. It is the natural ODE shadow
of the initial-value problem, not the field-equation Cauchy problem.

## 4. A PDE Cauchy theorem: the wave equation

The constraint and geodesic layers are not yet a PDE existence theorem for the
field equations. The first PDE layer is the one-dimensional wave equation

$$
\partial_t^2u=\partial_x^2u.
$$

For initial position $f$ and velocity $g$, the d'Alembert solution is

$$
u(t,x)=\frac{f(x+t)+f(x-t)}2
+\frac12\int_{x-t}^{x+t}g(s)\,ds.
$$

Assuming $f$ has first and second derivatives and $g$ is $C^1$, the
formula is proved to satisfy the wave equation for every $(t,x)$, with
$u(0,x)=f(x)$ and $\partial_tu(0,x)=g(x)$. The proof uses the fundamental
theorem of calculus and the chain rule; it is a genuine PDE theorem, not a
citation.

The energy of a solution on an interval $[0,L]$ is

$$
E(t)=\frac12\int_0^L
\left(u_t^2+u_x^2\right)dx.
$$

For homogeneous Dirichlet data, differentiation under the integral and
integration by parts give

$$
\frac{dE}{dt}=0.
$$

Vanishing energy forces $u_t=0$ and $u_x=0$, and hence $u$ is constant in
time; with zero initial data it vanishes. This gives zero-data uniqueness in
the interior and, with the Dirichlet endpoints, on the closed interval.
Applying the same argument to the difference of two solutions gives
general-data uniqueness for solutions with the same Cauchy and boundary data.

The construction extends to a three-dimensional spatial box. The energy
$$
E(t)=\frac12\int_{\mathrm{Box}}
\left(u_t^2+|\nabla u|^2\right)d^3x
$$
is conserved for $u_{tt}=\Delta u$ under homogeneous Dirichlet data. The box
divergence theorem turns the time derivative of the energy into a boundary
flux, which vanishes. Zero energy forces $u_t=0$ and $\nabla u=0$, and time
integration gives zero-data uniqueness; the difference argument then gives
general-data uniqueness on the closed box.

This is a real Cauchy theorem in the sense that the data are arbitrary
functions with the stated differentiability, and the formula is proved to have
the required derivatives. It is deliberately narrow: the equation is linear,
constant-coefficient and posed on a box. There is no quasilinear term, no
gauge, no constraint propagation and no curved spatial geometry. It is a model
of the reduced wave equations, not a proof of local existence for the Einstein
equations.

On top of the scalar wave model, the linearized Einstein equations in wave
gauge are represented by a perturbation $h$ with
$\Box\bar h_{\mu\nu}=0$, where
$\bar h_{\mu\nu}=h_{\mu\nu}-\tfrac12\eta_{\mu\nu}h$. The transverse–traceless
plane wave is a concrete instance. The manifold-level derivation of the
linearized Einstein equations from a gauge choice remains open.

## 5. The target: Choquet–Bruhat–Geroch

The theorem this programme aims at is the following, stated here in its
standard smooth form.

> **Theorem (Choquet–Bruhat–Geroch).** Let $\Sigma$ be a smooth
> three-dimensional manifold, $h$ a smooth Riemannian metric on $\Sigma$,
> and $K$ a smooth symmetric $(0,2)$-tensor on $\Sigma$. Suppose
> $(h,K)$ satisfies the vacuum constraint equations. Then there exists a
> spacetime $(M,g)$ solving the vacuum Einstein equations and an embedding
> $\Sigma\to M$ inducing $h$ and $K$, which is maximal among globally
> hyperbolic developments and unique up to isometry.

The local existence and uniqueness half is Choquet-Bruhat's theorem [4],
developed in her book [10] and recounted in the arXiv historical account [11];
the maximal-development and uniqueness half is the Choquet–Bruhat–Geroch paper
[1], with a Zorn-free construction by Sbierski [2]. Survey treatments are
Rendall [3] and Chruściel [9]. The two founding papers [1,4] predate arXiv and
have no arXiv version.

This theorem is **not** stated in Lean anywhere in this repository, is not
axiomatised, and is not a hidden hypothesis of any theorem in Paper I. It is
recorded here as the target, with its hypotheses and conclusion, so that the
distance to it is visible.

## 6. What is missing

Four layers separate the present pointwise development from the theorem above.

1. **Manifold and Lorentzian geometry.** A Cauchy development needs a smooth
   3-manifold $\Sigma$, a Lorentzian 4-manifold $M$, an embedding, an
   induced metric, an extrinsic curvature and isometries. The present
   $MetricTensor$ is a matrix with a proved inverse at a point. The chart
   layer derives the spatial Riemann tensor and the momentum derivative from
   component fields and reconstructs the Minkowski data, but it does not
   construct an intrinsic manifold curvature or an arbitrary atlas. The
   horizon-regular Eddington–Finkelstein metric and inverse are available at
   chart level, including at $r=2M$, and its coordinate Ricci tensor is proved
   flat directly there, but they are not a Cauchy development.
   The only proved chart gluing is the Eddington–Finkelstein–Schwarzschild
   exterior overlap, via a metric pullback identity. Mathlib has smooth manifolds, but this
   repository has no pseudo-Riemannian layer, manifold Levi-Civita connection
   or causality theory.
2. **Sobolev spaces and the constraint problem.** The theorem is usually stated
   for Sobolev data $H^s$ with $s$ large, or for smooth data. Mathlib's
   Sobolev module works on $\mathbb{R}^n$, not on manifolds, and the
   repository has no elliptic theory for solving the constraints. The present
   module checks the constraints; it does not solve them. The formalised
   examples are a 1D $H^1$ embedding and trace estimate, a 3D box $H^1$
   norm, the Brill–Lindquist harmonic conformal factor on
   $\mathbb{R}^3\setminus\{0\}$, a curved Schwarzschild–de Sitter slice with
   ${}^{3}R=2\Lambda$, and flat FLRW data. General elliptic constraint solving
   on an arbitrary 3-manifold remains outside.
3. **Quasilinear hyperbolic existence.** In harmonic or wave gauge the vacuum
   Einstein equations become a quasilinear symmetric hyperbolic system. Local
   existence for that system is the analytic core of [4]. No Mathlib or
   dependency PDE theorem supplies it, and the surveyed Lean PDE projects are
   elliptic or Navier–Stokes formalisations. The linear wave theorem of §4 is a
   constant-coefficient model, not this layer.
4. **Gauge and constraint propagation, then maximality.** One must show that a
   reduced solution satisfies the gauge condition and the full Einstein
   equations, that the constraints propagate, and that developments patch to a
   maximal one. Propagation uses the contracted Bianchi identity, which is
   proved in the general chart framework. Maximality needs the Zorn argument of
   [1] or the construction of [2]. The chart-level isometry and embedding API
   exists, but geometric four-dimensional Lorentzian patching and isometric
   amalgamation remain open.

Layers 1, 3 and 4 are this paper's goal: the full Choquet–Bruhat–Geroch
theorem. Layer 2 is the subject of a separate paper on elliptic constraint
solving on arbitrary 3-manifolds, which Paper II takes as an input rather than
reproving.

## 7. A roadmap

The layers above suggest an order in which the work can be made checkable.

| Milestone | Physics content | Current status |
| --- | --- | --- |
| M0 | Linear 3D wave model on a box: energy, conservation, zero-energy, zero-data and general-data uniqueness | **Done** for the constant-coefficient wave equation on a closed box, under explicit regularity and Dirichlet data |
| M0.5 | Linearized Einstein equations in wave gauge | **Interface** for wave-gauge perturbations with $\Box\bar h=0$, including a TT plane-wave instance; not a manifold derivation |
| M1 | Smooth manifolds, Lorentzian metrics, Levi-Civita connection, curvature, causality, Bianchi | **Done at chart/global-chart scope**, including a horizon-regular Eddington–Finkelstein metric and inverse with direct Ricci flatness at the horizon, a Kruskal–Szekeres chart with a certified nondegenerate metric across the horizon, and isometric chart transitions preserving the induced metric and initial data, including a proved Eddington–Finkelstein–Schwarzschild exterior overlap; arbitrary multi-chart gluing and geometric patching remain outside |
| M2 | Manifold Sobolev spaces $H^s$, trace and embedding estimates, constraint data | **Done at 1D/3D-box Sobolev and curved-slice scope**: chart regularity, derived spatial curvature and momentum derivative, Minkowski and exterior Schwarzschild manifold-level instances, Brill–Lindquist conformal factor, Schwarzschild–de Sitter slice, flat FLRW data; general elliptic solving remains outside |
| M3 | Harmonic/wave gauge and the reduced quasilinear hyperbolic system | **Done at linearized 3D box and nonlinear flat-FLRW scope**: directional plane waves, superposition, harmonic gauge condition, linearized-box existence, and the FLRW reduced Einstein ODE; full $H^s(\mathbb{R}^3)$ quasilinear existence remains outside |
| M4 | Gauge recovery and constraint propagation | **Done at linearized 3D box and nonlinear flat-FLRW scope**: Bianchi constraint-propagation split, linearized gauge recovery, and FLRW propagation recovering the full Einstein equation; non-symmetric nonlinear 4D $H^s$ propagation remains outside |
| M5 | Maximal development | **Done at abstract Zorn and 1D open-domain scope**: maximal existence and amalgamation uniqueness for an ordered development system; geometric 4D Lorentzian patching remains outside |
| M6 | Cross-checks against explicit solutions | **Done at explicit coordinate and $t=0$ slice scope**: Schwarzschild, Schwarzschild–de Sitter, Kerr and FLRW satisfy the 4D field equations and agree with their initial slices |

M0 is complete for the linear constant-coefficient wave model; it is a model
result, not an Einstein theorem. M0.5 is a coordinate-level interface for the
linearized wave-gauge equations, not a proof of the manifold-level reduction.
M1 is complete at chart/global-chart scope: coordinate Christoffel, Riemann,
Ricci, scalar and Einstein tensors, timelike/null/spacelike classification,
covariant derivatives, torsion-freeness, metric compatibility, a chart Cauchy
surface, Minkowski global hyperbolicity, and the general second and contracted
Bianchi identities. The EF chart is a concrete instance with direct Ricci
flatness, including at the horizon. Isometric chart transitions are checked,
including compatibility of induced initial data and the
Eddington–Finkelstein–Schwarzschild exterior overlap; arbitrary multi-chart
gluing remains open. M2 is complete
at 1D/3D-box Sobolev and curved-slice scope, but general elliptic constraint
solving on arbitrary 3-manifolds is open. M3 and M4 are complete at
linearized-box and nonlinear-FLRW scope; the non-symmetric nonlinear 4D
$H^s$ problem is open. M5 is complete at abstract Zorn and 1D open-domain
scope, while geometric Lorentzian patching remains open. M6 is complete at
explicit coordinate and $t=0$ slice scope.

A useful intermediate target, weaker than full Choquet–Bruhat–Geroch, is local
existence in a fixed gauge for smooth data. It would already give a
machine-checked Cauchy theorem for a neighbourhood of the slice, and it avoids
the maximality problem until M5.

## 8. Relation to Paper I

The development audited in Paper I has 1306 declarations. It contains the
constraint, geodesic, wave, energy, uniqueness, chart, Bianchi, Sobolev,
reduced-Cauchy, gauge-recovery, maximal-development and explicit-development
layers discussed here, together with the solution theory, the alternative
theories, the axiom audit and the numerical pass. This paper's formal
contribution is 356 declarations. The remainder of Paper I is the written
account of the exact solutions.

The two papers share a boundary. Paper I proves that explicit metrics solve
their field equations on their coordinate domains; this paper asks whether
arbitrary data have a development at all. The explicit solutions are the test
cases for M6, not a proof of existence for other data. Conversely, a future
proof of Choquet–Bruhat–Geroch would not replace the metric-level computations
of Paper I: it would supply the existence theorem those computations currently
take for granted when they exhibit a solution.

## 9. Reproducibility and trust

The build is silent, no declaration uses `sorry`, `admit` or an axiom of its
own, and every axiom report stays inside
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$. The
axiom audit covers 1306 declarations, 790 of them theorem-like, and the
generated proof-status table is checked against the audit. The commands are:

```sh
cd gravitation
lake build
bash ../scripts/check_messages.sh
bash ../scripts/audit_axioms.sh
bash ../scripts/proof_status.sh --check
```

The formal names and the per-declaration status are in `Proof-Status.md`; the
mathematical content is the content of this paper.

## 10. What is not claimed

- No formalisation of the Choquet–Bruhat–Geroch theorem.
- No local existence theorem for the non-symmetric four-dimensional
  quasilinear Einstein equations in $H^s(\mathbb{R}^3)$. The formalised
  existence results are the linearized 3D wave-gauge box and the nonlinear flat
  FLRW reduced ODE; the general 1952 Choquet–Bruhat theorem without symmetry
  remains open.
- No solution of the constraint equations on arbitrary 3-manifolds, and no
  manifold $H^s$ Sobolev theory. The formalised results are the 1D $H^1$
  embedding and trace inequality, the 3D closed-box $H^1$ norm, derived 3D
  curvature and nonlinear ADM constraints, the Brill–Lindquist conformal
  factor, the curved Schwarzschild–de Sitter slice, and flat FLRW data.
- No global existence or maximal-interval theorem for geodesics.
- No arbitrary multi-chart manifold gluing or general curved global
  hyperbolicity. The formalised M1 layer is chart-level.
- No global uniqueness theorem for the wave Cauchy problem. The formalised
  results are zero-data uniqueness on a closed interval and general-data
  uniqueness for solutions with the same Cauchy and boundary data, both under
  explicit regularity.
- 3D wave energy conservation and uniqueness are for the linear
  constant-coefficient wave equation on a closed box, not for the Einstein
  equations.
- The linearized wave-gauge layer is a coordinate-level interface, not a
  manifold-level derivation of the linearized Einstein equations.
- M1–M6 have kernel-checked instances only at the scopes stated in §7.
  Arbitrary multi-chart 3-manifold gluing, general elliptic constraint solving,
  full non-symmetric $H^s(\mathbb{R}^3)$ quasilinear hyperbolic local
  existence, and geometric 4D Lorentzian patching remain open.
- No axiom, `sorry`, or cited theorem smuggled in as a hypothesis. The CBG
  statement in §5 is prose with references; it is not a Lean declaration.

## References

1. Y. Choquet-Bruhat, R. Geroch. *Global aspects of the Cauchy problem in general relativity.* Comm. Math. Phys. 14 (1969) 329–335. doi:10.1007/BF01645389. No arXiv version.
2. J. Sbierski. *On the existence of a maximal Cauchy development for the Einstein equations — a dezornification.* arXiv:1309.7591 (2013).
3. A. D. Rendall. *Theorems on existence and global dynamics for the Einstein equations.* Living Rev. Relativ. 8 (2005) 6. arXiv:gr-qc/0505133.
4. Y. Choquet-Bruhat. *Théorème d'existence pour certains systèmes d'équations aux dérivées partielles non linéaires.* Acta Math. 88 (1952) 141–225. doi:10.1007/BF02392131. No arXiv version.
5. R. M. Wald. *General Relativity.* University of Chicago Press, 1984.
6. A. Vergara Gil. *A Machine-Checked Solution Theory of General Relativity and Its Alternatives.* `docs/Gravitation-Formalisation.md`, 2026.
7. The Mathlib Community. *The Lean Mathematical Library.* CPP 2020. `leanprover-community/mathlib4`, `v4.36.0`.
8. `leanprover-community/physlib`. https://github.com/leanprover-community/physlib
9. P. T. Chruściel. *Cauchy problems for the Einstein equations: an introduction.* Lecture notes, 2018. https://homepage.univie.ac.at/piotr.chrusciel/teaching/Cauchy/Roscoff.pdf
10. Y. Choquet-Bruhat. *General Relativity and the Einstein Equations.* Oxford Mathematical Monographs, Oxford University Press, 2009.
11. Y. Choquet-Bruhat. *Beginnings of the Cauchy problem.* arXiv:1410.3490 (2014).
