# A Machine-Checked Solution Theory of General Relativity and Its Alternatives

**Alex Vergara Gil**

21 November 2026; revised 25 November 2026

> **Revision note.** This version adds the horizon-regular ingoing
> Eddington–Finkelstein chart, the Kerr, Reissner–Nordström, FLRW and
> linearized-gravity results, and an expanded numerical cross-check. The Lean
> development is maintained in Physlib; this repository carries the vendored
> copy, the numerical pass and this account. A companion paper isolates the
> Cauchy problem and the remaining existence theory.

---

## Abstract

General relativity is usually presented through its curvature tensors, but the
physical content of a solution lies in the passage from a line element to the
field equations it satisfies. We report a machine-checked development of that
passage for a family of exact spacetimes. Starting from the metric and its
inverse, the Christoffel symbols, Riemann tensor, Ricci tensor, scalar curvature
and Einstein tensor are computed by differentiation and contraction. The
resulting solution theory covers Schwarzschild, Schwarzschild–de Sitter, Kerr,
Reissner–Nordström, FLRW and the interior Schwarzschild sphere, and it recovers
the Friedmann equations and the linearized Einstein equations in the
appropriate limits.

The central physical result concerns the cosmological constant. In
Schwarzschild–de Sitter spacetime, $\Lambda$ enters every independent Riemann
component, yet the electric part of the Weyl tensor is
$\mathrm{diag}(0,-2M/r^3,M/r^3,M/r^3)$, exactly as in Schwarzschild. The
cosmological constant changes the Ricci tensor and the Kretschmann scalar, but
not the free gravitational field. For Schwarzschild we also give the ingoing
Eddington–Finkelstein chart, in which the metric and its inverse remain finite
and nondegenerate at $r=2M$; the horizon is a coordinate singularity of the
static chart, not a curvature singularity.

The development includes the ADM constraints, local existence of geodesics, and
a one-dimensional wave Cauchy theorem with an energy uniqueness argument. It
also contains the field equations or exact reductions of sixteen alternative
theories. All statements are checked in Lean 4 against Mathlib, with no
`sorry` and no axiom beyond those of the base libraries; the audited surface
contains 1547 declarations, 936 of them theorem-like. An independent Vulkan
pass evaluates the same tensors in double precision and reproduces the closed
forms at the $10^{-6}$ level.

**Keywords:** general relativity · exact solutions · cosmological constant ·
black holes · Cauchy problem · alternative theories of gravity · formal
verification

---

## 1. Introduction

Curvature algebra is only the grammar of general relativity. The physical
question is whether a given line element actually solves the field equations,
and what geometry it describes. A calculation that defines the Riemann tensor
and then assumes the components of Schwarzschild's curvature verifies
bookkeeping, not physics. The content of a solution is the chain

$$
g_{\mu\nu}\;\longrightarrow\;\Gamma^\rho{}_{\mu\nu}
\;\longrightarrow\;R^\rho{}_{\sigma\mu\nu}
\;\longrightarrow\;\mathrm{Ric}_{\mu\nu}
\;\longrightarrow\;S\;\longrightarrow\;G_{\mu\nu},
$$

with every derivative and contraction carried out from the metric itself.

This paper reports a development that closes that chain for the static,
spherically symmetric family and for several further exact solutions, and
contrasts the results with the alternative theories usually discussed as
replacements for general relativity. The main contributions are:

1. **Exact solution theory from the line element.** For Schwarzschild and
   Schwarzschild–de Sitter, all independent Riemann components, the Ricci
   tensor, the scalar curvature and the Einstein tensor are derived directly
   from the metric. For Schwarzschild–de Sitter the result is
   $\mathrm{Ric}=\Lambda g$, $S=4\Lambda$, $G=-\Lambda g$; at
   $\Lambda=0$ it reduces to Schwarzschild's vacuum solution.
2. **The cosmological constant and the Weyl tensor.** The electric part of the
   Weyl tensor of Schwarzschild–de Sitter is proved to equal that of
   Schwarzschild for every $\Lambda$. The de Sitter contribution is pure
   trace: it changes the Ricci tensor but not the free gravitational field.
3. **A horizon-regular chart.** The ingoing Eddington–Finkelstein metric and
   its inverse are given explicitly, the metric is certified as a nondegenerate
   tensor at $r=2M$, and its coordinate Ricci tensor is proved flat directly
   from the EF components, including at the horizon. This removes the
   $f\neq0$ restriction for the metric and Ricci tensor, while leaving the full
   Riemann transfer and the maximal extension as separate problems.
4. **Further exact solutions and limits.** Kerr is proved Ricci flat in
   Boyer–Lindquist coordinates; Reissner–Nordström satisfies the
   Einstein–Maxwell equations; FLRW is equivalent to the Friedmann equations;
   and the linearized Einstein tensor reduces to
   $-\tfrac12\Box\bar h$ in Lorenz gauge.
5. **Initial-value and alternative-theory layers.** The ADM constraints,
   geodesic local existence, a wave Cauchy model, and the field equations or
   exact reductions of sixteen alternative theories are developed alongside
   the exact solutions.
6. **Independent numerical and formal checks.** A double-precision Vulkan pass
   evaluates the same tensors from the same metrics, and the Lean development
   is checked by a silent build, an axiom audit and a per-declaration proof
   status table.

## 2. The gap

A survey of the relevant repositories (November 2026) motivates the scope.

| Repository | Contents | Physics / GR |
| --- | --- | --- |
| `anthropics/formal-math` | self-contained Lean projects (zeta zeros, 3SUM-APSP, ETH) | none |
| `anthropics/fermats-last-theorem` | complete formalisation of Fermat's Last Theorem | none |
| `openai/ten-proofs` | Lean certificates for ten results | none |
| `openai/math` | 722 manuscripts, 162 with Lean formalisations | none |
| `leanprover-community/physlib` | classical mechanics, EM, QFT, QM, relativity | master: special-relativistic kinematics and Lorentz/Poincaré representation theory; the unmerged `gravity` branch adds the development reported here |
| HepLean | particles, gauge theory, spinors | not gravitation |
| `TataSatyaPratheek/mathematical-physics-lean` | dimension-parametric Einstein tensor and field equations | conditional on 365 axioms; the trust surface is the axioms, not the kernel |
| QIQT (Zenodo 20837810) | conditional derivation of the field equations from an information bound | explicitly conditional |

Two conclusions follow. First, curvature *definitions* are not the bottleneck.
Second, no surveyed project proves that a black-hole metric solves the vacuum
equations: Schwarzschild appears, where it appears at all, as an unproved
claim. The gap is the passage from definitions to solutions, and that is what
this development addresses.

## 3. From a line element to a field equation

The starting point is a four-dimensional metric $g_{\mu\nu}$ and its inverse
$g^{\mu\nu}$, with signature $(-,+,+,+)$. The Levi-Civita connection is

$$
\Gamma^\rho{}_{\mu\nu}
=\frac12 g^{\rho\sigma}
\left(\partial_\mu g_{\sigma\nu}
+\partial_\nu g_{\sigma\mu}
-\partial_\sigma g_{\mu\nu}\right),
$$

the Riemann tensor is

$$
R^\rho{}_{\sigma\mu\nu}
=\partial_\mu\Gamma^\rho{}_{\nu\sigma}
-\partial_\nu\Gamma^\rho{}_{\mu\sigma}
+\Gamma^\rho{}_{\mu\lambda}\Gamma^\lambda{}_{\nu\sigma}
-\Gamma^\rho{}_{\nu\lambda}\Gamma^\lambda{}_{\mu\sigma},
$$

and the Ricci tensor, scalar curvature and Einstein tensor are

$$
\mathrm{Ric}_{\sigma\nu}=R^\rho{}_{\sigma\rho\nu},
\qquad
S=g^{\sigma\nu}\mathrm{Ric}_{\sigma\nu},
\qquad
G_{\mu\nu}=\mathrm{Ric}_{\mu\nu}-\frac12 S\,g_{\mu\nu}.
$$

For a candidate metric, the calculation is therefore mechanical: differentiate
the components, invert the metric, contract, and compare with the required
field equation. The development follows exactly this route. A constant metric
gives $\Gamma=R=\mathrm{Ric}=S=G=0$, so Minkowski is a computed vacuum
solution rather than an assumption. For a curved metric, the same code
evaluates the connection and its derivatives and then contracts.

The metric and its inverse are kept together as a single object, with the proof
that their product is the identity. This matters physically: a contraction
$g^{\mu\nu}T_{\mu\nu}$ is only meaningful with the inverse of the metric that
actually appears in the line element. The curvature interface also carries the
algebraic symmetries of a Riemann tensor, so a tensor that fails antisymmetry
or the first Bianchi identity cannot be passed off as curvature.

### 3.1 Verification

The derivation is checked in Lean 4 with Mathlib. The audited surface contains
1547 declarations, 936 of them theorem-like; no declaration uses `sorry`,
`admit` or an axiom of its own, and every axiom report stays inside
`{propext, Classical.choice, Quot.sound}`. The build is silent, and CI checks
the axiom audit, the silent build and the generated proof-status table. The
mathematical statements are the ones in the text; the implementation names and
the per-declaration census are collected in Appendix A and
`Proof-Status.md`.

## 4. Results

### 4.1 Curvature calculus

For any metric satisfying the curvature interface, the Einstein tensor is
symmetric, and its trace is

$$
g^{ij}G_{ij}=\left(1-\frac n2\right)S.
$$

In four dimensions this gives the standard equivalence
$G=0\iff\mathrm{Ric}=0$: a vacuum solution can be characterised either by the
vanishing of the Einstein tensor or by Ricci flatness. The first Bianchi
identity is part of the curvature interface, and antisymmetry in the first pair
is derived from the other symmetries rather than assumed.

### 4.2 The initial-value problem

On a spacelike slice $\Sigma$ with induced metric $h_{ij}$ and extrinsic
curvature $K_{ij}$, the vacuum constraints are

$$
H={}^{3}R+(\operatorname{tr}K)^2-K_{ij}K^{ij}=0,
\qquad
M_i=\nabla_j K^i{}_j-\nabla_i\operatorname{tr}K=0.
$$

The first is the Hamiltonian constraint; the second is the momentum
constraint. At a moment of time symmetry, $K=0$, the Hamiltonian constraint
reduces to ${}^{3}R=0$, so a scalar-flat slice is vacuum data. Under maximal
slicing, $\operatorname{tr}K=0$, it becomes
${}^{3}R=K_{ij}K^{ij}$. Flat space with $K=0$ satisfies both constraints,
while flat space with $K=\mathrm{diag}(1,1,0)$ has $H=2$: the constraints
are not automatic.

The general existence theory for these data is the subject of the companion
paper. The founding local-existence and maximal-development papers are
Choquet-Bruhat [16] and Choquet-Bruhat–Geroch [10]; [17] is Choquet-Bruhat's
arXiv historical account, and [18] is her later book treatment. Here the
constraints are used as the initial-value layer that the exact solutions must
satisfy. The manifold wrapper also carries isometric chart
transitions: on an overlap, the induced spatial metric and the ADM data are
proved compatible, while arbitrary multi-chart atlas gluing remains outside.
A regular exterior Schwarzschild chart gives a concrete manifold-level
instance with the curved time-symmetric slice.

### 4.3 Geodesics

A geodesic $x^\mu(\lambda)$ satisfies

$$
\frac{d^2x^\mu}{d\lambda^2}
+\Gamma^\mu{}_{\rho\sigma}
\frac{dx^\rho}{d\lambda}
\frac{dx^\sigma}{d\lambda}=0.
$$

Writing this as a first-order system in $(x,\dot x)$, Picard–Lindelöf gives
local existence from every initial position and velocity, and local uniqueness
under a Lipschitz condition. In flat space the solutions are the straight lines
$x^\mu(\lambda)=x^\mu_0+\lambda v^\mu_0$. This is local existence for test
particles, not for the gravitational field.

### 4.4 Schwarzschild geometry

The Schwarzschild line element is

$$
ds^2=-f(r)\,dt^2+\frac{dr^2}{f(r)}
+r^2\left(d\theta^2+\sin^2\theta\,d\varphi^2\right),
\qquad
f(r)=1-\frac{2M}{r}.
$$

The horizon is at $r=2M$. The curvature scalar
$K=R_{\rho\sigma\mu\nu}R^{\rho\sigma\mu\nu}=48M^2/r^6$ is finite there, so
the horizon is not a curvature singularity; it is a coordinate singularity of
the $(t,r)$ chart. The physical curvature is best displayed in an orthonormal
frame, where the electric part of the Weyl tensor is

$$
\mathrm{diag}\left(0,-\frac{2M}{r^3},\frac{M}{r^3},\frac{M}{r^3}\right).
$$

This is the tidal field of a mass $M$: radial and angular eigenvalues of
opposite sign, with zero trace. The corresponding coordinate components,
obtained by differentiating the metric's Christoffel symbols, are:

| Component | Value |
| --- | --- |
| $R^t{}_{rtr}$ | $2M/(r^3f)$ |
| $R^t{}_{\theta t\theta}$ | $-M/r$ |
| $R^t{}_{\varphi t\varphi}$ | $-(M/r)\sin^2\theta$ |
| $R^r{}_{\theta r\theta}$ | $-M/r$ |
| $R^r{}_{\varphi r\varphi}$ | $-(M/r)\sin^2\theta$ |
| $R^\theta{}_{\varphi\theta\varphi}$ | $(2M/r)\sin^2\theta$ |

Contracting gives $\mathrm{Ric}=0$, $S=0$ and $G=0$. The derivation uses
the metric itself; no hand-supplied Riemann table enters the final statement.

The static chart hides the regular horizon. In ingoing
Eddington–Finkelstein coordinates $(v,r,\theta,\varphi)$, with
$v=t+r_*$ and $dr_*/dr=1/f$, the line element becomes

$$
ds^2=-f(r)\,dv^2+2\,dv\,dr
+r^2\left(d\theta^2+\sin^2\theta\,d\varphi^2\right).
$$

The inverse has the simple form

$$
g^{vv}=0,\qquad g^{vr}=g^{rv}=1,\qquad g^{rr}=f(r),
$$

with the angular entries $r^{-2}$ and
$r^{-2}\sin^{-2}\theta$. At $r=2M$, where $f=0$, the metric components
satisfy

$$
g_{rr}=0,\qquad g^{rr}=0,\qquad g_{vr}=1.
$$

The vanishing of the $rr$ component does not make the metric degenerate: the
cross term $g_{vr}=1$ keeps the determinant nonzero. This is the precise
sense in which the Eddington–Finkelstein chart removes the horizon obstruction.
It still excludes the curvature singularity $r=0$ and the polar axis
$\sin\theta=0$. The full Riemann computation above remains in Schwarzschild
coordinates, but the coordinate Ricci tensor is also proved to vanish directly
from the EF components, with no $f\neq0$ hypothesis, including at $r=2M$.

### 4.5 Schwarzschild–de Sitter for general $\Lambda$

With

$$
f(r)=1-\frac{2M}{r}-\frac{\Lambda r^2}{3},
\qquad
n(r)=\frac{f'}2=\frac{M}{r^2}-\frac{\Lambda r}{3},
$$

the $t\,r\,t\,r$ component is

$$
R^t{}_{rtr}
=-\partial_r\Gamma^t{}_{tr}
+\Gamma^t{}_{tr}\Gamma^r{}_{rr}
-\left(\Gamma^t{}_{tr}\right)^2
=-\frac{n'}f
=\frac{2M/r^3+\Lambda/3}{f}.
$$

The remaining independent components are:

| Component | Value |
| --- | --- |
| $R^t{}_{rtr}$ | $(2M/r^3+\Lambda/3)/f$ |
| $R^t{}_{\theta t\theta}=R^r{}_{\theta r\theta}$ | $\Lambda r^2/3-M/r$ |
| $R^t{}_{\varphi t\varphi}=R^r{}_{\varphi r\varphi}$ | $(\Lambda r^2/3-M/r)\sin^2\theta$ |
| $R^\theta{}_{\varphi\theta\varphi}$ | $(2M/r+\Lambda r^2/3)\sin^2\theta$ |

The angular Christoffel symbols carry no $M$ or $\Lambda$, so the
cosmological constant enters the angular components only through $1-f$.

Contracting the Riemann tensor gives

$$
\mathrm{Ric}_{\mu\nu}=\Lambda g_{\mu\nu},
\qquad
S=4\Lambda,
\qquad
G_{\mu\nu}=-\Lambda g_{\mu\nu}.
$$

The physically important point is the split between the trace and the Weyl
tensor. Since

$$
C_{titj}=R_{titj}+\frac{\Lambda}{3}g_{ij},
$$

the de Sitter contribution to the Riemann tensor is precisely the trace part
that the Weyl tensor removes. The frame electric part of $C$ is therefore

$$
\mathrm{diag}\left(0,-\frac{2M}{r^3},\frac{M}{r^3},\frac{M}{r^3}\right)
$$

for every $\Lambda$. A cosmological constant changes the Ricci tensor and the
volume, but not the free gravitational field.

Squaring the whole frame tensor gives the Kretschmann scalar

$$
K=\frac{48M^2}{r^6}+\frac{8\Lambda^2}{3}.
$$

The first term is Schwarzschild's Weyl square; the second is the trace
contribution. Thus $\Lambda$ survives in $K$ even though it cancels from the
electric Weyl eigenvalues. Figures 1 and 2 show the two effects.

![Frame eigenvalues of the Schwarzschild–de Sitter Riemann tensor against $r$, for $M=1$ and $\Lambda=0,0.05,0.1$.](figures/tidal-eigenvalues.svg)

**Figure 1.** Frame eigenvalues of the Riemann tensor of Schwarzschild–de Sitter against $r$, for $M=1$ and $\Lambda=0$ (blue), $0.05$ (orange) and $0.1$ (green). Solid curves are the angular eigenvalue $R_{t\theta t\theta}=M/r^3-\Lambda/3$; dashed curves the radial one, $R_{trtr}=-2M/r^3-\Lambda/3$; dotted lines mark $-\Lambda/3$. Raising $\Lambda$ shifts both families rigidly by $-\Lambda/3$ and leaves the splitting $R_{t\theta t\theta}-R_{trtr}=3M/r^3$ unchanged. That shift is the trace part, and exactly what the Weyl tensor removes: the Weyl eigenvalues stay on the $\Lambda=0$ curves while both Riemann eigenvalues tend to $-\Lambda/3$ at large $r$. Generated by `docs/figures/make_tidal_figure.py`.

![Kretschmann scalar of Schwarzschild and Schwarzschild–de Sitter against $r$, for $M=1$ and $\Lambda=0,0.05,0.1$.](figures/kretschmann.svg)

**Figure 2.** Kretschmann scalar $K=R_{\rho\sigma\mu\nu}R^{\rho\sigma\mu\nu}$ against $r$, for $M=1$ and $\Lambda=0$ (blue), $0.05$ (orange), $0.1$ (green). Because the Weyl part is $\Lambda$-independent, $K=48M^2/r^6+\tfrac83\Lambda^2$: each de Sitter curve is the Schwarzschild one lifted by the constant $(8/3)\Lambda^2$ (dotted), so instead of decaying to zero the curvature tends to $8\Lambda^2/3$. That lift is the trace part again — the same $\Lambda$ that cancels from the electric Weyl eigenvalues in Figure 1 survives in the full Riemann square. The dashed curve is the Weyl-only invariant $48M^2/r^6$; the GPU pass checks the sum for $\Lambda=0.1$ to $1.9\times10^{-7}$ relative. Generated by `docs/figures/make_kretschmann_figure.py`.

The metric-level statements hold where $r\neq0$, $f\neq0$ and
$\sin\theta\neq0$. For $\Lambda>0$, the middle condition excludes the roots
of $3r-6M-\Lambda r^3$.

### 4.6 Alternative theories

The `Modified` subtree develops sixteen alternatives, at the depth each admits.
Several are taken to their field equations, not merely named:

* **Einstein–Cartan.** An affine connection with torsion, metric compatibility,
  the contorsion tensor, and the algebraic inversion of Cartan's spin–torsion
  equation. In vacuum the torsion equation forces the GR reduction.
* **Teleparallel / TEGR.** The Weitzenböck connection and torsion from a tetrad,
  the superpotential and torsion scalar, a flat FLRW tetrad, the identity
  $R_{\mathrm{LC}}=-T+B$, and the $f(T)$ Friedmann equation.
* **Kaluza–Klein.** The five-dimensional metric with an explicit inverse, its
  unitriangular factorization, the compact-circle diffeomorphism inducing the
  $U(1)$ shift, the Kaluza miracle $R^5=R^4-\tfrac14F^2$, and the
  equivalence of the five-dimensional vacuum equations with four-dimensional
  Einstein–Maxwell.
* **Lovelock / Gauss–Bonnet.** Generalized Kronecker deltas, the five-index
  contraction identity, and the Bach–Lanczos theorem that the Gauss–Bonnet
  variation vanishes identically for $n\le4$.
* **Einstein–Aether.** The Jacobson–Mattingly coupling combinations, the
  kinetic tensor and quadratic Lagrangian, the spin-2/1/0 squared speeds, the
  GW170817 luminal-graviton condition, and the renormalized Newton constant.
* **Massive gravity.** The Fierz–Pauli mass term, the Boulware–Deser ghost-free
  tuning, the trace identities, the vDVZ static and light-deflection ratios,
  and the dRGT elementary-symmetric potentials.
* **PPN.** The full Will–Nordtvedt ten-parameter structure, the
  fully/semiconservative classes, embeddings of GR, Brans–Dicke, metric
  $f(R)$ and Nordström, and the light-deflection, Shapiro, perihelion and
  Nordtvedt factors.
* **Brans–Dicke and $f(R)$/Starobinsky.** The PPN parameter, coupling bounds
  and Cassini constraint, the $\omega\to\infty$ limit and ghost pole; the
  algebraic $f(R)$ field equation, its trace identity, the Starobinsky
  potential, scalar mass and Einstein-frame plateau.
* **Chameleon screening.** The density–mass–range chain, Yukawa suppression,
  the thin-shell factor, and the exterior profile with screened and unscreened
  fifth-force bounds.
* **MOND, MOG, TeVeS, Nordström.** The deep-MOND relation and flat rotation
  curves, the bounded MOG enhancement, the TeVeS disformal metric with explicit
  inverse and preserved Lorentzian signature, and Nordström's conformal metric
  with $S=-6\Box\phi/\phi^3$ and the Einstein–Fokker equivalence.
* **Galileon and Ostrogradsky.** The one-dimensional total-derivative and shift
  structure; the degenerate velocity Hessian and the Hamiltonian unbounded
  below, contrasted with a positive-definite kinetic term.

The depth is uneven and is stated per module. Einstein–Cartan, teleparallel,
Kaluza–Klein, Lovelock, Einstein–Aether, massive gravity, PPN, Brans–Dicke/$f(R)$
and chameleon screening carry their field equations or exact reductions; MOND,
MOG and TeVeS remain structural (their full cosmological perturbation theory is
not formalised), and the Galileon result is one-dimensional. None of these is a
full non-linear solution theory, and empirical strengths and weaknesses are
recorded in prose, not as theorems.

MOND, MOG and TeVeS are the subject of a fourth paper, which promotes them from
these structural statements to full field theories — action, field equations,
PPN limit, stability and cosmology — or records why a given alternative cannot
be promoted.

### 4.7 Conservation

The contracted Bianchi identity

$$
\nabla^\mu G_{\mu\nu}=0
$$

is proved for the Schwarzschild–de Sitter frame Einstein space, rather than
assumed. Because $\mathrm{Ric}=\Lambda\eta$ and $S=4\Lambda$ are constant,
the frame derivatives vanish and the identity reduces to
$\nabla^a\mathrm{Ric}_{ab}=\tfrac12\nabla_b S$; the divergence of the Einstein
tensor then follows. This is the conservation law that makes the field
equations consistent with the contracted Bianchi identity.

For a general curvature bundle the algebraic lemmas still take the identity as
an explicit parameter, because no covariant derivative for an arbitrary bundle
is formalised. That is a generality gap in the API, not an assumption in the
solution theory: no solution-theory theorem depends on it as a hypothesis. Once
the identity is supplied, $\alpha\,\mathrm{Ric}+\beta\,Sg$ is conserved only
when $\alpha=-2\beta$.

### 4.8 Kerr, Reissner–Nordström, FLRW, and linearized gravity

**Kerr.** In Boyer–Lindquist coordinates $(t,r,\theta,\varphi)$, with
$\Sigma=r^2+a^2\cos^2\theta$ and $\Delta=r^2-2Mr+a^2$, the metric is
stationary and axisymmetric. The development computes its Christoffel symbols
and proves

$$
\mathrm{Ric}_{\mu\nu}=0,\qquad S=0,\qquad G_{\mu\nu}=0
$$

at every point with $\Sigma\neq0$, $\Delta\neq0$ and $\sin\theta\neq0$.
It also proves the horizon structure $r_\pm=M\pm\sqrt{M^2-a^2}$, the extremal
coalescence at $a^2=M^2$, the stationary-limit surface, and the ZAMO
frame-dragging angular velocity. At $a=0$ the solution reduces to
Schwarzschild.

**Reissner–Nordström.** With

$$
f(r)=1-\frac{2M}{r}+\frac{Q^2}{r^2}
$$

and the radial Coulomb field $F_{01}=-Q/r^2$, the Maxwell stress-energy
satisfies

$$
G_{\mu\nu}=8\pi T^{\mathrm{EM}}_{\mu\nu}.
$$

The Ricci scalar vanishes and the electromagnetic stress-energy is trace free.
The inner and outer horizons, their coalescence at $Q^2=M^2$, and positivity
of $f$ in the overcharged regime follow from the same metric.

**FLRW.** For the homogeneous and isotropic metric with scale factor $a(t)$
and spatial curvature $k$,

$$
ds^2=-dt^2+a(t)^2
\left(\frac{dr^2}{1-kr^2}+r^2d\Omega^2\right),
$$

the coordinate pipeline gives the Ricci tensor, scalar curvature and Einstein
tensor. The Einstein equations hold exactly when the Friedmann equations do,
and the result is bridged to the cosmological FLRW API.

**Linearized gravity.** Around $g=\eta+h$, the trace-reversed perturbation is
$\bar h_{\mu\nu}=h_{\mu\nu}-\tfrac12\eta_{\mu\nu}h$. The linearized Riemann,
Ricci and Einstein tensors are invariant under linearized diffeomorphisms, and
in Lorenz gauge

$$
G^{\mathrm{lin}}_{\mu\nu}
=-\frac12\Box_\eta\bar h_{\mu\nu}.
$$

The transverse–traceless plane wave solves the linearized vacuum equations, and
the Newtonian limit reduces to Poisson's equation
$\nabla^2\Phi=4\pi\rho$.

## 5. Numerical cross-check

The same metrics are evaluated independently by a Vulkan compute pass in double
precision. For each lattice point it computes $g_{ab}$, central-difference
derivatives, $\Gamma^k{}_{ij}$, $\partial_\mu\Gamma^k{}_{ij}$,
$R^\rho{}_{\sigma\mu\nu}$, $\mathrm{Ric}$, $R$, $G$, the Kretschmann
scalar, the frame electric part and four Riemann components. The host compares
the emitted values with the closed forms.

Measured on an AMD RX 570 (RADV POLARIS10, Vulkan 1.4.354), 108 lattice points,
$h=10^{-4}$, tolerance $10^{-6}$ ($10^{-5}$ for Kerr, FLRW and the
interior sphere):

| Case / quantity | measured |
| --- | --- |
| Minkowski, $\max|Ric|$ | $0$ |
| Schwarzschild, $\max|Ric|$ | $1.831\times10^{-7}$ |
| Schwarzschild, Kretschmann vs $48M^2/r^6$ (relative) | $1.105\times10^{-7}$ |
| Schwarzschild–de Sitter $\Lambda=0.1$, $\max|Ric-\Lambda g|$ | $6.944\times10^{-7}$ |
| Schwarzschild–de Sitter, $K$ vs $48M^2/r^6+\tfrac83\Lambda^2$ (relative) | $1.910\times10^{-7}$ |
| Schwarzschild–de Sitter, $R^t{}_{rtr}$ | $5.923\times10^{-7}$ |
| Schwarzschild–de Sitter, Weyl electric part | $1.394\times10^{-8}$ |
| Kerr $a=0.5$, $\max|Ric|$ | $2.100\times10^{-7}$ |
| Kerr $a=0.5$, Kretschmann vs the closed form (relative) | $1.707\times10^{-7}$ |
| Kerr $a=0.5$, $\max|\nabla_a G^{ab}|$ (contracted Bianchi) | $5.044\times10^{-9}$ |
| Kerr $a=0.5$, $\max|G|$ | $1.416\times10^{-7}$ |
| Reissner–Nordström $Q=0.5$, $\max|G-8\pi T|$ | $1.085\times10^{-7}$ |
| Reissner–Nordström $Q=0.5$, $\max|R|$ | $2.405\times10^{-8}$ |
| Reissner–Nordström $Q=0.5$, Kretschmann vs the closed form (relative) | $1.173\times10^{-7}$ |
| Reissner–Nordström $Q=0.5$, $\max|\nabla_a G^{ab}|$ with $G\neq0$ | $6.827\times10^{-5}$ |
| Schwarzschild $M=2$ ($r\in[5,5.75]$), $\max|Ric|$ | $1.932\times10^{-7}$ |
| Schwarzschild–de Sitter $\Lambda=-0.05$, $\max|Ric-\Lambda g|$ | $1.833\times10^{-7}$ |
| Schwarzschild–de Sitter $\Lambda=-0.05$, Kretschmann vs the closed form (relative) | $7.513\times10^{-8}$ |
| FLRW $a=1+Ht+t^2$, $k=0.3$, $\max$ deviation of $Ric$, $R$, $G$ from the closed forms | $1.273\times10^{-6}$ |
| Interior Schwarzschild $Rc=5$, $Ra=4$, $\max|G-8\pi\,\mathrm{diag}(\rho,p,p,p)|$ | $8.895\times10^{-8}$ |

The de Sitter case is the control: it has genuinely nonzero Ricci curvature,
recovered at the same noise level as the vacuum case, so the vacuum test is not
vacuous. FLRW and the interior sphere are further non-vacuum controls: FLRW
exercises the expansion terms, and the interior sphere checks the
constant-density Einstein tensor. The host also forms the frame components
$R_{ab}/\sqrt{|g_{aa}g_{bb}|}$ and checks them against
$\Lambda\,\mathrm{diag}(-1,1,1,1)$, which lands at $2.0\times10^{-8}$ for
both static cases. It confirms the lifted Kretschmann scalar of Figure 2 to
$1.9\times10^{-7}$ relative. The Kerr and Reissner–Nordström Kretschmann
checks contract the full Riemann tensor rather than only its trace, and the
static checks are repeated at $M=2$ and at negative $\Lambda$, so no
tolerance is tuned to a single parameter set.

This is a regression test for the implementation and for the closed forms, not
evidence for the theorems. Finite differences say nothing about an analytic
solution; the Lean statement is exact, while the numerical agreement is
second-order accurate at $h^2\approx10^{-8}$ with roundoff
$\varepsilon/h^2\approx10^{-8}$.

## 6. Limitations

The frame-level Weyl, Kretschmann, Ricci and Einstein results are total. The
metric-level derivations in Schwarzschild coordinates assume $r\neq0$,
$f\neq0$ and $\sin\theta\neq0$. These are coordinate restrictions, not
physical ones. At $r=0$ the curvature scalar diverges, so no chart can remove
that point. At $f=0$ the static chart's $g_{rr}$ and $g^{rr}$ diverge,
although the curvature is finite; this is the horizon. At $\sin\theta=0$ the
angular coordinate $\varphi$ degenerates, as it does on any polar axis.

The ingoing Eddington–Finkelstein chart removes the $f\neq0$ obstruction at
the level of the metric and inverse: the metric is a nondegenerate tensor at
$r=2M$, with $g_{rr}=0$, $g^{rr}=0$ and $g_{vr}=1$. Its coordinate Ricci
tensor is proved flat directly from the EF components, including at $r=2M$.
It does not remove the curvature singularity or the axis, and the full Riemann
component theorems above remain stated in Schwarzschild coordinates. A Kruskal–Szekeres chart is now available at metric level, with a certified
nondegenerate metric across the horizon. The Eddington–Finkelstein and
Schwarzschild exterior charts are proved to agree on their overlap, via the
tortoise-coordinate transition map and a metric pullback identity; general
multi-chart gluing still requires the Cauchy development treated in the
companion paper.

## 7. Reproducibility

```sh
cd gravitation
lake exe cache get          # Mathlib oleans
lake build                  # silent: zero messages
bash ../scripts/check_messages.sh
bash ../scripts/audit_axioms.sh
bash ../scripts/proof_status.sh --check
cd vulkan && make && ./gr_vulkan shaders/tensor.comp.spv
```

The numerical pass checks quantities that are themselves theorems, so it tests
the implementation against the mathematics rather than substituting for it. CI
runs the silent-build check, the axiom audit and the proof-status check on every
push and pull request, and runs the Vulkan pass on the lavapipe software driver,
so no GPU runner is required.

## 8. Conclusion

The solution theory of general relativity is formalisable, at least for the
static spherically symmetric family and several further exact solutions. The
Schwarzschild–de Sitter calculation shows why this matters: the cosmological
constant appears in every Riemann component, yet cancels from the Weyl tensor.
A formalisation turns that cancellation into a theorem rather than a remark.
The same chain $g\mapsto\partial g\mapsto\Gamma\mapsto\partial\Gamma\mapsto
R\mapsto\mathrm{Ric}\mapsto S\mapsto G$ now runs from the line element to the
field equation for Schwarzschild, Schwarzschild–de Sitter, Kerr,
Reissner–Nordström and FLRW. The horizon-regular Eddington–Finkelstein metric
removes the first coordinate obstruction, and its coordinate Ricci tensor is
proved flat directly, including at the horizon. What remains is the global
initial-value problem: the existence and uniqueness of a maximal development
for arbitrary constraint-satisfying data.

## Appendix A. Declaration census

Generated from `gravitation/.lake/decls.tsv` by the axiom audit. The table
covers the local top-level modules, the 92 vendored modules under
`Gravitation.Relativity.*` and `Gravitation.Cosmology.*`, and the already-merged
`IncompressibleSphere` from the `physlib` dependency; the local
`Gravitation.KretschmannTotal` addendum contributes two corollaries. The names
in the proofs are the `GeneralRelativity` ones either way.

| Module | Declarations |
| --- | --- |
| `Gravitation.InitialDataInterface` | 77 |
| `Gravitation.ManifoldInterface` | 72 |
| `Gravitation.AqualVariation` | 67 |
| `PhyslibAlpha.Relativity.General.Schwarzschild.IncompressibleSphere` | 53 |
| `Gravitation.SobolevInitialData` | 42 |
| `Gravitation.DiracCounting` | 41 |
| `Gravitation.Bianchi` | 38 |
| `Gravitation.EddingtonFinkelstein` | 36 |
| `Gravitation.Relativity.General.SchwarzschildDeSitter.Basic` | 36 |
| `Gravitation.SchwarzschildManifold` | 34 |
| `Gravitation.KruskalSzekeres` | 33 |
| `Gravitation.Relativity.General.ReissnerNordstrom.Basic` | 31 |
| `Gravitation.Perturbation` | 31 |
| `Gravitation.Relativity.General.SchwarzschildDeSitter.DeSitterFrame` | 25 |
| `Gravitation.Relativity.Modified.PPNParameters` | 25 |
| `Gravitation.Relativity.General.Kerr.Basic` | 24 |
| `Gravitation.Relativity.General.Schwarzschild.Basic` | 24 |
| `Gravitation.Relativity.Modified.ChameleonScreening` | 24 |
| `Gravitation.CauchyInterfaces` | 22 |
| `Gravitation.ReducedCauchy` | 22 |
| `Gravitation.Relativity.Modified.EinsteinAether` | 21 |
| `Gravitation.ConformalDecomposition` | 20 |
| `Gravitation.Relativity.Modified.KaluzaKlein.Basic` | 19 |
| `Gravitation.PPNParameters` | 18 |
| `Gravitation.Relativity.General.GravitationalConstant` | 18 |
| `Gravitation.Relativity.Modified.BransDicke` | 18 |
| `Gravitation.Mathematics.Calculus.CoordDeriv` | 17 |
| `Gravitation.Relativity.General.Schwarzschild.ElectricWeyl` | 16 |
| `Gravitation.Relativity.Modified.FRGravity` | 15 |
| `Gravitation.WaveEnergy` | 15 |
| `Gravitation.Relativity.General.GeodesicSystem` | 14 |
| `Gravitation.Relativity.Metrics.CurvatureBridge` | 14 |
| `Gravitation.Relativity.Modified.MOND` | 14 |
| `Gravitation.Relativity.Modified.Teleparallel.FLRWTorsion` | 14 |
| `Gravitation.ReducedWave3D` | 13 |
| `Gravitation.Cosmology.FLRW.Basic` | 12 |
| `Gravitation.Cosmology.FLRW.FriedmannEquations` | 12 |
| `Gravitation.GaugeRecovery` | 12 |
| `Gravitation.Relativity.General.SchwarzschildDeSitter.CoordinateCurvature` | 12 |
| `Gravitation.Relativity.Metrics.Minkowski` | 12 |
| `Gravitation.Relativity.Metrics.StaticSphericalMetric.Basic` | 12 |
| `Gravitation.Relativity.Modified.EinsteinCartan.Contorsion` | 12 |
| `Gravitation.MaximalDevelopment` | 11 |
| `Gravitation.Relativity.General.Linearized.TraceReversed` | 11 |
| `Gravitation.Relativity.General.MinkowskiCoordinateMetric` | 11 |
| `Gravitation.Relativity.Metrics.StaticSphericalMetric.Christoffel` | 11 |
| `Gravitation.Relativity.Modified.MassiveGravity.DRGT` | 11 |
| `Gravitation.WaveCauchy` | 11 |
| `Gravitation.ClassicalMechanics.OrbitalMechanics.NewtonianGravity` | 10 |
| `Gravitation.Relativity.Metrics.CoordinateMetric` | 10 |
| `Gravitation.Relativity.Modified.EinsteinCartan.Basic` | 10 |
| `Gravitation.Relativity.Modified.Nordstrom` | 10 |
| `Gravitation.MondFieldTheory` | 9 |
| `Gravitation.Relativity.General.InitialData.Basic` | 9 |
| `Gravitation.Relativity.General.Kerr.RicciCurvature` | 9 |
| `Gravitation.Relativity.Metrics.MetricTrace` | 9 |
| `Gravitation.Relativity.Modified.EinsteinCartan.ModifiedTorsion` | 9 |
| `Gravitation.Relativity.Modified.MassiveGravity.FierzPauli` | 9 |
| `Gravitation.Relativity.Modified.TeVeS` | 9 |
| `Gravitation.Relativity.Modified.Teleparallel.Basic` | 9 |
| `Gravitation.Relativity.Modified.Lovelock.Basic` | 8 |
| `Gravitation.Relativity.Modified.Lovelock.ConstantCurvature` | 8 |
| `Gravitation.Relativity.Modified.MOG` | 8 |
| `Gravitation.Cosmology.FLRW.Christoffel` | 7 |
| `Gravitation.ExplicitDevelopments` | 7 |
| `Gravitation.Relativity.General.Kerr.Christoffel` | 7 |
| `Gravitation.Relativity.Metrics.CurvatureDerivatives` | 7 |
| `Gravitation.Relativity.Tensors.EinsteinTensor` | 7 |
| `Gravitation.Relativity.Tensors.RiemannTensor` | 7 |
| `Gravitation.WaveEnergy3D` | 7 |
| `Gravitation.WaveEnergy3DWave` | 7 |
| `Gravitation.MogFieldTheory` | 6 |
| `Gravitation.Relativity.General.Linearized.GaugeTransform` | 6 |
| `Gravitation.Relativity.General.Linearized.MinkowskiDalembertian` | 6 |
| `Gravitation.Relativity.Metrics.Basic` | 6 |
| `Gravitation.Relativity.Modified.Lovelock.Contract5` | 6 |
| `Gravitation.Relativity.Modified.MassiveGravity.Basic` | 6 |
| `Gravitation.Relativity.Modified.Ostrogradsky` | 6 |
| `Gravitation.Relativity.Modified.Teleparallel.FTGravity` | 6 |
| `Gravitation.Relativity.Tensors.MaxwellStressEnergy` | 6 |
| `Gravitation.TeVeSFieldTheory` | 6 |
| `Gravitation.Relativity.General.InitialData.AnisotropicSlice` | 5 |
| `Gravitation.Relativity.General.InitialData.FlatSlice` | 5 |
| `Gravitation.Relativity.General.Kerr.MetricDeriv` | 5 |
| `Gravitation.Relativity.General.Linearized.Basic` | 5 |
| `Gravitation.Relativity.General.Linearized.LorenzGauge` | 5 |
| `Gravitation.Relativity.General.Linearized.NewtonianPerturbation` | 5 |
| `Gravitation.Relativity.General.Linearized.TTWave` | 5 |
| `Gravitation.Relativity.Metrics.ConformalMetric` | 5 |
| `Gravitation.Relativity.Modified.Galileon` | 5 |
| `Gravitation.Relativity.Modified.KaluzaKlein.KaluzaMiracle` | 5 |
| `Gravitation.Relativity.Modified.KaluzaKlein.TriangularFactorization` | 5 |
| `Gravitation.Relativity.Modified.MassiveGravity.VDVZ` | 5 |
| `Gravitation.WaveUniqueness3D` | 5 |
| `Gravitation.Cosmology.FLRW.Curvature` | 4 |
| `Gravitation.LinearizedWaveGauge` | 4 |
| `Gravitation.Mathematics.GeneralizedKronecker` | 4 |
| `Gravitation.Relativity.General.Linearized.Laplacian3` | 4 |
| `Gravitation.Relativity.General.Linearized.LinearizedChristoffel` | 4 |
| `Gravitation.Relativity.General.Schwarzschild.CoordinateCurvature` | 4 |
| `Gravitation.Relativity.Metrics.Ricci` | 4 |
| `Gravitation.Relativity.Metrics.Riemann` | 4 |
| `Gravitation.Relativity.Modified.KaluzaKlein.GaugeTransform` | 4 |
| `Gravitation.Relativity.Tensors.RicciTensor` | 4 |
| `Gravitation.Relativity.General.Linearized.LinearizedRiemann` | 3 |
| `Gravitation.Relativity.Metrics.Christoffel` | 3 |
| `Gravitation.Relativity.Metrics.RicciScalar` | 3 |
| `Gravitation.Divergence3D` | 2 |
| `Gravitation.KretschmannTotal` | 2 |
| `Gravitation.Relativity.General.InitialData.CovariantDerivTensor2` | 2 |
| `Gravitation.Relativity.General.Linearized.LinearizedRicci` | 2 |
| `Gravitation.Relativity.Metrics.Einstein` | 2 |
| `Gravitation.Relativity.Metrics.NullVector` | 2 |
| `Gravitation.Relativity.Metrics.RiemannFromData` | 2 |
| `Gravitation.Relativity.Tensors.EMFieldStrength` | 2 |
| `Gravitation.Relativity.Tensors.Tensor2` | 2 |
| `Gravitation.WaveUniqueness` | 2 |
| `Gravitation.ManifoldSobolev` | 1 |
| `Gravitation.Mathematics.FinSum` | 1 |
| `Gravitation.Mathematics.MatrixInverse` | 1 |
| `Gravitation.Relativity.General.FrameSumOfSquares` | 1 |
| `Gravitation.Relativity.General.Linearized.LinearizedEinstein` | 1 |
| `Gravitation.Relativity.Metrics.SpaceTimeDerivBridge` | 1 |
| `Gravitation.Relativity.Tensors.PerfectFluidStressEnergy` | 1 |
| `Gravitation.WaveEnergy3DConservation` | 1 |
| **Total** | **1547** |

All 1547 declarations are `proved` against `{propext, Classical.choice, Quot.sound}`; the generated table is
`Proof-Status.md`.

## References

1. L. de Moura, S. Kong, J. Avigad, F. van Doorn, J. von Raumer. *The Lean 4 theorem prover and programming language.* CADE-28, 2021.
2. The Mathlib Community. *The Lean Mathematical Library.* CPP 2020. `leanprover-community/mathlib4`, `v4.36.0`.
3. `leanprover-community/physlib`. https://github.com/leanprover-community/physlib
4. J. Tooby-Smith. *HepLean.* arXiv:2405.08863.
5. QIQT. *An audited human–AI loop: a conditional derivation of the Einstein field equations.* Zenodo 20837810.
6. `TataSatyaPratheek/mathematical-physics-lean`. https://github.com/TataSatyaPratheek/mathematical-physics-lean
7. `anthropics/formal-math`, `anthropics/fermats-last-theorem`, `openai/ten-proofs`, `openai/math`.
8. R. M. Wald. *General Relativity.* University of Chicago Press, 1984.
9. C. W. Misner, K. S. Thorne, J. A. Wheeler. *Gravitation.* Freeman, 1973.
10. Y. Choquet-Bruhat, R. Geroch. *Global aspects of the Cauchy problem in general relativity.* Comm. Math. Phys. 14 (1969) 329–335.
11. M. Milgrom. *A modification of the Newtonian dynamics as a possible alternative to the hidden mass hypothesis.* ApJ 270 (1983) 365.
12. J. W. Moffat. *Scalar–tensor–vector gravity theory.* JCAP 03 (2006) 004.
13. J. D. Bekenstein. *Relativistic gravitation theory for the modified Newtonian dynamics paradigm.* Phys. Rev. D 70 (2004) 083509.
14. M. Ostrogradsky. *Mémoires sur les équations différentielles, relatives au problème des isopérimètres.* Mem. Acad. St. Petersbourg 6 (1850) 385.
15. A. Vergara Gil. *The Cauchy Problem for the Einstein Equations in Lean 4: Formalised Constraints, a Wave Model, and a Roadmap.* Companion manuscript, `docs/Cauchy-Problem.md`, 2026.
16. Y. Choquet-Bruhat. *Théorème d'existence pour certains systèmes d'équations aux dérivées partielles non linéaires.* Acta Math. 88 (1952) 141–225. doi:10.1007/BF02392131. No arXiv version.
17. Y. Choquet-Bruhat. *Beginnings of the Cauchy problem.* arXiv:1410.3490 (2014).
18. Y. Choquet-Bruhat. *General Relativity and the Einstein Equations.* Oxford Mathematical Monographs, Oxford University Press, 2009.

## Appendix B. Source format

This article is written in Markdown with LaTeX mathematics so that it can be read in the repository. For arXiv submission, `pandoc -f markdown -t latex Gravitation-Formalisation.md -o gravitation.tex` produces a LaTeX manuscript; the mathematics is already in `$…$`/`$$…$$` form and needs no rewriting. Figures 1 and 2 are SVGs produced by `docs/figures/make_tidal_figure.py` and `docs/figures/make_kretschmann_figure.py`; `rsvg-convert -f pdf` converts each to the PDF that arXiv prefers.
