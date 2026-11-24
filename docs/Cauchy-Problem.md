# The Cauchy Problem for the Einstein Equations in Lean 4: Formalised Constraints, a Wave Model, and a Roadmap

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

The initial-value formulation of general relativity rests on two formal
layers that are independent of any particular solution: the ADM constraint
equations on a Cauchy slice, and local well-posedness of the evolution
equations. This paper reports the first layer as formalised in Lean 4 — the
Hamiltonian and momentum constraints, their moment-of-time-symmetry and
maximal-slicing reductions, a flat vacuum data set, and a non-vacuum data set
showing that the constraints are not automatic — together with local existence
and uniqueness for the geodesic Cauchy problem via Mathlib's
Picard–Lindelöf theorem. It then formalises a genuine PDE Cauchy theorem: the
d'Alembert formula solves the one-dimensional wave equation with prescribed
initial position and velocity, including the proof that `∂ₜ²u = ∂ₓ²u`. This is
a linear model, not the Einstein equations. The paper states the
Choquet–Bruhat–Geroch theorem, which produces the unique maximal globally
hyperbolic development of arbitrary constraint-satisfying data, and explains
why that theorem cannot yet be stated, let alone proved, in the present
pointwise framework. The missing layers are identified and ordered into a
concrete formalisation roadmap. The energy method then proves zero-data
uniqueness on the closed interval, and applying it to the difference of two
solutions gives general-data uniqueness there, under explicit regularity and,
respectively, homogeneous Dirichlet or matching boundary hypotheses. The wave,
energy and uniqueness modules, together with the 3D divergence foundation,
contribute fifty-four of the 758 audited declarations in Paper I's development.

**Keywords:** general relativity · Cauchy problem · ADM constraints · Lean 4 ·
Mathlib · Choquet–Bruhat–Geroch · formal verification

---

## 1. Why a separate paper

Paper I answers questions of the form: *given this metric, what is its
curvature, and does it solve this field equation?* That is solution theory, and
it is where the kernel-checked results of this repository lie. It is not
existence theory. The statement that *arbitrary* constraint-satisfying initial
data have a development is a theorem of quasilinear hyperbolic PDE theory, not
a corollary of any curvature computation.

Keeping the two apart has three advantages. Paper I no longer carries an
open-ended PDE limitation that its results do not need. The Cauchy programme
gets a precise statement of its target and of its current frontier. And the
formalised constraint and geodesic layers are recorded where a reader looking
for the initial-value problem will find them, rather than as a short section in
a paper about exact solutions.

The division is also honest about dependencies. The constraint module is
pointwise: it checks the constraint *expressions* once the metric, its spatial
curvature and the derivative of the extrinsic curvature are supplied. It does
not construct a manifold, derive the spatial curvature from the metric, or
solve the constraints. The geodesic module proves local existence in a Banach
chart. Neither module is a substitute for the PDE layer, and this paper does
not present them as one.

## 2. Formalised initial data and constraints

The module `Gravitation.Relativity.General.InitialValue` (vendored at
`gravitation/vendor/Gravitation/Relativity/General/InitialValue.lean`) works in
the ADM 3+1 decomposition. Initial data consist of a Riemannian 3-metric `h`,
its 3-dimensional Riemann tensor `R3`, and a symmetric extrinsic curvature `K`:

```lean
structure InitialData where
  h : MetricTensor 3
  R3 : RiemannTensor 3
  K : Tensor2 3
  Ksymm : IsSymm K
```

The Hamiltonian and momentum constraints are

$$H = {}^{3}R + (\operatorname{tr} K)^2 - K_{ij}K^{ij},
\qquad
M_i = \partial_j K^{i}{}_{j} - \partial_i \operatorname{tr} K,$$

with `InitialData.ham` and `momConstraint` as their Lean definitions and
`InitialData.IsVacuumData` as the conjunction `H = 0 ∧ M = 0`. The momentum
constraint takes the derivative field `dK` as an argument; it does not derive
`dK` from `K`.

The formalised reductions and examples are:

| Lean declaration | Statement |
| --- | --- |
| `InitialData.ham_eq_scalarCurv_of_K_zero` | at a moment of time symmetry (`K = 0`), `H = ³R` |
| `InitialData.ham_zero_iff_scalarCurv_zero_of_K_zero` | hence `H = 0 ↔ ³R = 0` when `K = 0` |
| `InitialData.ham_eq_of_trace_zero` | under maximal slicing (`tr K = 0`), `H = ³R − K_{ij}K^{ij}` |
| `trace_sq_eq_of_ham_zero` | on a scalar-flat slice, `H = 0` forces `(tr K)² = K_{ij}K^{ij}` |
| `momConstraint_zero_of_dK_zero` | constant extrinsic curvature satisfies the momentum constraint |
| `flatData_isVacuum` | flat `ℝ³` with `K = 0` satisfies both vacuum constraints |
| `squeezedData_ham` | flat `ℝ³` with `K = diag(1,1,0)` has `H = 2` |
| `squeezedData_ham_ne_zero` | so the vacuum constraints are not automatic |

Two restrictions matter for what follows. First, `R3` is a field of
`InitialData`, not a function of `h`: the module checks the constraint
equation, not that `R3` is the curvature of `h`. Second, `h` and `R3` are
matrices and tensors at a point in a chart, not objects on a manifold. The
module therefore formalises the *algebra* of the constraints, which is exactly
what a pointwise development can do, and stops short of the geometric data a
Cauchy theorem needs.

## 3. Formalised geodesic Cauchy problem

The module `Gravitation.Relativity.General.Geodesics` treats the second-order
geodesic equation as a first-order autonomous ODE on `E × E`:

```lean
abbrev Christoffel (E : Type*) ... := E → E →L[ℝ] E →L[ℝ] E
def geodesicAccel (Γ : Christoffel E) (x v : E) : E := - Γ x v v
def geodesicField (Γ : Christoffel E) : E × E → E × E :=
  fun z => (z.2, geodesicAccel Γ z.1 z.2)
```

For `C¹` Christoffel symbols, Mathlib's Picard–Lindelöf theorem gives:

| Lean declaration | Statement |
| --- | --- |
| `geodesic_ivp_exists` | for every `(x₀, v₀)` there are `ε > 0` and a solution on `(-ε, ε)` |
| `geodesic_ivp_exists_curve` | the same existence statement in split curve/velocity form |
| `geodesic_ivp_unique` | uniqueness on `[a,b]` inside a ball where `geodesicField Γ` is Lipschitz |
| `flat_geodesic` | in flat space, `t ↦ x₀ + t • v₀` solves the geodesic equation for all `t` |

This is local existence, and it is stated for a Christoffel field on a Banach
space, not a connection on a manifold. It is the natural ODE shadow of the
initial-value problem, and it is genuinely proved; it is not the field-equation
Cauchy problem. In particular, the module proves no global continuation and no
maximal-interval theorem.

## 4. A formalised PDE Cauchy theorem: the one-dimensional wave equation

The constraint and geodesic modules are not yet a PDE existence theorem for the
field equations. The first PDE layer is formalised in
`gravitation/Gravitation/WaveCauchy.lean`, in the namespace
`GeneralRelativity`. For functions `f g : ℝ → ℝ` it defines

$$u(t,x)=\frac{f(x+t)+f(x-t)}2+\frac12\int_{x-t}^{x+t}g(s)\,ds.$$

The formula is the classical d'Alembert solution [10]; the Lean declaration is
`dAlembert`; the theorem `dAlembert_wave_equation`
proves

$$\partial_t^2 u(t,x)=\partial_x^2 u(t,x)$$

for every `t x`, assuming `f` has first and second derivatives `f'`, `f''` and
`g` has first derivative `g'` with `g` continuous. The initial conditions are
separate theorems: `dAlembert_zero` proves `u(0,x)=f x`, and
`hasDerivAt_dAlembert_zero` proves `∂ₜu(0,x)=g x`. The combined statement is
`dAlembert_cauchy_data`.

| Lean declaration | Statement |
| --- | --- |
| `dAlembert` | the d'Alembert formula |
| `dAlembert_zero` | `u(0,x) = f x` |
| `hasDerivAt_dAlembert_zero` | `∂ₜu(0,x) = g x` |
| `hasDerivAt_dAlembert_t`, `hasDerivAt_dAlembert_x` | the first derivatives in time and space |
| `hasDerivAt_waveT`, `hasDerivAt_waveX` | the second derivatives of those expressions |
| `dAlembert_wave_equation` | `∂ₜ²u = ∂ₓ²u` |
| `dAlembert_cauchy_data` | both initial conditions together |
| `waveEnergy`, `hasDerivAt_waveEnergy` | the energy functional and its time derivative |
| `waveEnergyDerivIntegral_eq_zero` | the integration-by-parts identity for homogeneous Dirichlet data |
| `waveEnergy_eq_initial` | energy conservation in time |
| `eq_zero_of_waveEnergy_eq_zero` | vanishing energy forces `u_t = u_x = 0` pointwise |
| `u_eq_initial_of_ut_zero` | vanishing time derivative makes the field constant in time |
| `wave_zero_of_zero_data` | interior zero-data uniqueness for the 1D wave equation |
| `wave_zero_of_zero_data_Icc` | zero-data uniqueness on the closed interval |
| `WaveSolutionOn` | bundled regularity for a 1D wave solution |
| `wave_unique_of_same_data` | two solutions with the same Cauchy data agree on the closed interval |
| `integral_divergence_box_eq_zero` | the 3D box divergence theorem with vanishing boundary flux |
| `waveEnergy3D` | the 3D wave energy on a spatial box |
| `hasDerivAt_waveEnergy3D` | differentiation of the 3D energy under the box integral |
| `waveEnergy3D_eq_initial_of_divergence` | 3D energy conservation conditional on an explicit divergence identity |
| `waveEnergy3D_eq_initial_of_wave` | 3D wave energy conservation from `u_tt = Δu` |
| `eq_zero_of_waveEnergy3D_eq_zero` | vanishing box energy forces `u_t = 0` and `∇u = 0` |
| `wave_zero_of_zero_data3D` | zero-data uniqueness on the closed 3D box |
| `wave_unique3D_of_same_data` | general-data uniqueness on the closed 3D box |
| `WaveGaugePerturbation`, `linEinstein_eq_zero_of_waveGauge` | wave-gauge perturbations with `□h̄ = 0` are linearized vacuum solutions |
| `ttWave_waveGauge` | the TT plane wave is a concrete wave-gauge perturbation |

This is a real Cauchy theorem in the sense that the data are arbitrary
functions with the stated differentiability, and the formula is proved to have
the required derivatives. It is deliberately narrow. The equation is
one-dimensional, linear and constant-coefficient; there is no quasilinear term,
no three-dimensional spatial domain, no gauge and no constraint propagation.
Uniqueness is now formalised on the closed interval by the energy method
(below); it is not a global result. It is therefore a model of the reduced wave
equations, not a proof
of local existence for the Einstein equations. It does, however, remove one item
from the "no PDE layer at all" column: the repository now has a kernel-checked
PDE Cauchy theorem whose proofs use the fundamental theorem of calculus and the
chain rule, rather than a citation.

The energy layer is in `gravitation/Gravitation/WaveEnergy.lean`. It defines
`waveEnergy` and proves `hasDerivAt_waveEnergy` (differentiation under the
interval integral), `waveEnergyDerivIntegral_eq_zero` (integration by parts with
homogeneous Dirichlet data), and `waveEnergy_eq_initial` (conservation in time).
The zero-energy lemma `eq_zero_of_waveEnergy_eq_zero` and the constancy lemma
`u_eq_initial_of_ut_zero` then yield `wave_zero_of_zero_data`: a solution with
zero initial position and velocity vanishes in the interior `Ioo 0 L`. The
boundary-inclusive form `wave_zero_of_zero_data_Icc` adds the homogeneous
Dirichlet endpoints and gives zero-data uniqueness on `Icc 0 L`.
`gravitation/Gravitation/WaveUniqueness.lean` packages the regularity as
`WaveSolutionOn` and proves `wave_unique_of_same_data`: two regular solutions
with the same initial position, velocity, spatial derivative and Dirichlet
boundary values agree on the closed interval. The proof applies
`wave_zero_of_zero_data_Icc` to their difference, with an explicit bound on the
difference energy integrand. This is closed-interval uniqueness under the stated
regularity and boundary hypotheses; it is not a global uniqueness theorem, and
it is not a uniqueness theorem for the Einstein equations.

The spatial 3+1 layer begins with `gravitation/Gravitation/Divergence3D.lean`.
Its theorem `integral_divergence_box_eq_zero` is Mathlib's Bochner divergence
theorem specialized to a box in `Fin 3 → ℝ`: if the vector field is continuous,
differentiable in the interior, and its normal component has zero integral on
every face, then the integral of its divergence vanishes. This is the
multidimensional integration-by-parts tool needed for the 3D energy method.
`gravitation/Gravitation/WaveEnergy3D.lean` then defines the energy on a
spatial box and proves `hasDerivAt_waveEnergy3D`, differentiating under the box
integral under explicit continuity and boundedness hypotheses. It does not yet
identify this derivative with the divergence of `u_t ∇u`, nor use
`u_tt = Δu`; that identification and the resulting 3D uniqueness theorem remain
the next step. `gravitation/Gravitation/WaveEnergy3DConservation.lean` combines
the energy derivative with the box divergence theorem to prove
`waveEnergy3D_eq_initial_of_divergence`: the energy is constant when the
differentiated energy density is twice the divergence of an explicit vector
field and the normal flux vanishes. The divergence identity is still an
explicit hypothesis, not a consequence of `u_tt = Δu` claimed here.
`gravitation/Gravitation/WaveEnergy3DWave.lean` closes that gap for the wave
case: it defines `F = u_t ∇u`, proves the flux derivative and the divergence
identity from `u_tt = Δu` and the mixed-partial relation
`∇u_t = (∇u)_t`, and concludes `waveEnergy3D_eq_initial_of_wave`. The energy is
conserved under explicit regularity and homogeneous Dirichlet data. The
zero-energy lemma `eq_zero_of_waveEnergy3D_eq_zero` then turns vanishing energy
into pointwise vanishing of `u_t` and `∇u`; time integration gives zero-data
uniqueness (`wave_zero_of_zero_data3D`), and applying it to the difference of
two solutions gives general-data uniqueness (`wave_unique3D_of_same_data`) on
the closed box, using homogeneous Dirichlet data for both the field and its time
derivative. This is uniqueness for the linear constant-coefficient wave
equation, not for the Einstein equations. On top of this layer,
`gravitation/Gravitation/LinearizedWaveGauge.lean` records the coordinate-level
wave-gauge interface `WaveGaugePerturbation` and proves
`linEinstein_eq_zero_of_waveGauge` from the vendored Lorenz-gauge reduction.
The existing TT plane wave is shown to satisfy this interface via
`ttWave_waveGauge`. The manifold-level layers remain open.

## 5. The target: Choquet–Bruhat–Geroch

The theorem this programme aims at is the following, stated here in its
standard smooth form.

> **Theorem (Choquet–Bruhat–Geroch).** Let `Σ` be a smooth three-dimensional
> manifold, `h` a smooth Riemannian metric on `Σ`, and `K` a smooth symmetric
> `(0,2)`-tensor on `Σ`. Suppose `(h, K)` satisfies the vacuum constraint
> equations. Then there exists a spacetime `(M, g)` solving the vacuum Einstein
> equations and an embedding `Σ → M` inducing `h` and `K`, which is maximal
> among globally hyperbolic developments and unique up to isometry.

The local existence and uniqueness half is Choquet-Bruhat's theorem
[4]; the maximal-development and uniqueness half is the Choquet–Bruhat–Geroch
paper [1], with a Zorn-free construction by Sbierski [2]. Survey treatments are
Rendall [3] and Chruściel [9].

This theorem is **not** stated in Lean anywhere in this repository, is not
axiomatised, and is not a hidden hypothesis of any theorem in Paper I. It is
recorded here as the target, with its hypotheses and its conclusion, so that the
distance to it is visible.

## 6. What is missing

The distance is not a single lemma. Five layers separate the present pointwise
development from the theorem above.

1. **Manifold and Lorentzian geometry.** The current `Metric` and
   `MetricTensor` are matrices with a proved two-sided inverse at a point.
   A Cauchy development needs a smooth 3-manifold `Σ`, a Lorentzian 4-manifold
   `M`, an embedding `Σ → M`, an induced metric, an extrinsic curvature, and
   isometries between developments. Mathlib has smooth manifolds, but the
   repository has no pseudo-Riemannian manifold layer, no Levi-Civita connection
   on a manifold, and no causality theory (Cauchy surfaces, global
   hyperbolicity).
2. **Curvature and derivative data from geometry.** In `InitialData`, `R3` and
   `dK` are supplied. A Cauchy theorem must obtain them from `h` and `K` via the
   connection and the embedding. The coordinate pipeline of Paper I computes
   curvature from a metric *field in a chart*; lifting it to a manifold is part
   of this layer.
3. **Sobolev spaces and the constraint problem.** The theorem is usually stated
   for Sobolev data `H^s` with `s` sufficiently large (or smooth data). Mathlib's
   `Analysis/Distribution/Sobolev.lean` module works on `ℝⁿ`, not on manifolds, and the
   repository contains no elliptic theory for solving the constraints. The
   present module checks the constraints; it does not solve them.
4. **Quasilinear hyperbolic existence.** After harmonic/wave gauge, the vacuum
   Einstein equations become a quasilinear symmetric hyperbolic system. Proving
   local existence for that system is the analytic core of [4]. Mathlib has no
   such theorem, and no PDE library currently in the dependency graph supplies
   one; the Lean PDE projects surveyed for this paper are elliptic or
   Navier–Stokes formalisations, not quasilinear hyperbolic systems. The
   one-dimensional linear wave theorem of §4 is a model, not this layer: it has
   constant coefficients, no quasilinearity and no gauge.
5. **Gauge and constraint propagation, then maximality.** One must show that a
   solution of the reduced system satisfies the gauge condition and the full
   Einstein equations, that the constraints propagate, and that developments can
   be patched to a maximal one. Constraint propagation uses the contracted
   Bianchi identity. Paper I proves that identity for the frame Einstein space
   (`sds_frame_bianchi`), but the general `CurvDeriv` lemmas still take it as a
   parameter, so the general covariant statement is also part of this layer.
   Maximality then needs the Zorn argument of [1] or the construction of [2],
   together with an isometry/embedding API.

## 7. A formalisation roadmap

The layers above suggest an order in which the work can be made checkable. Each
milestone has an acceptance criterion; none is claimed as done here.

| Milestone | Content | Acceptance criterion |
| --- | --- | --- |
| M0 | Linear 3D wave model on a box: energy, conservation, zero-energy, zero-data and general-data uniqueness | **Done**: `waveEnergy3D_eq_initial_of_wave`, `eq_zero_of_waveEnergy3D_eq_zero`, `wave_zero_of_zero_data3D`, `wave_unique3D_of_same_data`; closed-box uniqueness under explicit regularity |
| M0.5 | Linearized Einstein equations in wave gauge | **Interface**: `WaveGaugePerturbation` and `linEinstein_eq_zero_of_waveGauge`, with `ttWave_waveGauge` as a concrete TT-plane-wave instance; uses the existing `linEinstein_lorenz_gauge` reduction, not a manifold derivation |
| M1 | Smooth manifolds, Lorentzian metrics, Levi-Civita connection, curvature, causality | a manifold-level `Metric` with inverse, connection and Riemann tensor; `#print axioms` clean |
| M2 | Manifold Sobolev spaces `H^s`, trace/embedding estimates, constraint data | `H^s` data type and the constraint equations stated on a manifold |
| M3 | Harmonic/wave gauge and the reduced quasilinear hyperbolic system | a formal local-existence theorem for the reduced system |
| M4 | Gauge recovery and constraint propagation | a proof that reduced solutions satisfy the full Einstein equations and preserve the constraints |
| M5 | Maximal development | patching of developments, Zorn or Sbierski construction, uniqueness up to isometry |
| M6 | Cross-checks against explicit solutions | Schwarzschild, de Sitter, Kerr and FLRW recovered as developments of their initial data |

M0 is complete for the linear constant-coefficient wave model; it is a model
result, not an Einstein theorem. M0.5 is a concrete coordinate-level interface
for the linearized wave-gauge equations, not a proof of the manifold-level
reduction. The remaining milestones M1–M6 are deliberately stated as interfaces
first. M1 and M2 are foundational and reusable; M3 is the
analytic bottleneck; M4 depends on the general Bianchi identity; M5 is
order-theoretic once M3 and M4 exist; M6 is the regression test that ties the
abstract theorem back to Paper I's explicit metrics.

A useful intermediate target, weaker than full Choquet–Bruhat–Geroch, is local
existence in a fixed gauge for smooth data. It would already give a
machine-checked Cauchy theorem for a neighbourhood of the slice, and it avoids
the maximality API until M5.

## 8. Relation to Paper I

The development audited in Paper I now has 758 declarations. It contains the
constraint module, the geodesic module, the wave/energy/uniqueness modules, the
3D divergence foundation, the 3D energy derivative, conditional 3D energy
conservation, the wave-flux instantiation, the closed-box 3D zero-energy and
uniqueness theorems and the linearized wave-gauge interface discussed above,
together with the solution theory, the alternative theories, the axiom audit and
the numerical pass. This paper's Lean contribution is the fifty-four-declaration
nonet `Gravitation.WaveCauchy`, `Gravitation.WaveEnergy`,
`Gravitation.WaveUniqueness`, `Gravitation.Divergence3D`,
`Gravitation.WaveEnergy3D`, `Gravitation.WaveEnergy3DConservation`,
`Gravitation.WaveEnergy3DWave`, `Gravitation.WaveUniqueness3D` and
`Gravitation.LinearizedWaveGauge`; the remainder is the written account of the
initial-value side and of the roadmap. Every formal claim made here is therefore
part of the same audit.

The two papers share a boundary. Paper I proves that explicit metrics solve
their field equations on their coordinate domains; this paper asks whether
arbitrary data have a development at all. The explicit solutions are the test
cases for M6, not a proof of existence for other data. Conversely, a future
proof of Choquet–Bruhat–Geroch would not replace the metric-level computations
of Paper I: it would supply the existence theorem those computations currently
take for granted when they exhibit a solution.

## 9. Reproducibility and trust

This paper adds prose and nine Lean modules, `Gravitation.WaveCauchy`,
`Gravitation.WaveEnergy`, `Gravitation.WaveUniqueness`,
`Gravitation.Divergence3D`, `Gravitation.WaveEnergy3D`,
`Gravitation.WaveEnergy3DConservation`, `Gravitation.WaveEnergy3DWave`,
`Gravitation.WaveUniqueness3D` and `Gravitation.LinearizedWaveGauge`
(fifty-four declarations). The audited development is the one described in
Paper I: `lake build` is silent, `scripts/check_messages.sh` passes,
`scripts/audit_axioms.sh` reports 758 declarations with axioms inside
`{propext, Classical.choice, Quot.sound}`, and `scripts/proof_status.sh
--check` passes against `Proof-Status.md`. The module paths cited here are the
vendored `Gravitation.Relativity.General.*` paths; in Physlib they are
`PhyslibAlpha.Relativity.General.*`, with the same namespace and proofs.

The eleven formal modules named here can be read directly:

- `gravitation/Gravitation/WaveCauchy.lean`
- `gravitation/Gravitation/WaveEnergy.lean`
- `gravitation/Gravitation/WaveUniqueness.lean`
- `gravitation/Gravitation/Divergence3D.lean`
- `gravitation/Gravitation/WaveEnergy3D.lean`
- `gravitation/Gravitation/WaveEnergy3DConservation.lean`
- `gravitation/Gravitation/WaveEnergy3DWave.lean`
- `gravitation/Gravitation/WaveUniqueness3D.lean`
- `gravitation/Gravitation/LinearizedWaveGauge.lean`
- `gravitation/vendor/Gravitation/Relativity/General/InitialValue.lean`
- `gravitation/vendor/Gravitation/Relativity/General/Geodesics.lean`

## 10. What is not claimed

- No formalisation of the Choquet–Bruhat–Geroch theorem.
- No local existence theorem for the Einstein equations, in any gauge.
- No solution of the constraint equations, and no construction of `R3` from `h`
  or `dK` from `K`.
- No global existence or maximal-interval theorem for geodesics.
- No manifold, Sobolev, quasilinear-hyperbolic or causality layer. The wave
  theorem is one-dimensional, linear and constant-coefficient.
- No global uniqueness theorem for the wave Cauchy problem. The formalised
  results are zero-data uniqueness on `Icc 0 L` and, by applying it to the
  difference of two solutions, general-data uniqueness for two solutions with the
  same Cauchy and boundary data. Both require explicit regularity; the zero-data
  result uses homogeneous Dirichlet data, while the general result assumes
  matching boundary values.
- 3D wave energy conservation and 3D uniqueness are formalised for the linear
  constant-coefficient wave equation on a closed box, under explicit regularity
  and homogeneous Dirichlet data for both the field and its time derivative. They
  are not uniqueness theorems for the Einstein equations.
- The linearized wave-gauge layer is a coordinate-level interface
  (`WaveGaugePerturbation`, instantiated by `ttWave_waveGauge`), not a
  manifold-level derivation of the linearized Einstein equations.
- The remaining PDE layers are the M1–M6 milestones of §7: manifold and
  Lorentzian geometry; manifold Sobolev spaces and the constraint problem;
  harmonic/wave gauge and the reduced quasilinear hyperbolic system; gauge
  recovery and constraint propagation; maximal development; and cross-checks
  against explicit solutions.
- No axiom, `sorry`, or cited theorem smuggled in as a hypothesis. The CBG
  statement in §5 is prose with references; it is not a Lean declaration.

## References

1. Y. Choquet-Bruhat, R. Geroch. *Global aspects of the Cauchy problem in general relativity.* Comm. Math. Phys. 14 (1969) 329–335.
2. J. Sbierski. *On the existence of a maximal Cauchy development for the Einstein equations — a dezornification.* arXiv:1309.7591 (2013).
3. A. D. Rendall. *Theorems on existence and global dynamics for the Einstein equations.* Living Rev. Relativ. 8 (2005) 6.
4. Y. Choquet-Bruhat. *Théorème d'existence pour certains systèmes d'équations aux dérivées partielles non linéaires.* Acta Math. 88 (1952) 141–225.
5. R. M. Wald. *General Relativity.* University of Chicago Press, 1984.
6. A. Vergara Gil. *A Machine-Checked Formalisation of General Relativity and Its Alternatives in Lean 4.* `docs/Gravitation-Formalisation.md`, 2026.
7. The Mathlib Community. *The Lean Mathematical Library.* CPP 2020. `leanprover-community/mathlib4`, `v4.36.0`.
8. `leanprover-community/physlib`. https://github.com/leanprover-community/physlib
9. P. T. Chruściel. *Cauchy problems for the Einstein equations: an introduction.* Lecture notes, 2018.
10. L. C. Evans. *Partial Differential Equations.* 2nd ed., American Mathematical Society, 2010.
