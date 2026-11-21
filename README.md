# physics — a Lean 4 formalisation of gravitation

A component (coordinate) formalisation of the algebraic core of general
relativity, plus a Vulkan compute path that verifies solutions numerically.

Started after surveying what the Anthropic/OpenAI Lean repositories and the
physics-Lean community actually formalise — see [`STATUS.md`](STATUS.md). The
short version: curvature *definitions* exist in several projects, the Einstein
field equations have been derived only conditionally, and no end-to-end
formalisation of relativistic solution theory (initial value problem,
singularity theorems, black-hole uniqueness) exists. This repository is a small,
`sorry`-free step into that gap.

## Layout

```
gravitation/
├── Gravitation/
│   ├── Basic.lean               metric with explicit inverse, Minkowski η
│   ├── Curvature.lean           Riemann, Ricci, scalar curvature
│   ├── Einstein.lean            Einstein tensor, trace identity, vacuum theorem
│   ├── InitialValue.lean        initial data, constraint equations, reductions
│   ├── Geodesics.lean           geodesic Cauchy problem: local existence/uniqueness
│   ├── Alternatives.lean        MOND, MOG and TeVeS: proved structural properties
│   └── Examples/Minkowski.lean  Minkowski as a proved vacuum solution
├── Gravitation.lean             library root
├── lakefile.toml                Mathlib v4.36.0, Lean v4.36.0
└── vulkan/
    ├── shaders/tensor.comp      GLSL compute: Γ, Ric, R, G on a spacetime lattice
    ├── src/gr_vulkan.c          Vulkan host: dispatch, readback, tolerance checks
    └── Makefile
```

## What is proved in Lean

All in `gravitation/`, checked by the Lean kernel against Mathlib v4.36.0, no
`sorry`, no added axioms.

| Result | Statement |
| --- | --- |
| `eta4_mul_self` | `η * η = 1`, i.e. `η` is its own inverse |
| `Metric.ginv_symm` | the inverse of a symmetric metric is symmetric |
| `Riemann.zero_of_repeated_first/last` | components with a repeated antisymmetric index vanish |
| `Riemann.swap_mixed` | `R_{ijkl} = R_{jilk}` |
| `Riemann.skew_first` | `R_{ijkl} = −R_{jikl}`, *derived* from pair symmetry and antisymmetry in the last pair |
| `ricci_symm` | `Ric_{ij} = Ric_{ji}`, derived from pair symmetry |
| `einstein_symm` | the Einstein tensor is symmetric |
| `sum_ginv_mul_g` | `∑ g^{ij} g_{ij} = n` |
| `metricTrace_einstein` | `g^{ij}G_{ij} = (1 − n/2) S`; in 4D the trace of `G` is `−S` |
| `vacuum_iff_ricci_flat` | in 4D, `G = 0 ↔ Ric = 0` |
| `Minkowski.einstein_eq_zero` | Minkowski spacetime is a vacuum solution |

The Riemann tensor carries three structure fields: antisymmetry in the last
pair, pair symmetry `R_{ijkl} = R_{klij}`, and the first Bianchi identity.
Antisymmetry in the first pair is now *proved* from those
(`Riemann.skew_first`), not assumed. Ricci contracts against the inverse metric,
`Ric_{ij} = Σ_k g^{kk} R_{kikj}`, which is exact for charts with diagonal
inverse metric (Minkowski, Schwarzschild and FLRW in standard coordinates); the
fully general `g^{kl} R_{kilj}` contraction is the next refinement.

Deliberately *not* claimed: coordinate invariance (everything is componentwise in
one frame), the connection/Levi-Civita construction, and any global or PDE
statement. `vacuum_iff_ricci_flat` is an algebraic identity at a point, not a
statement about solution spaces.

## Initial value problem

One solution theory per commit. This commit adds `Gravitation.InitialValue`: the
constraint half of the Cauchy problem, which is the part that is genuinely
provable without PDE analysis.

| Result | Statement |
| --- | --- |
| `InitialData.ham` | `H = ³R + (tr K)² − K_ij K^ij` |
| `momConstraint` | `M_i = ∂_j K_ij − ∂_i (tr K)` |
| `ham_zero_iff_scalarCurv_zero_of_K_zero` | at a moment of time symmetry (`K = 0`), vacuum data are exactly scalar-flat data |
| `momConstraint_zero_of_dK_zero` | constant `K` gives `M ≡ 0` |
| `ham_eq_of_trace_zero` | maximal slicing (`tr K = 0`) gives `H = ³R − K_ij K^ij` |
| `trace_sq_eq_of_ham_zero` | on a scalar-flat slice, `H = 0` forces `(tr K)² = K_ij K^ij` |
| `flatData_isVacuum` | flat `ℝ³` with `K = 0` satisfies both constraints |
| `squeezedData_ham` / `_ne_zero` | `K = diag(1,1,0)` on flat space has `H = 2`, so the constraints are not automatic |

**Not formalised, and not axiomatised:** existence and uniqueness of a maximal
globally hyperbolic development (Choquet–Bruhat–Geroch). That is quasilinear
hyperbolic PDE theory, absent from Mathlib; rather than adding an axiom, the
gap is left open and stated here. In particular `IsVacuumData` is a predicate on
the slice, not a theorem that a spacetime exists.

## Conservation of the Einstein tensor

`Gravitation.Conservation` takes the contracted Bianchi identity
`∇^a Ric_ab = ½ ∇_b S` (a consequence of the second Bianchi identity and
metric compatibility) as an explicit hypothesis and proves what follows.

| Result | Statement |
| --- | --- |
| `sum_eta_mul` | `Σ_a f a · η^{aa} η_ab = f b` |
| `divergence_combination` | `∇^a(α Ric + β S g)_b = (α/2 + β) ∇_b S` |
| `divergence_einstein_eq_zero` | `∇^a G_ab = 0` |
| `combination_conserved_iff` | if `∇S ≠ 0` somewhere, `α Ric + β S g` is conserved only when `α = -2β` |

So `G` is the unique combination of `Ric` and `S g` that is conserved, up to
scale — the algebraic reason Einstein's tensor is the one that appears in the
field equations. The differential identity itself is *not* formalised; assuming
it is stated plainly in the module, and it is the next target.

## Geodesic Cauchy problem

`Gravitation.Geodesics` is the solution theory for free fall. The geodesic
equation `γ'' = -Γ(γ)(γ', γ')` becomes a first-order system on `E × E`, and
Mathlib's Picard–Lindelöf theorem (proved, not assumed) supplies existence.

| Result | Statement |
| --- | --- |
| `geodesic_ivp_exists` | `C¹` Christoffel symbols: every `(x₀, v₀)` has a solution on some `Ioo (-ε) ε` |
| `geodesic_ivp_exists_curve` | the same split into `γ` and its velocity `w`, with `γ 0 = x₀`, `w 0 = v₀` |
| `geodesic_ivp_unique` | two solutions agreeing at `t₀`, confined to a ball where the field is `K`-Lipschitz, agree on the interval |
| `geodesicField_zero`, `flat_geodesic` | in flat space the geodesics are the straight lines `t ↦ x₀ + t • v₀` |

Existence is local in time and inside the chart, because the field is only `C¹`
at a point. The uniqueness statement carries its Lipschitz hypothesis explicitly
rather than hiding it behind a choice of constants.

## Alternative theories: MOND, MOG, TeVeS

`Gravitation.Alternatives` states the three models in the form in which they are
used and proves their structural properties. Proved:

| Model | Result | Statement |
| --- | --- | --- |
| MOND | `newtonian_limit` | where `μ(a/a₀) = 1`, the MOND relation gives `a = g_N` |
| MOND | `flat_rotation` | deep regime: `v⁴ = G M a₀`, independent of radius |
| MOND | `newtonian_velocity_ne` | Newtonian orbits with fixed mass cannot share a speed at two radii |
| MOG | `factor_bounds` | the enhancement factor lies in `[1, 1 + α]` |
| MOG | `factor_zero` | the enhancement is exactly `1` at `r = 0` |
| TeVeS | `metric_lorentzian` | the physical metric is Lorentzian for every `φ` |
| TeVeS | `metric_spatial` | the spatial part is the conformal rescaling `e^{-2φ} δ` |

Empirical strengths and weaknesses are **not** theorems and are not claimed as
such — they are assessments from the literature:

| Model | Strength | Weakness |
| --- | --- | --- |
| MOND | fits galaxy rotation curves with one constant `a₀`; predicts the baryonic Tully–Fisher relation (`v⁴ = G M a₀`) | non-relativistic; no cosmology or lensing of its own; galaxy clusters still require extra mass; the value of `a₀` is unexplained |
| TeVeS | relativistic; reproduces the MOND limit; produces lensing without dark matter | needs a scalar and a unit-timelike vector field; parameters unconstrained; gravitational-wave speed and cluster/CMB fits are in tension with data |
| MOG | fits rotation curves and cluster masses; the potential is a one-parameter deformation of Newton's | the enhancement is capped at `1 + α`; `α` and `μ` must be retuned per system; cosmological and lensing fits are contested |

The formal content is the structure that makes those claims testable; the
empirical verdict is not decidable inside Lean.

References: Milgrom, ApJ 270 (1983) 365; Bekenstein, PRD 70 (2004) 083509;
Moffat, JCAP 0603 (2006) 004; Abbott et al. (LIGO/Virgo), ApJL 848 (2017) L13;
Famaey & McGaugh, Living Rev. Rel. 15 (2012) 10.

How these models line up with quantum-gravity and unification approaches
(string theory, loop quantum gravity, emergent gravity) is analysed in
[`docs/QUANTUM-GRAVITY-MAPPING.md`](docs/QUANTUM-GRAVITY-MAPPING.md): MOND maps
onto emergent/entropic gravity, TeVeS onto Einstein–aether/Hořava–Lifshitz,
MOG onto massive gravity, while string theory and LQG have no established
match. Those are structural correspondences, not derivations.

## Scalar–tensor and higher-order theories

`Gravitation.ScalarTensor` covers the three families that dominate viable
modifications of GR: Brans–Dicke, `f(R)`, and Horndeski/Galileons.

### Brans–Dicke

| Result | Statement |
| --- | --- |
| `BransDicke.gamma_eq_one_sub` | `γ = 1 − 1/(2+ω)` |
| `BransDicke.gamma_bounds` | `ω > 0 ⇒ 1/2 < γ < 1` |
| `BransDicke.cassini_deviation` | `ω > 40000 ⇒ 1 − γ < 1/40000` (the Cassini bound) |
| `BransDicke.fR_gamma` | `ω = 0` gives `γ = 1/2`, the `f(R)` PPN value |
| `BransDicke.coupling_eq_one_add` | effective coupling `= 1 + 1/(3+2ω)` |
| `BransDicke.coupling_bounds` | `ω ≥ 0 ⇒ 1 ≤ G_eff/G ≤ 4/3` |
| `BransDicke.coupling_pole` | `ω = −3/2` is a pole: the kinetic term degenerates |

### f(R) gravity

| Result | Statement |
| --- | --- |
| `fR.linear_is_einstein` | `f = R − 2Λ` gives exactly `G + Λg` |
| `fR.phi_inverse` | `φ = 1 + 2αR` inverts to `R = (φ−1)/(2α)` |
| `fR.potential_eq` | Starobinsky potential `V(φ) = (φ−1)²/(8α)` |
| `fR.mass_sq` | scalar mass `m² = 1/(3f'') = 1/(6α)` |
| `fR.not_gr` | `α ≠ 0` ⇒ `f'` not constant ⇒ an extra scalar propagates |

### Horndeski and Galileons

| Result | Statement |
| --- | --- |
| `Galileon.cubic_total_derivative` | `(φ')²φ''` is `d/dt[(φ')³/3]` |
| `Galileon.shift_total_derivative` | a constant velocity shift moves the cubic density by a total derivative |
| `Galileon.shift_forbids_potential` | an exactly shift-symmetric potential is constant |

What is **not** formalised: the four-dimensional field equations of these
theories, the variational calculus behind Horndeski's theorem (that `G₂…G₅`
yields second-order equations), the Ostrogradsky instability of generic
higher-derivative theories, and the full four-dimensional Galileon
total-derivative identities. The one-dimensional statements above are the
shadow of those, proved end to end. The QG mapping is in
[docs/QUANTUM-GRAVITY-MAPPING.md](docs/QUANTUM-GRAVITY-MAPPING.md).

## Vulkan tensor pass

The shader takes any metric given as an analytic function of `(t, r, θ, φ)`,
differentiates it by central differences, and computes

`Γ^k_{ij}` → `∂Γ` → `R^ρ_{σμν}` → `Ric_{σν} = R^ρ_{σρν}` → `R = g^{μν}Ric_{μν}` →
`G_{μν} = Ric_{μν} − ½ R g_{μν}`,

writing all 49 components per lattice point to an SSBO; the host checks the
deviations against tolerances.

Measured on an AMD RX 570 (RADV POLARIS10, Vulkan 1.4.354), 108 points,
`h = 1e-2`:

| Case | max abs Ric | max abs R | max abs G | check |
| --- | --- | --- | --- | --- |
| Minkowski | 0.000e+00 | 0.000e+00 | 0.000e+00 | exact |
| Schwarzschild `r ∈ [3, 3.45]`, `M = 1` | 2.253e-03 | 6.794e-04 | 1.878e-03 | vacuum to FD error |
| Schwarzschild–de Sitter `Λ = 0.1` | 4.255e+00 | 4.005e-01 | 4.247e+00 | `max abs(Ric − Λg) = 6.614e-03` |

The Minkowski zeros are exact (a constant metric differentiates to zero). The
Schwarzschild residual is central-difference noise, not curvature: `|Ric|` is
four orders of magnitude below the curvature scale `M/r³ ≈ 0.04`. The de Sitter
case is the control — it has genuinely nonzero Ricci curvature and is recovered
to the same noise level, so the vacuum test is not vacuous.

This is a numerical sanity check on the same objects the Lean side defines; it is
not a proof, and finite differences say nothing about the analytic solution.

## Build and run

Lean (first build fetches Mathlib):

```sh
cd gravitation
lake exe cache get          # Mathlib oleans
lake build                  # kernel checks Gravitation
```

Vulkan:

```sh
cd gravitation/vulkan
make
./gr_vulkan shaders/tensor.comp.spv
```

Requires `glslc` (shaderc), `libvulkan` and an ICD; exits nonzero if a case
exceeds tolerance. `torchvulkan` is not needed — the pipeline is a native
compute shader with no PyTorch dependency.

## Licence

MIT — see [LICENSE](LICENSE). Copyright (c) 2026 Alex Vergara Gil.
