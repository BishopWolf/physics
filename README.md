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
| `ricci_symm` | `Ric_{ij} = Ric_{ji}`, derived from pair symmetry |
| `einstein_symm` | the Einstein tensor is symmetric |
| `sum_ginv_mul_g` | `∑ g^{ij} g_{ij} = n` |
| `metricTrace_einstein` | `g^{ij}G_{ij} = (1 − n/2) S`; in 4D the trace of `G` is `−S` |
| `vacuum_iff_ricci_flat` | in 4D, `G = 0 ↔ Ric = 0` |
| `Minkowski.einstein_eq_zero` | Minkowski spacetime is a vacuum solution |

The Riemann tensor carries its four algebraic symmetries as structure fields
(the standard definition of a curvature tensor): antisymmetry in each pair,
pair symmetry `R_{ijkl} = R_{klij}`, and the first Bianchi identity. `skew_first`
is therefore an assumption, not a derived theorem — deriving it from the other
three would be a worthwhile refinement.

Deliberately *not* claimed: coordinate invariance (everything is componentwise in
one frame), the connection/Levi-Civita construction, and any global or PDE
statement. `vacuum_iff_ricci_flat` is an algebraic identity at a point, not a
statement about solution spaces.

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

No licence file yet; add one before publishing.
