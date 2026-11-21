# Vulkan tensor pass

GPU evaluation of the curvature tensors for a metric supplied analytically as a
function of the coordinates, used as a numerical check on the Lean definitions.

## Pipeline

`shaders/tensor.comp` (GLSL 450, `local_size_x = 64`) is dispatched over a flat
lattice of spacetime points. Per point it evaluates:

```
g_ab  ->  ∂_μ g_ab (central differences)
      ->  Γ^k_ij = ½ g^{kl}(∂_i g_jl + ∂_j g_il − ∂_l g_ij)
      ->  ∂_μ Γ^k_ij (central differences)
      ->  R^ρ_σμν = ∂_μΓ^ρ_νσ − ∂_νΓ^ρ_μσ + Γ^ρ_μλΓ^λ_νσ − Γ^ρ_νλΓ^λ_μσ
      ->  Ric_σν = R^ρ_σρν,  R = g^{μν}Ric_μν,  G_μν = Ric_μν − ½ R g_μν
```

Output is 49 floats per point: `g` (16), `Ric` (16), `R` (1), `G` (16), all
row-major. The inverse metric comes from a cofactor inverse of the 4×4 metric,
so non-diagonal metrics are handled.

The metric is selected by a push constant (`metricId`), with parameters `massM`,
`lambdaC`, and the lattice geometry `lo`, `stepv`, `grid`:

| id | metric |
| --- | --- |
| 0 | Minkowski, `diag(−1, 1, 1, 1)` |
| 1 | Schwarzschild, `(−f, 1/f, r², r²sin²θ)`, `f = 1 − 2M/r` |
| 2 | Schwarzschild–de Sitter, `f = 1 − 2M/r − Λr²/3` |

## Host

`src/gr_vulkan.c` creates a compute-only device (prefers a discrete GPU), a
host-visible SSBO of 49 floats per point, runs the three cases, and checks
`max|Ric|` (cases 0, 1) or `max|Ric − Λg|` (case 2) against a tolerance,
exiting nonzero on failure. No validation layers, no staging buffers, no
external dependencies beyond `libvulkan`.

## Accuracy

Single precision with `h = 1e-2`. The derivative is second-order accurate, so the
noise floor is roughly `ε/h² ≈ 1e-3` in the components; the measured
Schwarzschild residual (`2.3e-3`) sits at that floor, while the curvature itself
is `O(1)` for the de Sitter control. Tighten `h` only after moving the shader to
`float64` (`GL_ARB_gpu_shader_fp64`), otherwise cancellation dominates.
