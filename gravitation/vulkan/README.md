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
      ->  R_{ρσμν} = g_{ρλ}R^λ_σμν,  K = R_{ρσμν}R^{ρσμν}
      ->  E_ij = R_{t i t j} / √|g_tt g_ii g_tt g_jj|  (unit normal e_t)
```

Output is 70 doubles per point: `g` (16), `Ric` (16), `R` (1), `G` (16),
Kretschmann `K` (1), the electric part `E` (16) in the orthonormal frame, and
`R^t_rtr`, `R^t_θtθ`, `R^r_θrθ`, `R^θ_φθφ`, all row-major. The inverse metric comes from a cofactor inverse of the 4×4 metric,
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
host-visible SSBO of 70 doubles per point, runs the three cases, and checks
`max|Ric|` (cases 0, 1) or `max|Ric − Λg|` (case 2) against a tolerance,
exiting nonzero on failure. For cases 1 and 2 it also checks the closed forms
proved in the Lean development: the Kretschmann scalar against `48M²/r⁶`
(`kretschmann_scalar`) — and, for case 2, the lifted invariant
`48M²/r⁶ + 8Λ²/3` — the Weyl electric part against `diag(0, −2k, k, k)` with
`k = M/r³` after adding back the trace `Λ/3` (`weyl_rr_sds`,
`weyl_thetatheta_sds`, `weyl_phiphi_sds`), and the four Riemann components
`R^t_rtr = (2M/r³ + Λ/3)/f`, `R^t_θtθ = R^r_θrθ = Λr²/3 − M/r`,
`R^θ_φθφ = (2M/r + Λr²/3) sin²θ` (`riemann_t_rtr_sds`,
`riemann_t_thetatheta_sds`, `riemann_r_thetar_sds`,
`riemann_theta_phitheta_sds`). Schwarzschild is the `Λ = 0` special case of the
same expressions; `sin²θ` is taken from the emitted `g_φφ/g_θθ`, which is exact. No validation layers, no staging buffers, no
external dependencies beyond `libvulkan`.

## Accuracy

Double precision (`GL_ARB_gpu_shader_fp64`) with `h = 1e-4`. The host queries
`shaderFloat64` and refuses a device without it. The central differences are
second-order accurate, so truncation is about `h² = 1e-8` and roundoff about
`ε/h² ≈ 1e-8`. The measured Schwarzschild residual is `1.8e-7` on `|Ric|`, and
the Kretschmann deviation from `48M²/r⁶` is `1.2e-7`; both are checked against
`1e-6`.

GLSL has no double-precision `sin`, so the metric's `sin²θ` is expanded in
double around the float `sin`/`cos` of each lattice line's base angle.
Evaluating `sin` in float directly would put a `1e-7` kink in `θ`, which the
difference quotient amplifies by `1/h`.

The Kretschmann tolerance reflects the discretisation, not the theorem: the Lean
statement is exact. The measured deviations are `2.6e-9` for the Weyl electric
part and `7.8e-9` for `R^t_rtr` at `Λ = 0`; with `Λ = 0.1` they are `1.4e-8`
(Weyl part), `5.9e-7` (`R^t_rtr`), `3.7e-10` (`R^t_θtθ`), `1.5e-8`
(`R^r_θrθ`) and `5.5e-9` (`R^θ_φθφ`).

CI runs the whole check on lavapipe, so it needs no GPU runner. It installs
`vulkan-tools` and prints `vulkaninfo --summary` rather than pinning
`VK_ICD_FILENAMES`: a wrong path makes the loader enumerate zero devices instead
of falling back to its default scan.
