# Vulkan tensor pass

GPU evaluation of the curvature tensors for a metric supplied analytically as a
function of the coordinates, used as a numerical check on the Physlib theorems
this repository reports on.

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
`R^t_rtr`, `R^t_θtθ`, `R^r_θrθ`, `R^θ_φθφ`, all row-major. The inverse metric
comes from a cofactor inverse of the 4×4 metric, so non-diagonal metrics are
handled; Kerr is the first case that exercises this.

The metric is selected by a push constant (`metricId`), with parameters `massM`,
`lambdaC`, and the lattice geometry `lo`, `stepv`, `grid`:

| id | metric | parameter |
| --- | --- | --- |
| 0 | Minkowski, `diag(−1, 1, 1, 1)` | — |
| 1 | Schwarzschild, `(−f, 1/f, r², r²sin²θ)`, `f = 1 − 2M/r` | `M` |
| 2 | Schwarzschild–de Sitter, `f = 1 − 2M/r − Λr²/3` | `M`, `Λ` |
| 3 | Kerr, Boyer–Lindquist, `g_tt`, `g_tφ`, `g_rr`, `g_θθ`, `g_φφ` | `M`, spin `a` |
| 4 | Reissner–Nordström, `f = 1 − 2M/r + Q²/r²` | `M`, charge `Q` |
| 5 | FLRW, `a(t) = 1 + Ht + t²`, curvature `k` | `H`, `k` |
| 6 | Interior Schwarzschild, `A = 3/2 cos χ_a − 1/2 √(1 − r²/Rc²)` | `Rc`, `Ra` |

## Host

`src/gr_vulkan.c` creates a compute-only device (prefers a discrete GPU), a
host-visible SSBO of 70 doubles per point, runs the nine cases, and checks the
closed forms proved in Physlib, exiting nonzero on failure.

For cases 0–2 it checks `max|Ric|` (cases 0, 1) or `max|Ric − Λg|` (case 2),
the frame Ricci tensor against `Λ diag(−1,1,1,1)` (`sdsRic_eq`), the
Kretschmann scalar against `48M²/r⁶` (`kretschmann_scalar`) — and, for case 2,
the lifted invariant `48M²/r⁶ + 8Λ²/3` (`kretschmann_sds`) — the Weyl electric
part against `diag(0, −2k, k, k)` with `k = M/r³` after adding back the trace
`Λ/3`, and the four Riemann components
`R^t_rtr = (2M/r³ + Λ/3)/f`, `R^t_θtθ = R^r_θrθ = Λr²/3 − M/r`,
`R^θ_φφ = (2M/r + Λr²/3) sin²θ`.

Case 3 checks the Kerr vacuum: `Ric = 0` and `G = 0` from the Boyer–Lindquist
metric, which is `ricciOf_kerr_eq_zero` and `einsteinOf_kerr_eq_zero`. It also
checks the Kerr Kretschmann scalar
`K = 48M²(r⁶ − 15a²r⁴cos²θ + 15a⁴r²cos⁴θ − a⁶cos⁶θ)/Σ⁶`, `Σ = r² + a²cos²θ`,
which contracts the full Riemann tensor of a non-diagonal metric rather than
its trace. It also checks the contracted Bianchi identity `∇_a G^{ab} = 0` by
second-order lattice differences of the emitted `G`, with the connection
recovered from differences of the emitted metric; for a vacuum metric the
residual is a consistency check on the emitted tensor field.

Case 4 checks the Reissner–Nordström Einstein–Maxwell equations
`G_ij = 8π T_ij` of `einsteinOf_rn_eq_maxwell`, with the Maxwell stress-energy
of `F_01 = −Q/r²`. The expected right-hand side is
`diag(Q²f/r⁴, −Q²/(f r⁴), Q²/r², Q²sin²θ/r²)`. Besides `G = 8πT` it checks
the scalar curvature `R = 0` (the Maxwell stress-energy is traceless) and the
Kretschmann scalar `K = 48M²/r⁶ − 96MQ²/r⁷ + 56Q⁴/r⁸`, which involves the
angular components of the Riemann tensor. Since `G` is nonzero here, the
contracted Bianchi identity `∇_a G^{ab} = 0` is a genuine conservation test:
the lattice residual is `6.83e-5` against a curvature scale of `0.028`.

Case 5 checks the FLRW closed forms `ricciOf_flrw`, `scalarOf_flrw` and
`einsteinOf_flrw` for `a(t) = 1 + Ht + t²` (so `a'' = 2` is exercised) and
spatial curvature `k`.

Case 6 checks the interior Schwarzschild metric of the incompressible sphere:
`G` against `8π diag(ρ, p, p, p)`, with constant density `ρ = 3/(8πRc²)` and the
pressure `p = ρ(2cos χ_a/(3cos χ_a − cos χ) − 1)`. The Lean module proves the
junction conditions and the Buchdahl bound, not the interior field equations;
this case is the textbook solution, checked numerically.

Cases 1 and 2 appear twice, at a second mass (`M = 2`, radial range starting at
`r = 5`) and with negative cosmological constant (`Λ = −0.05`), so the
closed-form checks are not tuned to one parameter set and cover both signs of
the de Sitter term.

Schwarzschild is the `Λ = 0` special case of the same expressions; `sin²θ` is
taken from the emitted `g_φφ/g_θθ`, which is exact. No validation layers, no
staging buffers, no external dependencies beyond `libvulkan`.

## Accuracy

Double precision (`GL_ARB_gpu_shader_fp64`) with `h = 1e-4`. The host queries
`shaderFloat64` and refuses a device without it. The central differences are
second-order accurate, so truncation is about `h² = 1e-8` and roundoff about
`ε/h² ≈ 1e-8`.

Measured on an AMD RX 570 (RADV POLARIS10, Vulkan 1.4.354) and on lavapipe
(llvmpipe, Mesa 26.2.7, Vulkan 1.4.354 — the driver CI runs), 108 lattice points:

| Case | check | RX 570 | lavapipe |
| --- | --- | --- | --- |
| Schwarzschild | `max\|Ric\|` | `1.83e-7` | `1.80e-7` |
| Schwarzschild | Kretschmann vs `48M²/r⁶` | `1.11e-7 rel` | `1.06e-7 rel` |
| Schwarzschild–de Sitter | `max\|Ric − Λg\|` | `6.94e-7` | `6.62e-7` |
| Schwarzschild–de Sitter | `K` vs `48M²/r⁶ + 8Λ²/3` | `1.91e-7 rel` | `1.79e-7 rel` |
| Kerr `a = 0.5` | `max\|Ric\|`, `max\|G\|` | `2.10e-7, 1.42e-7` | `1.78e-7, 1.28e-7` |
| Kerr `a = 0.5` | `K` vs the closed form | `1.71e-7 rel` | `1.85e-7 rel` |
| Kerr `a = 0.5` | `max\|∇_a G^{ab}\|` (contracted Bianchi) | `5.04e-9` | `4.84e-9` |
| Reissner–Nordström `Q = 0.5` | `max\|G − 8πT\|`, `max\|R\|` | `1.08e-7, 2.41e-8` | `1.16e-7, 2.23e-8` |
| Reissner–Nordström `Q = 0.5` | `K` vs the closed form | `1.17e-7 rel` | `1.12e-7 rel` |
| Reissner–Nordström `Q = 0.5` | `max\|∇_a G^{ab}\|` (`G ≠ 0`) | `6.83e-5` | `6.83e-5` |
| FLRW `H = 1`, `k = 0.3` | `Ric`, `R`, `G` vs closed forms | `1.27e-6` | `1.24e-6` |
| Interior Schwarzschild `Rc = 5`, `Ra = 4` | `max\|G − 8π diag(ρ,p,p,p)\|` | `8.89e-8` | `9.17e-8` |
| Schwarzschild `M = 2`, `r ∈ [5, 5.75]` | `max\|Ric\|`, `K` | `1.93e-7, 1.05e-7 rel` | `1.91e-7, 1.02e-7 rel` |
| Schwarzschild–de Sitter `Λ = −0.05` | `max\|Ric − Λg\|`, `K` | `1.83e-7, 7.51e-8 rel` | `1.80e-7, 8.56e-8 rel` |
GLSL has no double-precision `sin`, so the metric's `sin²θ` is expanded in
double around the float `sin`/`cos` of each lattice line's base angle.
Evaluating `sin` in float directly would put a `1e-7` kink in `θ`, which the
difference quotient amplifies by `1/h`. Kerr and Reissner–Nordström use the
same expansion.

The tolerances reflect the discretisation, not the theorems: the Lean
statements are exact. Kerr, FLRW and the interior sphere use `1e-5`: the Boyer–Lindquist
metric has larger coordinate derivatives near `r = 3` than the static metrics,
and FLRW's deviation (`1.27e-6`) is second-derivative noise from the `a''` term.

CI runs the whole check on lavapipe, so it needs no GPU runner. It installs
`vulkan-tools` and prints `vulkaninfo --summary` rather than pinning
`VK_ICD_FILENAMES`: a wrong path makes the loader enumerate zero devices instead
of falling back to its default scan.

## Frame Ricci against `Λη`

For the diagonal cases 0–2 the host forms the orthonormal-frame components
`Ric_ab / sqrt(|g_aa g_bb|)` and checks them against `Λ diag(−1,1,1,1)`, the
frame statement proved as `sdsRic_eq`; at `Λ = 0` this is the vanishing of the
Schwarzschild frame Ricci tensor (`schwarzschild_ricci_zero`). Reported as
`frame Ricci |Ric - Lambda eta|`.
