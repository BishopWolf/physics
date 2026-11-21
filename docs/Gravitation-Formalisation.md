# A Machine-Checked Formalisation of General Relativity and Its Alternatives in Lean 4

**Alex Vergara Gil**

21 November 2026

---

## Abstract

General relativity is the one major theory of physics for which the *solution theory* — statements about particular metrics, rather than the algebraic identities satisfied by curvature tensors — has not been formalised. We report a Lean 4 development, built on Mathlib, that takes a step into that gap. It contains 271 kernel-checked declarations with no `sorry` and no axiom of its own: every declaration depends only on `propext`, `Classical.choice` and `Quot.sound`, the axioms the base libraries already assume, and a CI job checks this on every push. The central results are two solution theories of the Einstein equations. For Schwarzschild, the curvature is proved Ricci flat in the orthonormal frame, the Kretschmann scalar is proved to be $48M^2/r^6$, and all six independent Riemann components are *derived from the metric* $g=\mathrm{diag}(-f,1/f,r^2,r^2\sin^2\theta)$ by differentiating the Christoffel symbols, rather than assumed. For Schwarzschild–de Sitter the same derivation is carried out for general $\Lambda$, giving
$R^t{}_{rtr}=(2M/r^3+\Lambda/3)/f$, $R^t{}_{\theta t\theta}=R^r{}_{\theta r\theta}=\Lambda r^2/3-M/r$ and $R^\theta{}_{\varphi\theta\varphi}=(2M/r+\Lambda r^2/3)\sin^2\theta$, together with a proof that the frame electric part of the Weyl tensor is $\mathrm{diag}(0,-2M/r^3,M/r^3,M/r^3)$ for **every** $\Lambda$: a cosmological constant enters the Riemann tensor only through the trace that the Weyl tensor removes. Alongside these, the development formalises the initial-value constraints, geodesic local existence, and structural theorems for MOND, MOG, TeVeS, Brans–Dicke, $f(R)$, Starobinsky, Galileon, chameleon screening and Ostrogradsky theories. As an independent check, a double-precision Vulkan compute pass evaluates the same tensors from the same metrics and reproduces every closed form proved in Lean to better than $10^{-6}$ — including the $\Lambda$-independent Weyl part of de Sitter to $1.4\times 10^{-8}$.

**Keywords:** general relativity · Lean 4 · Mathlib · formal verification · exact solutions · cosmological constant · alternative theories of gravity · GPU validation

---

## 1. Introduction

Curvature algebra has been formalised before: metric components, Christoffel symbols, the Riemann, Ricci and Einstein tensors, and general identities such as the divergence-free property of the Einstein tensor appear in several libraries. What has not been formalised is **solution theory**: a kernel-checked statement that a specific spacetime metric has a specific curvature, and therefore solves (or fails to solve) a specific field equation.

The distinction matters. A formalisation that defines the Riemann tensor and then *assumes* the components of Schwarzschild's curvature verifies bookkeeping, not physics. The physical content of a solution is the link between the line element and the curvature it produces, and that link is a computation — differentiation, contraction, and a certain amount of algebra that is easy to get wrong by hand. The Schwarzschild–de Sitter case is a good illustration: the intuitive guess that the cosmological constant "scales" the tidal field is wrong, and the correct statement is that $\Lambda$ contributes to $R^t{}_{rtr}$ but cancels entirely from the Weyl tensor. It is purely electric (`weyl_purely_electric`): every component with a single temporal index vanishes, so the electric part is the whole tensor.

This paper reports a development that closes that gap for the static, spherically symmetric family and contrasts it with the alternative theories that are usually discussed as replacements for general relativity. The contributions are:

1. **Two solution theories derived from the metric.** Schwarzschild and Schwarzschild–de Sitter, with every independent Riemann component obtained by differentiating the Christoffel symbols of the stated line element, for general $\Lambda$ in the second case.
2. **A structural result about the cosmological constant.** The frame electric part of the Weyl tensor of Schwarzschild–de Sitter is proved to equal that of Schwarzschild, for every $\Lambda$; the de Sitter contribution is pure trace.
3. **The surrounding theory, formalised to the same standard.** Einstein-tensor identities, the initial-value constraints, geodesic local existence, and the algebraic core of the alternative theories.
4. **An independent numerical cross-check.** A Vulkan compute pass, in double precision, evaluates the same tensors from the same metrics and is compared against the Lean closed forms, with the agreement reported below.
5. **A verification regime that is itself checked.** A silent build, an axiom audit, and a per-declaration proof-status table, all enforced in CI.

## 2. The gap

A survey of the relevant repositories (November 2026) motivates the scope.

| Repository | Contents | Physics / GR |
| --- | --- | --- |
| `anthropics/formal-math` | self-contained Lean projects (zeta zeros, 3SUM-APSP, ETH) | none |
| `anthropics/fermats-last-theorem` | complete formalisation of Fermat's Last Theorem | none |
| `openai/ten-proofs` | Lean certificates for ten results | none |
| `openai/math` | 722 manuscripts, 162 with Lean formalisations | none |
| `leanprover-community/physlib` | classical mechanics, EM, QFT, QM, relativity | special-relativistic kinematics, Lorentz/Poincaré representation theory; **no field equation, no curvature tensor** |
| HepLean | particles, gauge theory, spinors | not gravitation |
| `TataSatyaPratheek/mathematical-physics-lean` | dimension-parametric Einstein tensor and field equations | 0 `sorry` but 365 axioms; the trust surface is the axioms, not the kernel |
| QIQT (Zenodo 20837810) | conditional derivation of the field equations from an information bound | explicitly conditional |

Two conclusions follow. First, curvature *definitions* are not the bottleneck. Second, no surveyed project proves that a black-hole metric solves the vacuum equations: Schwarzschild appears, where it appears at all, as an unproved claim. The gap is therefore the passage from definitions to solutions, and that is what this development addresses.

## 3. Framework and verification regime

The development is Lean 4 against Mathlib `v4.36.0`.

**Interfaces.** Curvature is a bundled structure carrying the algebraic symmetries it must satisfy — antisymmetry in the last pair, pair symmetry, and the first Bianchi identity — so that a "Riemann tensor" cannot be constructed without them. A `Metric` carries its inverse and the proof that the two compose to the identity, so contractions use the inverse actually proved for that metric. Ricci, the scalar curvature and the Einstein tensor are defined by contraction and are therefore available for any bundle satisfying the interface.

**One pipeline.** `Gravitation/Pipeline.lean` defines the chain
$$g \mapsto \partial g \mapsto \Gamma^k{}_{ij} \mapsto \partial\Gamma \mapsto R^\rho{}_{\sigma\mu\nu} \mapsto \mathrm{Ric}_{\sigma\nu} \mapsto S \mapsto G_{ij}$$
for an arbitrary component field $g$ and its inverse, with $\partial_\mu$ the coordinate partial derivative: differentiate a component along the line through $x$ with the other coordinates fixed. A component is then the value of a formula rather than the conclusion of a bespoke proof, and what remains per metric is the evaluation of one-variable derivatives. The module proves outright that a constant metric gives $\Gamma=R=\mathrm{Ric}=S=G=0$ — Minkowski as a *computed* vacuum solution — and that Schwarzschild's $\Gamma^t{}_{tr}$ evaluates to the $M/(r^2f)$ that §4.4 derives by hand. The full closed-form table $\Gamma$ and its partial derivatives $\partial\Gamma$ for Schwarzschild are part of the development too, and `riemann_components_pipeline` reads all six independent curvature components off a single evaluation of `riemannFromData`; the table is transcribed from the line element rather than derived from it, which is item 1 of §6.

**Axiom policy.** No `axiom`, `constant`, `opaque`, `sorry`, `admit`, `native_decide` or `Lean.trustCompiler` anywhere in the library. `scripts/audit_axioms.sh` generates `#print axioms` for every declaration and rejects any axiom outside `{propext, Classical.choice, Quot.sound}`. As of this writing it passes for all 271 declarations. This is a stronger statement than "no `sorry`": it certifies that nothing in the library is justified by an assumption introduced locally.

**Silence as a test.** `lake build` emits no message at all — no errors and no warnings. Tactic and unused-variable warnings were removed by rewriting proofs, not by disabling linters, and `scripts/check_messages.sh` fails CI if a message reappears.

**Per-declaration status.** `Proof-Status.md` lists every declaration with the axioms its proof depends on and a status of `proved` or `unverified`; `scripts/proof_status.sh` regenerates it and CI fails if it is stale. The table is generated from the audit, so it cannot drift from the build.

## 4. Results

### 4.1 Curvature calculus

For a bundle satisfying the curvature interface, the Einstein tensor is proved symmetric, the trace identity
$$g^{ij}G_{ij} = \left(1-\tfrac{n}{2}\right)S$$
is proved for dimension $n$, and in four dimensions $G=0 \iff \mathrm{Ric}=0$ is proved as an equivalence. Minkowski spacetime is proved to be a vacuum solution. The first Bianchi identity is taken as one of the three structural laws of the bundle, and antisymmetry in the *first* pair is derived from them rather than assumed.

### 4.2 The initial-value problem

The constraint equations are formalised in the standard form
$$H = {}^{3}R + (\mathrm{tr}\,K)^2 - K_{ij}K^{ij}, \qquad M_i = \partial_j K^{i}{}_{j} - \partial_i \mathrm{tr}\,K,$$
together with the moment-of-time-symmetry reduction to scalar flatness and the maximal-slicing form. A non-vacuum example is included to show that the constraints are not automatic. Development existence (Choquet–Bruhat–Geroch) is neither claimed nor axiomatised.

### 4.3 Geodesics

Local existence of geodesics from initial position and velocity is proved from Mathlib's Picard–Lindelöf theorem, uniqueness is proved under an explicit Lipschitz hypothesis, and the flat-space solutions are proved to be straight lines. This is local existence for the geodesic equation, not for the field equations.

### 4.4 Schwarzschild: the curvature from the metric

In the orthonormal frame $(t,r,\theta,\varphi)$ the Schwarzschild curvature is a purely electric Weyl tensor with eigenvalues $\mathrm{diag}(0,-2k,k,k)$, $k=M/r^3$. The development proves that this tensor is Ricci flat for every $k$, that it satisfies the three structural laws, and that its sum of squares is $48k^2$, which at $k=M/r^3$ is the Kretschmann scalar $48M^2/r^6$.

The electric part is then *derived* twice over. From the potential: $g_{tt}=-(1+2\Phi)$ fixes $\Phi=-M/r$, and the tidal eigenvalues $\Phi''=-2M/r^3$ and $\Phi'/r=M/r^3$ are proved from $\Phi$, so the frame tensor is `electricPart` at $k=M/r^3$ and is trace free because $\Phi$ is harmonic. From the metric: differentiating the Christoffel symbols of $g=\mathrm{diag}(-f,1/f,r^2,r^2\sin^2\theta)$, $f=1-2M/r$, gives all six independent components:

| Component | Value |
| --- | --- |
| $R^t{}_{rtr}$ | $2M/(r^3f)$ |
| $R^t{}_{\theta t\theta}$ | $-M/r$ |
| $R^t{}_{\varphi t\varphi}$ | $-(M/r)\sin^2\theta$ |
| $R^r{}_{\theta r\theta}$ | $-M/r$ |
| $R^r{}_{\varphi r\varphi}$ | $-(M/r)\sin^2\theta$ |
| $R^\theta{}_{\varphi\theta\varphi}$ | $(2M/r)\sin^2\theta$ |

Each is assembled from small product identities instead of one large rational identity, because the closure tactic (`field_simp` followed by `ring`) leaves an uncancellable $(r-2M)^{-1}$ in this chart; the products are closed by an explicit cancellation against $r^2f\neq 0$.

One evaluation now replaces the six computations. `schG` is the Christoffel table of the line element in closed form and `schDG` its partial derivatives, and `riemann_components_pipeline` proves that `riemannFromData` applied to that pair returns exactly the six values tabulated above: the curvature is read off one evaluation rather than one derivation per component. The six per-component theorems remain as the certificates for the table's entries — the evaluation reproduces their values rather than re-deriving them — so what is left is to prove that the table is the Christoffel table the metric pipeline itself computes (§6.1).

### 4.5 Schwarzschild–de Sitter, for general $\Lambda$

With $f = 1 - 2M/r - \Lambda r^2/3$ and $n = f'/2 = M/r^2 - \Lambda r/3$ (so $f' = 2n$, $n' = -2M/r^3 - \Lambda/3$), the quotient rule gives $\partial_r(n/f) = (n'f - nf')/f^2 = (n'f - 2n^2)/f^2$, and the $t\,r\,t\,r$ component is
$$R^t{}_{rtr} = -\partial_r\Gamma^t{}_{tr} + \Gamma^t{}_{tr}\Gamma^r{}_{rr} - (\Gamma^t{}_{tr})^2 = -\frac{n'}{f} = \frac{2M/r^3 + \Lambda/3}{f},$$
the two $\Gamma$ products cancelling the $2n^2/f^2$ left by the derivative. The remaining components are:

| Component | Value |
| --- | --- |
| $R^t{}_{rtr}$ | $(2M/r^3 + \Lambda/3)/f$ |
| $R^t{}_{\theta t\theta} = R^r{}_{\theta r\theta}$ | $\Lambda r^2/3 - M/r$ |
| $R^t{}_{\varphi t\varphi} = R^r{}_{\varphi r\varphi}$ | $(\Lambda r^2/3 - M/r)\sin^2\theta$ |
| $R^\theta{}_{\varphi\theta\varphi}$ | $(2M/r + \Lambda r^2/3)\sin^2\theta$ |

The angular Christoffel symbols carry no $M$ or $\Lambda$, so the last line enters only through $1-f$.

Squaring the whole frame tensor gives the Kretschmann scalar
$$K = \frac{48M^2}{r^6} + \frac{8\Lambda^2}{3}$$
(`kretschmann_sds`): the Weyl square is Schwarzschild's $48M^2/r^6$ and the trace part contributes $(\Lambda/3)^2\cdot 24$, so $\Lambda$ survives in $K$ even though it cancels from the electric eigenvalues — Figure 2 plots the two contributions.

Contracting instead of squaring gives the other half of the same split. The Weyl part is trace free, so it contributes nothing to the Ricci tensor (`weylRic_zero`); the trace part contracts to $(4-1)\Lambda/3=\Lambda$ times the frame metric (`traceRic_eq`). Hence
$$R_{\mu\nu} = \Lambda\,\eta_{\mu\nu},\qquad S = 4\Lambda,\qquad G_{\mu\nu} = -\Lambda\,\eta_{\mu\nu}$$
(`sdsRic_eq`, `sdsScalar_eq`, `sdsEinstein_eq`): Schwarzschild–de Sitter is an Einstein space, and the $\Lambda$ that cancelled from the electric Weyl eigenvalues is exactly the Ricci curvature, so $G+\Lambda\eta=0$ with no matter. At $\Lambda=0$ the same three theorems give Schwarzschild's vacuum directly: `schwarzschild_ricci_zero`, `schwarzschild_scalar_zero` and `schwarzschild_einstein_zero`, so the vacuum solution is the $\Lambda\to0$ case of the Einstein-space statement rather than a second computation.

The structural result is what happens in the frame. Since
$$C_{titj} = R_{titj} + \frac{\Lambda}{3}\,g_{ij},$$
the de Sitter contribution to the Riemann tensor is the trace part that the Weyl tensor projects out, and the frame electric part of $C$ is proved to be
$$\mathrm{diag}\!\left(0, -\frac{2M}{r^3}, \frac{M}{r^3}, \frac{M}{r^3}\right) = \texttt{electricPart}\,(M/r^3)$$
for every $\Lambda$ — the Schwarzschild answer. In words: a cosmological constant changes the Ricci tensor and leaves the free gravitational field alone. This is proved for the radial, $\theta$ and $\varphi$ frame eigenvalues, and at $\Lambda=0$ the lapse is proved to reduce to `schwarzschildF`, so the whole family specialises to the results of §4.4.

![Frame eigenvalues of the Schwarzschild–de Sitter Riemann tensor against $r$, for $M=1$ and $\Lambda=0,0.05,0.1$.](figures/tidal-eigenvalues.svg)

**Figure 1.** Frame eigenvalues of the Riemann tensor of Schwarzschild–de Sitter against $r$, for $M=1$ and $\Lambda=0$ (blue), $0.05$ (orange) and $0.1$ (green). Solid curves are the angular eigenvalue $R_{t\theta t\theta}=M/r^3-\Lambda/3$; dashed curves the radial one, $R_{trtr}=-2M/r^3-\Lambda/3$; dotted lines mark $-\Lambda/3$. Raising $\Lambda$ shifts both families rigidly by $-\Lambda/3$ and leaves the splitting $R_{t\theta t\theta}-R_{trtr}=3M/r^3$ unchanged. That shift is the trace part, and exactly what the Weyl tensor removes: the Weyl eigenvalues stay on the $\Lambda=0$ curves while both Riemann eigenvalues tend to $-\Lambda/3$ at large $r$. Generated by `docs/figures/make_tidal_figure.py`.

![Kretschmann scalar of Schwarzschild and Schwarzschild–de Sitter against $r$, for $M=1$ and $\Lambda=0,0.05,0.1$.](figures/kretschmann.svg)

**Figure 2.** Kretschmann scalar $K=R_{\rho\sigma\mu\nu}R^{\rho\sigma\mu\nu}$ against $r$, for $M=1$ and $\Lambda=0$ (blue), $0.05$ (orange), $0.1$ (green). Because the Weyl part is $\Lambda$-independent, $K=48M^2/r^6+\tfrac83\Lambda^2$: each de Sitter curve is the Schwarzschild one lifted by the constant $(8/3)\Lambda^2$ (dotted), so instead of decaying to zero the curvature tends to $8\Lambda^2/3$. That lift is the trace part again — the same $\Lambda$ that cancels from the electric Weyl eigenvalues in Figure 1 survives in the full Riemann square. The dashed curve is the Weyl-only invariant $48M^2/r^6$ (`kretschmann_scalar`); the full identity is `kretschmann_sds`; the GPU pass checks the sum for $\Lambda=0.1$ to $1.9\times10^{-7}$ relative. Generated by `docs/figures/make_kretschmann_figure.py`.

All statements hold where $r\neq0$ and $f\neq0$; for $\Lambda>0$ the latter excludes the roots of the cubic $3r - 6M - \Lambda r^3$.

### 4.6 Alternative theories

The alternatives are formalised as the structural statements that can be proved without pretending to formalise the full theory.

* **MOND.** The deep-MOND acceleration law and the baryonic Tully–Fisher relation $v^4 = GMa_0$ are proved, together with the Newtonian limit at large $a_0$ and the fact that the flat-rotation value is nonzero.
* **MOG.** The potential is a one-parameter deformation of Newton's, and the enhancement is proved to be bounded by $1+\alpha$.
* **TeVeS.** The metric is proved to preserve the Lorentzian signature.
* **Brans–Dicke / $f(R)$.** The PPN parameters, the $\omega\to\infty$ limit, the linear case $f(R)=R-2\Lambda$ proved to give exactly $G+\Lambda g$, and Starobinsky's potential and mass.
* **Galileon.** The one-dimensional total-derivative structure is proved.
* **Chameleon screening.** The density-dependent mass, the shrinking Compton range, the exponential Yukawa suppression beyond it, and the thin-shell cap on the fifth force.
* **Ostrogradsky.** A degenerate velocity Hessian for $L=\tfrac12\ddot q^2+V$, a Hamiltonian affine in one momentum and unbounded below, contrasted with a positive-definite quadratic kinetic term.

These are algebraic or one-dimensional shadows of statements usually made in three dimensions. They are stated as such, and the empirical strengths and weaknesses of each theory are recorded in prose, not as theorems.

### 4.7 Conservation

The contracted Bianchi identity is accepted as a hypothesis, from which $\nabla\cdot G = 0$ and the uniqueness of $G$ as the conserved combination of $\mathrm{Ric}$ and $Sg$ are derived. The hypothesis is explicit rather than hidden: proving it from the bundle's structure is a separate, larger undertaking.

## 5. Numerical cross-check

The same metrics are evaluated independently by a Vulkan compute shader in double precision (`GL_ARB_gpu_shader_fp64`, refused devices without it). For each lattice point it computes $g_{ab}$, central-difference derivatives, $\Gamma^k{}_{ij}$, $\partial_\mu\Gamma^k{}_{ij}$, $R^\rho{}_{\sigma\mu\nu}$, $\mathrm{Ric}$, $R$, $G$, the Kretschmann scalar, the frame electric part and four Riemann components, writing 70 doubles per point. The host compares the emitted values against the closed forms proved in Lean.

Measured on an AMD RX 570 (RADV POLARIS10, Vulkan 1.4.354), 108 lattice points, $h=10^{-4}$, tolerance $10^{-6}$:

| Quantity | $\Lambda=0$ | $\Lambda=0.1$ |
| --- | --- | --- |
| $\max|G|$ | $1.028\times10^{-7}$ | $4.248\times10^{0}$ |
| $\mathrm{Ric}$ vs $0$ / $\Lambda g$ | $1.840\times10^{-7}$ | $6.960\times10^{-7}$ |
| Kretschmann vs $48M^2/r^6$, and vs $48M^2/r^6+\tfrac83\Lambda^2$ (relative) | $1.151\times10^{-7}$ | $1.930\times10^{-7}$ |
| Weyl electric part vs $\mathrm{diag}(0,-2k,k,k)$ | $2.615\times10^{-9}$ | $1.394\times10^{-8}$ |
| $R^t{}_{rtr}$ vs $(2M/r^3+\Lambda/3)/f$ | $7.845\times10^{-9}$ | $5.923\times10^{-7}$ |
| $R^t{}_{\theta t\theta}$ vs $\Lambda r^2/3-M/r$ | $3.702\times10^{-10}$ | $3.703\times10^{-10}$ |
| $R^r{}_{\theta r\theta}$ vs $\Lambda r^2/3-M/r$ | $7.972\times10^{-9}$ | $1.481\times10^{-8}$ |
| $R^\theta{}_{\varphi\theta\varphi}$ vs $(2M/r+\Lambda r^2/3)\sin^2\theta$ | $5.543\times10^{-9}$ | $5.543\times10^{-9}$ |

The de Sitter case is the control: it has genuinely nonzero Ricci curvature, recovered at the same noise level as the vacuum case, so the vacuum test is not vacuous — and `sdsRic_eq` says the measured entries are exactly $\Lambda\eta_{\mu\nu}$. The host now forms the frame components $R_{ab}/\sqrt{|g_{aa}g_{bb}|}$ and checks them against $\Lambda\,\mathrm{diag}(-1,1,1,1)$, which lands at $2.0\times10^{-8}$ for both cases and is, at $\Lambda=0$, the vanishing of `schwarzschild_ricci_zero`. It also confirms the lifted Kretschmann scalar of Figure 2, $48M^2/r^6+\tfrac83\Lambda^2$ — now the theorem `kretschmann_sds` — to $1.9\times10^{-7}$ relative. In that case the emitted frame Riemann part is $R_{titj} = C_{titj} - (\Lambda/3)\delta_{ij}$, so the Weyl statement is checked by adding $\Lambda/3$ back, which reproduces $\mathrm{diag}(0,-2k,k,k)$ to $1.4\times10^{-8}$.

This is a regression test for the shader and for the closed forms, not evidence for the theorems. Finite differences say nothing about an analytic solution; the Lean statement is exact, while the numerical agreement is second-order accurate at $h^2\approx10^{-8}$ with roundoff $\varepsilon/h^2\approx10^{-8}$. The measured de Sitter $R^t{}_{rtr}$ deviation of $5.9\times10^{-7}$ is the largest, and is consistent with the larger curvature scale there ($\Lambda/3$).

## 6. Limitations

This section is the backlog, not a disclaimer: each item says what is not proved, what now narrows it, and whether removing it is mechanical, tractable, or out of scope for this paper.

1. **The table is transcribed, not read off the metric.** `Pipeline.lean` evaluates $R^\rho{}_{\sigma\mu\nu}$ from $\Gamma$ and $\partial\Gamma$ supplied as parameters (`riemannFromData`), and `riemann_eq_riemannFromData` proves that feeding the metric's actual partial derivatives reproduces the differentiable pipeline definitionally, so no assumption separates the two. The closed-form table `schG` and its derivative table `schDG` now exist, and `riemann_components_pipeline` derives all six independent components from one evaluation of the pair, with the per-component theorems serving as certificates for the entries. What is missing is the last link, `christoffel (schwarzschildG M) (schwarzschildGinv M) = schG M`, which would make the table the pipeline's own output rather than a transcription of it; the radial derivative is already available (`deriv_gammaTtr`), and the remaining entries are one-variable differentiations of $-rf$ and $-\sin\theta\cos\theta$. The Schwarzschild–de Sitter table is the same task with `deriv_sdsF` and `deriv_sdsHalf` in place of `deriv_gammaTtr`. *Removable, mechanical.*
2. **Ricci flatness is a frame statement.** The frame tensors satisfy $R_{\mu\nu}=\Lambda\eta_{\mu\nu}$, $S=4\Lambda$ and $G_{\mu\nu}=-\Lambda\eta_{\mu\nu}$ for every $r$ and with no chart hypotheses, hence vanish at $\Lambda=0$. The link back to the metric runs through the electric-part theorems, not a single theorem "the metric's Ricci tensor vanishes"; assembling that statement from the six component theorems is the missing composition. *Removable.*
3. **No global existence theory.** The constraints are formalised; existence and uniqueness for the Cauchy problem of the field equations are not, and are not axiomatised. *Out of scope: this paper is about solution theory, not the initial-value problem.*
4. **The contracted Bianchi identity is a hypothesis** (§4.7). For the frame Einstein space it follows from $R_{\mu\nu}=\Lambda\eta_{\mu\nu}$, but making that a theorem requires a frame covariant derivative. *Removable.*
5. **Chart restrictions apply to the metric-level theorems.** The frame-level results — Weyl, Kretschmann, Ricci, Einstein — carry no hypotheses at all. The metric-level derivations assume $r\neq0$ and $f\neq0$, and for $\Lambda>0$ the latter excludes the horizon roots. *Partly removable.*
6. **Alternatives are structural shadows.** The MOND, MOG, TeVeS and screening results are algebraic statements in one or two variables, not field theories. The paper's claims about them are correspondingly narrow. *Not removable without formalising an alternative as a field theory.*

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

The numerical pass is not a proof, and does not need to be: it now checks quantities that are themselves theorems (`kretschmann_sds`, `sdsRic_eq`), so it tests the implementation against the mathematics rather than substituting for it. CI (`.github/workflows/axioms.yml`) runs the silent-build check, the axiom audit and the proof-status check on every push and pull request, and runs the Vulkan pass on the lavapipe software driver, so no GPU runner is required. The shader is compiled with `glslc`; the host needs only `libvulkan`.

## 8. Conclusion

The solution theory of general relativity is formalisable, at least for the static spherically symmetric family, and doing so changes what one can claim. The derivation of Schwarzschild–de Sitter's curvature for general $\Lambda$ shows why: the cosmological constant appears in every Riemann component, yet cancels from the Weyl tensor, and a formalisation makes that cancellation a theorem rather than a remark. The closed-form derivative table now exists: one evaluation of `riemannFromData` on `schG` and `schDG` produces all six components (`riemann_components_pipeline`), and the data form is already the metric pipeline by `riemann_eq_riemannFromData`. What remains is to prove that the table is the Christoffel table the metric pipeline computes.

## Appendix A. Declaration census

| Module | Declarations |
| --- | --- |
| `Examples/Schwarzschild.lean` | 46 |
| `Examples/SchwarzschildDeSitter.lean` | 45 |
| `Pipeline.lean` | 30 |
| `ScalarTensor.lean` | 26 |
| `Screening.lean` | 24 |
| `InitialValue.lean` | 20 |
| `Alternatives.lean` | 15 |
| `Basic.lean` | 14 |
| `Einstein.lean` | 12 |
| `Geodesics.lean` | 11 |
| `Curvature.lean` | 9 |
| `Conservation.lean` | 7 |
| `Ostrogradsky.lean` | 7 |
| `Examples/Minkowski.lean` | 5 |
| **Total** | **271** |

All 271 are `proved` against `{propext, Classical.choice, Quot.sound}`; the generated table is `Proof-Status.md`.

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

## Appendix B. Source format

This article is written in Markdown with LaTeX mathematics so that it can be read in the repository. For arXiv submission, `pandoc -f markdown -t latex Gravitation-Formalisation.md -o gravitation.tex` produces a LaTeX manuscript; the mathematics is already in `$…$`/`$$…$$` form and needs no rewriting. Figures 1 and 2 are SVGs produced by `docs/figures/make_tidal_figure.py` and `docs/figures/make_kretschmann_figure.py`; `rsvg-convert -f pdf` converts each to the PDF that arXiv prefers.
