# Survey: Lean formalisation of physics and mathematics (Nov 2026)

Context gathered for this repository: what the Anthropic and OpenAI Lean
repositories contain, what the physics-Lean community has done, and where
general relativity currently stands as *formalised theorems*.

Repositories were inspected through the GitHub contents API and their
published documentation on 2026-11-21.

## Anthropic

| Repository | Contents | Physics / GR |
| --- | --- | --- |
| [`anthropics/formal-math`](https://github.com/anthropics/formal-math) | Self-contained Lake projects, Apache-2.0: `zeta23` (Riemann zeta zeros), `3sum-apsp` (fine-grained complexity), `eth` (2^o(n) 3-SAT) | None |
| [`anthropics/fermats-last-theorem`](https://github.com/anthropics/fermats-last-theorem) | Complete Lean 4 formalisation of Fermat's Last Theorem (Frey–Serre–Ribet–Wiles), Lean 4.33.1 / Mathlib v4.33.0, `#print axioms` restricted to the three standard axioms | None |

Both are pure mathematics/TCS. Neither contains a physics library, a metric, or
a curvature tensor.

## OpenAI

| Repository | Contents | Physics / GR |
| --- | --- | --- |
| [`openai/ten-proofs`](https://github.com/openai/ten-proofs) | Lean 4 certificates for ten results (sphere packing, binary/spherical codes, permanent, Ramsey, non-sofic groups, quantum parallel repetition, Ehrhart, GapCVP, Connes rigidity, compactness/degeneracy) | None (quantum parallel repetition is information-theoretic, not field theory) |
| [`openai/math`](https://github.com/openai/math) | 722 manuscripts in 372 families; `lean/` catalogue lists 162 papers whose main result has a Lean formalisation (snapshot 2026-10-07) | None found; the collection is mathematics |

## Community physics formalisation

* [`leanprover-community/physlib`](https://github.com/leanprover-community/physlib)
  (`Physlib`, `PhyslibAlpha`). Top-level areas: `ClassicalMechanics`,
  `ClassicalFieldTheory`, `Electromagnetism`, `QFT`, `QuantumMechanics`,
  `StatisticalMechanics`, `Cosmology`, `Relativity`, `SpaceAndTime`, …
  `Physlib/Relativity/` contains `MinkowskiMatrix.lean`, `LorentzGroup/`,
  `LorentzAlgebra/`, `Tensors/`, `Special/`, `Causality/`, `Poincare/`,
  `Bispinors/`, `Fermions/`, `SL2C/`, `PauliMatrices/`. That is
  special-relativistic kinematics and Lorentz/Poincaré representation theory;
  there is no Einstein field equation and no curvature tensor.
* HepLean (Tooby-Smith) — high-energy physics: particles, gauge theory,
  spinors; not gravitation.
* `TataSatyaPratheek/mathematical-physics-lean` — a from-scratch,
  Mathlib-free dimension-parametric development reaching the Einstein tensor and
  Einstein equations (`Relativity/EinsteinN.lean`). Its own README states
  0 `sorry` but 365 axioms; trust surface is the axioms, not the kernel alone.
* QIQT / Zenodo 20837810 — an audited human-AI loop whose case study proves a
  *conditional* statement: the Einstein field equations follow from a
  finite-information capacity bound plus a Jacobson-style equation of state,
  with the physics inputs as explicit hypotheses
  (`QIQTH.QiqtToGR.qiqt_bekenstein_gives_gr`). The authors stress the result is
  conditional, not a derivation of GR from first principles.

## Has general relativity been formalised as theorems?

**No, not end to end.** As of the surveyed state:

1. **Curvature algebra** is formalised in places: metric components,
   Christoffel symbols, Riemann/Ricci/scalar curvature, the Einstein tensor and
   its divergence-free property.
2. **The field equations** have been *stated* and derived only conditionally
   from extra physical premises.
3. **Solution theory** — the initial value formulation, local existence and
   uniqueness for the Einstein equations, singularity theorems (Penrose–
   Hawking), black-hole uniqueness/no-hair, energy conditions, global
   hyperbolicity — is not formalised in any of these projects.
4. **No Lean theorem** in the surveyed repositories states that a specific
   black-hole metric solves the vacuum equations; the Schwarzschild solution
   appears, if at all, as an unproved claim.

So the meaningful gap is not "definitions of curvature" but "theorems about
solutions". This repository is a small, kernel-checked step into that gap, plus
a GPU numerical check of the solutions the Lean side cannot yet reach.

## What this repository adds

* `gravitation/Gravitation/` — Mathlib-based, `sorry`-free component
  formalisation: metric with explicit inverse, Riemann tensor with its
  algebraic symmetries, Ricci, scalar curvature, Einstein tensor; proved
  symmetry of `G`, the trace identity `g^{ij}G_{ij} = (1 - n/2)S`, and
  `G = 0 ↔ Ric = 0` in four dimensions; Minkowski as a proved vacuum solution.
  (The structure carries three symmetries — pair symmetry, antisymmetry in the
  last pair, and the first Bianchi identity — and `skew_first` is proved from
  them. Ricci contracts with the diagonal inverse metric.)
* `gravitation/Gravitation/InitialValue.lean` — the initial value problem's
  constraint equations: `H = ³R + (tr K)² − K_ij K^ij`, `M_i = ∂_j K_ij −
  ∂_i tr K`, the moment-of-time-symmetry reduction to scalar flatness, the
  maximal-slicing form, and a non-vacuum example proving the constraints are not
  automatic. Development existence (Choquet–Bruhat–Geroch) is deliberately not
  claimed and not axiomatised.
* `gravitation/Gravitation/ScalarTensor.lean` — Brans–Dicke PPN parameters, the
  `ω → ∞` GR limit and coupling bounds, the `f(R)` linear case, Starobinsky
  potentials/masses, the four-dimensional trace equation and the
  one-dimensional Galileon total-derivative structure.
* `gravitation/Gravitation/Screening.lean` — chameleon screening: the
  density-dependent mass, the shrinking Compton range, exponential Yukawa
  suppression beyond it, and the thin-shell cap on the fifth force.
* `gravitation/Gravitation/Ostrogradsky.lean` — the Ostrogradsky instability:
  a degenerate velocity Hessian for `L = ½q̈² + V`, a Hamiltonian affine in one
  momentum and unbounded below, contrasted with a positive-definite quadratic
  kinetic term.
* Axiom policy — no `axiom`, `constant`, `opaque`, `sorry`, `admit` or
  `native_decide` anywhere in `Gravitation/`; `scripts/audit_axioms.sh` checks
  every declaration against `{propext, Classical.choice, Quot.sound}`, the
  axioms the base libraries already assume, and runs in CI on every push. The
  README carries a per-declaration proof-status table generated by
  `scripts/proof_status.sh`; CI fails if the table goes stale.
* Silent build — `lake build` emits no messages. Tactic and unused-variable
  warnings were removed by rewriting the proofs, not by disabling linters, and
  Lake's module-system advisory is opted out with `allowNonModules = true`.
  `scripts/check_messages.sh` fails if a message reappears; CI runs it.
* GPU check — the Vulkan tensor pass runs in double precision and, for the
  Schwarzschild metric, reproduces the proved `48M²/r⁶` to `1.2e-7`. CI runs it
  on the lavapipe software driver, so no GPU runner is needed.
* `gravitation/Gravitation/Examples/Schwarzschild.lean` — the Schwarzschild
  curvature in an orthonormal frame: proved Ricci flat for every mass
  parameter, with the Kretschmann sum `48 M²/r⁶`. The electric part is derived
  rather than asserted: `g_tt = −(1 + 2Φ)` fixes `Φ = −M/r`, and the tidal
  eigenvalues `Φ'' = −2M/r³`, `Φ'/r = M/r³` are proved from the potential, so
  the tensor is `electricPart` at `k = M/r³` and is trace free because `Φ` is
  harmonic. Contracting the full metric Riemann tensor against the frame is
  still not formalised, and is stated as such.
* `gravitation/Gravitation/Conservation.lean` — the contracted Bianchi identity
  accepted as a hypothesis, yielding `∇·G = 0` and the uniqueness of `G` as the
  conserved combination of `Ric` and `S g`.
* `gravitation/Gravitation/Geodesics.lean` — the geodesic Cauchy problem:
  local existence from initial position and velocity via Mathlib's
  Picard–Lindelöf theorem, uniqueness under an explicit Lipschitz hypothesis,
  and the flat-space straight lines.
* `gravitation/Gravitation/Alternatives.lean` — MOND, MOG and TeVeS stated as
  used, with proved structural theorems (deep-MOND flat rotation, MOG's bounded
  enhancement, TeVeS's preserved Lorentzian signature) and the empirical
  strengths/weaknesses recorded in prose, not as theorems.
* `gravitation/vulkan/` — Vulkan compute path computing `Γ`, `Ric`, `R`, `G`
  from any metric supplied as an analytic function of the coordinates, used to
  check numerically that Schwarzschild is Ricci flat and that
  Schwarzschild–de Sitter has `Ric = Λg`.

## Sources

* https://github.com/anthropics/formal-math
* https://github.com/anthropics/fermats-last-theorem
* https://github.com/openai/ten-proofs
* https://github.com/openai/math
* https://github.com/leanprover-community/physlib
* https://arxiv.org/abs/2405.08863 (HepLean)
* https://zenodo.org/records/20837810 (conditional EFE derivation)
* https://github.com/TataSatyaPratheek/mathematical-physics-lean
