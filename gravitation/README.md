# Gravitation (Lean 4 + Mathlib)

Downstream formalisation of general relativity. The development itself lives in
Physlib's unmerged `gravity` branch; this repository depends on `physlib` and
vendors the branch's 37 GR modules under `vendor/` until they are merged. The
umbrella module `Gravitation.lean` imports them (plus `IncompressibleSphere`
from the dependency) under the `Gravitation.Relativity.General.*` path. A local
`Gravitation.KretschmannTotal` addendum removes the remaining `r ≠ 0` from the
frame Kretschmann theorems; nothing else is local.

Pinned to Lean `v4.36.0` and Mathlib `v4.36.0` (`lean-toolchain`,
`lakefile.toml`). Build with:

```sh
lake exe cache get
lake build
```

See the top-level `README.md` for the full layout, `vendor/README.md` for
provenance and removal, and `Proof-Status.md` for the declaration census.

## What is here

* The static spherically symmetric pipeline: metric, inverse, Christoffel,
  Riemann, Ricci, scalar and Einstein tensors, with the Schwarzschild and
  Schwarzschild–de Sitter solutions, their Kretschmann invariants and Weyl
  components.
* Kerr, Reissner–Nordström, FLRW and linearized gravity.
* The `Modified` subtree: Einstein–Cartan, teleparallel/TEGR, Kaluza–Klein,
  Lovelock/Gauss–Bonnet, Einstein–Aether, massive gravity, PPN, Brans–Dicke,
  `f(R)`/Starobinsky, chameleon screening, MOND, MOG, TeVeS, Nordström,
  Galileon and Ostrogradsky — field equations or exact reductions where the
  module provides them, structural laws otherwise.
* Conservation: the contracted Bianchi identity is **proved** for the frame
  Einstein space (`sds_frame_bianchi`), not assumed, and
  `sds_frame_einstein_conserved` derives `∇·G = 0`. The generic `CurvDeriv`
  lemmas take the identity as a parameter because no covariant derivative for
  an arbitrary bundle is formalised.
* The ADM constraints and the coordinate pipeline that feeds the Vulkan
  numerical pass.

## Conventions

Metric signature `(−, +, +, +)`. `Ric_{ij} = R^k{}_{ikj}`,
`R = g^{ij}Ric_{ij}`, `G_{ij} = Ric_{ij} − ½ R g_{ij}`, units with `c = G = 1`
so the field equations read `G = 8πT`.

## Scope

Everything is pointwise in a coordinate chart: there is no smooth manifold
structure, no global existence theory, and no PDE theory. The chart
restrictions of the metric-level theorems are listed in the paper's §6.
