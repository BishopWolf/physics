# Gravitation (Lean 4 + Mathlib)

Component formalisation of the algebraic core of general relativity.

Pinned to Lean `v4.36.0` and Mathlib `v4.36.0` (`lean-toolchain`,
`lakefile.toml`). Build with:

```sh
lake exe cache get
lake build
```

## Modules

* `Gravitation.Basic` — `Tensor2 n` (rank-2 covariant tensors as real matrices),
  `IsSymm`, the Minkowski metric `eta4`, and `Metric` (a symmetric matrix with an
  explicit two-sided inverse). Proves `η * η = 1` and that the inverse of a
  symmetric metric is symmetric.
* `Gravitation.Curvature` — `Riemann` with the four algebraic symmetries
  (antisymmetry in each pair, pair symmetry, first Bianchi), the flat curvature
  `Riemann.flat`, the contraction `ricci`, and the proof that `ricci` is
  symmetric. `scalarCurv` is `g^{ij} Ric_{ij}`.
* `Gravitation.Einstein` — `einstein M R = Ric − ½ S g`; symmetry; the trace
  identity `g^{ij}G_{ij} = (1 − n/2) S`; and in four dimensions
  `G = 0 ↔ Ric = 0`.
* `Gravitation.Examples.Minkowski` — Minkowski spacetime as a proved vacuum
  solution, plus the instantiated vacuum theorem.

## Conventions

Metric signature `(−, +, +, +)`. `Ric_{ij} = R^k{}_{ikj}`,
`R = g^{ij}Ric_{ij}`, `G_{ij} = Ric_{ij} − ½ R g_{ij}`, units with `8πG = 1` so
the field equations read `G = T`.

## Scope

Everything is pointwise in a single coordinate frame. There is no smooth
manifold structure, no connection, and no PDE theory; `vacuum_iff_ricci_flat` is
an algebraic identity, not a statement about the space of solutions. See the
top-level `STATUS.md` for what this does and does not close relative to the
existing Lean physics projects.
