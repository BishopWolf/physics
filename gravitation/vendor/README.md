# Vendored copy of the Physlib `gravity` branch

This directory is a **temporary source copy** of the general-relativity
development that lives on the unmerged `gravity` branch of Physlib. The proofs
and the `GeneralRelativity` namespace are unchanged; only module paths are
rewritten from `PhyslibAlpha.*` to `Gravitation.*`, because Lake maps
`PhyslibAlpha.*` to the dependency's own library globs and the vendored files
would otherwise be located in the upstream checkout (where they do not exist).

## Provenance

| | |
| --- | --- |
| Upstream project | [leanprover-community/physlib](https://github.com/leanprover-community/physlib) |
| Branch | `gravity` (`origin/gravity` of the author's fork) |
| Commit | `b81c896ac3b7a25487d3d97aaa869dd6704e0ae5` (merge of master `7910f51f` into `gravity`) |
| Copied | 25 November 2026 |
| Scope | `PhyslibAlpha/Relativity/General/` (except `Schwarzschild/IncompressibleSphere.lean`), `PhyslibAlpha/Relativity/Metrics/`, `PhyslibAlpha/Relativity/Tensors/{Tensor2,RiemannTensor,RicciTensor,EinsteinTensor,MaxwellStressEnergy}.lean`, and `PhyslibAlpha/Cosmology/FLRW/Metric.lean` |
| Rewrites | import lines only: `PhyslibAlpha.Relativity.General.` → `Gravitation.Relativity.General.`, `PhyslibAlpha.Relativity.Metrics.` → `Gravitation.Relativity.Metrics.`, `PhyslibAlpha.Relativity.Tensors.` → `Gravitation.Relativity.Tensors.`, `PhyslibAlpha.Cosmology.` → `Gravitation.Cosmology.` |
| Local patch | `Modified/MOND.lean`: removed `[Fact frame.IsMetricConserved]`, because that class is not present in the pinned Physlib revision `7910f51f`; the lemma statement and proof are otherwise unchanged |

`Schwarzschild/IncompressibleSphere.lean` is **not** copied: it is already on
Physlib master, so the build imports it from the upstream dependency. The
vendored files are otherwise unchanged from the branch commit, including their
Apache-2.0 headers; the rest of this repository is MIT. There are 57 vendored
Lean modules in total (43 under `Relativity/General`, 8 under
`Relativity/Metrics`, 5 under `Relativity/Tensors`, and 1 under
`Cosmology/FLRW`).

The `physlib` requirement in `gravitation/lakefile.toml` therefore points at
Physlib **master** (`7910f51f`, the merge base the vendored modules were written
against), not at the unmerged branch. Nothing in the build depends on the branch
remaining available.

## Why

The branch is not merged upstream, so a git dependency on it would make the
build depend on a personal fork and a moving ref. Vendoring the branch's
sources keeps the proofs auditable and the build reproducible; the axiom audit
covers the vendored tree as well as the local module.

`scripts/check_vendor_sync.sh` runs in CI: it fetches the branch, fails if its
tip differs from `REVISION`, and diffs every vendored file against the branch
after applying the same import rewrites and the MOND compatibility patch, so
this copy cannot drift unnoticed.

## Removal once merged

1. Delete `gravitation/vendor/`.
2. Delete the `[[lean_lib]]` block `GravitationVendor` from
   `gravitation/lakefile.toml` (and its `srcDir = "vendor"`).
3. Switch the imports in `gravitation/Gravitation.lean` from
   `Gravitation.Relativity.General.*`, `Gravitation.Relativity.Metrics.*`,
   `Gravitation.Relativity.Tensors.*`, and `Gravitation.Cosmology.*` back to
   the corresponding `PhyslibAlpha.*` paths (the already-merged
   `IncompressibleSphere` line is unchanged).
4. Change the `physlib` requirement to a revision that contains all four
   vendored subtrees (upstream master after the merge).
5. Run `lake update physlib && lake build`, then `scripts/audit_axioms.sh` and
   `scripts/proof_status.sh`.
6. Delete this README.

The namespace and every theorem name are already the upstream ones, so no other
Lean source changes.
