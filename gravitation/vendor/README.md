# Vendored copy of the Physlib `gravity` branch

This directory is a **temporary source copy** of the general-relativity
development that lives on the unmerged `gravity` branch of Physlib. The proofs
and the `GeneralRelativity` namespace are unchanged; only the module path is
rewritten from `PhyslibAlpha.Relativity.General.*` to
`Gravitation.Relativity.General.*`, because Lake maps `PhyslibAlpha.*` to the
dependency's own library globs and the vendored files would otherwise be located
in the upstream checkout (where they do not exist).

## Provenance

| | |
| --- | --- |
| Upstream project | [leanprover-community/physlib](https://github.com/leanprover-community/physlib) |
| Branch | `gravity` (`origin/gravity` of the author's fork) |
| Commit | `41abde06da753a8a52903232e12c9f5ecb7a9a3b` (merge of master `cbd02238` into `gravity`) |
| Copied | 24 November 2026 |
| Scope | `PhyslibAlpha/Relativity/General/`, except `Schwarzschild/IncompressibleSphere.lean` |
| Rewrites | import lines only: `PhyslibAlpha.Relativity.General.` → `Gravitation.Relativity.General.` |

`Schwarzschild/IncompressibleSphere.lean` is **not** copied: it is already on
Physlib master, so the build imports it from the upstream dependency. The
vendored files are otherwise unchanged from the branch commit, including their
Apache-2.0 headers; the rest of this repository is MIT.

The `physlib` requirement in `gravitation/lakefile.toml` therefore points at
Physlib **master** (`cbd02238`, the merge base the vendored modules were written
against), not at the unmerged branch. Nothing in the build depends on the branch
remaining available.

## Why

The branch is not merged upstream, so a git dependency on it would make the
build depend on a personal fork and a moving ref. Vendoring the branch's
sources keeps the proofs auditable and the build reproducible; the axiom audit
covers the vendored tree as well as the local module.

`scripts/check_vendor_sync.sh` runs in CI: it fetches the branch, fails if its
tip differs from `REVISION`, and diffs every vendored file against the branch
after the same import rewrite, so this copy cannot drift unnoticed.

## Removal once merged

1. Delete `gravitation/vendor/`.
2. Delete the `[[lean_lib]]` block `GravitationVendor` from
   `gravitation/lakefile.toml` (and its `srcDir = "vendor"`).
3. Switch the imports in `gravitation/Gravitation.lean` from
   `Gravitation.Relativity.General.*` back to
   `PhyslibAlpha.Relativity.General.*` (the already-merged
   `IncompressibleSphere` line is unchanged).
4. Change the `physlib` requirement to a revision that contains
   `PhyslibAlpha/Relativity/General/` (upstream master after the merge).
5. Run `lake update physlib && lake build`, then `scripts/audit_axioms.sh` and
   `scripts/proof_status.sh`.
6. Delete this README.

The namespace and every theorem name are already the upstream ones, so no other
Lean source changes.
