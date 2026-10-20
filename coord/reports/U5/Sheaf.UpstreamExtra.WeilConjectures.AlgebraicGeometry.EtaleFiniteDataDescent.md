## What changed

Restored the assigned quarantined module
`Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent`
from its current source in `quarantine/`. The live path is absent from `lean/`;
`coord/rework.tsv` retains the restoration assignment and U5 retains its claim.
For the latest return of delivery `7d5eaf21a2` (base `6488bba00`), reread the
current archive and regenerated the repair from it. Compared both private helper
signatures and complete proofs with the retained returned packet: they agree.
The delivery tool fetches the current `sheaf-dag` and constructs a new commit on
that base, so the earlier changed-since-base delivery is not reused.

Removed the dangling `set_option linter.unusedVariables false in` immediately
before `end AlgebraicGeometry`. Its scoped option opens an unnamed scope at the
namespace-closing command and causes the recorded parser error. Preserved both
private helpers `AlgebraicGeometry.pullbackComp_inv_fst` and
`AlgebraicGeometry.comparison_fst`, every public import, and the original blueprint
provenance. Wrapped the provenance comment to 100 columns and disabled the
`linter.privateModule` warning for this intentionally private-helper-only module.
Change record: `coord/changes/u5-etale-finite-data-descent-quarantine-scope.md`.

## Proved and sorry left

Assigned parser repair completed. Original holes: 0. Holes closed: none (0 of 0).
Holes added: none. Sorries left: none. Split-off statements: none.
Both private comparison proofs remain complete and unchanged.

Validation: single-file server compilation through `lcompile.py`; delivery
preflight additionally checks the declarations with its axiom probe.

## No longer needed

None. No imports, declarations, nodes, or modules were removed. The dangling scoped
linter option was leftover extraction syntax and is unnecessary.

## Where the brief, the DAG or earlier work was wrong

This is a zero-hole quarantine rework, rather than a theorem-proving item. The
recorded failure was `Unexpected name AlgebraicGeometry after end: The current
section is unnamed`, caused by the dangling scoped option left during extraction.
No DAG node is attached to this helper-only module. The finite-data descent node
remains attached to the upstream theorem; its attachment and dependencies stay
unchanged. Searches of live and quarantined Lean sources found no importers of
this helper-only module, so no consumer adaptation is needed.

The latest return (`7d5eaf21a2`) concerns the changed-since-base landing check.
This retry reconstructs the substantive parser repair from the current archived
source and restores it on the current delivery base. It does not withdraw the
quarantined module, alter the upstream theorem, or deliver an empty module.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
