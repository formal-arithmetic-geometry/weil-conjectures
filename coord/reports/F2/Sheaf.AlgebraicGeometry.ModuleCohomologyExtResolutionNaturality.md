## What changed

Repair the returned delivery at `dfe7664f3`, rebased on the current `sheaf-dag`.
Retire the proved duplicate
`Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality` through
`deleted.txt`. Its existing upstream declaration and companion extension keep
the complete comparison API available.

The current base includes B2's reviewed consumer migration (landing
`20261020T230711-L-602865`). All eight consumer adaptations from the old F2
packet are therefore superseded. This packet preserves their current sources,
including B2's new proofs and component API, and changes no consumer or adopted
source-library file. The node copy retains its current statement, dependencies,
proof steps and review data; its Lean note and proof-origin description now
record the retirement of the remaining duplicate.

The change record is
`coord/changes/retire-module-cohomology-ext-resolution-naturality-F2.md`.
It is complete in this packet; no reviewer fix file is required.

Server validation through `lcompile.py --all` compiled the empty withdrawal
module and a scratch module importing all eight live consumers together with
the adopted owner and extension (0.3 s and 2.6 s). The helper-cache, naturality
and current component APIs resolve. `#print axioms` for the adopted naturality
theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Item baseline: zero holes. Holes proved: zero of zero. Holes added: zero.
Split off: zero. No delivered declaration contains `sorry`.
The already proved
`AlgebraicGeometry.Scheme.Modules.moduleCohomologyExtResolutionEquiv_naturality`
remains the node's declaration in the adopted source module.

The old consumer snapshots are not delivered, so this packet changes no
consumer hole or proof. In particular the current proved
`exists_unique_qcoherentNormalizedComparison` is preserved.

## No longer needed

Only the duplicate module
`Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality` is pruned.
No current live library file directly imports it. The quarantine archives for
`CoherentFrobeniusPullback`, `QcoherentNormalizedComparison`, and
`QcoherentNormalizedPullbackSquare` retain their historical imports; their
restored live versions already carry the reviewed migrations and are preserved.
The eight consumer migrations in the retained packet are no longer needed in
this delivery because they are already on the current base; the stale snapshots
and compiled overlay are archived under the sandbox's scratchpad.

No mathematical node, parent reference, proof dependency or unit step is
pruned. The node stays attached to the same upstream naturality theorem. Its
three declared proof dependencies are preserved. The existing source extension
continues to supply `comparisonHasSheafify`, `comparisonHasExt`, and
`ExtEdgeResolution.sectionsComparisonNatIso`.

## Where the brief, the DAG or earlier work was wrong

This is an explicitly listed zero-hole duplicate retirement, rather than a
new proof obligation. The prior mathematical review passed, but the landing
rejected a reviewer fix named
`retire-module-cohomology-ext-resolution-naturality-F2.md`. The stage-3 fix
lookup in `tools/batch_land.py` expects a change-record fix to be named
`retire-module-cohomology-ext-resolution-naturality-F2.change.md`; its delivered
repository path remains the ordinary `.md` path above. This packet includes the
complete record and needs no external fix, avoiding that mismatch.

Since the returned head, B2's reviewed delivery migrated all eight consumers
and reattached the node to the adopted source declaration. Replaying the old
F2 consumer snapshots would undo those later proofs and APIs. This repair
therefore retains only the actual remaining retirement and its records.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
