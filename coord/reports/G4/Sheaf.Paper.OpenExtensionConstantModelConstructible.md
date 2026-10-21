## What changed

Restored `lean/Sheaf/Paper/OpenExtensionConstantModelConstructible.lean` verbatim
from its quarantine archive, as assigned by its current `coord/rework.tsv` row.
The library path was absent following a cluster restore; the archived module
already contains the complete proof of
`AlgebraicGeometry.ProEtale.constantModelConstructible_openImmersionLowerShriek`.
This delivery restores that implementation, rather than withdrawing its node or
replacing the archive with an empty module. Its existing DAG attachment, proof,
proof dependencies, statement, public imports, and all declarations are preserved.

Read the current node, unit record, blueprint Constructibility paragraph, archived
module, prior T2 report and change record, and the coefficient, local-model,
stratification and lower-shriek interfaces. The proof constructs the old strata
plus the reduced closed complement, uses the open adjunction unit on old strata,
proves complement vanishing by empty fibre products and adjunctions, and
transports the supplied finite constant local models. Empty schemes and
invertible open immersions are handled explicitly. No new mathematical lemma
or definition repair was required.

Validation: the restored module compiled without errors or warnings using
`lcompile.py` against the current library (5.9 seconds). Delivery preflight also
checks every delivered declaration using the project's axiom probe.
The restoration record is `coord/changes/G4-open-extension-quarantine-restore.md`.

## Proved and sorry left

Actual archived hole count: zero. Actual delivered hole count: zero.
Holes closed in this repair: none. Holes added: none. Split off: none.
The complete retained proof is
`AlgebraicGeometry.ProEtale.constantModelConstructible_openImmersionLowerShriek`
(node `lem-sf-open-extension-zero-constant-model-constructible`).
Every private theorem also has a complete proof; no `sorry` remains in the module.
This is a source restoration, not a new hole closure or decomposition.
Imported library obligations are not claimed closed.

## No longer needed

None relative to the quarantine archive: no imports, nodes, declarations or
modules were pruned. All existing dependencies and the unit route are retained.
Mathlib searches via LeanFinder, Loogle and grep found no replacement theorem
for finite constant models of pro-etale module objects. The archived direct
adjunction argument is preserved.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief does not mean that this repair has an open theorem:
the source is quarantined and already has zero holes. The actual assigned repair
is restoring its missing library path. The rework row records a cluster restore,
not a mathematical withdrawal or a request to alter the statement. No current
G4 return supplies a further numbered repair request.
`tools/downstream.py` reports the item as an unknown module because its library
path is absent. A source search also checked the quarantined parent
`Sheaf.Paper.OpenImmersionLocalizing`, which imports this module and applies its
original theorem; both interface and intended dependency are preserved.
No source statement error was found.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
