## What changed

Retired `Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`, which
was a forwarding shim around the canonical upstream module. The 13 current
consumers were migrated to import
`WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`
with the same visibility. `RawModuleFreeSourceAcyclic` keeps `import all` so its
private evaluation helper resolves from the upstream module. The unbounded
exchange consumer also imports the canonical upstream underived exchange theorem
and records that dependency in its node. The four affected DAG attachments now
point at the canonical upstream declarations. All migrated files compile together.
The change record is `coord/changes/J2-retire-module-abelian-derived-direct-image-comparison.md`.

## Proved and sorry left

The retired module has zero declarations and zero sorries. This delivery closes
zero theorem holes and adds zero holes; it is a retirement and import migration.
Existing sorries in consumers are unchanged, including
`AlgebraicGeometry.Etale.sf_directImage_ctf_open_tor` and
`AlgebraicGeometry.Etale.unboundedProperOpenInterchange`.

## No longer needed

The forwarding shim, its private alias and its private duplicate evaluation
wrapper are no longer needed. No mathematical proof dependency is pruned: the
canonical upstream declarations remain attached to their existing nodes. The
Sheaf shim import is removed from every current consumer; the corresponding
upstream import supplies the same public API.

## Where the brief, the DAG or earlier work was wrong

The assigned item is a zero-hole retirement repair, rather than a theorem proof.
The previous retirement packet was removed during batch recovery, so this
redelivery restores that migration on the current base. The upstream module is
the canonical owner of the derived comparison and coefficient-forgetting API;
keeping the forwarding shim duplicates declarations and causes import collisions.
Several listed historical consumers are quarantined or absent and therefore are
not restored or edited here.

## Forced adaptations

### Sheaf.Paper.UnboundedProperOpenInterchange
Original imports module(s) explicitly withdrawn in deleted.txt: Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison. Those imports must be migrated in this delivery; the baseline's compiled copies are not valid counterfactual dependencies. Adapted module compiled in the delivered set. CODEX verifies the migration and every accompanying API adaptation is needed.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
