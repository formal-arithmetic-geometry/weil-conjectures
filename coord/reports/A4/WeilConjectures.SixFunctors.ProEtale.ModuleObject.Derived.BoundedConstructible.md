## What changed

Restored the quarantined module
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
to its original `lean/WeilConjectures/` path, byte for byte from the quarantine
archive listed in `coord/rework.tsv`. The assignment is the rework root whose
recorded cause is "reverted by the merge queue after a cluster restore".
The source is currently absent from the library, so this delivery restores the
bounded-constructible restricted functors, adjunctions, compactification-based
lower shriek, and monoidal interfaces; it does not withdraw or empty the module.

The rework contract in `tools/rework.py` requires upstream modules to return
verbatim. No public signatures, attributes, imports, definitions, proof bodies,
or DAG attachments are changed from the archived source. No consumer needs an
adaptation because the restored interface is exactly the archived interface.
The landing machinery restores the module's root import and retains the archive
until a green global build reconciles the rework row.

Validation: the restored complete module compiled through the required
`lcompile.py` with exit code 0 in 44.5 seconds. The archive already includes the
proved pullback, extension-by-zero and tensor-preservation arguments. Searches
also checked the two remaining obligations; historical reductions are not part
of the packet, and no historical split statements are reintroduced.

## Proved and sorry left

This is a quarantine restoration, with 0 of the 2 archived holes closed,
0 new holes, and 0 split-off statements. The two unchanged holes are:

- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_obj`
  (`lem-sfb-dc-lower-star-preserves`).
- `AlgebraicGeometry.ProEtale.CondensedRing.isMonoidalClosed_boundedConstructible`
  (`lem-sfb-dc-hom-small-coefficients`).

No new proof or axiom-freedom claim is made. The three already completed
preservation arguments remain intact. The actual archived hole count is two,
not the five mentioned by the older A4 report.

## No longer needed

None. No declaration, import, node, module, dependency, or quarantine archive is
withdrawn. All original imports and the existing unit route are preserved.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief and older reports describe previous proof assignments.
The current claim is a rework assignment: `coord/rework.tsv` records this module
as quarantined after the upstream-sync cluster restore was reverted. Its absence
from `lean/` is not evidence that its mathematics is unused. The current archive
compiles without source edits, so restoring the actual module is the repair.
The historical no-new-hole tensor proof is already present in that archive;
claiming to close it again would misstate progress.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
