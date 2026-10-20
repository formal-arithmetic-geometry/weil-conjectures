## What changed

Restored `lean/Sheaf/Paper/ContinuousAlgClConstructibleTor.lean` from the quarantine
archive named by its current `coord/rework.tsv` row. Replaced the obsolete
`import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian`
with
`import all Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian`.
The scheduled upstream sync moved the proved private comparison
`CategoryTheory.Mod.relativeTensorRightIso` into this companion module. An ordinary
public import of the companion did not expose that private declaration.
The existing public imports, declaration signatures, definitions, theorem bodies,
and DAG attachment and dependency route are preserved. No consumer adaptation or
statement/definition change record is needed for this proof-import repair.

The whole restored module compiles through `lcompile.py` without errors or warnings
(9.5 seconds on the repair retry). Its unchanged proof first establishes flatness of constructible
modules using the local finite-free theorem and stratified detection of maps, then
uses bounded Postnikov devissage and the Tor amplitude of a flat single object.
The empty scheme, rank zero, and zero complex follow the same existing argument.

## Proved and sorry left

This is a zero-hole compilation repair, not a newly closed proof hole.
The restored theorem `AlgebraicGeometry.ProEtale.continuousAlgCl_bounded_finiteTor`
and its private helpers `stratified_map_eq` and
`continuousAlgCl_constructible_flat` have complete proofs.
Original module holes: 0. Remaining module holes: 0.
Holes closed: none. Holes added: none. Split off: none.
No new declaration or module is introduced. Existing dependencies retain their
own proof obligations; this delivery does not claim to close those.

## No longer needed

The obsolete private import of
`WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian` is replaced by
the private import of its `Sheaf.UpstreamExtra` companion. The upstream module
remains a transitive dependency through the unchanged public imports; it is not
pruned or withdrawn. No mathematical node or module is pruned, and every declared
proof dependency of `det-sf-comp-continuous-algcl-constructible-tor` remains used.

## Where the brief, the DAG or earlier work was wrong

The item is present in quarantine and has zero `sorry`s. Its recorded rework
failure is stale private-declaration visibility after upstream sync, rather than
an unfinished theorem. The archive's `import all` targeted the old upstream home,
while its ordinary public companion import did not make private declarations
available. Importing all of the actual companion repairs every reference to the
comparison without editing the adopted source library. The DAG and unit route
need no changes.

For the return at delivery head `b63499875f`, compared the retained sandbox with
the current repository source and its rework archive. The item is still absent
from `lean/`, and the current quarantined source differs from the retained file
only in the private import repaired above. Restoring that current source with
this import replacement preserves all intervening public imports and proofs.
The repair was recompiled and its new delivery dry run passed.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
