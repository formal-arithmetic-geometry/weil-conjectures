## What changed

Restored the quarantined `Sheaf.Paper.LisseFiniteHomLift` module and repaired its
proof import after the 2026-10-20 upstream sync. The private
`CategoryTheory.Mod.relativeTensorRightIso` comparison now lives in
`Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian`.
Import that module with `import all` instead of importing all private declarations
from its original upstream module. All public imports, declaration signatures,
definitions, attributes and proof bodies are preserved verbatim.

The restored file compiles through lcompile.py (10.6 seconds, exit 0).

## Proved and sorry left

This is a zero-hole repair, not a new hole closure: zero holes closed, zero added,
zero remaining in the restored module. The existing complete proof of
`AlgebraicGeometry.ProEtale.exists_lisse_finite_hom_lift`
(node `lem-sfb-lisse-finite-hom-lift`) now compiles against the synced library.
Its three private helpers also remain completely proved. Imported dependencies
are unchanged mathematically; this does not assert that their transitive axiom
closure is free of upstream proof holes.

## No longer needed

Removed only the obsolete private-proof import
`import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian`;
the original upstream module remains publicly available through the unchanged
public imports. The comparison is used from its new Sheaf.UpstreamExtra location.
No mathematical dependency, DAG node, module or declaration is pruned.
The unit route and all six stated proof dependencies are preserved.

## Where the brief, the DAG or earlier work was wrong

The item is quarantined for an unknown-constant compilation failure, not for a
remaining sorry. Its rework row names `Mod.relativeTensorRightIso`: the sync moved
that proved private definition to Sheaf.UpstreamExtra, but the archived module
still imported private declarations only from the old path. No mathematical
statement or construction requires correction. The archive and its node attachment
are preserved; no deletion is requested.

Change record: `coord/changes/E2-lisse-finite-hom-lift-private-import.md`.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
