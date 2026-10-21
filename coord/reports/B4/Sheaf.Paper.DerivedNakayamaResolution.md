## What changed

Restored `lean/Sheaf/Paper/DerivedNakayamaResolution.lean` from its recorded quarantine
archive. Closed `AlgebraicGeometry.ProEtale.DerivedNakayama.pullback_regular` by `rfl`:
transporting the regular module and forming the regular module of the transported ring
produce the same object and action. Every signature, coefficient construction, import,
attribute and existing docstring is preserved. The quarantine archive is preserved.

The original archive compiled on the server in 7.2 seconds. The changed file compiled
in 10.6 seconds; a later ordered sandbox compile took 9.9 seconds. A separate consumer
compiled against that sandbox output in 4.0 seconds. It imports only the item, applies
the proved equality and verifies by `rfl` that `regularPullbackIso.hom.hom` is the identity.
`#print axioms` for both `pullback_regular` and `regularPullbackIso` gives exactly
`propext`, `Classical.choice`, `Quot.sound`. The consumer was removed from the delivery.

Change record: `coord/changes/B4-derived-nakayama-resolution-restoration.md`.

## Proved and sorry left

The archived module had two holes. One hole closed:
`AlgebraicGeometry.ProEtale.DerivedNakayama.pullback_regular`
(node `det-pe-derived-nakayama-resolution`, step 3).

One original hole remains, with its original source and seven-step proof in its docstring:
`AlgebraicGeometry.ProEtale.DerivedNakayama.derived_nakayama_resolution`
(node `det-pe-derived-nakayama-resolution`). This delivery does not claim to prove or
reduce that theorem. No new holes, statements, nodes or decompositions are added.

## No longer needed

None. All imports, nodes, declarations and dependency edges are retained. In particular,
the main theorem's pending proof plan still needs its declared coefficient-exactness,
K-flat tensor and quotient-triangle dependencies. No quarantined path is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The live item is absent because of the recorded cluster-restore rollback; the archive
is the authoritative source to restore. It compiles unchanged against the current
published library. The regular-module equality does not require the extended argument
suggested in its docstring: its two sides are already definitionally equal. This closes
that auxiliary hole without changing the mathematical route of the main theorem.

Searches included the stated dependency signatures, the unit and resolution proof,
Lean Finder, Loogle, launcher grep, and both library roots. The existing
`DerivedCategory.principalDerivedTensorCone` concerns ordinary `ModuleCat` and an
objectwise mixed tensor, not the present natural comparison for continuous internal
module objects. It is not a direct replacement for the remaining resolution theorem.
Live importer counts miss the nine quarantined consumers listed in the change record.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
