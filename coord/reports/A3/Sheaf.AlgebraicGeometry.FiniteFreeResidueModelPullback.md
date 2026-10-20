## What changed

Restored and proved `Sheaf.AlgebraicGeometry.FiniteFreeResidueModelPullback` with its existing
statement `AlgebraicGeometry.Scheme.finiteFreeResidueModel_pullback`. The proof is the existing
bounded-above finite-free transport argument: it uses the open-site equivalence, bounded-above
flat K-flatness, the derived pullback counit on K-flat complexes, and the universe-aware
open-restriction comparison. The withdrawn duplicate Sheaf derived-pullback module is replaced
by the adopted upstream `WeilConjectures.AlgebraicGeometry.DerivedPullback` public import so
that the required declarations are available without an environment collision.

Validation: `lcompile.py` compiles the module successfully with no warnings.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.finiteFreeResidueModel_pullback`; zero original sorries remain,
zero sorries were added, and zero statements were split off.

## No longer needed

No proof-plan dependencies were pruned. The original private helper lemmas and all imports used
by the proof remain necessary; no unrelated modules were added.

## Where the brief, the DAG or earlier work was wrong

The quarantined module imported both the withdrawn Sheaf `DerivedPullback` stub and the adopted
upstream `WeilConjectures.AlgebraicGeometry.DerivedPullback`, causing the rework error that
`AlgebraicGeometry.derivedPullback` was already present. The corrected public import directly
uses the adopted upstream module and compiles against the current library. The DAG statement and
proof plan are unchanged.

Change record: `coord/changes/finite-free-residue-model-pullback-import.md`.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
