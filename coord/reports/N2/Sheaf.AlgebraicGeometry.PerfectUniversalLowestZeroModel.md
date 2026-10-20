## What changed

Restored `Sheaf.AlgebraicGeometry.PerfectUniversalLowestZeroModel` from the exact
quarantine path in `coord/rework.tsv`. Redirected its public derived-pullback
import and private composition import to the adopted WeilConjectures modules.
The archived theorem signature and complete proof body are unchanged.

The proof uses the residue-field rank tests, the finite-free residue model and
its pullback, derived composition and homology comparison, and the full-rank
bottom-kernel vanishing theorem. All five DAG proof dependencies remain needed.
The node retains its attachment and route; its proof-origin note records the
restoration. The unit route is preserved.

The original source failed with unknown `derivedPullback` in its public signature
and unknown `exists_derivedPullbackComposition` in its proof. The repaired module
compiled cleanly through `lcompile.py` in 19.0 seconds.

Change record:
`coord/changes/N2-perfect-universal-lowest-zero-model-restoration.md`.

## Proved and sorry left

`AlgebraicGeometry.Scheme.perfectUniversalLowest_zero_model` is restored with its
complete proof. The archived item has zero holes: zero closed, zero added, zero
left, and zero split off. This is a quarantine/import repair, not a new hole
closure or a decomposition. No additional theorem or module is introduced.

## No longer needed

Removed the two withdrawn compatibility imports
`Sheaf.AlgebraicGeometry.DerivedPullback` and
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition`; their adopted source modules
provide the declarations. No mathematical node, dependency, or unit step is pruned.

LeanFinder returned generic K-projective, free-sheaf presentation and free-locus
lemmas, not a shorter scheme-level zero-bottom model theorem. Loogle confirmed
the existing `SheafOfModules.freeHomEquiv` API used for the zero-rank argument.
Local searches found the degree-zero bottom-model theorem, which does not replace
the current arbitrary-degree interface. The existing DAG combination is retained.

## Where the brief, the DAG or earlier work was wrong

The current assignment is a restoration of a zero-hole module, not an unproved
statement. Its archived imports predate the adoption of the source derived
pullback and composition declarations. The current node already points its
composition dependency at the correct source declaration. Its statement and
proof plan need no mathematical correction.

The sole direct consumer is itself quarantined and retains this theorem in both
its Lean proof and DAG dependencies. Its absence from the live Lean import graph
does not authorize withdrawal. This packet restores the assigned declaration.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
