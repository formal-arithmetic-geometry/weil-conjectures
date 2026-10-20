## What changed

Restore `Sheaf.Algebra.Homology.AffinePushforwardComparisonFactorization` from quarantine
as a public re-export of its proved adopted upstream counterpart. The upstream theorem
`AlgebraicGeometry.affinePushforwardComparison_factorization` is the quarantined theorem
and proof with five explicit `SheafOfModules.{u}` annotations (apart from its copyright
header). Those universes agree with the current comparison-coordinate definitions.
The DAG's Lean record points to this existing canonical declaration. Its two-step
naturality proof and coordinate dependency stay intact. No upstream source changes.

The return for head `d9e7e9592c` reports a landing-base conflict, after the independent
reader passed the repair. Rechecked current `sheaf-dag`: the item is absent from `lean/`,
its original is preserved at the quarantine path in `coord/rework.tsv`, and the upstream
provider is present and fully proved. The restored module retains the reviewed public
re-export and now includes the prescribed `@[expose] public section` header. This retry
rebuilds the delivery on the latest `sheaf-dag` through `deliver3.py`; it does not withdraw
the quarantined item or erase its attachment or dependencies.

Fresh server checks: the delivered module compiles without warnings (1.4 seconds).
A scratch consumer with only its own six sheaf-universe annotations made explicit
compiles against the delivered re-export; its original proof and theorem application
are unchanged. A fresh `#print axioms` for the canonical theorem lists exactly
`propext`, `Classical.choice`, and `Quot.sound`. The import-direction check reports no cycle.

Change record: `coord/changes/affine-pushforward-comparison-factorization-universes-G5.md`.

## Proved and sorry left

Zero-hole quarantine repair: 0 holes before, 0 after, 0 closed, 0 added, 0 split off.
`AlgebraicGeometry.affinePushforwardComparison_factorization` is the existing proved
upstream declaration. No delivered file contains a proof hole. The duplicate local
theorem and private `cancelComparison` helper are replaced by the public re-export.

## No longer needed

The duplicate local theorem proof and private `cancelComparison` helper are unnecessary.
The direct public import of
`WeilConjectures.Algebra.Homology.AffinePushforwardComparisonCoordinates` is replaced
by the public import of the upstream factorization module, which publicly imports
those same coordinates. Their definitions, node, and module remain needed by the
upstream proof. No DAG dependency or library module is claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The assigned module is quarantined, rather than withdrawn. Its archived version already
has zero holes and duplicates the now-proved adopted upstream theorem. Its implicit
sheaf universes do not elaborate against the current comparison-coordinate definitions;
the upstream version makes precisely those universes explicit. The original naturality
argument remains valid in every degree, on zero and unbounded complexes, and over zero rings.

The quarantined direct consumer has an independent universe error in its own instance
binder, recorded before this repair. Its original proof works once its own sheaf universes
are explicit, including the final application of the reused factorization theorem.
That consumer's separate repair is not part of this delivery. The return required a
fresh delivery base and compilation; it requested no change to the mathematical proof.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
