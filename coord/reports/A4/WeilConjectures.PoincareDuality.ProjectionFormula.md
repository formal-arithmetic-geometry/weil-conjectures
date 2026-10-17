## What changed

Updated `WeilConjectures.PoincareDuality.ProjectionFormula` with a complete proof of
`isIso_openImmersionProjectionComparison`. The proof establishes invertibility of the
open-immersion adjunction unit, transports the underived module projection formula through
complexes and K-flat resolutions, and identifies the derived projection comparison with the
adjunction counit. Added the proof-only import and local transparency/cache declarations
needed to keep elaboration below the file limit. Existing naturality proofs and signatures
are unchanged.

## Proved and sorry left

Closed one existing hole:

- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_openImmersionProjectionComparison`.

One existing hole remains:

- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleExceptionalProjectionMorphism`
  (the source module has no attached DAG node for this declaration; it remains the original
  postponed theorem).

No new `sorry`s were added. No definitions contain `sorry`.

## No longer needed

No imports, nodes, or modules were removed. The proof follows the open-extension and
compactification route already present in the module. The finite-coefficient projection
formula modules are not imported because they do not state the condensed module-object
comparison used here.

## Where the brief, the DAG or earlier work was wrong

The earlier returned delivery was based on a pre-upstream-sync source snapshot. The proof
here is rebuilt against the current source and uses the current local cache declarations
from `Sheaf.Paper.IntegralResidueDerivedMonoidal`. The remaining bounded-constructible
isomorphism is still an unresolved source theorem and was not weakened or renamed. The change record is `coord/changes/A4-projection-open-iso.md`.

## New nodes

None.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
