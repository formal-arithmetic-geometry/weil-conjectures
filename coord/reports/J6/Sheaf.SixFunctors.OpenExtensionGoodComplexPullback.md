## What changed

Proved `WeilConjectures.IntegralSystemRealization.openExtension_goodComplex_pullback`
in `Sheaf.SixFunctors.OpenExtensionGoodComplexPullback` from the existing
`openExtension_goodComplex_extension` and the proved pro-etale specialization
`AlgebraicGeometry.ProEtale.VaryingRing.ringPull_preserves_flat` of the ringed-topos
K-flat pullback theorem. Added private proof imports for these declarations and
to access the existing private geometric specialization. The statement and public imports
are unchanged.
Updated this item's node to record the actual proof dependencies. The proof compiled
without warnings in 2.9 seconds; the delivery tool checks the final packet after
removing an unused proof import.

## Proved and sorry left

Closed the one existing hole:
`WeilConjectures.IntegralSystemRealization.openExtension_goodComplex_pullback`
(node `lem-sf-open-extension-good-complex-pullback`). Zero holes remain in the item;
zero holes were added or split off. The imported existing theorem
`WeilConjectures.IntegralSystemRealization.openExtension_goodComplex_extension`
(node `lem-sf-open-extension-good-complex-extension`) still has its existing hole;
this delivery does not modify it.

## No longer needed

Removed the unused trial proof import of `Sheaf.Paper.IntegralOperationsWellDefined`;
the original public bridge import already supplies the exposed goodness predicate.
No existing public import was removed and no module is withdrawn. The item no longer
needs direct proof dependencies `lem-sp-proetale-open-slice-presentation`
(`Sheaf.AlgebraicGeometry.ProEtaleOpenSlicePresentation`) and
`lem-cbc-ringed-open-flat-resolution`
(`Sheaf.Algebra.Homology.RingedOpenFlatResolution`): their completed-extension
specialization is already stated by `openExtension_goodComplex_extension`.
They remain needed for that theorem, so no global pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The old proof step required goodness of the extended complex but did not name
the existing completed-extension theorem supplying that input. Reusing that
statement and the already proved geometric pullback specialization avoids
repeating either the slice transport or the ringed-topos argument. No new
statement, definition repair, target change, or unit-route change is needed.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
