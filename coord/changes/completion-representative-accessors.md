# RepresentativeComparison named accessors

## Reason

The coherence theorem's signature repeatedly expands the large normalized representative subtype while elaborating its val fields. Named projections allow clients to mark the original definition locally irreducible and keep its large categorical predicate abstract. They are the existing Subtype.val and Subtype.property, with the concrete output types checked once. No original definition or theorem statement changes.

## Old

The value and predicate were available only through the generic subtype projections, which require reduction of RepresentativeComparison.

## New

The public module Sheaf.Algebra.Homology.CompletionRepresentativeAccessors defines RepresentativeComparison.val as Subtype.val and proves RepresentativeComparison.property by Subtype.property, retaining precisely the original quotient and counit equations. The coherence module publicly imports these projection names and marks RepresentativeComparison locally irreducible. The defining module Sheaf.Algebra.Homology.FiniteFreeCompletionExchange stays at its published version (the predicate factorization proposed by the delivery was withdrawn by the reviewer, see representative-condition-factorization.md).

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence | B4 | Uses the named projections while the large definition remains abstract. |
| Sheaf.Algebra.Homology.SectionsScalarDerivedTransport | unclaimed | No RepresentativeComparison uses and no adaptation. |
| Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent | unclaimed | Imports the extracted scalarTensorSection API; no representative uses. |

These are the direct item consumers; indirect importers also receive the same projections through public reexports. They are definitionally the previous subtype projections, so the original seven public signatures and all target meanings are preserved.

## Status

landed 20261025T201357-L-2465468 2026-10-25 (merge of deliver/B4/Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence)
