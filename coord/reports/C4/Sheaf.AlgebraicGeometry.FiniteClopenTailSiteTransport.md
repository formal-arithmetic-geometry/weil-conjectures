## What changed

Filled `AlgebraicGeometry.ProEtale.finiteClopenTailSiteTransport` in the assigned module.
The statement and `finiteClopenProEtaleTail` construction are unchanged. Private proved helpers
identify the extension comparison as the mate of the inverse-image comparison, characterize
clopen projections by restriction, invert the existing compositor-coherence equations, and
paste the three squares. The private mate-transport calculations follow the existing proof in
`Sheaf.SixFunctors.ComparisonOpenTensorCoherence`; the final import uses the narrower pullback
coherence interface instead. Updated the item's DAG proof to describe this argument. The final application uses the
concrete canonical terms, avoiding nested local data aliases that made kernel
checking take over 60 seconds; no shared definition was changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.finiteClopenTailSiteTransport`
(node `lem-cbc-finite-clopen-tail-site-transport`). No holes added or split off; no sorry remains
in the delivered module. The completed module passed its single-file compile in 21.8 seconds. Debug profiling options
were then removed; the delivery checks compile the final file and inspect its axioms.
The argument uses the existing declared comparison-coherence results,
not the higher proper-mate normalization conclusion. It also covers empty components and the
zero ring, since it uses adjunction injectivity and has no nonemptiness hypotheses.

## No longer needed

No original imports, nodes or modules are withdrawn. All three original proof dependencies
remain used: clopen geometry/projection, inverse-image comparison coherence, and extension by
zero comparison coherence. No derived localization or cartesian base-change compatibility
lemma is needed for this tail calculation. The exploratory tensor-comparison proof import is
removed in favor of `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`; no tensor
coherence theorem is used.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The disjoint-open projector step admits a direct
adjunction proof: maps into clopen extension by zero are detected by restriction after
identifying extension by zero with direct image. This closes that step without another split.
The unit and chapter routes are unchanged. No existing shared interface was changed.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
