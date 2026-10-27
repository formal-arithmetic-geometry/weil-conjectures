## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleRingPullback_openSupport` without changing its
statement or any public import. The only added proof import is
`Sheaf.AlgebraicGeometry.RingedOrdinaryOpenExchange`.

A proved private helper completes an isomorphism triangle across an equality of indices.
Applied to the inverse-image coefficient rings, it supplies the missing comparison along
`a`, with exactly the coherence needed by `StrictTowerRingedSquare`. The existing proved
`ordinary_open_isIso` then identifies the right adjoints. Composite adjunctions and
`leftAdjointUniq` give the actual essential-image witness.

Validation: the final file compiled through `lcompile.py` in 3.6 seconds, exit 0,
with no warnings.

Updated the item's DAG proof and dependencies to this argument. No other existing module,
statement, definition, instance, or public interface changed. The unit route stays intact.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.proEtaleRingPullback_openSupport`
(`lem-sf-ringed-pullback-ordinary-open-support`).

Holes closed: 1. Holes added: 0. Remaining holes in this delivery: none.
No split-off statements or new modules.

## No longer needed

No original import was removed: `Sheaf.Paper.ProjectionCompactification` remains necessary
for the statement. The previous direct proof dependencies
`lem-sp-proetale-open-slice-presentation`
(`Sheaf.AlgebraicGeometry.ProEtaleOpenSlicePresentation`),
`lem-sfb-proetale-open-restriction-counit`
(`Sheaf.AlgebraicGeometry.ProEtaleOpenRestrictionCounit`), and
`lem-weil-pbc-site-morphism-composition`
(`Sheaf.CategoryTheory.SiteMorphismComposition`) are not separately invoked or imported
by this proof. The existing arbitrary-ring ordinary exchange theorem packages that
calculation. This does not withdraw those modules: they retain other consumers, and
some remain transitive dependencies of ordinary exchange. No library module is pruned.

## Where the brief, the DAG or earlier work was wrong

The original plan is valid, but overlooks the already proved arbitrary-coefficient
`RingedRestrictionExchange.ordinary_open_isIso`. Its coherence hypothesis can be satisfied
by completing the missing coefficient isomorphism, rather than by separately rebuilding
and transporting the sectionwise comparison. Empty and identity opens, and zero rings,
need no extra hypotheses. No statement repair is necessary.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
