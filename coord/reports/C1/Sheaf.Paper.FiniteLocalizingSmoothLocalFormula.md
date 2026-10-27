## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.localizingExceptionalAdjoint_smoothLocalFormula`
in `Sheaf.Paper.FiniteLocalizingSmoothLocalFormula`, preserving its statement and public imports.
Added proved private helpers for the coefficient pullback comparison, ordinary finiteness
adjunction, over-site trivializations, and natural local smooth formula. The specified
localizing right adjoint is identified using the existing generator-preservation argument
and uniqueness of right adjoints. A fiber-product common refinement trivializes both the
smooth dualizing line and the actual Tate line; the ordinary formula is transported back
through the coefficient equivalences. Updated the existing node's proof route and dependencies.
No public statement, definition, unit route, or adopted source-library file changed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.localizingExceptionalAdjoint_smoothLocalFormula`
(node `lem-sf-finite-localizing-smooth-local-formula`). Added zero holes; split off zero
statements. Every private helper has a complete proof. There are zero `sorry`s left in
the delivered module. Existing imported obligations remain the library's own dependencies.

## No longer needed

Removed the proof imports `Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalTransport`
and `Sheaf.CategoryTheory.LocalizingHomTest`.

The proof does not use `lem-sf-etale-proetale-exceptional-transport`
(`Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalTransport`): the existing ordinary
finite-coefficient finiteness adjunction and uniqueness of right adjoints supply the comparison.
It does not use `lem-weil-pbc-finite-ring-constructible-derived-origin`
(`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`): the ordinary constructible finite-Tor
API already supplies bounded etale origin. It does not use the planned
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: the proof uses the established ordinary
monoidal derived pullback and the exact etale/pro-etale pullback square instead.
The separately planned `lem-sf-localizing-hom-test` declaration is not invoked; the proved
private generator-preservation argument in `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer`
provides the localizing comparison. These are removals from this node's proof dependencies,
not requests to withdraw modules still needed by other consumers. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The statement is unchanged and no false assertion was found. The planned comparison was
more general than necessary: the existing ordinary finite-coefficient small adjunction and
its generator argument suffice. The updated node records the actual route. The common
cover is explicitly constructed, and the result is a natural isomorphism of functors,
not merely an objectwise assertion. No forced adaptations or new nodes were needed.

Compilation diagnostics exposed expensive equality checks between the continuous
coefficient ring and the normalized encoding abbreviation. The private comparison
helpers consistently use the encoding API abbreviation. Proved private categorical
transport and reassociation helpers keep the final functor composition abstract. The adjoint
hypothesis is locally normalized and the final conversion unfolds only the recorded local
abbreviations. The complete module compiled cleanly in 39.6 seconds; no file was split,
no public definition changed, and the single-file time limit remains unchanged.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
