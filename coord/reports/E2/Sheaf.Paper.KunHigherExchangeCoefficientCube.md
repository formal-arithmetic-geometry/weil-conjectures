## What changed

Proved `AlgebraicGeometry.Etale.abelianHigherExchange_coefficient_cube` in
`Sheaf.Paper.KunHigherExchangeCoefficientCube`. The theorem signature and the complete
`abelianHigherExchange` definition are unchanged. No other module is changed.

The proof derives the derived cube identity from the two horizontal pasting identities
in `WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal`, inserts the
arbitrary coefficient morphism by naturality, and applies cohomology. The private
cube-pasting calculation reuses the proved argument in
`WeilConjectures.AlgebraicGeometry.AbelianExchangeCubeComparisons`; importing that
whole module would pull in unrelated declarations. Additional proved private helpers
establish composition and square compatibility for exact inverse-image/cohomology
and inverse-image/single-complex comparisons. New proof imports are private.
The DAG proof records this route. No statement, definition, or new node is introduced.
Import and command-context changes are recorded in
`coord/changes/E2-higher-exchange-proof-context.md`; the downstream tool reports
zero existing importers, so there are no consumers to adapt.

## Proved and sorry left

Closed one of one holes:
`AlgebraicGeometry.Etale.abelianHigherExchange_coefficient_cube`
(node `lem-kun-higher-exchange-coefficient-cube`).
There are zero `sorry` left in the assigned module, zero holes added elsewhere,
and zero split-off statements. Every private helper is proved.
The complete module compiled cleanly through `lcompile.py` in 51.3 and 53.3 seconds.
The delivery dry run passed at `5f9ac4cb8c`. Later compiles sometimes exceeded the
60-second limit. Profiling showed costs in kernel conversion of the derived
inverse-image/single-complex comparisons; alternative explicit rewrites and generic
cancellation calculations did not improve this reliably. Those experiments were
removed, preserving the packet that passed the full dry run.
The axiom audit retains `sorryAx` through existing imported dependencies; no new
axiom or hole is introduced by this packet. This delivery closes the local hole,
not every transitive dependency of the target.

## No longer needed

Removed imports `Sheaf.Paper.KunBcMapOnCohomology`,
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`, and
`Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`.
The proof does not import `Sheaf.SecSmoothPurity.DerivedExchangeCube`: the needed
cube identity is proved from horizontal pasting, so `lem-kun-derived-exchange-cube`
is removed from the proof dependencies. Neither the source cube-comparisons module
nor its unrelated consumers are imported.

The proof does not use `lem-kun-bc-map-on-cohomology`,
`def-weil-pbc-derived-exchange`, or `def-weil-pbc-derived-square-iso` as proof lemmas.
Their resolution/cartesian-mate identification is unnecessary because the displayed
higher exchange is defined directly from the commutative derived mate. The cartesian
square type and all statement dependencies are preserved. These pruning statements
concern this proof; they do not claim that other consumers are absent globally.
No unit-level statement or proof step is bypassed, and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original last proof step planned a separate resolution-model identification
that the Lean statement does not require. The derived cube dependency is an old
non-module file; an attempted header adaptation was rejected as not forced and
has been removed completely from this packet. Direct horizontal pasting supplies
the needed identity without changing that dependency or relying on its hole.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
