## What changed

Proved `WeilConjectures.isomorphismQuotientRoosComparison` in
`Sheaf.TraceFormula.IsomorphismQuotientRoosComparison`, preserving its statement,
universes and public imports. Added one proof-only import,
`Sheaf.Paper.PodReindexingRoosComparison`.

Four proved private helpers construct the module inverse-image equivalence,
prove the difference square for arbitrary additive functors, assemble the
existing projection-normalized Roos comparison into a natural isomorphism,
and restate its second projection at arbitrary matching degrees.
The theorem specializes and whiskers that isomorphism to the actual quotient
tower. Both required projection equations come from its existing coordinate API.
Local transparency attributes keep the quotient tower abstract during the proof;
no shared definition or exported instance changes. The node now records this route.
The remote single-file compile passed without warnings in 32.0 seconds.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.isomorphismQuotientRoosComparison`
(`lem-trf-isomorphism-quotient-roos-comparison`).
Added zero holes. Zero `sorry` remain in the delivered Lean module.
All four private helpers are proved. No split-off modules or statements.

## No longer needed

No original import was removed; the public strict-model import supplies the
statement's definitions. The only added import is used by the proof.

The direct proof dependencies
`lem-cbc-exact-product-functor-strict-limit`
(`Sheaf.Paper.ExactProductFunctorStrictLimit`),
`lem-weil-strict-roos-comparison`
(`Sheaf.CategoryTheory.StrictRoosComparison`), and
`lem-weil-proetale-countable-products-exact`
(`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`)
are not needed for this strict chain-level assertion. Equivalences preserve
products, and the existing general additive-equivalence comparison already has
the required cocone coordinates and naturality. Their edges were removed from
this node. These modules may remain in transitive public imports or be needed
elsewhere; this delivery does not withdraw them or claim global closure pruning.

## Where the brief, the DAG or earlier work was wrong

The original plan identifies the strict comparison with a canonical derived-limit
comparison, including a signed-coordinate normalization. The actual Lean statement
requires only the strict natural isomorphism and its two coordinate formulas, so
that extra argument is unnecessary. The more general result already exists as
`podReindexingRoosComparison`, `podReindexingRoosNaturality`, and
`podReindexingRoosCoordinates`. The original module exactness proof constructs the
module equivalence internally without exposing it; the local helper preserves
that construction without editing its shared module.

The recorded unit route is unchanged, and no target or statement was altered.
The rework row's Lean attachment and all required model definitions are preserved.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
