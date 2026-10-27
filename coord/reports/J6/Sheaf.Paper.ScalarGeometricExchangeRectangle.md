## What changed

Repaired the return at head 9643e6768: removed the duplicate private
`eqToIso_symm_congr` theorem. `reverse_compositor` now applies the existing
`scalarSquare_eqToIso_symm` from `ScalarPullbackSquareCoherence`, accessed through
a private `import all`; the original public import is retained.

Proved the categorical mate rectangle by transposing under the final adjunction,
using the four counit identities and naturality. Proved its compatibility with
section realization: a general mate transport calculation carries rho and ambient
exchange to their specified section mates, and naturality identifies both full
routes through the fixed source and target isomorphisms. Every original public
signature and original public import is preserved. The data body of
`scalarAmbientExchange` now constructs the same mate through the typed aliases
`adj` and `scalarPullbackSquare`, avoiding kernel conversion through the enormous
concrete derived adjunction. The change record records its two downstream
importers (neither uses this definition), and its defining data module is public.
The forward map of `scalarSectionPushComparison` is also presented as its typed
mate; the proved `scalarSectionPushMate_eq` identifies it with the unchanged
canonical comparison. Its inverse and inverse laws use the existing isomorphism.
The separate change record identifies both downstream users; no adaptation is needed.

Added three modules. `NormalizedScalarSectionFamily` is proved: apply the existing
internal scalar/pullback normalization theorem at identity maps, choose the
normalized scalar comparisons pointwise, and apply endpoint transport on each
edge. `SectionPullNormalizationTransport` isolates independence of normalized
endpoint scalar models. `ScalarPullbackSquareCoherence` isolates the normalized
pullback-compositor square before taking geometric mates. Its real definition
`scalarPullbackSquare` exposes the existing canonical geometric comparison and
is irreducible to keep the derived compositor construction out of unification.
A proved `sectionRectangleLambda_witness` extracts the same uniquely determined
realization comparison once; its definition then chooses from that normalized
existence statement. The associated change record checks both downstream importers.
The main module uses the geometric normalization module's existing linter settings
(`linter.all false` and `linter.unusedVariables false`): profiling identified
unused-variable linting spending about 34 seconds unfolding derived interfaces.
The route definitions use the generic `mateRouteLeft` and `mateRouteRight`
word constructors, preserving the exact three-factor composites while keeping
endpoint types abstract during kernel checking. Separate change records record
that neither downstream importer mentions the internal or section route definitions.
The realization calculations accept the full natural transformations defining
each route, so naturality is proved with abstract endpoints before specialization.
Abstract `compositionCoherence_eq` proves equality transport by substitution
before specialization to concrete derived categories. `squareCoherence` and
`compositionCoherence` keep the corresponding equations abstract during checking.
Private typed wrappers similarly normalize the imported geometric realization
interfaces once before using the categorical calculations.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.ProEtale.QuotientChange.scalar_geometric_exchange_rectangle`
(`lem-sfb-scalar-geometric-exchange-rectangle`).

New proved theorems:

`AlgebraicGeometry.ProEtale.QuotientChange.scalarSectionPushMate_eq` and
`AlgebraicGeometry.ProEtale.QuotientChange.sectionRectangleLambda_witness`
(both owned by the existing item node).

`AlgebraicGeometry.ProEtale.QuotientChange.normalized_scalar_section_family`
(`lem-sfb-normalized-scalar-section-family`).

Two new holes remain, each the entire proof of its named theorem:

- `AlgebraicGeometry.ProEtale.QuotientChange.section_pull_normalized_of_normalized`
  (`lem-sfb-section-pull-normalization-transport`).
- `AlgebraicGeometry.ProEtale.QuotientChange.scalar_pullback_square_coherence`
  (`lem-sfb-scalar-pullback-square-coherence`).

This is a decomposition: one original hole closed, two lower holes added, hence
net holes closed minus added is -1. Neither remaining statement concerns a
pushforward, geometric exchange, mate rectangle, or its realized routes. Both
are strictly the pullback normalization steps of the argument. No definition
contains a sorry and no original signature changes.

## No longer needed

The duplicate helper `eqToIso_symm_congr` is removed; its proof is supplied by
`scalarSquare_eqToIso_symm` in the already-required coherence module.

Removed the main module's direct proof imports of
`Sheaf.Paper.KFlatScalarComparisonNormalization` and
`Sheaf.CategoryTheory.InternalSectionScalarAdjunction`: the main calculation now
uses the two named normalization results. Those dependencies, and the coefficient
cocycle `lem-sfb-eta-comp`, remain needed transitively by the normalization lemmas;
no transitive module or dependency is claimed pruned. The geometric normalization
module's proved `derivedMate` and `derivedPullComp` helpers are used through a
private `import all`. Its public normalization theorem is not treated as an
additional axiom.

## Where the brief, the DAG or earlier work was wrong

The returned packet proved the equality-transport symmetry helper twice under
different private names. The repair reuses the coherence module's helper instead.

The existing internal scalar/pullback normalization theorem supplies endpoint
comparisons for one edge and an existentially chosen internal balancing map.
It does not directly supply section normalization for an arbitrary given
normalized b using already fixed endpoint comparisons. Identity instances do
supply the pointwise normalized scalar family; that part is now proved in Lean.
The endpoint-independence argument is isolated as its separate transport lemma.

The K-flat scalar composition law concerns independently constructed ringed
inverse-image models. Relating it to the concrete internal pullback compositors
and arbitrary supplied normalized family requires the square-coherence argument
isolated in the second remaining lemma. No existing statement is claimed false,
and the blueprint unit route is preserved.

## New nodes

`lem-sfb-normalized-scalar-section-family` records the proved simultaneous-family
construction from identity normalization and endpoint transport.

`lem-sfb-section-pull-normalization-transport` records the separate one-edge
normalization transport. Its proof in words constructs the ordinary identity
restriction square, takes its normalized scalar/geometric conjugate, descends
on flat-term K-flat resolutions, and compares computation counits.

`lem-sfb-scalar-pullback-square-coherence` records the scalar/pullback compositor
square before transposition. Its source is the original proof step 2: inverted
K-flat scalar composition, the coefficient cocycle, and resolution descent.

`def-sfb-scalar-pullback-square-data` owns the real typed alias of the existing
canonical geometric compositor and pullback square used by the coherence statement. They make
no new comparison choice.

Change records: `coord/changes/scalarAmbientExchange-typed-mate.md` and
`coord/changes/scalarSectionPushComparison-typed-mate.md` and
`coord/changes/sectionRectangleLambda-witness-api.md` and
`coord/changes/scalarExchangeRoutes-word-api.md` and
`coord/changes/sectionRectangleRoutes-word-api.md`.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
