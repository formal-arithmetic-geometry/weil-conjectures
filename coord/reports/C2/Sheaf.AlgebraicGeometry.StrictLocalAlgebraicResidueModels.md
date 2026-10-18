## What changed

Proved `AlgebraicGeometry.Scheme.exists_strictLocal_algebraicResidue_models` without changing
its public signature. No existing definition or statement was changed, and no consumer
needs adaptation.

The models are spectra of the actual subalgebras `L[image(E_i → B)]`, indexed by the original
filtered category of étale stages. The proof establishes finite generation over L, exhaustivity,
the ring-colimit universal property, the limit in `Over U`, nonemptiness, the K-scalar square,
affine transitions, and compatibility with the canonical strict-local structural map.

Four new intermediate theorems are all proved. The rational-chart construction lifts a finite
transcendence basis to affine functions. Nonzero polynomials have nonzero residue, so their
images are units in the strict-local ring; localization embeds the rational function field.
The coefficient-chart construction takes its relative separable closure in the strict-local
residue field and lifts that separable extension through henselianity. Its algebra map gives
both scalar identities, and the transcendence-degree tower gives the required degree.
The coefficient-presentation theorem constructs a small filtered diagram in the under-category
from the existing affine-chart ind-étale theorem.

The residue-algebraicity theorem works at every model prime, including primes with no preimage
in Spec B. The shared domain embeds in the contracted residue field, its fraction field extends
there, and the coefficient-field images are algebraic. Adjoin induction and fractions give the
whole residue extension. The proof transports ideal residue fields to scheme residue fields
and composes this extension with the étale residue extension.

Every object is constructed inside a proof of existence. No definition chooses an arbitrary
witness from an unproved existence statement.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.Scheme.exists_strictLocal_algebraicResidue_models`.

Added holes: zero. Sorries left in the delivery: zero.

The following new declarations and all their private helpers are proved:

- `AlgebraicGeometry.Scheme.exists_strictLocal_rational_chart`
- `AlgebraicGeometry.Scheme.exists_strictLocal_coefficient_chart`
- `AlgebraicGeometry.Scheme.exists_strictLocal_coefficient_presentation`
- `AlgebraicGeometry.Scheme.coefficientImage_residue_algebraic`

These proofs use the existing named dependency declarations, as stage 3 requires. This is
one original hole closed with no lower holes added; it does not assert that every pre-existing
dependency in the targets' closure is already axiom-free.

Validation: each component has compiled through the prescribed remote compiler. The final set
is compiled in import order, and the delivery dry run checks declarations and axioms before push.

## No longer needed

Removed direct proof imports from the item module:

- `Sheaf.RingTheory.StrictHenselizationTriples`
- `Sheaf.Paper.StrictHenselizationFunctoriality`
- `WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples`
- `Sheaf.AlgebraicGeometry.StrictHenselization`
- `Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift`

The strict-local structural facts and étale presentation are obtained through the smaller
interfaces used by the new intermediate proofs. The closed-lift lemma is not needed.
No whole original dependency node is declared obsolete: the complete proof still uses the
original field and strict-local inputs, affine étale criterion, elementwise colimit
representatives, spectrum limits, affine maps and étale residue algebraicity.

The compatible-triple category, finite-presentation lifting and eventual-equality calculations,
and tensor-product models of the old plan are unnecessary. Using image subalgebras makes all
transition maps inclusions, so injectivity gives eventual equality directly. No second
coefficient-field diagram is needed. The existing unit route is preserved.

Unused direct proof imports were removed from the new modules too; in particular the rational
chart does not import the algebraic-independence adjoin-field equivalence, and the coefficient
presentation does not need a separate filtered-colimit import.

## Where the brief, the DAG or earlier work was wrong

The old plan is mathematically valid but longer than needed for this statement. It constructs
compatible tensor-product models even though no dimension or quasi-finiteness requirement
forces that choice here. Enlarging the images of the full étale stages retains residue
control and gives a direct colimit proof.

No existing statement was disputed or weakened. Edge cases checked include zero transcendence
degree, noninjective maps E_i → B, nonreduced chart rings, arbitrary filtered categories rather
than directed posets, and model primes with no preimage in Spec B. The empty transcendence
basis uses the polynomial ring on no variables. There are no forced adaptations or definition
repairs.

## New nodes

`lem-kun-strict-local-rational-chart` is proved. It constructs a polynomial domain chart and
embeds its fraction field in the strict-local ring, with both canonical scalar identities
and the residue transcendence degree.

`lem-kun-strict-local-coefficient-chart` is proved from that rational chart, strict henselianity,
and the existing henselian-colimit lifting theorem. It constructs the separably closed
coefficient field and proves its scalar equations and transcendence degree.

`lem-kun-strict-local-coefficient-presentation` is proved from that chart and the existing
`lem-weil-pbc-strict-henselization-affine-chart-ind-etale`. It constructs the small filtered
étale presentation under the affine coordinate ring.

`lem-kun-coefficient-image-residue-algebraic` is proved. It handles the ring-theoretic residue
argument and its transport to affine schemes independently of strict henselizations.

All four nodes lie in the item's chapter and unit and point to the same blueprint ancestor.
The item's node records the image-subalgebra route. There is no change record because all
existing public signatures and definitions are unchanged, and the new interfaces have their
own nodes.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
