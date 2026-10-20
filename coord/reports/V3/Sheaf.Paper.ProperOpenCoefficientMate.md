## What changed

Proved `AlgebraicGeometry.Etale.properOpen_coefficient_mate` from the
normalized proper/open exchange, the canonical open scalar-unit equations and
`openRestriction_scalar_exchange`. The latter is a new, fully proved theorem in
`Sheaf.Paper.OpenRestrictionScalarExchange`, for an arbitrary commutative square
with open horizontal maps. It identifies the prescribed coefficient maps, rather
than choosing new ones. Its proof descends the restriction-of-scalars cube through
exact localization, takes scalar mates, proves the exact-adjunction counit formula
for `finiteCoefficientDirectImageMap`, and applies the existing proved
`CategoryTheory.Adjunction.coefficient_exchange_of_counit`.

Extracted `properOpenInterchange_normalization` with a uniqueness proof, and
changed the existing choice definition to use this small interface. The old
large existential projection caused a 60-second timeout even before the new
coefficient proof. The same normalization uniquely determines the same map;
no statement or target signature changes. Adapted the sole direct downstream
user in `Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange`.
The change record is `coord/changes/V3-proper-open-normalization.md`.

Added one private proof import in the item. Existing public imports and declaration
signatures are preserved. No WeilConjectures module is edited.
The new module caches exact inverse-image functors and their structural instances
in a private abbreviation, and expresses its proof goal through that abbreviation
before applying the mate calculation. This avoids repeatedly unfolding the large
chosen constructions while checking the final equation.

Validation: `lcompile.py --all` compiled all three delivery modules in import order,
without errors or warnings: OpenRestrictionScalarExchange (47.3 seconds),
ProperOpenCoefficientMate (25.4 seconds), and EtaleOriginProperOpenInterchange
(17.0 seconds). All three source files contain zero `sorry`s. The new node's Lean
statement matches its declaration verbatim, and both nodes' `proof_deps` match
the union of their proof-step dependencies.

## Proved and sorry left

Closed the item's sole original hole:
`AlgebraicGeometry.Etale.properOpen_coefficient_mate`
(node `lem-sp-proper-open-coefficient-mate`).

Added zero holes. The new public theorem
`AlgebraicGeometry.Etale.openRestriction_scalar_exchange`
(node `lem-sp-open-restriction-scalar-exchange`), the normalization uniqueness
lemma, and all private helpers are proved. There are no retained `sorry`s in any
delivered module. This is one hole proved, not a decomposition. Existing imported
statements remain dependencies; their proofs are not replaced or weakened.

## No longer needed

No existing import is removed. The item's coefficient proof no longer directly invokes
`lem-weil-pbc-mate-pasting` or the general ringed-topos tensor/pullback theorem;
its DAG proof edges now use the explicit scalar/open exchange lemma and elementary
adjunction cancellation. The tensor/pullback node remains a statement dependency
and is still needed below the existing scalar interfaces. No whole module or
blueprint-unit step is withdrawn or pruned.

## Where the brief, the DAG or earlier work was wrong

The existing coefficient proof plan needed an explicit normalization comparison:
the open scalar/restriction comparison is defined using the open restriction
functor, whereas the scalar comparison for a general map is defined using the
geometric adjunction. The new proof identifies these maps by the site triangle
identity and then by exact localization. It also transports the finite-coefficient
counit equation from left-derived inverse image to the exact derived adjunction.
A generic invocation of mate pasting alone does not provide these identifications.
The original statement is unchanged and needs no flatness assumption. Identity
maps, the zero ring, and empty schemes introduce no extra hypothesis: the proof
uses adjunction identities and localization, and never cancels a coefficient
pushforward map.

## New nodes

`lem-sp-open-restriction-scalar-exchange`, attached to
`Sheaf.Paper.OpenRestrictionScalarExchange`, is a fully proved, strictly simpler
part of the coefficient argument. It concerns restriction/exchange on arbitrary
unbounded objects and commutative squares, before extension by zero or proper/open
interchange enters. Its statement has no cartesianness, properness, finiteness,
flatness or lower-bound assumptions. The existing node is updated to reflect its
use. The unit route is retained. Change record:
`coord/changes/V3-proper-open-normalization.md`.

## Forced adaptations

`Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange` was unclaimed. Its
original proof failed at line 237, rewriting with `hg`, because the pattern
`(unboundedProperOpenInterchange ...).choose_spec.choose ...` was no longer the
head of the changed definition. Only the obtain expression at original lines
232–234 is changed to obtain the same restriction isomorphism and the same two
normalization equations from `properOpenInterchange_normalization`. Public
signatures and all subsequent proof steps are preserved.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
