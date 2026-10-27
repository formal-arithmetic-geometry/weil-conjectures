## What changed

Filled `WeilConjectures.realization_restriction_normalizations` from the existing
localized-push datum, its specified transpose formula, the ring-sheaf-change Hom
formula, and the ordinary scalar-pull unit equation. The integral coefficient
isomorphism is identified by its hom; the rational one is identified via the sheaf
adjunction and its normalized values on continuous functions. Thus the push datum
uses the supplied pull datum's actual coefficient maps.

Added `Sheaf.Paper.RealizationOrdinaryPullScalarUnit`, proving the ordinary ambient
unbounded unit equation before completion. Its module calculation is exactly the
supplied `module_unit`; its derived calculation uses `complex_terms`,
`derived_normalization`, both supplied scalar-unit formulas, and invertible
computation maps. Private helpers identify the ordinary left-adjoint uniqueness
map with its homotopy and derived computation maps. Generic diagram lemmas handle
naturality and cancellation without unfolding concrete sheaf functors. The quotient
identifications and the combined diagram are likewise proved over abstract
categories before specializing to the actual sheaf functors. Local
irreducibility settings and private definitions for the two canonical coordinate
isomorphisms keep the proof behind these computation interfaces. The natural-
transformation calculation is packaged with `as_aux_lemma` to avoid repeatedly
checking its local coordinate definitions.
The existing assigned theorem, auxiliary definitions, and target statements retain
their signatures and bodies
apart from the theorem proof. All additional imports are proof imports.

## Proved and sorry left

Original holes closed: `WeilConjectures.realization_restriction_normalizations`
(1 of 1). Added holes: none. The new theorem
`WeilConjectures.realizationOrdinaryPull_scalarUnit` is also proved; it does not
move the original hole into a new theorem. Every private helper is proved.
The delivery has zero literal `sorry`s. Existing imported unfinished theorems,
including `realization_localized_push`, remain dependencies as stage 3 intends.

## No longer needed

No modules are withdrawn. No source-library declaration is removed or weakened.
The proposed proof import `Sheaf.SixFunctors.ExactLocalizationInverseMate` was
removed; a private generic square calculation needs only the exact-functor API.
The parent proof no longer directly uses
`lem-weil-pbc-localization-inverse-image-coherence`,
`lem-weil-pbc-continuous-coefficients-immersion-restriction`, or
`lem-weil-pbc-realization-coefficient-square`: the supplied arrow already contains
the normalized comparison and coefficient square. The first equation is proved
from its concrete module-unit and complex-computation fields instead. These nodes
remain statement dependencies or dependencies of the supplied data, so no claim
is made that their modules disappear from the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The plan's application of abstract localization coherence requires a substantial
identification with the supplied concrete ordinary comparison; it is not a direct
one-line invocation. The new proof supplies this identification using the
normalized module and complex data, without a new mathematical hypothesis.
The ambient counit argument uses the adjunction right triangle identity to identify
the rational adjunct with the identity and left-adjoint uniqueness to transport
the integral counit. No boundedness or constructibility of the restricted rational
object is used.

Edge cases checked: zero objects and complexes, identity morphisms, empty schemes,
torsion objects with zero rationalization, and arbitrary unbounded complexes.
No scalar-unit injectivity or nonempty scheme assumption enters the proof.

## New nodes

`lem-weil-pbc-realization-ordinary-pull-scalar-unit` records the strictly separate
ordinary pull-unit compatibility, proved in its own module. It serves step 2 of the
assigned node; its own proof combines the module tensor-unit calculation,
compatibility of canonical adjunction coordinates with derived computation, and
localization from complexes. The unit's finite-extension proper-base-change route
is preserved. The generic cochain square factorization is proved privately from
three exact-functor factorization formulas. The proposed private import
`Sheaf.Paper.CompletedTowerPullback` was also removed; the universal adjunction API
suffices. The generic square calculation follows the existing private
`square_fac` proof from `Sheaf.SixFunctors.ExactLocalizationInverseMate`, while
avoiding that module’s unrelated six-functor and open-immersion dependencies. No off-unit theorem or alternate proper-base-change
route is used. No definition or statement change record is required.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
