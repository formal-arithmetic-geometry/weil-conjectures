## What changed

Proved `Algebra.conormal_generators_global_complete_intersection` in
`Sheaf.RingTheory.ConormalGeneratorsGlobalCompleteIntersection` with its signature unchanged.
Added private proof imports of `WeilConjectures.RingTheory.LocalizedIdealConormalGeneratorBound`,
`WeilConjectures.RingTheory.LocalCompleteIntersectionPresentation`, and
`WeilConjectures.RingTheory.PrincipalNeighborhoodDimension`. The existing polynomial-quotient
height-difference import is used. All public imports are unchanged.

The proof obtains d and its bound from the height formula, applies the existing conormal
spanFinrank bound, explicitly enumerates a minimal generating finset and pads with zeros,
and uses the existing local-generator presentation theorem. The principal-neighborhood
lemma gives a further localization of dimension d, so its presentation with n+1 variables
and n-d+1 equations satisfies the definition of global complete intersection.
Updated the item's proof docstring and DAG proof, proof_deps and proof_origin accordingly.
No definitions, other modules or public interfaces changed. The unit route is unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
`Algebra.conormal_generators_global_complete_intersection`
(blueprint: `lem-weil-pbc-lci-conormal-generators-global-complete-intersection`).
Holes added: 0. Holes left in the delivery: 0. Split off: 0.
The module compiled without warnings through lcompile.py; the final import set compiled
in 6.6 seconds. The argument covers empty local generating sets and n-d=0 by its explicit
zero-padding construction; it assumes no positivity or nonzero generator.

## No longer needed

No existing imports removed and no modules withdrawn. A trial explicit
`Mathlib.RingTheory.Polynomial.Basic` proof import was removed after compilation showed
it is already available through the existing imports.

The direct proof dependencies `lem-weil-pbc-local-generators-clearing`,
`lem-weil-pbc-quotient-away-clearing`, and `new-equation-count-localize-presentation`
are now carried by the already proved
`lem-weil-pbc-lci-regular-sequence-global-complete-intersection-presentation`
(`WeilConjectures.RingTheory.LocalCompleteIntersectionPresentation`). They remain
transitive dependencies, so none is claimed as a pruned module.

`lem-weil-pbc-polynomial-ring-field-regular-ring` is unnecessary for this proof:
only Noetherianity is used, supplied by Mathlib's `MvPolynomial.isNoetherianRing`.
The DAG now records the Noetherian definition and omits the stronger regular-ring node.
No regular local ring or regular sequence result is needed.

## Where the brief, the DAG or earlier work was wrong

The existing eight-step Lean docstring predated the reviewed six-step DAG plan.
Both describe a valid argument, but the already proved local-generator presentation
lemma combines the clearing, quotient comparison and inverse-variable steps exactly.
Using it avoids duplicating those proofs. The mathematical statement and the source
argument (Stacks 00SC, implication (3) implies (1)) were correct; no statement repair
or new node was needed.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
