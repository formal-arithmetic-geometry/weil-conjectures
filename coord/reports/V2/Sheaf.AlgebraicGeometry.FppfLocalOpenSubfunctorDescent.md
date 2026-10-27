## What changed

Proved `AlgebraicGeometry.fppf_local_open_subfunctor_descent` with its existing signature.
All helpers are proved private theorems in the item module. The proof evaluates the
chart pullback, establishes compatibility, applies the existing fpqc descent of opens,
and glues sections of G using injectivity and the two sheaf conditions. A pointwise
factorization criterion constructs the representing pullback isomorphism. The same
criterion proves independence and base change. No definitions or consumer interfaces change.
The node route records the direct Mathlib proof that fppf coverings are fpqc.

## Proved and sorry left

Closed: `AlgebraicGeometry.fppf_local_open_subfunctor_descent`
(node `lem-trf-fppf-local-open-subfunctor-descent`), 1 of 1 original holes.
Holes added: none. Holes left in delivered Lean: none. Split off: none.
The proof imports the existing, proved `AlgebraicGeometry.openSubscheme_existsUnique_of_fpqc`.

## No longer needed

Removed proof imports `Sheaf.CategoryTheory.SiteCoveringAxioms` and
`Sheaf.AlgebraicGeometry.FppfAffineRefinement`.
The custom `Precoverage.IsSiteForCoverings` is not used: the argument uses the actual
Mathlib fppf topology, its stable precoverage, and sheaf conditions directly.
Removed proof dependency and tool approval `lem-pc-fppf-affine-refinement`:
`Scheme.fppfPrecoverage_le_fpqcPrecoverage` supplies its entire role.
Removed proof dependency `lem-weil-pbc-open-immersion-base-change`: inverse-image opens
and the open-factorization universal property suffice; pullbacks of covering arrows
are supplied by the fppf precoverage's base-change axiom.
No modules are withdrawn; these facts can still have other consumers.
The existing public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

The planned affine-refinement argument is unnecessary because Mathlib already states
fppf implies fpqc. The plan otherwise gives the argument implemented here.
Edge cases require no inhabited index types: the empty base and empty cover are covered
by sheaf gluing and joint surjectivity, as are W empty and W all of U. No injectivity of
q or representability of F or G is used.

Validation: after removing unused proof imports the full module compiled without errors
or warnings (12.2 seconds). `#print axioms` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`.
The original public theorem signature was compared verbatim and is unchanged.
All Lean lines have at most 100 characters; every private helper has a complete proof.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
