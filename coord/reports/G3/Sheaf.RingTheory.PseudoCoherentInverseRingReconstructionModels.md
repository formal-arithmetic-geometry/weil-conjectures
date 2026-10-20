## What changed

Completed `DerivedCategory.reconstruction_models` without changing its statement.
The proof normalizes the supplied derived adjunctions by their universal property,
transports marked lifting along a quotient-ring isomorphism, and constructs the
entire marked complex tower recursively. Compatible finite bases identify the
explicit complex of compatible tuples with finite free modules degreewise.
The surjective tower triangle and a comparison of distinguished triangles give
the projection-respecting marking of the limit. The normalized counit on the
bounded-above free model proves every ordinary/derived scalar-extension equation.

Added proof imports cover universal module scalar-extension resolutions, derived
adjunctions, finite bases, the Orzech property, complex limits and sequence functors.
All added helpers are private and proved. The limit complex, differential and
projections are explicit constructions. No arbitrary object is selected from an
unproved mere-existence statement. The existing DAG node records this proof route.
The command-change record is
`coord/changes/g3-reconstruction-models-proof-commands.md`; it documents the added
file-local elaboration commands and the three unchanged downstream consumers.

## Proved and sorry left

Closed: the single original hole in `DerivedCategory.reconstruction_models`
(node `lem-weil-pbc-pseudocoherent-inverse-ring-reconstruction-models`).
Added: zero holes. Split off: zero. Remaining holes in the delivered module: zero.

The complete module compiles with zero `sorry` tokens and no warnings. Its public
theorem statement is textually identical to the shared source. The required
`deliver3.py --no-push` run passed compilation, the axiom probe and server preflight
(review class CODEX, dry-run commit `6458858a774`).

## No longer needed

Removed the unused `Mathlib.Algebra.Homology.DerivedCategory.KProjective` import
and the proof imports
`Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`,
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`, and
`Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`.
The one-object ringed-site route of
`lem-pur-sheaf-ring-derived-coefficient-adjunction` and the direct use of
`lem-pur-derived-change-of-rings` are unnecessary: the universal derived module
scalar-extension pair and uniqueness of left adjoints normalize the given
adjunctions directly. These two nodes are removed from the item's proof dependencies.
The existing public import of `Sheaf.Algebra.Homology.DerivedChangeOfRings`
is preserved; it also remains a dependency of marked lifting. No module is withdrawn,
and no claim is made that these dependencies are unused elsewhere in the project.

## Where the brief, the DAG or earlier work was wrong

The previous import-loading conflict has cleared in the published build.
The stated surjective-tower theorem fixes the standard derived-category universe,
whereas this item's statement permits an arbitrary supplied derived category.
Its kernel/one-minus-shift proof is reused privately at the supplied universe,
using the same module-product helpers and countable-product theorem.
For the compatible basis argument, nilpotent Nakayama and the Orzech property
replace the matrix inverse construction; this includes zero rings and empty bases.
No target, definition, existing signature, or consumer was changed.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
