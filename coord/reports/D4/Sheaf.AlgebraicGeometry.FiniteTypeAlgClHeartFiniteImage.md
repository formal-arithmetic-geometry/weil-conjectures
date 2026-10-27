## What changed

Implemented `AlgebraicGeometry.ProEtale.CondensedRing.finiteTypeAlgClHeart_finiteImage`
from the existing constructible sheaf finite-coefficient descent theorem and the
bounded-below algebraic-closure/direct-image comparison. The source is Noetherian;
the morphism is qcqs. Flat extension commutes with the degree-zero single functor.
The proof composes the canonical direct-image comparison with direct image of the
single-functor image of the descended sheaf isomorphism.

The original declaration, geometry binders, public imports, header and docstrings
are preserved. The proof imports are private. Proved private tensor-instance caches,
local irreducibility attributes on large derived-functor definitions and colimit-instance
priorities prevent repeated expansion of the graded tensor construction while
elaborating the unchanged derived scalar-functor signature. No existing source-library
declaration, definition, target, or unit route is changed.

The item's DAG proof, proof dependencies and proof origin now describe this direct
sheaf-descent route. The existing theorem
`exists_constructible_finiteCoefficient_model` is used as a generic tool: it works
for every topologically Noetherian scheme, and gives precisely the sheaf model
needed here. It is the sheaf-level input already used by the planned two-colimit
theorem, rather than an alternative coefficient-finiteness route.

## Proved and sorry left

Closed the one assigned hole:
`AlgebraicGeometry.ProEtale.CondensedRing.finiteTypeAlgClHeart_finiteImage`
(node `lem-sfb-finite-type-alg-cl-heart-finite-image`).

The complete proof compiled in 41.0 seconds. The only warning concerned unused
inherited section variables; the existing geometry binders were retained and that
linter was scoped off at this theorem. The final packet is checked again by the
delivery tool with its declaration/axiom probe.

The delivered module contains zero sorries. No new holes or split statements are
added. This is a complete assembly from existing named declarations, not a claim
that their entire dependency closure is already free of sorry.

## No longer needed

`sk-thm-sfb-qlbar-two-colimit`, module
`Sheaf.Paper.FiniteCoefficientDescentTwoColimit`, is no longer a direct proof
dependency of this item. Its derived descent and recovery of the degree-zero
sheaf are unnecessary because `exists_constructible_finiteCoefficient_model` in
`Sheaf.Paper.CondensedFinitePresentationDescent` already supplies the finite-field
constructible sheaf model. This narrower existing theorem is imported instead.

The flatness and bounded-below direct-image comparison dependencies remain used.
No module is withdrawn, and no global pruning of the two-colimit theorem or its
other consumers is claimed. The original module had no proof imports to remove.

## Where the brief, the DAG or earlier work was wrong

The shared source checkout initially lacked the assigned Lean module, although its
node was present. The checkout refreshed during proof development and supplied the
original source. Its declaration and geometry binders matched the reconstruction;
the delivery uses its original text with the proof and private elaboration helpers.

The planned derived-descent route is longer than necessary. The existing sheaf
finite-presentation descent theorem has exactly the required constructible input
and output. Taking H^0 of a descended complex and invoking faithful flatness to
show concentration can therefore be omitted.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
