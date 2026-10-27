## What changed

Replaced the hole in `Sheaf.Paper.AdicFiniteCompletionTower` with a proof from the
existing strict-tower Roos theorem and one finite successor calculation. The original
statement, coefficient universes, and public import are unchanged.

The proof chooses a flat-term K-flat representative, uses the quotient presentation's
invertible computation to identify its strict tower, identifies the two total right
derived limit functors by `Functor.rightDerivedUnique`, and transports a distinguished
triangle through the resulting vertex and product isomorphisms. Naturality of the
transition endomorphism proves the middle square; the connecting arrow is transported
by the triangle isomorphism. A generic private helper assembles isomorphisms of inverse
sequences from successor squares.

Added `Sheaf.Paper.AdicFiniteStrictReductionSuccessor`. Both the evaluation isomorphism
and every finite-level scalar isomorphism are explicit, sorry-free constructions. The
only deferred statement is the equality for one specified successor. It does not assert
existence of a tower isomorphism, product, derived limit, or completion comparison.

Both delivery modules compile through `lcompile.py`: the new successor module in
23.6 seconds and the item in 28.1 seconds, with no compiler errors or warnings.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.Scheme.adicFiniteCompletion_tower`.
The item's module now contains zero sorries. The private tower assembly and triangle
transport proofs are complete.

New hole: `AlgebraicGeometry.Scheme.adicFiniteStrictReduction_successor`, node
`lem-sfb-adic-finite-strict-reduction-successor`. Its docstring and node give the scalar
unit, balancing, exact-restriction, and pure-tensor calculation to perform. Its hypothesis
includes flat terms so the recorded K-flat change-of-rings lemma applies directly.

Counts: 1 original hole removed, 1 finite-arrow hole added, net 0. This delivery is a
decomposition, not a claim of net sorry closure. No hole occurs inside any definition.

## No longer needed

No original import was removed. No existing module or declaration is withdrawn.

The item's proof no longer needs `det-pe-products-exact`
(`Sheaf.AlgebraicGeometry.ProEtaleProductsExact`) or `lem-weil-strict-roos-comparison`
(`Sheaf.CategoryTheory.StrictRoosComparison`): the already proved
`lem-weil-pbc-ringed-strict-tower-homotopy-limit` directly supplies derived products
and the distinguished Roos triangle, without assuming exact ordinary products.
These are removals from this node's direct proof dependencies, not claims that the
modules leave every target's transitive import closure.

The separate planned applications of `lem-pur-derived-change-of-rings` and
`lem-pur-resolving-class-derived-adjunction` are also unnecessary in this proof: their
computations and normalized units are already packaged in the existing
`derivedExtension` and `adicFiniteUnit` interfaces. They are not withdrawn; those
interfaces and their implementation dependencies remain. K-flat scalar base change
remains a dependency of the finite successor calculation.

## Where the brief, the DAG or earlier work was wrong

The planned exact-products and termwise-cone comparison was stronger than needed.
The strict-tower theorem already contains the triangle with derived products, and
uniqueness of right derived functors identifies its chosen limit with the one selected
by `completion`. No Noetherian hypothesis, reflector theorem, completeness hypothesis,
or Tor bound is used.

The remaining square is not supplied by the nearby
`adicResidueQuotientTensorLevelIso_successor`: that statement concerns modules over a
completed coefficient sheaf on a slice and a scalar-adjoint counit tower. This item uses
constant coefficients on the entire model site and the prescribed unit-based
`adicFiniteTransition`. The new lemma records only this missing finite computation.

The edge cases J=0, J=A, zero complexes and empty schemes are covered by the same
specified scalar formulas; no nonzero or proper-ideal hypothesis was introduced.
The unit's statement and realized route are unchanged.

## New nodes

`lem-sfb-adic-finite-strict-reduction-successor` in
`dag/nodes/sec-six-functors-basics/` records one equality between explicit successor
maps, with its three supporting scalar-construction declarations in the new module.
Mathlib searches used LeanSearch, LeanFinder and grep; the blueprint and local library
were also searched. No exact matching constant-coefficient successor statement was
found. This is strictly part of the original argument: all level constructions,
assembly of the whole tower, derived-limit uniqueness, product transport and triangle
transport are implemented outside its remaining proof hole.

No change record is needed: no existing file outside the assigned module and its node
was changed, and no existing public interface was changed.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
