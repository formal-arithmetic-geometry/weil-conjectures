## What changed

Proved `DerivedCategory.bounded_bifunctor_devissage`, preserving its full signature and
universes. Added the proved private helper `DerivedCategory.bounded_functor_devissage`.
It applies the source library's existing, fully proved
`DerivedCategory.exists_iteratedExtensions_of_bounded` and `DerivedCategory.iteratedExtensions_le`
to the properties `P(X) := S(G(X[0]))` and `Q(L) := S(G(L))`. These properties inherit
closure under isomorphisms; Q also inherits triangulated and shift closure. The canonical
`singleFunctors.shiftIso` identifies a single object in degree n with its degree-zero
version shifted by -n, completing the one-variable argument.

Apply this helper to `F.flip.obj M` and then, for each nonzero cohomology object of K,
to `F.obj (H^q(K)[0])`. Zero cohomology objects are handled by `Functor.map_isZero` and
`ObjectProperty.prop_of_isZero`; all remaining pairs are exactly the hypothesis h₀.
Thus arbitrary non-iso-closed input classes, empty classes, gaps, acyclic inputs and
negative cohomological intervals require no extra assumptions.

Added one private proof import,
`WeilConjectures.CategoryTheory.DerivedCategory.BoundedEssentiallySmall`, and removed
the two unused truncation proof imports. No public imports or interfaces changed;
no consumers require adaptation or change records. Updated the item's DAG proof,
proof dependencies and origin to describe this reuse of the existing Postnikov induction.
The integral-model unit's statement and route are unchanged.

## Proved and sorry left

Closed the sole original hole:
`DerivedCategory.bounded_bifunctor_devissage`
(node `lem-sfb-bounded-bifunctor-devissage`).

The private helper `DerivedCategory.bounded_functor_devissage` is also fully proved.
Holes closed: 1. Holes added: 0. Holes remaining in the delivered module: 0.
Split off: none. This is a proof, not a decomposition.

Remote single-file compilation succeeded without warnings (2.0 seconds).
A further compile with `#print axioms DerivedCategory.bounded_bifunctor_devissage`
succeeded (2.1 seconds) and reported exactly `propext`, `Classical.choice`, and `Quot.sound`.
The diagnostic command was removed from the delivered source.

## No longer needed

Removed the proof imports `Sheaf.CategoryTheory.TruncationDescends` and
`WeilConjectures.CategoryTheory.TruncationTriangle`. Their nodes
`lem-weil-pbc-truncation-descends` and `lem-weil-pbc-truncation-triangle` are no longer
proof dependencies of this item, and their two obsolete top-level tool approvals were
removed. The already proved standard-t-structure Postnikov induction provides the finite
extension description directly; constructing descended truncation functors and their
successive triangles again is unnecessary. These modules may still be needed elsewhere;
this delivery does not withdraw or change them.

The original definition dependencies remain relevant. The standard-t-structure definition
is now explicitly listed among proof dependencies as well as statement dependencies.
No other node, module or import is pruned.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement and the five-step proof plan were sound. The plan did not exploit
the existing proved one-variable Postnikov results in `BoundedEssentiallySmall`; using them
implements the same two finite cohomological inductions with substantially less glue.
No statement or definition repair was needed. LeanFinder and Loogle searches found no direct
Mathlib result for the assertion; repository `rg` found the usable source-library theorem.
The source text read was `literature/stacks-project/derived.tex`, Remark 08J5
(lines 4076 onward); the code uses its finite Postnikov argument already proved in the library.
No new mathematical statement or open dependency was introduced.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
