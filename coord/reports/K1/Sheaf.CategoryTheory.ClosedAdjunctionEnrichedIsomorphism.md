## What changed

Proved `CategoryTheory.ClosedAdjunctionComparison.enriched_isomorphism` in
`lean/Sheaf/CategoryTheory/ClosedAdjunctionEnrichedIsomorphism.lean`, preserving its
statement, universes, imports, definitions and existing docstrings.

The proof follows all five steps of
`lem-coef-closed-adjunction-enriched-isomorphism`: derive the uncurrying formula
from evaluation and test-object naturality; compose the five Hom equivalences;
identify that composite with postcomposition by the specified `adjointComparison`
using naturality of the tensor comparison and the adjunction Hom equivalence;
construct a two-sided inverse using surjectivity and injectivity; obtain the
naturality clause from the already proved `ClosedAdjunctionComparison.naturality`.
The DAG's proof and dependencies already describe this argument, so no node
changes are needed.

The source formulas were checked in `literature/stacks-project/categories.tex`,
Definition `definition-adjoint` and the following unit/counit formulas (Tag 0037).
The Mathlib ingredients are `Adjunction.homEquiv`, `homEquiv_counit`, and
`homEquiv_naturality_left`. LeanFinder's internal-Hom search returned the monoidal
closed adjunction and transport APIs, which require additional monoidal data.
Loogle confirmed the generic adjunction Hom-equivalence API. The grep search
located `rightAdjointUniq` and `isIso_of_yoneda_map_bijective`; directly constructing
the two-sided inverse implements the node's elementary argument without another
import. Searches of both library roots found no shorter exact theorem for the
arbitrary tensor-bifunctor hypotheses.

## Proved and sorry left

Closed one hole:
`CategoryTheory.ClosedAdjunctionComparison.enriched_isomorphism`
(node `lem-coef-closed-adjunction-enriched-isomorphism`).

Original holes: 1. Proved: 1. Holes left: 0. Holes added: 0. Split off: 0.
No decomposition or new declarations. The whole module compiles through
`lcompile.py`; delivery preflight also checks its axioms.

## No longer needed

None. No imports were added or removed. All three declared proof dependencies
remain used: `def-nagata-category` supplies category laws,
`lem-weil-pbc-adjunction-of-natural-bijection` supplies the Mathlib adjunction
Hom-equivalence formulas, and `lem-coef-closed-adjunction-naturality` supplies the
second conclusion. No nodes or modules are withdrawn or pruned, and the unit
route is unchanged.

## Where the brief, the DAG or earlier work was wrong

None. The existing declarations fit the five-step proof plan without statement
or definition repairs. No other module was changed.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
