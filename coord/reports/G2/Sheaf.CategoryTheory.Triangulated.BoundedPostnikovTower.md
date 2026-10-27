## What changed

Completed both proofs in `Sheaf.CategoryTheory.Triangulated.BoundedPostnikovTower` without
changing any declaration signature or definition. The finite family is
`L j = (t.truncLT (a + j)).obj K`. The zero and terminal isomorphisms use the given
bounds on K. Each adjacent triangle is Mathlib's `triangleLTLTGELT_distinguished`,
transported along `truncGELEIsoTruncGELT` and inverse-shift cancellation. The bounds
on double truncations give heart membership after shifting, for every integer q.

For the standard derived category, classify the double truncation in degrees [q,q]
as `singleFunctor C q` of an object Y. Apply H^q to this isomorphism, identify
H^q of both truncation maps using the proved source-library comparison lemmas,
and recover an isomorphism Y ≅ H^q(K). Shift by q and apply the degree-zero single
functor to this coefficient isomorphism. The additional proof-only import is
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`.

Updated the node's proof, proof dependencies and proof origin to describe this
route. The unit's statement and realized steps are unchanged. The original
public imports and documentation are preserved.

## Proved and sorry left

Closed 2 of 2 existing holes, both belonging to
`lem-sfb-bounded-postnikov-extension-generation`:

- `CategoryTheory.Triangulated.TStructure.exists_bounded_postnikov_tower`.
- `DerivedCategory.bounded_postnikov_cohomology_iso`.

No sorry remains in the item; no holes or new declarations were added and none
were split off. The construction includes the n = 0 case without a case
restriction: Fin 0 has no adjacent triangles and both endpoint isomorphisms are
still provided. No global boundedness or nondegeneracy assumption is used.

## No longer needed

Removed the proof-only import `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`
and the proof dependency `def-kun-truncations`: the derived identification follows
from existing shifted-heart classification and cohomology comparison isomorphisms,
so the good-truncation model and sequential homotopy-colimit infrastructure are
unnecessary for this item. This is a local dependency removal; no source module or
existing declaration is withdrawn. The nested-counit clause of
`lem-sfb-upper-truncation-counit-calculus` is unnecessary here because Mathlib
already packages the adjacent truncation triangle. Its endpoint clauses and
`lem-sfb-adjacent-t-truncation-layer` remain used. No other nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

No false statement or source error was found. The DAG's representative-level
calculation for the standard specialization was longer than necessary: the
existing derived-category API already supplies its comparison isomorphisms.
The node now records the actual argument. No statement, target or unit route
was changed.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
