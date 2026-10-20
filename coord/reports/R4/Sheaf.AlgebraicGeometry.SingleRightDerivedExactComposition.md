## What changed

Retired `Sheaf.AlgebraicGeometry.SingleRightDerivedExactComposition`, the zero-hole
`retire` item in `coord/retire-items.tsv`. Listed its file in `deleted.txt` and removed the
sandbox copy. The delivery tool replaces it with the standard empty module.

Redirected node `lem-sc-single-right-derived-exact-composition` to the existing theorem
`CategoryTheory.Functor.single_rightDerived_exact_composition` in
`WeilConjectures.AlgebraicGeometry.SingleRightDerivedExactComposition`. The theorem has
the same conclusion, with no K-injective-resolution hypothesis on the intermediate
category A. The source-library declaration, proof, imports, and all targets stay verbatim.
The node's proof route and proof dependencies still describe that proof.

Change record: `coord/changes/retire-single-right-derived-exact-composition.md`.

Validation through `lcompile.py`:
- A scratch example with the former statement and context is proved by the upstream
  theorem: `exact F.single_rightDerived_exact_composition T M` (1.3 seconds).
- `#print axioms CategoryTheory.Functor.single_rightDerived_exact_composition` lists
  only `propext`, `Classical.choice`, and `Quot.sound`.
- The unchanged upstream consumer
  `WeilConjectures.AlgebraicGeometry.FiniteExactHomSingleCounitTransport` compiles alone
  without warnings (31.0 seconds).
- `tools/downstream.py` reports zero downstream modules for the withdrawn copy; source
  searches find no import of it. Thus there is no consumer to adapt or new import closure
  in which twin declarations could collide.

The scratch checks are under `scratchpad/` and are not part of the delivery. Searches
with `msearch.py` (Lean Finder, Loogle, grep) are recorded in `searches.jsonl`; direct
repository searches found the adopted source theorem.

## Proved and sorry left

The item already had zero holes: 0 closed, 0 added, 0 left; 0 split off. Its proved
`CategoryTheory.Functor.single_rightDerived_exact_composition` is retained through the
upstream declaration with the same name, rather than duplicated in Sheaf. This delivery
is a duplicate retirement, not a new proof or decomposition.

## No longer needed

Withdrawn module: `Sheaf.AlgebraicGeometry.SingleRightDerivedExactComposition`.
Its duplicate theorem and its import of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`
are removed with it. That infrastructure module remains needed by the upstream theorem
and is not claimed as pruned.

No DAG nodes are deleted or bypassed. Node
`lem-sc-single-right-derived-exact-composition` remains realized by the upstream theorem;
`def-weil-abstract-derived-category` remains its proof dependency. No unit step changes.
No consumer import needs removal: the former Sheaf consumer has already been retired.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proving an open obligation, but this assignment is listed as
`retire` and has zero holes. The hand-off lists
`Sheaf.AlgebraicGeometry.FiniteExactHomSingleCounitTransport` as one consumer; that module
is now absent, and its upstream twin already imports and applies the upstream theorem.
The DAG attachment still named the duplicate despite the available adopted theorem;
this delivery corrects the attachment. No mathematical error or new statement is involved.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
