## What changed

Added the proof-only import `Mathlib.CategoryTheory.Sites.EpiMono`. Added the named
intermediate theorem `finiteEtaleSplitHom_local_surjective`, whose proof remains a
single split hole for the local lifting argument. Reproved
`finiteEtaleSplitHom_epi` from that local-surjectivity statement: the sheaf
criterion gives `Epi f.hom`, and `Mod.forget` reflects epimorphisms. The existence
half and the final descent assembly are unchanged.

The epi node's proof route now depends on the local-surjectivity node. The new
node is recorded under `dag/nodes/sec-six-functors-basics/`.

## Proved and sorry left

- Closed `AlgebraicGeometry.ProEtale.CondensedRing.finiteEtaleSplitHom_epi`.
- `AlgebraicGeometry.ProEtale.CondensedRing.finiteEtaleSplitHom_exists` remains a
  sorry (existing node `lem-sfb-finite-etale-split-hom-descent-existence`).
- Added `AlgebraicGeometry.ProEtale.CondensedRing.finiteEtaleSplitHom_local_surjective`
  as a single sorry (new node `lem-sfb-finite-etale-split-hom-descent-local-surjective`).
- `AlgebraicGeometry.ProEtale.CondensedRing.finiteEtaleSplitHom_descent` remains
  proved.

No definition contains a sorry and no axiom was introduced.

## No longer needed

No imports or declared mathematical dependencies were pruned. The previous direct
localization and gluing dependencies of the epi proof are now carried by its
strictly smaller local-surjectivity node.

## Where the brief, the DAG or earlier work was wrong

The earlier epi split left the categorical epimorphism conclusion itself as a
hole. Once local surjectivity of the underlying sheaf map is isolated, the
remaining categorical step is short and complete: the sheaf local-surjectivity
criterion yields `Epi f.hom`, and the internal-module forgetful functor reflects
epimorphisms. This preserves the original theorem signature and its hypotheses.

## New nodes

`lem-sfb-finite-etale-split-hom-descent-local-surjective` records the strictly
smaller local lifting statement used by the epi proof. Its source is the finite
etale splitting and sheaf Hom-gluing argument of Stacks Tags 03EM, 04TQ and 04HN.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
