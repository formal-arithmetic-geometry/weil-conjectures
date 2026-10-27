## What changed

Filled `CategoryTheory.Adjunction.boundedBelowDerivedMateModel` in
`Sheaf.CategoryTheory.BoundedBelowDerivedMateModel`. The proof applies the existing,
fully proved `Adjunction.derivedPlus_mateEquiv_app_fac`. It proves that theorem's
computed-square hypothesis from `FullyFaithful.map_preimage` for the unchanged
`boundedBelowDerivedSquare`, evaluates the natural-transformation components, and
cancels only the exact localization comparison isomorphisms. All existing signatures,
definitions, docstrings, and imports remain unchanged. The item node records this route.

## Proved and sorry left

Closed one of one holes: `CategoryTheory.Adjunction.boundedBelowDerivedMateModel`
(node `lem-trf-bounded-below-derived-mate-model`). Zero holes added, zero split off,
zero holes left in the delivered Lean module. The new DAG node attaches an already
proved source theorem; it introduces no Lean declaration or proof obligation.

## No longer needed

No existing imports were removed. This proof does not import or use:

- `lem-trf-bounded-below-square-localization`, module
  `Sheaf.CategoryTheory.BoundedBelowSquareLocalization`: the explicit localization
  construction's `map_preimage` identity supplies its needed component formula directly.
- `lem-trf-derived-mate-counit-reduction`, module
  `Sheaf.CategoryTheory.DerivedCategory.DerivedMateCounitReduction`: the complete
  source mate theorem already performs this counit calculation.
- `lem-trf-derived-transpose-comparison-unit`, module
  `Sheaf.CategoryTheory.DerivedCategory.TransposeComparisonUnit`: the same complete
  source theorem already performs the primed-unit and termwise-mate calculation.

These are dependencies pruned from this item's proof route, not withdrawal requests;
other consumers may still need them. The old direct `tool_uses` approval for
`lem-weil-pbc-termwise-adjunction-homotopy` is removed from this item: the source
computed-square theorem now carries that calculation and its dependency explicitly.
The old direct proof dependencies `def-weil-abstract-derived-category` and
`lem-trf-bounded-below-derived-adjunction` are subsumed by the named source theorem
(they remain available as statement prerequisites). The unit's statement and route stay.

## Where the brief, the DAG or earlier work was wrong

The proposed three-helper reduction is unnecessary: the adopted source library already
contains the complete mate factorization theorem, including arbitrary noninvertible
squares and no preservation-of-injectives hypothesis for H. Its only extra input is
precisely the factorization obtained from this module's existing preimage construction.
No mathematical statement was corrected. The zero and identity squares, noninvertible
squares, and zero categories require no special cases or new assumptions.

## New nodes

`lem-trf-computed-bounded-below-square-mate` records the existing, proved
`CategoryTheory.Adjunction.derivedPlus_mateEquiv_app_fac` in
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`.
It gives the mate formula for a supplied square satisfying the termwise-computation
hypothesis, so the item separately verifies that hypothesis for its canonical square.
The node includes the source proof's unit/counit and naturality argument, a verbatim
Lean signature, and LeanSearch, Loogle, and library/Mathlib grep searches. There is no
new module, new hole, interface change, consumer adaptation, or change record.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
