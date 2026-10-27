## What changed

Restored the complete proof of `CategoryTheory.finitarySlice_enoughPoints` from
H3's previously landed proof (7de3abe5b26), recovered from the parent of
af2f412b751. Its signature, universes and six public imports are unchanged.
All added helper declarations are private and proved.

The proof transports the slice precoverages through `AsSmall`, applies the existing
`finitarySite_enoughPoints`, constructs the localization geometric morphisms using
Mathlib, and composes the slice points. It derives `CoversTop U` from the assumed
epimorphism using sheafification and local surjectivity, then applies Mathlib's
`Sheaf.isIso_of_coversTop`. This includes an empty index family. The node's proof,
proof dependencies and proof origin are restored to this implemented route.

Verification: the recovered four-module chain (PointSystemRefine,
PointSystemSaturation, FinitarySiteEnoughPoints, FinitarySliceEnoughPoints) compiled
against the current library, respectively in 4.8, 6.8, 4.5 and 3.9 seconds.
Only the assigned module is included in this delivery: PointSystemRefine is held
by Y3 and FinitarySiteEnoughPoints by K3, who have their own restoration items.
Their recovered source files were used for that validation and removed from this
sandbox afterward. No source-library module is changed.

## Proved and sorry left

Closed 1 of 1 existing holes: `CategoryTheory.finitarySlice_enoughPoints`
(node `lem-sfb-site-finitary-slice-enough-points`). There are zero `sorry`s left in
the assigned module and zero holes added elsewhere. No statements are split off.
The proof uses the existing declared theorem `CategoryTheory.finitarySite_enoughPoints`;
its separate restoration belongs to K3 and its refinement prerequisite to Y3.
No claim is made here to have closed those groups' holes.

## No longer needed

Removed proof imports:
- `Sheaf.CategoryTheory.ContinuousCocontinuousToposAdjunctionForCoverings`:
  the localization adjunction is supplied directly by Mathlib.
- `WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings`:
  Mathlib already provides cocontinuity for `Over.forget`.

Accordingly the proof no longer uses nodes
`lem-weil-pbc-continuous-cocontinuous-topos-adjunction` and
`def-weil-pbc-special-cocontinuous-functor`. Their modules and declarations remain
in the library for their other consumers. The former is removed from this node's
`tool_uses`; all other approved tool uses are retained. No module is withdrawn.
The slice criterion, finitary-site criterion and unit route remain in place.

## Where the brief, the DAG or earlier work was wrong

The return correctly identifies an already completed proof removed during an
unrelated build take-out. Restoring that proof compiles without mathematical or
signature repair. The live DAG still described the longer covering-level topos
adjunction route; its restored proof now records the actual Mathlib localization
adjunction and local-isomorphism descent route. No statement is disputed.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
