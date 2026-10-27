## What changed

Proved `CategoryTheory.Endofunctor.IsoAlgebra.cyclicDerivedFreeDefect_coordinates`
in `Sheaf.CategoryTheory.CyclicDerivedFreeDefectCoordinates`, with its statement unchanged.
Added private, proved helpers for the summand-one differential calculation, the localized
unit/structure/differential comparisons, and the two adjunction-coordinate calculations.
Added the proof import `WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor`
for shift compatibility of the canonical localized structure isomorphism.
Updated the item's DAG proof to describe the implemented calculation.

Validation: the complete module compiled without errors or warnings through `lcompile.py`
in 14.4 seconds. The added proof import was checked to introduce no import cycle.

The key identity is T(e(d followed by f)) = T(e(f)) - e(f). It follows from summand one
rather than an explicit construction of the inverse action. Substituting the adjunct of
T(u) and using injectivity of T gives both required equations. The shifted clause uses
the specified shift adjunction and the canonical exact-functor comparisons.

## Proved and sorry left

Closed 1 hole: `CategoryTheory.Endofunctor.IsoAlgebra.cyclicDerivedFreeDefect_coordinates`
(node `lem-sf-cyclic-free-defect-coordinates`). Added 0 holes and split off 0 statements.
No `sorry` remains in the item or in any helper. No other existing module is changed.

## No longer needed

None. All three declared dependencies remain necessary: the normalized resolution data,
the free Hom coordinates and injectivity of the action, and the derived action definitions.
No public import was removed and no node or module is withdrawn. The calculation does not
use exactness or the boundary fields of the resolution datum.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. Library and Mathlib searches found generic adjunction,
localization and cyclic-resolution lemmas, but no existing result for this native derived
calculation. The original summand-zero/inverse-action plan is equivalent to the implemented
summand-one argument; the latter avoids constructing inverse action data.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.CategoryTheory.CyclicDerivedFreeDefectCoordinates": "5006ef56e128aa6ba2c3a808609a6cfb31da9729"}, "results": {"Sheaf.CategoryTheory.CyclicDerivedOffDiagonalCalculus": {"hash": "16b25fa049930b838006af4d4eb25df0145251e2", "status": "OK"}}, "seconds": 21, "time": "2026-10-28T02:09:35+0800", "transitive": 0, "version": 1}
```

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
