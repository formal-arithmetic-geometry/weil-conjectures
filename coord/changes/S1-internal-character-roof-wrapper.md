# CategoryTheory.CondensedDerivedRestriction.characterRoof

## Reason

Profiling found repeated type checking of the expanded concrete localized roof expensive:
characterRoof_as_conjugate took about 25 seconds and the subsequent induction about 14 seconds.
Package exactly the original composite in the generic localizedShiftedRoof construction,
with an irreducible body and proved composition and zero-shift API. This keeps the concrete
action-category and localization structures out of subsequent shift algebra. All objects,
maps, shifts, signs, coefficient universes and hypotheses are the same. No target meaning
changes: unfolding localizedShiftedRoof gives the old body verbatim, with its canonical
singleFunctorIsoCompQ component written as an isomorphism argument.

## Old

```lean
def characterRoof (R : Resolution A.toMon G) (e : RoofAugmentation R) [QuasiIso e]
    (q : ℕ) (F : complex R ⟶ (complex R)⟦(q : ℤ)⟧) :
    coefficient A G ⟶ (coefficient A G)⟦(q : ℤ)⟧ :=
  (DerivedCategory.singleFunctorIsoCompQ (Equivariant A G) 0).hom.app
      (regularTrivial A G) ≫
    inv (DerivedCategory.Q.{u + 1}.map e) ≫
    DerivedCategory.Q.{u + 1}.map (F ≫ e⟦(q : ℤ)⟧') ≫
    (DerivedCategory.Q.{u + 1}.commShiftIso (q : ℤ)).hom.app
      (single 0 (regularTrivial A G)) ≫
    ((DerivedCategory.singleFunctorIsoCompQ (Equivariant A G) 0).inv.app
      (regularTrivial A G))⟦(q : ℤ)⟧'
```

## New

```lean
def characterRoof (R : Resolution A.toMon G) (e : RoofAugmentation R) [QuasiIso e]
    (q : ℕ) (F : complex R ⟶ (complex R)⟦(q : ℤ)⟧) :
    coefficient A G ⟶ (coefficient A G)⟦(q : ℤ)⟧ :=
  localizedShiftedRoof DerivedCategory.Q.{u + 1} e
    ((DerivedCategory.singleFunctorIsoCompQ (Equivariant A G) 0).app
      (regularTrivial A G)) (q : ℤ) F
```

Added the public import Sheaf.CategoryTheory.InternalShiftedRoof to expose this definition
body. Existing public imports are retained. The only new transparency boundary is the new
generic definition; characterRoof itself retains its previous reducibility.

The existing `orderedShiftedArrows` definition is moved verbatim from the item into
InternalShiftedRoof, in the same namespace and with the same universes, signature,
visibility and recursion. The item's public import reexports it. Its finite-roof
induction is now the proved generic theorem localizedShiftedRoof_ordered; specializing
that theorem avoids repeatedly checking concrete action-category structures.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.InternalBarCharacterRoofCup | S1 | Same statement and roof formula; reexports orderedShiftedArrows and uses the generic finite-composition API. |
| Sheaf.CategoryTheory.InternalBarCharacterLiftNormalization | S1 (new) | States the degree-one roof using the same generic definition. |

Read-only downstream.py --uses and a direct-import search found no existing external
Lean importer or declaration user of this item. Therefore there are no existing direct
importers to adapt or compile. DAG parents with unfinished proofs retain the item and
its unchanged mathematical statement. No existing source-library file was changed.

## Status

landed 20261026T082912-L-2235193 2026-10-26 (merge of deliver/S1/Sheaf.CategoryTheory.InternalBarCharacterRoofCup)
