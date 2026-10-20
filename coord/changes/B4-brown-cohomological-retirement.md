# CategoryTheory.brownCohomologicalRepresentability

## Reason

`coord/retire-items.tsv` explicitly lists this item as a duplicate of the adopted
source module. Both declarations have the same fully elaborated type: the Sheaf
file's surrounding variable declaration supplies the explicit category argument
and all the same instances. The source theorem is completely proved. Retire the
Sheaf copy and point its DAG attachment and the sole live direct importer to the
canonical owner. No adopted source file is changed.

## Old

The category and instance parameters come from the file's `variable (C : Type u)` block.

```lean
theorem brownCohomologicalRepresentability
    (hC : IsCompactlyGeneratedTriangulated.{v} C)
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    (hH : ∀ (I : Type v), PreservesLimitsOfShape (Discrete I) H) :
    ∃ G : C, Nonempty (H ≅ preadditiveYoneda.obj G)
```

## New

No replacement declaration is introduced. The existing proved source theorem is:

```lean
theorem brownCohomologicalRepresentability (C : Type u) [Category.{v} C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [IsTriangulated C] [HasCoproducts.{v} C]
    (hC : IsCompactlyGeneratedTriangulated.{v} C)
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    (hH : ∀ (I : Type v), PreservesLimitsOfShape (Discrete I) H) :
    ∃ G : C, Nonempty (H ≅ preadditiveYoneda.obj G)
```

The item is withdrawn through `deleted.txt`. The only live consumer changes just
`import Sheaf.CategoryTheory.BrownCohomologicalRepresentability` to
`import WeilConjectures.CategoryTheory.BrownCohomologicalRepresentability`.
Its signature, visibility, docstring and proof body are byte-identical.
No definition, target statement or target meaning changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.BrownCohomologicalRepresentability | B4 | Withdraw the duplicate; retain its node on the complete canonical source theorem. |
| Sheaf.CategoryTheory.GrothendieckDerivedBrownRetractData | unclaimed | Sole live direct importer; change only its proof import, preserving every declaration. |
| WeilConjectures.CategoryTheory.BrownRepresentabilityRightAdjoint | unclaimed | The old retirement list names a now-retired Sheaf twin; current canonical module already imports the canonical Brown source. No edit. |
| WeilConjectures.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransferAux | unclaimed | DAG parent already imports and applies the canonical Brown theorem. No edit. |

`tools/downstream.py --uses brownCohomologicalRepresentability` confirms one
downstream module and two name-use modules (the item and that consumer). A scan
of both live roots and quarantine finds no other direct importer. The
quarantine copy of GrothendieckDerivedBrownRetractData has already been restored
in the live tree; the delivery adapts that live version, not the obsolete archive.
The three DAG parents are lem-pc-brown-representability-right-adjoint,
lem-pc-brown-representability-universe-transfer-aux and
lem-g2-grothendieck-derived-localization-brown-data. Their existing dependencies
continue to refer to the retained node, now attached to the canonical source.
No unit's realized field mentions this node; its unit's statement and steps stay.

The source proof uses its own complete BrownRepresentability.exists_bijective
construction. Its axiom probe reports only propext, Classical.choice, Quot.sound.
The adapted consumer compiles cleanly through lcompile.py (1.2 seconds). An
example retaining the exact old signature applies the canonical source theorem
and compiles in 1.0 seconds, checking category, binders and universes directly.

## Status

landed 20261020T162536-L-3619900 2026-10-20 (merge of deliver/B4/Sheaf.CategoryTheory.BrownCohomologicalRepresentability)
