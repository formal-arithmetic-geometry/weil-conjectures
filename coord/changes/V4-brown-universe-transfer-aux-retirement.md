# CategoryTheory.brownCohomologicalRepresentabilityUniverseTransfer_aux

## Reason

Retire item `lean/Sheaf/CategoryTheory/BrownCohomologicalRepresentabilityUniverseTransferAux.lean` is listed in coord/retire-items.tsv. The adopted source library now proves the auxiliary conclusion without the extra common-universe Brown hypothesis. Use that stronger theorem and remove the duplicate declaration. No file under lean/WeilConjectures is changed.

## Old

```lean
theorem brownCohomologicalRepresentabilityUniverseTransfer_aux
    (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [IsTriangulated C] [HasCoproducts.{max w v vH} C]
    (hC : IsCompactlyGeneratedTriangulated.{max w v vH} C)
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{vH}) [H.IsHomological]
    (hH : ∀ I : Type (max w v vH), PreservesLimitsOfShape (Discrete I) H)
    (hBrown : ∀ (A : Type u) [Category.{max w v vH} A]
      [HasZeroObject A] [HasShift A ℤ] [Preadditive A]
      [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
      [IsTriangulated A] [HasCoproducts.{max w v vH} A],
      IsCompactlyGeneratedTriangulated.{max w v vH} A →
      ∀ (K : Aᵒᵖ ⥤ AddCommGrpCat.{max w v vH}) [K.IsHomological],
      (∀ I : Type (max w v vH), PreservesLimitsOfShape (Discrete I) K) →
      ∃ G : A, Nonempty (K ≅ preadditiveYoneda.obj G)) :
    ∃ G : C, Nonempty ((H ⋙ forget AddCommGrpCat).RepresentableBy G)
```

## New

The declaration is provided by `WeilConjectures.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransferAux`:

```lean
theorem brownCohomologicalRepresentabilityUniverseTransfer_aux
    (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [IsTriangulated C] [HasCoproducts.{max w v vH} C]
    (hC : IsCompactlyGeneratedTriangulated.{max w v vH} C)
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{vH}) [H.IsHomological]
    (hH : ∀ I : Type (max w v vH), PreservesLimitsOfShape (Discrete I) H) :
    ∃ G : C, Nonempty ((H ⋙ forget AddCommGrpCat).RepresentableBy G)
```

The Sheaf item is withdrawn using deleted.txt. Its sole consumer imports this source module, clears hBrown and applies the source theorem to C hC H hH. Every binder, universe and visibility of the consumer is unchanged. A declaration-local linter.unusedVariables option suppresses the warning about the intentionally retained unused hBrown parameter. No definition or target meaning changes. The auxiliary DAG node records the stronger source statement and its Brown dependency.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransferAux | V4 | Duplicate withdrawn; node attached to the stronger proved source declaration. |
| Sheaf.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransfer | unclaimed | Only direct importer and use found by tools/downstream.py --uses; private import and theorem application adapted, signature unchanged. |

The full downstream scan finds only the single consumer above. The only DAG parent is lem-pc-brown-representability-universe-transfer; its dependency still points to the retained auxiliary node, now attached to the adopted source. No unit realized field mentions the auxiliary. No quarantine/rework row names either module. The original universe-transfer proof handles empty generator families through its preserved generation hypothesis; the replacement has the same category, coproduct, homologicality and product assumptions and identical conclusion.

## Status

landed 20261020T153024-L-2864932 2026-10-20 (merge of deliver/V4/Sheaf.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransferAux)
