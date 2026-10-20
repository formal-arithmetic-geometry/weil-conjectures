# CategoryTheory.brownCohomologicalRepresentabilityUniverseTransfer

## Reason

The item is explicitly listed in coord/retire-items.tsv. Its adopted-source twin
proves the same representability conclusion without the extra common-universe
Brown principle. Retire the duplicate and use the complete source theorem.
No adopted-source file is changed, and no target statement or definition changes.

## Old

```lean
theorem brownCohomologicalRepresentabilityUniverseTransfer
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
    (H ⋙ forget AddCommGrpCat).IsRepresentable
```

## New

The canonical declaration in
WeilConjectures.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransfer is:

```lean
theorem brownCohomologicalRepresentabilityUniverseTransfer
    (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [IsTriangulated C] [HasCoproducts.{max w v vH} C]
    (hC : IsCompactlyGeneratedTriangulated.{max w v vH} C)
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{vH}) [H.IsHomological]
    (hH : ∀ I : Type (max w v vH), PreservesLimitsOfShape (Discrete I) H) :
    (H ⋙ forget AddCommGrpCat).IsRepresentable
```

The Sheaf copy is withdrawn through deleted.txt. In its only live consumer,
GrothendieckDerivedBrownRetractData, replace the private import by the canonical
source import and remove the now-superfluous hBrown lambda argument. Remove the
private BrownCohomologicalRepresentability import used only by that lambda.
Every declaration and public import of the consumer stays identical.

The universe-transfer node is attached to the stronger source declaration, and
its statement explicitly drops the redundant Brown hypothesis. Its two DAG
citers retain the same conclusion. The localization-data node records the direct
source application and removes its separate common-universe Brown dependency.
The right-adjoint node already attaches to the adopted-source implementation;
its module neither imports nor calls the retired copy, so it needs no Lean edit.
No unit realized entry uses the retired attachment; the Picard-duality unit's
statement and steps are untouched. This changes no definitions and constructs
no data from an unproved existence statement.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransfer | G1 | Withdraw duplicate and attach its node to the proved stronger source twin. |
| Sheaf.CategoryTheory.GrothendieckDerivedBrownRetractData | unclaimed | Sole live importer and call; change private import and drop redundant Brown argument and import. |
| WeilConjectures.CategoryTheory.BrownRepresentabilityRightAdjoint | unclaimed | Other consumer in old retirement list is now this canonical module; already independent of the retired copy, no edit. |
| Sheaf.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint | unclaimed | Transitive importer only; consumer public interface is unchanged, no edit. |
| Sheaf.CategoryTheory.GrothendieckDerivedBrownCohomologicalRepresentability | unclaimed | Transitive importer only; consumer public interface is unchanged, no edit. |
| Sheaf.CategoryTheory.GrothendieckDerivedBrownRetract | unclaimed | Transitive importer only; consumer public interface is unchanged, no edit. |
| Sheaf.CategoryTheory.GrothendieckDerivedBrownRightAdjoint | unclaimed | Transitive importer only; consumer public interface is unchanged, no edit. |

The downstream scan lists five modules in all; only the localization-data
module directly imports or calls the item.

The two direct DAG parents are
lem-pc-brown-representability-right-adjoint and
lem-g2-grothendieck-derived-localization-brown-data. Both retain the full
representability conclusion. The auxiliary node mentions the item only in
historical creation/blueprint metadata, not in proof or statement dependencies.
Neither the item nor its consumer has a current quarantine/rework row.
The replacement preserves all category, universe, coproduct, compact-generation,
homologicality and product-preservation hypotheses. In particular no nonempty
index set or generator assumption has been added: empty families are covered
by exactly the same compact-generation predicate. A compatibility probe proves
the entire old conditional signature directly from the canonical theorem.

Validation: the adapted consumer compiles cleanly through lcompile.py (1.2 s).
The old-signature compatibility probe compiles cleanly (1.0 s), and both it and
the canonical source theorem report only propext, Classical.choice and Quot.sound.

## Status

landed 20261020T211713-L-3490468 2026-10-20 (merge of deliver/G1/Sheaf.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransfer)
