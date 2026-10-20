# AlgebraicGeometry.Etale.supportRestrictionTriangle

## Reason

Withdraw the unused existence-only support-triangle interface under the dispatched
brief, step 8d. The current DAG node `lem-pur-support-restriction-triangle` is already
realized by `NormalizedSupportTriangle`, whose constructions and statements do not
use `supportRestrictionTriangle`. A source search finds the latter name only at its
own declaration. The only remaining incoming imports are the two consumers listed below.
Their imports must be removed in the same delivery because the withdrawal protocol
requires that no source imports a withdrawn module. This is pruning an unused
statement, not proving it or replacing it by a weaker statement.

## Old

The withdrawn module publicly exposed this theorem:

```lean
theorem supportRestrictionTriangle (R : Type (u + 1)) [CommRing R]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c] :
    ∃ (a : supportedEtaleSections R T (b.openComplement ⊔ c.openComplement) ⟶
        supportedEtaleSections R T b.openComplement)
      (r : supportedEtaleSections R T b.openComplement ⟶
        upperStar (ModuleCat.{u + 1} R) c.openComplement.ι ⋙
          supportedEtaleSections R c.openComplement
            (c.openComplement.ι ⁻¹ᵁ b.openComplement))
      (e : (upperStar (ModuleCat.{u + 1} R) c.openComplement.ι ⋙
          supportedEtaleSections R c.openComplement
            (c.openComplement.ι ⁻¹ᵁ b.openComplement)).rightDerivedFunctorPlus ≅
        (upperStar (ModuleCat.{u + 1} R) c.openComplement.ι).mapDerivedCategoryPlus ⋙
          (supportedEtaleSections R c.openComplement
            (c.openComplement.ι ⁻¹ᵁ b.openComplement)).rightDerivedFunctorPlus)
      (δ : (upperStar (ModuleCat.{u + 1} R) c.openComplement.ι).mapDerivedCategoryPlus ⋙
          derivedSupportedEtaleSections R c.openComplement
            (c.openComplement.ι ⁻¹ᵁ b.openComplement) ⟶
        derivedSupportedEtaleSections R T (b.openComplement ⊔ c.openComplement) ⋙
          shiftFunctor (DerivedCategory (ModuleCat.{u + 1} R)) (1 : ℤ)),
      (∀ M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R),
        a.app M ≫ (supportedEtaleSectionsι R T b.openComplement).app M =
          (supportedEtaleSectionsι R T (b.openComplement ⊔ c.openComplement)).app M) ∧
      (∀ M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R),
        r.app M ≫ (supportedEtaleSectionsι R c.openComplement
            (c.openComplement.ι ⁻¹ᵁ b.openComplement)).app
              ((upperStar (ModuleCat.{u + 1} R) c.openComplement.ι).obj M) =
          (supportedEtaleSectionsι R T b.openComplement).app M ≫
            globalSectionsUpperStarMap (ModuleCat.{u + 1} R) c.openComplement.ι M) ∧
      ((upperStar (ModuleCat.{u + 1} R) c.openComplement.ι ⋙
          supportedEtaleSections R c.openComplement
            (c.openComplement.ι ⁻¹ᵁ b.openComplement)).rightDerivedFunctorPlusUnit ≫
          Functor.whiskerLeft DerivedCategory.Plus.Qh e.hom =
        Functor.rightDerivedFunctorPlusCompUnit
            (upperStar (ModuleCat.{u + 1} R) c.openComplement.ι)
            (supportedEtaleSections R c.openComplement
              (c.openComplement.ι ⁻¹ᵁ b.openComplement)) ≫
          Functor.whiskerLeft DerivedCategory.Plus.Qh
            (Functor.whiskerRight
              (upperStar (ModuleCat.{u + 1} R)
                c.openComplement.ι).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom
              (supportedEtaleSections R c.openComplement
                (c.openComplement.ι ⁻¹ᵁ b.openComplement)).rightDerivedFunctorPlus)) ∧
      ∀ F : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)),
        Triangle.mk
          (DerivedCategory.Plus.ι.map ((Functor.rightDerivedFunctorPlusNatTrans a).app F))
          (DerivedCategory.Plus.ι.map
            ((Functor.rightDerivedFunctorPlusNatTrans r).app F ≫ e.hom.app F))
          (δ.app F) ∈ distTriang (DerivedCategory (ModuleCat.{u + 1} R))
```

The two remaining consumers imported `Sheaf.AlgebraicGeometry.SupportRestrictionTriangle`.
The import was public in `NormalizedSupportTriangle` and proof-only in `SupportedProductLocalization`.

## New

The item is listed in `deleted.txt`; the delivery tool installs the prescribed empty
module with no declarations. Each consumer loses exactly the obsolete import line.
Every declaration, signature, visibility, proof and other import in those consumers
is unchanged. Both consumers are compiled together after the import removal. No target
statement or definition is changed. The actual normalized support-triangle node,
its proof plan, and its dependencies remain in the library.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SupportRestrictionTriangle | Q5 | Withdraw unused theorem and module. |
| Sheaf.AlgebraicGeometry.NormalizedSupportTriangle | P1 | Remove obsolete public import only. |
| Sheaf.AlgebraicGeometry.SupportedProductLocalization | V2 | Remove obsolete proof import only. |
| Sheaf.AlgebraicGeometry.SupportedLocalizationComparisons | unclaimed | Indirect importer; no declaration use and no adaptation. |

`tools/downstream.py ... --uses AlgebraicGeometry.Etale.supportRestrictionTriangle`
finds no declaration consumer outside the withdrawn module. The three downstream
modules listed by the script are all included in the table above; none uses the
removed declaration.
The two direct importers retain exactly their import line removal; they
retain the public interfaces needed by their downstream users.

The returned delivery at `51f08d1875` misidentified the holder of
`Sheaf.AlgebraicGeometry.SupportedProductLocalization` as D3. The holder is V2,
as corrected in the table above. Both adapted files are refreshed from current
main before dropping the obsolete import, preserving subsequent import migrations.
`Sheaf.AlgebraicGeometry.KunnethSupported` has already been removed from current
main; its stale sandbox copy is removed from this packet rather than restored.

## Status

landed 20261020T132026-L-1403260 2026-10-20 (merge of deliver/Q5/Sheaf.AlgebraicGeometry.SupportRestrictionTriangle)
