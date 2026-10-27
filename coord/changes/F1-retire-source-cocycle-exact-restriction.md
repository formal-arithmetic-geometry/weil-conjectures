# AlgebraicGeometry.Etale.sourceCocycleExactRestriction: obsolete duplicate retirement

## Reason

This is the retirement assigned by coord/retire-items.tsv, row whose copy is
Sheaf.AlgebraicGeometry.SourceCocycleExactRestriction. The item has zero sorry bodies.
The human's approved retirement policy is recorded in
coord/changes/retire-sheaf-twins-20261020.md. Reconcile that inventory with the current
library rather than treating its historical consumer list as current.

The old module redeclares the adopted source theorem's fully qualified name, but its
scheme is strictHenselizationScheme, not the source theorem's strictLocalization.
They are distinct constructions. The original-model theorem is already fully proved
under the unambiguous smallModel_sourceCocycleExactRestriction name in
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceCocycleExactRestriction. Its existing
DAG attachment is the one required by the original-model parent, and is preserved.

The sole DAG parent is lem-weil-pbc-strict-local-localized-hom-germ. Its Lean attachment
already points to StrictLocalSmallModel.StrictLocalLocalizedHomGerm; that module imports
the retained small-model theorem privately and applies it in its complete proof.
Its proof text is corrected to name those actual helpers. No dependency edge is removed.
The historical consumer Sheaf.AlgebraicGeometry.StrictLocalLocalizedHomGerm already
re-exports the adopted source implementation, whose private proof import uses the
canonical source cocycle theorem. Neither parent needs this obsolete duplicate.

A full import/declaration search of lean/Sheaf, lean/WeilConjectures and quarantine
finds no importer of the obsolete module and no external reference to its declaration.
The retired module's current path exists, is not an absent quarantined assignment,
and is withdrawn via deleted.txt. No archive, mathematical statement, needed proof,
source-library declaration, source public import or target is removed.

## Old

The old module publicly imports:

```lean
public import WeilConjectures.AlgebraicGeometry.SourceLocalizedCocycleHomology
public import Sheaf.AlgebraicGeometry.StrictHenselizationSchemeSectionsExact
```

Its public signature in namespace AlgebraicGeometry.Etale is verbatim:

```lean
theorem sourceCocycleExactRestriction {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (r : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ) (W : S.Etale)
    (τ : (sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj (op W) ⟶
      upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s) ⋙
        Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          AddCommGrpCat.{v + 1})
    (f : (strictLocalFreeSheaf S.smallEtaleTopology).obj W ⟶ L.X n)
    (hf : f ≫ L.d n (n + 1) = 0) :
    let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)
    let G := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}
    letI := strictHenselization_globalSections_preservesFiniteColimits s
    let c := CohomologyClass.mk (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf)
    let C := (U.mapHomologicalComplex (.up ℤ)).obj L
    let a := (NatTrans.mapHomologicalComplex τ (.up ℤ)).app L
    let x := ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).map
      (sourceFreeSectionsComplexIso W L).hom)
        ((leftHomologyData
          ((CochainComplex.singleFunctor _ 0).obj
            ((strictLocalFreeSheaf S.smallEtaleTopology).obj W)) L n).homologyIso.inv c)
    (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} n).inv.app _ ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
        (DerivedCategory.Q.map a ≫ G.mapDerivedCategoryFactors.inv.app C ≫
          G.mapDerivedCategory.map
            (U.mapDerivedCategoryFactors.inv.app L ≫ U.mapDerivedCategory.map r.inv)) ≫
      (G.mapDerivedCategoryHomologyFunctorIso n).inv.app (U.mapDerivedCategory.obj K.obj))
        x : G.obj ((DerivedCategory.Plus.homologyFunctor _ n).obj
          (U.mapDerivedCategoryPlus.obj K))) =
      (G.map ((U.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K))
        (τ.app ((DerivedCategory.Plus.homologyFunctor _ n).obj K)
          (sourceCocycleHomologySection K L r n W f hf))
```

Its three completely proved private helpers are exactHomologyProjection,
sourceSectionsCocycleRestriction and exactHomologyTransport. They implement the same
calculation already present in the retained small-model module and the canonical source.

## New

The obsolete Sheaf module is withdrawn. The existing original-model provider is
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceCocycleExactRestriction, with this
unchanged signature in namespace AlgebraicGeometry.Etale:

```lean
theorem smallModel_sourceCocycleExactRestriction {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (r : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ) (W : S.Etale)
    (τ : (sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj (op W) ⟶
      upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s) ⋙
        Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          AddCommGrpCat.{v + 1})
    (f : (strictLocalFreeSheaf S.smallEtaleTopology).obj W ⟶ L.X n)
    (hf : f ≫ L.d n (n + 1) = 0) :
    let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)
    let G := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}
    letI := strictHenselizationScheme_globalSections_preservesFiniteColimits s
    let c := CohomologyClass.mk (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf)
    let C := (U.mapHomologicalComplex (.up ℤ)).obj L
    let a := (NatTrans.mapHomologicalComplex τ (.up ℤ)).app L
    let x := ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).map
      (smallModel_sourceFreeSectionsComplexIso W L).hom)
        ((leftHomologyData
          ((CochainComplex.singleFunctor _ 0).obj
            ((strictLocalFreeSheaf S.smallEtaleTopology).obj W)) L n).homologyIso.inv c)
    (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} n).inv.app _ ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
        (DerivedCategory.Q.map a ≫ G.mapDerivedCategoryFactors.inv.app C ≫
          G.mapDerivedCategory.map
            (U.mapDerivedCategoryFactors.inv.app L ≫ U.mapDerivedCategory.map r.inv)) ≫
      (G.mapDerivedCategoryHomologyFunctorIso n).inv.app (U.mapDerivedCategory.obj K.obj))
        x : G.obj ((DerivedCategory.Plus.homologyFunctor _ n).obj
          (U.mapDerivedCategoryPlus.obj K))) =
      (G.map ((U.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K))
        (τ.app ((DerivedCategory.Plus.homologyFunctor _ n).obj K)
          (smallModel_sourceCocycleHomologySection K L r n W f hf))
```

The existing canonical provider remains unchanged at
WeilConjectures.AlgebraicGeometry.SourceCocycleExactRestriction, with the original
source name sourceCocycleExactRestriction. It uses strictLocalization and
strictLocalizationToBase. It is not substituted for the original-model DAG statement.

Only proof text, proof provenance and the item's Lean note are updated in the two node
copies. All statement fields, Lean signatures, attachments, dependencies, unit routes,
source fields and review records stay unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SourceCocycleExactRestriction | F1 | Withdraw the obsolete, unused duplicate. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceCocycleExactRestriction | unclaimed | Existing complete original-model replacement; source unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalLocalizedHomGerm | unclaimed | Sole DAG parent already imports and applies the original-model replacement; source unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalLocalizedHomGerm | unclaimed | Historical listed consumer already re-exports the canonical source; source unchanged. |
| WeilConjectures.AlgebraicGeometry.SourceCocycleExactRestriction | unclaimed | Existing complete canonical theorem retained verbatim. |
| WeilConjectures.AlgebraicGeometry.StrictLocalLocalizedHomGerm | unclaimed | Existing canonical consumer and proof import retained verbatim. |

The complete tools/downstream.py --uses census reports zero downstream modules and
only the obsolete item itself mentioning its theorem. A structural DAG scan finds
exactly the parent described above. A scan of all unit records finds no direct use
of the obsolete path or declaration. The item's unit sk-prop-h2 has empty realized
statement and step arrays; its unit statement and route are not bypassed.
The archived rework rows quoted in the C2 maintenance record are historical evidence;
those former parents have already been rebound/restored and their current sources do
not import the withdrawn module. No quarantine archive is edited or discarded.

## Status

landed 20261022T113942-L-430451 2026-10-22 (merge of deliver/F1/Sheaf.AlgebraicGeometry.SourceCocycleExactRestriction)
