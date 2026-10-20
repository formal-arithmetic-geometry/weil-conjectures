# AlgebraicGeometry.Scheme.open_union_restriction_comparison_coherence

## Reason

The item is listed in coord/retire-items.tsv. Its current Sheaf copy already has
zero holes and duplicates a completely proved source-library theorem. Both copies
now import exactly the same source restriction maps and isomorphism descent
modules. The inventory's old DIFFERENT classification reflects dependency copies
that the current files no longer import.

The only statement difference is that the Sheaf version binds unused JW and JV.
A scratch theorem with its verbatim signature is proved by directly applying the
source theorem. The kernel accepts that application, so no hypothesis, universe,
comparison map, or pasting equation changes, including for empty, equal and
disjoint opens. The source theorem uses only propext, Classical.choice and Quot.sound.

## Old

The duplicate declaration in Sheaf.AlgebraicGeometry.OpenUnionRestrictionComparisonCoherence:

```lean
theorem open_union_restriction_comparison_coherence
    (X : Scheme.{u}) (W V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊔ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings ((W ⊔ V).ι ⁻¹ᵁ W).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings ((W ⊔ V).ι ⁻¹ᵁ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (((W ⊔ V).ι ⁻¹ᵁ W) ⊓ ((W ⊔ V).ι ⁻¹ᵁ V)).toScheme.toRingedSpace))]
    :
    let L := (schemeOpenRestriction X (W ⊔ V)).mapDerivedCategory
    let JW := (schemeOpenRestriction X W).mapDerivedCategory
    let JV := (schemeOpenRestriction X V).mapDerivedCategory
    let SW := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : W ⊓ V ⟶ W)).mapDerivedCategory
    let SV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : W ⊓ V ⟶ V)).mapDerivedCategory
    let sW := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : W ⊓ V ⟶ W)
    let sV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : W ⊓ V ⟶ V)
    let PW := (schemeOpenOverlapRestriction X
      (homOfLE le_sup_left : W ⟶ W ⊔ V)).mapDerivedCategory
    let PV := (schemeOpenOverlapRestriction X
      (homOfLE le_sup_right : V ⟶ W ⊔ V)).mapDerivedCategory
    let kW := schemeDerivedOpenRestrictionCompIso X (homOfLE le_sup_left : W ⟶ W ⊔ V)
    let kV := schemeDerivedOpenRestrictionCompIso X (homOfLE le_sup_right : V ⟶ W ⊔ V)
    let U := (W ⊔ V).ι ⁻¹ᵁ W
    let T := (W ⊔ V).ι ⁻¹ᵁ V
      let RU := (schemeOpenRestriction (W ⊔ V).toScheme U).mapDerivedCategory
      let RT := (schemeOpenRestriction (W ⊔ V).toScheme T).mapDerivedCategory
      let SU := (schemeOpenOverlapRestriction (W ⊔ V).toScheme
        (homOfLE inf_le_left : U ⊓ T ⟶ U)).mapDerivedCategory
      let ST := (schemeOpenOverlapRestriction (W ⊔ V).toScheme
        (homOfLE inf_le_right : U ⊓ T ⟶ T)).mapDerivedCategory
      let tU := schemeDerivedOpenRestrictionCompIso (W ⊔ V).toScheme
        (homOfLE inf_le_left : U ⊓ T ⟶ U)
      let tT := schemeDerivedOpenRestrictionCompIso (W ⊔ V).toScheme
        (homOfLE inf_le_right : U ⊓ T ⟶ T)
      ∀ (eW : schemeDerivedCategory U.toScheme ≌ schemeDerivedCategory W.toScheme)
        (eV : schemeDerivedCategory T.toScheme ≌ schemeDerivedCategory V.toScheme)
        (qW : RU ⋙ eW.functor ≅ PW) (qV : RT ⋙ eV.functor ≅ PV),
      ∀ (eI : schemeDerivedCategory (U ⊓ T).toScheme ≌
          schemeDerivedCategory (W ⊓ V).toScheme)
        (_qIY : (schemeOpenRestriction (W ⊔ V).toScheme (U ⊓ T)).mapDerivedCategory ⋙
          eI.functor ≅ (schemeOpenOverlapRestriction X
            (homOfLE (inf_le_left.trans le_sup_left) : W ⊓ V ⟶ W ⊔ V)).mapDerivedCategory),
      ∃ (cW : SU ⋙ eI.functor ≅ eW.functor ⋙ SW)
        (cV : ST ⋙ eI.functor ≅ eV.functor ⋙ SV)
        (qI : (L ⋙ (schemeOpenRestriction (W ⊔ V).toScheme (U ⊓ T)).mapDerivedCategory) ⋙
          eI.functor ≅ (schemeOpenRestriction X (W ⊓ V)).mapDerivedCategory),
      (∀ G : schemeDerivedCategory X,
        eI.functor.map (tU.inv.app (L.obj G)) ≫ cW.hom.app (RU.obj (L.obj G)) ≫
          SW.map (qW.hom.app (L.obj G)) ≫ SW.map (kW.hom.app G) ≫ sW.hom.app G =
            qI.hom.app G) ∧
      (∀ G : schemeDerivedCategory X,
        eI.functor.map (tT.inv.app (L.obj G)) ≫ cV.hom.app (RT.obj (L.obj G)) ≫
          SV.map (qV.hom.app (L.obj G)) ≫ SV.map (kV.hom.app G) ≫ sV.hom.app G =
            qI.hom.app G)
```

The consumer Sheaf.AlgebraicGeometry.OpenUnionRestrictionComparisonDiagram has:

```lean
import Sheaf.AlgebraicGeometry.OpenUnionRestrictionComparisonCoherence
```

## New

The Sheaf duplicate is withdrawn through deleted.txt. Its DAG node keeps the same
mathematical statement, proof, dependencies and declaration name, and attaches to
WeilConjectures.AlgebraicGeometry.OpenUnionRestrictionComparisonCoherence, whose
existing declaration is:

```lean
theorem open_union_restriction_comparison_coherence
    (X : Scheme.{u}) (W V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊔ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings ((W ⊔ V).ι ⁻¹ᵁ W).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings ((W ⊔ V).ι ⁻¹ᵁ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (((W ⊔ V).ι ⁻¹ᵁ W) ⊓ ((W ⊔ V).ι ⁻¹ᵁ V)).toScheme.toRingedSpace))]
    :
    let L := (schemeOpenRestriction X (W ⊔ V)).mapDerivedCategory
    let SW := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : W ⊓ V ⟶ W)).mapDerivedCategory
    let SV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : W ⊓ V ⟶ V)).mapDerivedCategory
    let sW := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : W ⊓ V ⟶ W)
    let sV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : W ⊓ V ⟶ V)
    let PW := (schemeOpenOverlapRestriction X
      (homOfLE le_sup_left : W ⟶ W ⊔ V)).mapDerivedCategory
    let PV := (schemeOpenOverlapRestriction X
      (homOfLE le_sup_right : V ⟶ W ⊔ V)).mapDerivedCategory
    let kW := schemeDerivedOpenRestrictionCompIso X (homOfLE le_sup_left : W ⟶ W ⊔ V)
    let kV := schemeDerivedOpenRestrictionCompIso X (homOfLE le_sup_right : V ⟶ W ⊔ V)
    let U := (W ⊔ V).ι ⁻¹ᵁ W
    let T := (W ⊔ V).ι ⁻¹ᵁ V
      let RU := (schemeOpenRestriction (W ⊔ V).toScheme U).mapDerivedCategory
      let RT := (schemeOpenRestriction (W ⊔ V).toScheme T).mapDerivedCategory
      let SU := (schemeOpenOverlapRestriction (W ⊔ V).toScheme
        (homOfLE inf_le_left : U ⊓ T ⟶ U)).mapDerivedCategory
      let ST := (schemeOpenOverlapRestriction (W ⊔ V).toScheme
        (homOfLE inf_le_right : U ⊓ T ⟶ T)).mapDerivedCategory
      let tU := schemeDerivedOpenRestrictionCompIso (W ⊔ V).toScheme
        (homOfLE inf_le_left : U ⊓ T ⟶ U)
      let tT := schemeDerivedOpenRestrictionCompIso (W ⊔ V).toScheme
        (homOfLE inf_le_right : U ⊓ T ⟶ T)
      ∀ (eW : schemeDerivedCategory U.toScheme ≌ schemeDerivedCategory W.toScheme)
        (eV : schemeDerivedCategory T.toScheme ≌ schemeDerivedCategory V.toScheme)
        (qW : RU ⋙ eW.functor ≅ PW) (qV : RT ⋙ eV.functor ≅ PV),
      ∀ (eI : schemeDerivedCategory (U ⊓ T).toScheme ≌
          schemeDerivedCategory (W ⊓ V).toScheme)
        (_qIY : (schemeOpenRestriction (W ⊔ V).toScheme (U ⊓ T)).mapDerivedCategory ⋙
          eI.functor ≅ (schemeOpenOverlapRestriction X
            (homOfLE (inf_le_left.trans le_sup_left) : W ⊓ V ⟶ W ⊔ V)).mapDerivedCategory),
      ∃ (cW : SU ⋙ eI.functor ≅ eW.functor ⋙ SW)
        (cV : ST ⋙ eI.functor ≅ eV.functor ⋙ SV)
        (qI : (L ⋙ (schemeOpenRestriction (W ⊔ V).toScheme (U ⊓ T)).mapDerivedCategory) ⋙
          eI.functor ≅ (schemeOpenRestriction X (W ⊓ V)).mapDerivedCategory),
      (∀ G : schemeDerivedCategory X,
        eI.functor.map (tU.inv.app (L.obj G)) ≫ cW.hom.app (RU.obj (L.obj G)) ≫
          SW.map (qW.hom.app (L.obj G)) ≫ SW.map (kW.hom.app G) ≫ sW.hom.app G =
            qI.hom.app G) ∧
      (∀ G : schemeDerivedCategory X,
        eI.functor.map (tT.inv.app (L.obj G)) ≫ cV.hom.app (RT.obj (L.obj G)) ≫
          SV.map (qV.hom.app (L.obj G)) ≫ SV.map (kV.hom.app G) ≫ sV.hom.app G =
            qI.hom.app G)
```

The consumer's only edit is:

```lean
import WeilConjectures.AlgebraicGeometry.OpenUnionRestrictionComparisonCoherence
```

Its theorem signature and complete proof stay verbatim. No source-library file is
changed. The shared node remains a dependency of the parent comparison-diagram
node, preserving that argument and every unit route. No target meaning changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.OpenUnionRestrictionComparisonCoherence | M6 (assigned item) | Retire duplicate theorem and private cancellation helper. |
| Sheaf.AlgebraicGeometry.OpenUnionRestrictionComparisonDiagram | unclaimed | Replace its private proof import; unchanged statement and proof compile. |

The downstream script lists only the comparison-diagram module. Searches across
both Lean roots and quarantine find no other importer of the withdrawn module.
The source comparison diagram already imports the source coherence theorem.
Only the coherence node and its parent diagram node mention this node in the DAG;
the parent keeps the same dependency, now resolved to the source declaration.
The unit's realized statement and step lists contain neither node.

## Status

landed 20261020T221253-L-4167184 2026-10-20 (merge of deliver/M6/Sheaf.AlgebraicGeometry.OpenUnionRestrictionComparisonCoherence)
