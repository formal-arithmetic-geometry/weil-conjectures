# AlgebraicGeometry.higherDirectImage_baseChange_of_limit

## Reason

The theorem and all public imports stay verbatim. The proof introduces elaboration
commands: it selects the direct category instance for morphism notation, opens
`Etale` for the proof helpers, and controls transparency while comparing inverse
image and higher-image functor endpoints. The selected category instance and the
bundled-category instance are definitionally equal; no mathematical object, map,
hypothesis or conclusion changes. The two inverse-image constructors are marked
irreducible locally only. The unused-variable lint setting is scoped to the
immutable theorem, whose torsion hypothesis is retained.

These commands are recorded because the static preflight treats new elaboration
commands as a possible change to what importers see. Existing public declarations,
attributes on source declarations, data definitions and target meanings are
preserved. The consumer call in `SmoothBaseChangeLimit` uses the identical theorem
signature and requires no adaptation. No module held by another group is edited.

## Old

The original declaration is:

```lean
theorem higherDirectImage_baseChange_of_limit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (DX DY DS DT : Iᵒᵖ ⥤ Scheme.{u})
    (cX : Cone DX) (hcX : IsLimit cX)
    (cY : Cone DY) (hcY : IsLimit cY)
    (cS : Cone DS) (hcS : IsLimit cS)
    (cT : Cone DT) (hcT : IsLimit cT)
    (ηf : DX ⟶ DS) (ηe : DY ⟶ DT) (ηg : DT ⟶ DS) (ηh : DY ⟶ DX)
    (f : cX.pt ⟶ cS.pt) (e : cY.pt ⟶ cT.pt)
    (g : cT.pt ⟶ cS.pt) (h : cY.pt ⟶ cX.pt)
    (hf : ∀ i : Iᵒᵖ, cX.π.app i ≫ ηf.app i = f ≫ cS.π.app i)
    (he : ∀ i : Iᵒᵖ, cY.π.app i ≫ ηe.app i = e ≫ cT.π.app i)
    (hg : ∀ i : Iᵒᵖ, cT.π.app i ≫ ηg.app i = g ≫ cS.π.app i)
    (hh : ∀ i : Iᵒᵖ, cY.π.app i ≫ ηh.app i = h ≫ cX.π.app i)
    (sq : ChosenCartesianSquare e h g f)
    (sqi : ∀ i : Iᵒᵖ,
      ChosenCartesianSquare (ηe.app i) (ηh.app i) (ηg.app i) (ηf.app i))
    [∀ i : Iᵒᵖ, QuasiCompact (ηg.app i)] [∀ i : Iᵒᵖ, QuasiSeparated (ηg.app i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DY.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DT.map a)]
    (Fi : ∀ i : Iᵒᵖ,
      Sheaf (DT.obj i).smallEtaleTopology AddCommGrpCat.{u + 1})
    (torsionFi : ∀ i : Iᵒᵖ, CategoryTheory.Sheaf.IsTorsion (Fi i))
    (φ : ∀ {i j : I} (a : i ⟶ j),
      (Etale.upperStar AddCommGrpCat.{u + 1} (DT.map a.op)).obj (Fi (op i)) ⟶ Fi (op j))
    (hφid : ∀ i : I,
      φ (𝟙 i) = eqToHom (congrArg
        (fun a : DT.obj (op i) ⟶ DT.obj (op i) ↦
          (Etale.upperStar AddCommGrpCat.{u + 1} a).obj (Fi (op i)))
        (DT.map_id (op i))) ≫
        (Etale.upperStarId AddCommGrpCat.{u + 1} (DT.obj (op i))).hom.app (Fi (op i)))
    (hφcomp : ∀ {i j k : I} (a : i ⟶ j) (b : j ⟶ k),
      φ (a ≫ b) = (Etale.upperStarComp AddCommGrpCat.{u + 1}
        (DT.map b.op) (DT.map a.op) (DT.map (a ≫ b).op)
        (DT.map_comp b.op a.op)).hom.app (Fi (op i)) ≫
        (Etale.upperStar AddCommGrpCat.{u + 1} (DT.map b.op)).map (φ a) ≫ φ b)
    (D : I ⥤ Sheaf cT.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (ιF : ∀ i : I, D.obj i ≅
      (Etale.upperStar AddCommGrpCat.{u + 1} (cT.π.app (op i))).obj (Fi (op i)))
    (hD : ∀ {i j : I} (a : i ⟶ j),
      D.map a ≫ (ιF j).hom = (ιF i).hom ≫
        (Etale.upperStarComp AddCommGrpCat.{u + 1} (cT.π.app (op j))
          (DT.map a.op) (cT.π.app (op i)) (cT.w a.op).symm).hom.app (Fi (op i)) ≫
        (Etale.upperStar AddCommGrpCat.{u + 1} (cT.π.app (op j))).map (φ a))
    (cF : Cocone D) (hcF : IsColimit cF)
    (q : ℕ)
    (hbase : ∀ i : Iᵒᵖ, IsIso ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (DX.obj i).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        (sqi i).toCommSq).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf (DT.obj i).smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
          (Fi i))))) :
    IsIso ((DerivedCategory.Plus.homologyFunctor
      (Sheaf cX.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf cT.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj cF.pt)))
```

The original namespace began without the new commands:

```lean
namespace AlgebraicGeometry
```

## New

The declaration is identical:

```lean
theorem higherDirectImage_baseChange_of_limit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (DX DY DS DT : Iᵒᵖ ⥤ Scheme.{u})
    (cX : Cone DX) (hcX : IsLimit cX)
    (cY : Cone DY) (hcY : IsLimit cY)
    (cS : Cone DS) (hcS : IsLimit cS)
    (cT : Cone DT) (hcT : IsLimit cT)
    (ηf : DX ⟶ DS) (ηe : DY ⟶ DT) (ηg : DT ⟶ DS) (ηh : DY ⟶ DX)
    (f : cX.pt ⟶ cS.pt) (e : cY.pt ⟶ cT.pt)
    (g : cT.pt ⟶ cS.pt) (h : cY.pt ⟶ cX.pt)
    (hf : ∀ i : Iᵒᵖ, cX.π.app i ≫ ηf.app i = f ≫ cS.π.app i)
    (he : ∀ i : Iᵒᵖ, cY.π.app i ≫ ηe.app i = e ≫ cT.π.app i)
    (hg : ∀ i : Iᵒᵖ, cT.π.app i ≫ ηg.app i = g ≫ cS.π.app i)
    (hh : ∀ i : Iᵒᵖ, cY.π.app i ≫ ηh.app i = h ≫ cX.π.app i)
    (sq : ChosenCartesianSquare e h g f)
    (sqi : ∀ i : Iᵒᵖ,
      ChosenCartesianSquare (ηe.app i) (ηh.app i) (ηg.app i) (ηf.app i))
    [∀ i : Iᵒᵖ, QuasiCompact (ηg.app i)] [∀ i : Iᵒᵖ, QuasiSeparated (ηg.app i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DY.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DT.map a)]
    (Fi : ∀ i : Iᵒᵖ,
      Sheaf (DT.obj i).smallEtaleTopology AddCommGrpCat.{u + 1})
    (torsionFi : ∀ i : Iᵒᵖ, CategoryTheory.Sheaf.IsTorsion (Fi i))
    (φ : ∀ {i j : I} (a : i ⟶ j),
      (Etale.upperStar AddCommGrpCat.{u + 1} (DT.map a.op)).obj (Fi (op i)) ⟶ Fi (op j))
    (hφid : ∀ i : I,
      φ (𝟙 i) = eqToHom (congrArg
        (fun a : DT.obj (op i) ⟶ DT.obj (op i) ↦
          (Etale.upperStar AddCommGrpCat.{u + 1} a).obj (Fi (op i)))
        (DT.map_id (op i))) ≫
        (Etale.upperStarId AddCommGrpCat.{u + 1} (DT.obj (op i))).hom.app (Fi (op i)))
    (hφcomp : ∀ {i j k : I} (a : i ⟶ j) (b : j ⟶ k),
      φ (a ≫ b) = (Etale.upperStarComp AddCommGrpCat.{u + 1}
        (DT.map b.op) (DT.map a.op) (DT.map (a ≫ b).op)
        (DT.map_comp b.op a.op)).hom.app (Fi (op i)) ≫
        (Etale.upperStar AddCommGrpCat.{u + 1} (DT.map b.op)).map (φ a) ≫ φ b)
    (D : I ⥤ Sheaf cT.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (ιF : ∀ i : I, D.obj i ≅
      (Etale.upperStar AddCommGrpCat.{u + 1} (cT.π.app (op i))).obj (Fi (op i)))
    (hD : ∀ {i j : I} (a : i ⟶ j),
      D.map a ≫ (ιF j).hom = (ιF i).hom ≫
        (Etale.upperStarComp AddCommGrpCat.{u + 1} (cT.π.app (op j))
          (DT.map a.op) (cT.π.app (op i)) (cT.w a.op).symm).hom.app (Fi (op i)) ≫
        (Etale.upperStar AddCommGrpCat.{u + 1} (cT.π.app (op j))).map (φ a))
    (cF : Cocone D) (hcF : IsColimit cF)
    (q : ℕ)
    (hbase : ∀ i : Iᵒᵖ, IsIso ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (DX.obj i).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        (sqi i).toCommSq).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf (DT.obj i).smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
          (Fi i))))) :
    IsIso ((DerivedCategory.Plus.homologyFunctor
      (Sheaf cX.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf cT.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj cF.pt)))
```

The new commands inside the namespace, before private helpers, are:

```lean
attribute [-instance] CategoryTheory.catToReflQuiver
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
```

After the private helper namespace closes, before the theorem, the commands are:

```lean
open Etale

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Keep inverse-image objects in their functorial form during endpoint comparison.
attribute [local irreducible] Etale.upperStar Etale.lowerStar

-- The immutable statement retains torsion; continuity works for all abelian sheaves.
set_option linter.unusedVariables false in
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.HigherDirectImagesLimits | K6 | Item; statement and public imports preserved verbatim. |
| Sheaf.AlgebraicGeometry.SmoothBaseChangeLimit | unclaimed | Direct importer and theorem caller; unchanged signature, no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGenericDirectImageExchange | unclaimed | Transitive importer; no declaration or definition changes. |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | unclaimed | Transitive importer; no declaration or definition changes. |
| Sheaf.AlgebraicGeometry.FieldExtensionExchange | unclaimed | Transitive importer; no declaration or definition changes. |
| Sheaf.AlgebraicGeometry.OpenExchangeSeparableClosureReduction | unclaimed | Transitive importer; no declaration or definition changes. |
| Sheaf.AlgebraicGeometry.SeparableFieldExtensionExchange | unclaimed | Transitive importer; no declaration or definition changes. |
| Sheaf.AlgebraicGeometry.NormalGenericFibreVanishing | unclaimed | Quarantined direct public importer; preserved. |
| Sheaf.AlgebraicGeometry.OpenProductExchange | unclaimed | Quarantined direct private importer; preserved. |
| Sheaf.AlgebraicGeometry.AbelianArbitrarySchemeUntensoredBaseChange | unclaimed | Quarantined direct private importer; preserved. |
| Sheaf.AlgebraicGeometry.PunctualTensorBaseChange | unclaimed | Quarantined direct private importer; preserved. |

The table includes every module printed by `tools/downstream.py` with
`--uses higherDirectImage_baseChange_of_limit`, plus the quarantined direct
importers found by an import search. Existing consumer files are unchanged.

## Status

landed 20261020T211752-L-3499036 2026-10-20 (merge of deliver/K6/Sheaf.AlgebraicGeometry.HigherDirectImagesLimits)
