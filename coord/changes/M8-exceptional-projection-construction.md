# AlgebraicGeometry.Etale.exceptionalConstantProjectionMap

## Reason

Share the canonical projection composite through the generic real construction
`exceptionalProjectionConstruction`. Kernel conversion between an expanded concrete tensor
composite and the public map previously exceeded 60 seconds. The public map and the proof's
projection characterization now use exactly the same generic constructor. Its data is the
original sequence of signed symmetry, compactification projection, tensor of the specified
pullback identification, and signed symmetry on the source. There is no new existence choice
or postponed proof in this data.

The existing declaration's signature is verbatim unchanged. Unfolding the new constructor
recovers exactly its old construction, so every map and every target meaning is preserved.
The other two public definitions and all existing theorem signatures are unchanged. Only
the assigned Sheaf module changes; no adopted source-library declaration changes.

## Old

```lean
noncomputable def exceptionalConstantProjectionMap (C : Type (u + 1)) [CommRing C]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (V : DerivedCategory (ModuleCat.{u + 1} C)) (K : DerivedCategoryModule C X) :
    ((exceptionalCoefficientTensor C Y).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj K)).obj V ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj
        (((exceptionalCoefficientTensor C X).obj K).obj V) :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} C) Y).hom.app
      ((constantSheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} C)).mapDerivedCategory.obj V)).app
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj K) ≫
    ((projectionMapOfCompactification (ModuleCat.{u + 1} C) c).app K).app
      ((constantSheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} C)).mapDerivedCategory.obj V) ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).map
      (((derivedTensor (ModuleCat.{u + 1} C) X).obj K).map
          ((exceptionalConstantPullbackIso C f).hom.app V) ≫
        ((derivedTensorSymmetry (ModuleCat.{u + 1} C) X).hom.app K).app
          ((constantSheaf X.smallEtaleTopology
            (ModuleCat.{u + 1} C)).mapDerivedCategory.obj V))
```

## New

```lean
section ProjectionConstruction

variable (A : Type*) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- The canonical projection composite after a specified identification of coefficient pullback.
It applies signed symmetry, the compactification projection map, tensor of the identification,
and signed symmetry on the source. This generic constructor keeps these maps shared when
specialized to constant coefficient complexes.
Source: Zheng, Theorem 2.18(2) and Construction 2.26
(blueprint: lem-pur-etale-exceptional-constant-tensor). -/
noncomputable def exceptionalProjectionConstruction
    {D : Type*} [Category D] {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (H : D ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (H' : D ⥤ DerivedCategory (Sheaf X.smallEtaleTopology A))
    (t : H ⋙ (upperStar A f).leftDerivedFunctor ≅ H') (V : D)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedTensor A Y).obj (H.obj V)).obj
        ((rightDerivedLowerShriekOfCompactification A c).obj K) ⟶
      (rightDerivedLowerShriekOfCompactification A c).obj
        (((derivedTensor A X).obj (H'.obj V)).obj K) :=
  ((derivedTensorSymmetry A Y).hom.app (H.obj V)).app
      ((rightDerivedLowerShriekOfCompactification A c).obj K) ≫
    ((projectionMapOfCompactification A c).app K).app (H.obj V) ≫
    (rightDerivedLowerShriekOfCompactification A c).map
      (((derivedTensor A X).obj K).map (t.hom.app V) ≫
        ((derivedTensorSymmetry A X).hom.app K).app (H'.obj V))

end ProjectionConstruction

noncomputable def exceptionalConstantProjectionMap (C : Type (u + 1)) [CommRing C]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (V : DerivedCategory (ModuleCat.{u + 1} C)) (K : DerivedCategoryModule C X) :
    ((exceptionalCoefficientTensor C Y).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj K)).obj V ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj
        (((exceptionalCoefficientTensor C X).obj K).obj V) :=
  exceptionalProjectionConstruction (ModuleCat.{u + 1} C) c
    (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory
    (exceptionalConstantPullbackIso C f) V K
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor --uses
exceptionalConstantProjectionMap` reports 525 transitive importers and the following three
lexical users. The two consumer modules are unclaimed and are not adapted. Their displayed
projection maps remain the identical canonical composites after unfolding the generic
constructor. Quotient tensor compatibility, normalization, and mate formulas therefore keep
exactly their old hypotheses and conclusions. No consumer adaptation is necessary.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor | M8 | Shared constructor; same canonical map and theorem statement |
| Sheaf.Paper.EtaleQuotientTensorProjection | unclaimed | Same map in quotient tensor compatibility |
| Sheaf.Paper.EtaleSystemQuotientNormalization | unclaimed | Same normalized projection and its transpose |

The new constructor is used only by the assigned module and is attached to its existing DAG
node. All five Challenge targets retain exactly their existing statements and mathematical
meanings. Because a definition in their closure is refactored, this record flags the target
definition review required by stage 2. The old map is recovered by one unfolding, with the
same parameters and no mathematical hypothesis added or removed.

## Status

landed 20261026T002040-L-53023 2026-10-26 (merge of deliver/M8/Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor)
