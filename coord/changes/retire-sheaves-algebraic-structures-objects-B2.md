# CategoryTheory.sheaves_algebraicStructures_objects_with_finiteProducts

## Reason

Retire the duplicate module listed in coord/retire-items.tsv. Its sole theorem packages
Mathlib's existing finite-products instance together with the already proved upstream
CategoryTheory.sheaves_algebraicStructures_objects. No declaration in either source root
uses the extra wrapper. The node already names the upstream declaration, but its module
and file still point to the duplicate; correct that attachment. The blueprint unit is kept.

## Old

The retired wrapper had this signature, verbatim:

```lean
theorem sheaves_algebraicStructures_objects_with_finiteProducts
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    Nonempty (HasFiniteProducts (Sheaf J (Type (max u v w)))) ∧
    (∀ (F G : Sheaf J (Type (max u v w))) (U : Cᵒᵖ),
      (F ⊗ G).obj.obj U = (F.obj.obj U × G.obj.obj U)) ∧
    (∀ U : Cᵒᵖ,
      Subsingleton ((𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U) ∧
      Nonempty ((𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U)) ∧
    (∃ (F : Sheaf J AddCommGrpCat.{max u v w} ⥤ CommGrp (Sheaf J (Type (max u v w))))
        (G : CommGrp (Sheaf J (Type (max u v w))) ⥤ Sheaf J AddCommGrpCat.{max u v w})
        (hF : F ⋙ CommGrp.forget _ = sheafCompose J (forget AddCommGrpCat.{max u v w})),
      G ⋙ sheafCompose J (forget AddCommGrpCat.{max u v w}) = CommGrp.forget _ ∧
      F ⋙ G = 𝟭 (Sheaf J AddCommGrpCat.{max u v w}) ∧
      G ⋙ F = 𝟭 (CommGrp (Sheaf J (Type (max u v w)))) ∧
      (∀ (A : Sheaf J AddCommGrpCat.{max u v w}) (U : Cᵒᵖ),
        (∀ a b : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.mul (X := (F.obj A).X)).hom.app U (a, b)) =
            (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a) +
              (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.one (X := (F.obj A).X)).hom.app U t) =
            (0 : A.obj.obj U)) ∧
        (∀ a : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((GrpObj.inv (X := (F.obj A).X)).hom.app U a) =
            -(show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a))) ∧
      (∀ (A B : Sheaf J AddCommGrpCat.{max u v w})
          (α : (sheafCompose J (forget AddCommGrpCat.{max u v w})).obj A ⟶
            (sheafCompose J (forget AddCommGrpCat.{max u v w})).obj B),
        (∃ f : A ⟶ B, (sheafCompose J (forget AddCommGrpCat.{max u v w})).map f = α) ↔
          IsMonHom (show (F.obj A).X ⟶ (F.obj B).X from
            (eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) ∧
          GrpObj.inv (X := (F.obj A).X) ≫
              ((eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) =
            ((eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) ≫
              GrpObj.inv (X := (F.obj B).X))) ∧
    (∃ (F : Sheaf J CommRingCat.{max u v w} ⥤ CommRingObjCat (Sheaf J (Type (max u v w))))
        (G : CommRingObjCat (Sheaf J (Type (max u v w))) ⥤ Sheaf J CommRingCat.{max u v w})
        (hF : F ⋙ CommRingObjCat.forget _ = sheafCompose J (forget CommRingCat.{max u v w})),
      G ⋙ sheafCompose J (forget CommRingCat.{max u v w}) = CommRingObjCat.forget _ ∧
      F ⋙ G = 𝟭 (Sheaf J CommRingCat.{max u v w}) ∧
      G ⋙ F = 𝟭 (CommRingObjCat (Sheaf J (Type (max u v w)))) ∧
      (∀ (A : Sheaf J CommRingCat.{max u v w}) (U : Cᵒᵖ),
        (∀ a b : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((AddMonObj.add (X := (F.obj A).X)).hom.app U (a, b)) =
            (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a) +
              (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((AddMonObj.zero (X := (F.obj A).X)).hom.app U t) =
            (0 : A.obj.obj U)) ∧
        (∀ a : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((AddGrpObj.neg (X := (F.obj A).X)).hom.app U a) =
            -(show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a)) ∧
        (∀ a b : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.mul (X := (F.obj A).X)).hom.app U (a, b)) =
            (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a) *
              (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.one (X := (F.obj A).X)).hom.app U t) =
            (1 : A.obj.obj U))) ∧
      (∀ (A B : Sheaf J CommRingCat.{max u v w})
          (α : (sheafCompose J (forget CommRingCat.{max u v w})).obj A ⟶
            (sheafCompose J (forget CommRingCat.{max u v w})).obj B),
        (∃ f : A ⟶ B, (sheafCompose J (forget CommRingCat.{max u v w})).map f = α) ↔
          IsRingHom (show (F.obj A).X ⟶ (F.obj B).X from
            (eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) ∧
          AddGrpObj.neg (X := (F.obj A).X) ≫
              ((eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) =
            ((eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) ≫
              AddGrpObj.neg (X := (F.obj B).X)))
```

## New

Remove the unused wrapper and withdraw its module using deleted.txt. Redirect consumers
to the upstream twin; the held consumers only change private imports. LocalizationInverseImageCoherence
also drops its unused ExactFunctorDerivedFunctor proof import after repeated whole-file
60-second timeouts; the minimal removal compiled in 18.2 seconds with all proofs unchanged.
The node points to this unchanged existing upstream declaration:

```lean
theorem sheaves_algebraicStructures_objects
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    (∀ (F G : Sheaf J (Type (max u v w))) (U : Cᵒᵖ),
      (F ⊗ G).obj.obj U = (F.obj.obj U × G.obj.obj U)) ∧
    (∀ U : Cᵒᵖ,
      Subsingleton ((𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U) ∧
      Nonempty ((𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U)) ∧
    (∃ (F : Sheaf J AddCommGrpCat.{max u v w} ⥤ CommGrp (Sheaf J (Type (max u v w))))
        (G : CommGrp (Sheaf J (Type (max u v w))) ⥤ Sheaf J AddCommGrpCat.{max u v w})
        (hF : F ⋙ CommGrp.forget _ = sheafCompose J (forget AddCommGrpCat.{max u v w})),
      G ⋙ sheafCompose J (forget AddCommGrpCat.{max u v w}) = CommGrp.forget _ ∧
      F ⋙ G = 𝟭 (Sheaf J AddCommGrpCat.{max u v w}) ∧
      G ⋙ F = 𝟭 (CommGrp (Sheaf J (Type (max u v w)))) ∧
      (∀ (A : Sheaf J AddCommGrpCat.{max u v w}) (U : Cᵒᵖ),
        (∀ a b : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.mul (X := (F.obj A).X)).hom.app U (a, b)) =
            (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a) +
              (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.one (X := (F.obj A).X)).hom.app U t) =
            (0 : A.obj.obj U)) ∧
        (∀ a : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((GrpObj.inv (X := (F.obj A).X)).hom.app U a) =
            -(show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a))) ∧
      (∀ (A B : Sheaf J AddCommGrpCat.{max u v w})
          (α : (sheafCompose J (forget AddCommGrpCat.{max u v w})).obj A ⟶
            (sheafCompose J (forget AddCommGrpCat.{max u v w})).obj B),
        (∃ f : A ⟶ B, (sheafCompose J (forget AddCommGrpCat.{max u v w})).map f = α) ↔
          IsMonHom (show (F.obj A).X ⟶ (F.obj B).X from
            (eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) ∧
          GrpObj.inv (X := (F.obj A).X) ≫
              ((eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) =
            ((eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) ≫
              GrpObj.inv (X := (F.obj B).X))) ∧
    (∃ (F : Sheaf J CommRingCat.{max u v w} ⥤ CommRingObjCat (Sheaf J (Type (max u v w))))
        (G : CommRingObjCat (Sheaf J (Type (max u v w))) ⥤ Sheaf J CommRingCat.{max u v w})
        (hF : F ⋙ CommRingObjCat.forget _ = sheafCompose J (forget CommRingCat.{max u v w})),
      G ⋙ sheafCompose J (forget CommRingCat.{max u v w}) = CommRingObjCat.forget _ ∧
      F ⋙ G = 𝟭 (Sheaf J CommRingCat.{max u v w}) ∧
      G ⋙ F = 𝟭 (CommRingObjCat (Sheaf J (Type (max u v w)))) ∧
      (∀ (A : Sheaf J CommRingCat.{max u v w}) (U : Cᵒᵖ),
        (∀ a b : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((AddMonObj.add (X := (F.obj A).X)).hom.app U (a, b)) =
            (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a) +
              (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((AddMonObj.zero (X := (F.obj A).X)).hom.app U t) =
            (0 : A.obj.obj U)) ∧
        (∀ a : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((AddGrpObj.neg (X := (F.obj A).X)).hom.app U a) =
            -(show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a)) ∧
        (∀ a b : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.mul (X := (F.obj A).X)).hom.app U (a, b)) =
            (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a) *
              (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.one (X := (F.obj A).X)).hom.app U t) =
            (1 : A.obj.obj U))) ∧
      (∀ (A B : Sheaf J CommRingCat.{max u v w})
          (α : (sheafCompose J (forget CommRingCat.{max u v w})).obj A ⟶
            (sheafCompose J (forget CommRingCat.{max u v w})).obj B),
        (∃ f : A ⟶ B, (sheafCompose J (forget CommRingCat.{max u v w})).map f = α) ↔
          IsRingHom (show (F.obj A).X ⟶ (F.obj B).X from
            (eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) ∧
          AddGrpObj.neg (X := (F.obj A).X) ≫
              ((eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) =
            ((eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) ≫
              AddGrpObj.neg (X := (F.obj B).X)))
```

Finite products remain available from CategoryTheory.Sheaf.instHasFiniteProducts in
Mathlib.CategoryTheory.Sites.Limits, already publicly imported by the upstream twin.
No definition or target statement changes, and no source-library file is edited.

## Users

A whole-library text search finds no use of the removed wrapper outside its declaration.
These are all seven direct module consumers; declarations and proofs are unchanged.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineComponentSiteProjection | unclaimed | Remove the obsolete private import; existing imports supply the upstream API. |
| Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite | unclaimed | Replace only the private import by the upstream twin. |
| Sheaf.CategoryTheory.ConstantLeftModuleInverseImage | H3 | Remove the obsolete private import; existing imports supply the upstream API. |
| Sheaf.CategoryTheory.LocalizationInverseImageCoherence | A4 | Remove the obsolete private import and the unused ExactFunctorDerivedFunctor proof import; existing imports supply the API. The latter avoids the diagnosed timeout. |
| Sheaf.CategoryTheory.Sites.GeometricInverseImageExact | B4 | Remove the obsolete private import; existing imports supply the API. |
| Sheaf.TraceFormula.BigSmallEtaleExactRetraction | unclaimed | Replace only the private import by the upstream twin. |
| Sheaf.TraceFormula.BigSmallEtaleLocalizationDerivedPushforward | unclaimed | Replace only the private import by the upstream twin. |

Repair of returned head 01cb941338: the adapted module
Sheaf.CategoryTheory.LocalizationInverseImageCoherence is held by A4. The consumer
copy was refreshed from current main before reapplying only the two private import
removals, preserving all newly landed proofs, signatures and visibility. The current holder
of Sheaf.CategoryTheory.Sites.GeometricInverseImageExact is B4; its only adaptation
is the obsolete private import removal recorded above.

## Status

landed 20261020T135348-L-1813867 2026-10-20 (merge of deliver/B2/Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects)
