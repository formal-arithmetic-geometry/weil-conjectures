# AlgebraicGeometry.Etale.exists_higherDirectImage_limit_presheaf_class_cover

## Reason

Retire the duplicate listed in `coord/retire-items.tsv` for
`Sheaf.AlgebraicGeometry.HigherDirectImageLimitPresheafClassDescent`.
The adopted source theorem proves exactly the same conclusion without the unused
`hK` transition equation. Every other binder and the conclusion agree. Its proof
uses the same affine representative theorem, affine cover, presentation transport,
and restriction naturality as the duplicate. No adopted source file is changed.

The duplicate's sole direct Lean importer is migrated to the source theorem in
this packet. Its call drops the unnecessary `hK` argument, while its own public
signature and docstring stay verbatim. The local `_hK` binding retains the explicit
hypothesis reference required by the unused-variable linter.

The existing DAG node is attached to the adopted source theorem, with its Lean
statement recorded verbatim. Its mathematical statement, proof steps and dependency
edges stay: the stronger theorem proves the recorded claim. The sole semantic
parent remains attached to the same node and uses the same local lifting argument.
No unit route or target statement changes. This changes no definition.

## Old

Module: `Sheaf.AlgebraicGeometry.HigherDirectImageLimitPresheafClassDescent`

```lean
theorem exists_higherDirectImage_limit_presheaf_class_cover {S : Scheme.{v}}
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S)
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i : Iᵒᵖ, QuasiCompact (D.obj i).hom]
    [∀ i : Iᵒᵖ, QuasiSeparated (D.obj i).hom]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eH : ∀ i : I, H.obj i ≅
      (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i))
    (hH : ∀ {i j : I} (f : i ⟶ j), H.map f =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{v + 1} (c.π.app (op j)).left (D.map f.op).left
          (c.π.app (op i)).left
          (congrArg (fun t => t.left) (c.w f.op)).symm).hom.app (F i) ≫
        (((c.π.app (op j)).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ (eH j).inv)
    [HasColimit H] (p : ℕ)
    (K : I ⥤ Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eK : ∀ i : I, K.obj i ≅
      (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
        (R+(((D.obj (op i)).hom)_*[AddCommGrpCat.{v + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (F i))))
    (hK : ∀ {i j : I} (f : i ⟶ j), K.map f =
      (eK i).hom ≫ abelianHigherDirectImageMap (D.map f.op).left
        (D.obj (op i)).hom (D.obj (op j)).hom (Over.w (D.map f.op)) p
        (F i) (F j) (φ f) ≫ (eK j).inv)
    (η : K ⟶ (Functor.const I).obj
      ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
        (R+((c.pt.hom)_*[AddCommGrpCat.{v + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (colimit H)))))
    (hη : ∀ i : I, η.app i = (eK i).hom ≫
      abelianHigherDirectImageMap (c.π.app (op i)).left (D.obj (op i)).hom c.pt.hom
        (Over.w (c.π.app (op i))) p (F i) (colimit H)
        ((eH i).inv ≫ colimit.ι H i)) :
    let T := (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
      (R+((c.pt.hom)_*[AddCommGrpCat.{v + 1}]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (colimit H)))
    let P := (uliftYoneda.{v + 1} ⋙
      (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
      presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{v + 1} ⋙
      upperStar AddCommGrpCat.{v + 1} c.pt.hom ⋙
      DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj
          (((DerivedCategory.Plus.singleFunctor _ 0).obj (colimit H))⟦(p : ℤ)⟧)
    ∃ (e : (presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj P ≅ T),
      ∀ (U : S.Etale) (z : P.obj (op U)),
        ∃ (R : Sieve U), R ∈ S.smallEtaleTopology U ∧
          ∀ {V : S.Etale} (f : V ⟶ U), R f →
            ∃ (i : I) (y : (K.obj i).obj.obj (op V)),
              (η.app i).hom.app (op V) y =
                T.obj.map f.op
                  ((toSheafify S.smallEtaleTopology P ≫ e.hom.hom).app (op U) z)
```

## New

The duplicate module is withdrawn. Its existing upstream replacement is in
`WeilConjectures.AlgebraicGeometry.HigherDirectImageLimitPresheafClassDescent`:

```lean
theorem exists_higherDirectImage_limit_presheaf_class_cover {S : Scheme.{v}}
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S)
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i : Iᵒᵖ, QuasiCompact (D.obj i).hom]
    [∀ i : Iᵒᵖ, QuasiSeparated (D.obj i).hom]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eH : ∀ i : I, H.obj i ≅
      (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i))
    (hH : ∀ {i j : I} (f : i ⟶ j), H.map f =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{v + 1} (c.π.app (op j)).left (D.map f.op).left
          (c.π.app (op i)).left
          (congrArg (fun t => t.left) (c.w f.op)).symm).hom.app (F i) ≫
        (((c.π.app (op j)).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ (eH j).inv)
    [HasColimit H] (p : ℕ)
    (K : I ⥤ Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eK : ∀ i : I, K.obj i ≅
      (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
        (R+(((D.obj (op i)).hom)_*[AddCommGrpCat.{v + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (F i))))
    (η : K ⟶ (Functor.const I).obj
      ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
        (R+((c.pt.hom)_*[AddCommGrpCat.{v + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (colimit H)))))
    (hη : ∀ i : I, η.app i = (eK i).hom ≫
      abelianHigherDirectImageMap (c.π.app (op i)).left (D.obj (op i)).hom c.pt.hom
        (Over.w (c.π.app (op i))) p (F i) (colimit H)
        ((eH i).inv ≫ colimit.ι H i)) :
    let T := (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
      (R+((c.pt.hom)_*[AddCommGrpCat.{v + 1}]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (colimit H)))
    let P := (uliftYoneda.{v + 1} ⋙
      (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
      presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{v + 1} ⋙
      upperStar AddCommGrpCat.{v + 1} c.pt.hom ⋙
      DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj
          (((DerivedCategory.Plus.singleFunctor _ 0).obj (colimit H))⟦(p : ℤ)⟧)
    ∃ (e : (presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj P ≅ T),
      ∀ (U : S.Etale) (z : P.obj (op U)),
        ∃ (R : Sieve U), R ∈ S.smallEtaleTopology U ∧
          ∀ {V : S.Etale} (f : V ⟶ U), R f →
            ∃ (i : I) (y : (K.obj i).obj.obj (op V)),
              (η.app i).hom.app (op V) y =
                T.obj.map f.op
                  ((toSheafify S.smallEtaleTopology P ≫ e.hom.hom).app (op U) z)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitPresheafClassDescent | R5 | Withdraw duplicate; retain the adopted source theorem unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassDescent | unclaimed | Replace its private proof import and omit hK at the theorem call; public signature unchanged. |

`tools/downstream.py --uses` lists precisely these two modules (the first is the
declaration's own module); the import downstream list contains only the second.
No quarantined Lean file imports the retired module or names its theorem.
The sole semantic DAG parent is
`sbc-lem-higher-direct-image-limit-class-descent`; its existing dependency on
`lem-sbc-higher-direct-image-limit-presheaf-class-cover` is preserved and now
resolves to the source theorem. The unit `sk-lem-failure-field` has no realized
attachment to the retired file; its statement and steps are untouched.

## Status

landed 20261021T111549-L-310510 2026-10-21 (merge of deliver/R5/Sheaf.AlgebraicGeometry.HigherDirectImageLimitPresheafClassDescent)
