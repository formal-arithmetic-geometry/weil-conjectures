# AlgebraicGeometry.Etale.exists_higherDirectImage_limit_fiber_rep

## Reason

Complete the duplicate retirement listed in coord/retire-items.tsv. The source
module proves the same fiber class descent result without the unused hK
hypothesis. Every other binder and the conclusion agree verbatim. After removing
the duplicate's local unused-hypothesis binding, both proof bodies are identical.
The source uses the same presheaf class-cover theorem and pointed-cover argument.

The recorded consumer Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem has
already been retired. Its surviving source counterpart imports the source class
descent module and calls the theorem without hK. No current Lean module imports
the duplicate, including quarantined modules. tools/downstream.py reports zero
modules downstream of it. The only semantic parent is
sbc-lem-higher-direct-image-limit; its unchanged Lean attachment is the surviving
source system theorem, which already applies this source class descent theorem.

Reattach the existing class descent node to the source theorem and preserve its
mathematical statement, proof steps, and dependency edges. No mathematical node,
unit route, definition, target statement, or adopted source file changes.

## Old

Module: Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassDescent

```lean
theorem exists_higherDirectImage_limit_fiber_rep {S : Scheme.{v}}
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
    [HasColimit K]
    (η : K ⟶ (Functor.const I).obj
      ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
        (R+((c.pt.hom)_*[AddCommGrpCat.{v + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (colimit H)))))
    (hη : ∀ i : I, η.app i = (eK i).hom ≫
      abelianHigherDirectImageMap (c.π.app (op i)).left (D.obj (op i)).hom c.pt.hom
        (Over.w (c.π.app (op i))) p (F i) (colimit H)
        ((eH i).inv ≫ colimit.ι H i)) (s : S) :
    ∀ x : ((S.uliftPointSmallEtale s).sheafFiber (A := AddCommGrpCat.{v + 1})).obj
      ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
        (R+((c.pt.hom)_*[AddCommGrpCat.{v + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (colimit H)))),
      ∃ (i : I)
        (y : ((S.uliftPointSmallEtale s).sheafFiber
          (A := AddCommGrpCat.{v + 1})).obj (K.obj i)),
        (((S.uliftPointSmallEtale s).sheafFiber
          (A := AddCommGrpCat.{v + 1})).map (η.app i)) y = x
```

## New

Module: WeilConjectures.AlgebraicGeometry.HigherDirectImageLimitClassDescent

```lean
theorem exists_higherDirectImage_limit_fiber_rep {S : Scheme.{v}}
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
    [HasColimit K]
    (η : K ⟶ (Functor.const I).obj
      ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
        (R+((c.pt.hom)_*[AddCommGrpCat.{v + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (colimit H)))))
    (hη : ∀ i : I, η.app i = (eK i).hom ≫
      abelianHigherDirectImageMap (c.π.app (op i)).left (D.obj (op i)).hom c.pt.hom
        (Over.w (c.π.app (op i))) p (F i) (colimit H)
        ((eH i).inv ≫ colimit.ι H i)) (s : S) :
    ∀ x : ((S.uliftPointSmallEtale s).sheafFiber (A := AddCommGrpCat.{v + 1})).obj
      ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
        (R+((c.pt.hom)_*[AddCommGrpCat.{v + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (colimit H)))),
      ∃ (i : I)
        (y : ((S.uliftPointSmallEtale s).sheafFiber
          (A := AddCommGrpCat.{v + 1})).obj (K.obj i)),
        (((S.uliftPointSmallEtale s).sheafFiber
          (A := AddCommGrpCat.{v + 1})).map (η.app i)) y = x
```

The old module is withdrawn through deleted.txt. The existing declaration name
is retained on the source theorem; the omitted hK hypothesis was unused in the
old proof. Existing compatibility data in the parent remain unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassDescent | U1 | Withdraw duplicate. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem | absent, already retired | Historical inventory consumer; no source remains to adapt. |
| WeilConjectures.AlgebraicGeometry.HigherDirectImageLimitSystem | unchanged | Actual semantic parent already imports and applies the source theorem. |

No current module is downstream of the withdrawn module. No consumer adaptation
is required. The actual semantic parent is compiled unchanged with the source
replacement. The DAG edge to the existing class descent node is preserved.

## Status

landed 20261021T134553-L-1372516 2026-10-21 (merge of deliver/U1/Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassDescent)
