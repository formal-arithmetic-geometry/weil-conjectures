# CategoryTheory private ideal-descent proof interfaces

## Reason

The original private helpers repeatedly compare module structures obtained by scalar
restriction along an identity with the same structures written directly on slice sheaves.
Those conversions unfold large constructions and prevent the completed proof from meeting
the single-file time bound. Use the direct pushforward restriction functor, together with
a proved natural isomorphism to the existing restriction functor, and explicitly type the
slice models and section modules over the restriction of the global scalar sheaf.

Every declaration below is private. The public theorem signature and all public imports
are unchanged. No definition used in any target statement changes. These are proof
interfaces for the same canonical comparisons; their unit formulas and the natural
isomorphism connect them to the original constructions. All new data has a real
construction; all new private theorems are proved.

## Old

Existing private definitions, or theorem signatures, verbatim:


```lean
private instance overMap_additive
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C} (a : W ⟶ U) :
    (SheafOfModules.overMap.{u} R a).Additive :=
  ⟨fun {_ _} b c ↦ by ext X x; rfl⟩
```

```lean
private theorem restricted_ringFamily_model_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U W : C) (a : W ⟶ U) (r : ℕ) (f : Fin r → O.obj.obj (op U)) :
    ∃ e : (ringFamilySheafModel (O.over W) K ε m hm r
      (commonSpanSections O U W a r f)).1 ≅
      ((SheafOfModules.overMap
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) a).mapHomologicalComplex
          (.up ℤ)).obj (ringFamilySheafModel (O.over U) K ε m hm r
            (fun i ↦ ringedSliceSection O U (f i))).1,
      ∀ (n : ℤ) (X : (Over W)ᵒᵖ)
        (x : ((ringFamilyPresheafComplex (O.over W) K ε m hm r
          (commonSpanSections O U W a r f)).X n).obj X),
        (e.hom.f n).val.app X
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((sheafCompose (J.over W) (forget₂ CommRingCat RingCat)).obj
              (O.over W)).obj)).unit.app
                ((ringFamilyPresheafComplex (O.over W) K ε m hm r
                  (commonSpanSections O U W a r f)).X n)).app X x) =
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj
              (O.over U)).obj)).unit.app
                ((ringFamilyPresheafComplex (O.over U) K ε m hm r
                  (fun i ↦ ringedSliceSection O U (f i))).X n)).app
                    ((Over.map a).op.obj X) x)
```

```lean
private abbrev sliceUnit
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U : C) (r : ℕ) (f : Fin r → O.obj.obj (op U)) (n : ℤ) :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)).obj)).unit.app
      ((ringFamilyPresheafComplex (O.over U) K ε m hm r
        (fun i ↦ ringedSliceSection O U (f i))).X n))
```

```lean
private abbrev sliceModelComplex
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U : C) (r : ℕ) (f : Fin r → O.obj.obj (op U)) :=
  (ringFamilySheafModel (O.over U) K ε m hm r
    (fun i ↦ ringedSliceSection O U (f i))).1
```

```lean
private abbrev restrictedModel
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U W : C) (a : W ⟶ U) (r : ℕ) (f : Fin r → O.obj.obj (op U)) :=
  ((SheafOfModules.overMap
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) a).mapHomologicalComplex
      (.up ℤ)).obj (sliceModelComplex O K ε m hm U r f)
```

```lean
private abbrev commonSpanCanonical
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U V W : C) (a : W ⟶ U) (b : W ⟶ V)
    (r s : ℕ) (f : Fin r → O.obj.obj (op U)) (g : Fin s → O.obj.obj (op V))
    (q : restrictedModel O K ε m hm U W a r f ≅
      restrictedModel O K ε m hm V W b s g) : Prop :=
  ∀ (n : ℤ) (X : (Over W)ᵒᵖ)
    (h : ringFamilySectionIdeal (O.over W) r (commonSpanSections O U W a r f) X =
      ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) X)
    (x : ((ringFamilyPresheafComplex (O.over W) K ε m hm r
      (commonSpanSections O U W a r f)).X n).obj X),
    (q.hom.f n).val.app X
      ((sliceUnit O K ε m hm U r f n).app ((Over.map a).op.obj X) x) =
      (sliceUnit O K ε m hm V s g n).app ((Over.map b).op.obj X)
        (ringFamilyComponentEquiv K ((O.over W).obj.obj X) _ _ h n x)
```

```lean
private theorem commonSpanModels_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U V W : C) (a : W ⟶ U) (b : W ⟶ V)
    (r s : ℕ) (f : Fin r → O.obj.obj (op U)) (g : Fin s → O.obj.obj (op V))
    (heq : ∀ (T : C) (h : T ⟶ W), ∃ S ∈ J T,
      ∀ (Z : C) (k : Z ⟶ T), S k →
        Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ h ≫ a).op (f t))) =
          Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ h ≫ b).op (g t)))) :
    ∃ q : ((SheafOfModules.overMap
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) a).mapHomologicalComplex
          (.up ℤ)).obj (ringFamilySheafModel (O.over U) K ε m hm r
            (fun i ↦ ringedSliceSection O U (f i))).1 ≅
      ((SheafOfModules.overMap
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) b).mapHomologicalComplex
          (.up ℤ)).obj (ringFamilySheafModel (O.over V) K ε m hm s
            (fun i ↦ ringedSliceSection O V (g i))).1,
      ∀ (n : ℤ) (X : (Over W)ᵒᵖ)
        (h : ringFamilySectionIdeal (O.over W) r (commonSpanSections O U W a r f) X =
          ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) X)
        (x : ((ringFamilyPresheafComplex (O.over W) K ε m hm r
          (commonSpanSections O U W a r f)).X n).obj X),
        (q.hom.f n).val.app X
          ((sliceUnit O K ε m hm U r f n).app ((Over.map a).op.obj X) x) =
        (sliceUnit O K ε m hm V s g n).app ((Over.map b).op.obj X)
          (ringFamilyComponentEquiv K ((O.over W).obj.obj X) _ _ h n x)
```

```lean
private def spanEvaluationEquiv
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C} (a : W ⟶ U)
    (M : SheafOfModules.{u} (R.over U)) :
    ((SheafOfModules.overMap R a).obj M).val.obj (op (Over.mk (𝟙 W))) ≃ₗ[R.obj.obj (op W)]
      M.val.obj (op (Over.mk a)) :=
  let e : M.val.obj (op (Over.mk ((𝟙 W) ≫ a))) ≃ₗ[R.obj.obj (op W)]
      M.val.obj (op (Over.mk a)) :=
    (eqToIso (congrArg (fun b : W ⟶ U ↦
      (show ModuleCat (R.obj.obj (op W)) from M.val.obj (op (Over.mk b))))
        (Category.id_comp a))).toLinearEquiv
  { toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := e.map_add
    map_smul' := e.map_smul }
```

```lean
private theorem spanEvaluationEquiv_naturality
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C} (a : W ⟶ U)
    (M N : SheafOfModules.{u} (R.over U)) (g : M ⟶ N)
    (x : ((SheafOfModules.overMap R a).obj M).val.obj (op (Over.mk (𝟙 W)))) :
    spanEvaluationEquiv R a N
        ((((SheafOfModules.overMap R a).map g).val.app (op (Over.mk (𝟙 W)))) x) =
      g.val.app (op (Over.mk a)) (spanEvaluationEquiv R a M x)
```

```lean
private def spanTransitionEquiv
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U V W : C} (a : W ⟶ U) (b : W ⟶ V)
    (M : CochainComplex (SheafOfModules.{u} (R.over U)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (R.over V)) ℤ)
    (q : ((SheafOfModules.overMap R a).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((SheafOfModules.overMap R b).mapHomologicalComplex (.up ℤ)).obj N) (n : ℤ) :
    (M.X n).val.obj (op (Over.mk a)) ≃ₗ[R.obj.obj (op W)]
      (N.X n).val.obj (op (Over.mk b)) :=
  let e : ((SheafOfModules.overMap R a).obj (M.X n)).val.obj (op (Over.mk (𝟙 W))) ≃ₗ[
      R.obj.obj (op W)]
      ((SheafOfModules.overMap R b).obj (N.X n)).val.obj (op (Over.mk (𝟙 W))) :=
    ((SheafOfModules.evaluation (R.over W) (op (Over.mk (𝟙 W)))).mapIso
      (HomologicalComplex.Hom.isoApp q n)).toLinearEquiv
  (spanEvaluationEquiv R a (M.X n)).symm.trans
    (e.trans (spanEvaluationEquiv R b (N.X n)))
```

```lean
private theorem spanTransitionEquiv_differential
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U V W : C} (a : W ⟶ U) (b : W ⟶ V)
    (M : CochainComplex (SheafOfModules.{u} (R.over U)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (R.over V)) ℤ)
    (q : ((SheafOfModules.overMap R a).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((SheafOfModules.overMap R b).mapHomologicalComplex (.up ℤ)).obj N)
    (n k : ℤ) (x : (M.X n).val.obj (op (Over.mk a))) :
    spanTransitionEquiv R a b M N q k ((M.d n k).val.app (op (Over.mk a)) x) =
      (N.d n k).val.app (op (Over.mk b)) (spanTransitionEquiv R a b M N q n x)
```

```lean
private theorem spanTransitionEquiv_comp
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U V T W : C}
    (a : W ⟶ U) (b : W ⟶ V) (c : W ⟶ T)
    (M : CochainComplex (SheafOfModules.{u} (R.over U)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (R.over V)) ℤ)
    (P : CochainComplex (SheafOfModules.{u} (R.over T)) ℤ)
    (q : ((SheafOfModules.overMap R a).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((SheafOfModules.overMap R b).mapHomologicalComplex (.up ℤ)).obj N)
    (z : ((SheafOfModules.overMap R b).mapHomologicalComplex (.up ℤ)).obj N ≅
      ((SheafOfModules.overMap R c).mapHomologicalComplex (.up ℤ)).obj P)
    (n : ℤ) (x : (M.X n).val.obj (op (Over.mk a))) :
    spanTransitionEquiv R a c M P (q ≪≫ z) n x =
      spanTransitionEquiv R b c N P z n (spanTransitionEquiv R a b M N q n x)
```

```lean
private theorem commonSpanHom_ext
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U W : C) (a : W ⟶ U) (r : ℕ) (f : Fin r → O.obj.obj (op U))
    (E : (Over W)ᵒᵖ → Prop)
    (hcover : ∀ X : Over W, ∃ S ∈ (J.over W) X,
      ∀ (Y : Over W) (k : Y ⟶ X), S k → E (op Y))
    (B : ringedSiteComplex (O.over W))
    (τ χ : ((SheafOfModules.overMap
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) a).mapHomologicalComplex
          (.up ℤ)).obj (ringFamilySheafModel (O.over U) K ε m hm r
            (fun i ↦ ringedSliceSection O U (f i))).1 ⟶ B)
    (h : ∀ (n : ℤ) (X : (Over W)ᵒᵖ), E X →
      ∀ x : ((ringFamilyPresheafComplex (O.over U) K ε m hm r
        (fun i ↦ ringedSliceSection O U (f i))).X n).obj ((Over.map a).op.obj X),
      (τ.f n).val.app X ((sliceUnit O K ε m hm U r f n).app ((Over.map a).op.obj X) x) =
        (χ.f n).val.app X
          ((sliceUnit O K ε m hm U r f n).app ((Over.map a).op.obj X) x)) : τ = χ
```

```lean
private theorem sheafModelAugmentationZero_unit
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (r : ℕ) (f : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (X : Cᵒᵖ) (x : ((ringFamilyPresheafComplex O K ε m hm r f).X 0).obj X) :
    (sheafModelAugmentationZero O K ε m hm r f).val.app X
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).unit.app
          ((ringFamilyPresheafComplex O K ε m hm r f).X 0)).app X x) =
      ringComplexAugmentationValue (ε (O.obj.obj X) (ringFamilySectionIdeal O r f X)) x
```

```lean
private theorem commonSpanCanonical_augmentationZero
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U V W : C) (a : W ⟶ U) (b : W ⟶ V)
    (r s : ℕ) (f : Fin r → O.obj.obj (op U)) (g : Fin s → O.obj.obj (op V))
    (q : restrictedModel O K ε m hm U W a r f ≅ restrictedModel O K ε m hm V W b s g)
    (hq : commonSpanCanonical O K ε m hm U V W a b r s f g q)
    (hcover : ∀ X : Over W, ∃ S ∈ (J.over W) X,
      ∀ (Y : Over W) (k : Y ⟶ X), S k →
        ringFamilySectionIdeal (O.over W) r (commonSpanSections O U W a r f) (op Y) =
          ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) (op Y)) :
    let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
    (q.hom.f 0) ≫ (SheafOfModules.overMap R b).map
        (sheafModelAugmentationZero (O.over V) K ε m hm s
          (fun i ↦ ringedSliceSection O V (g i))) ≫
        (SheafOfModules.overMapUnitIso (R := R) b).hom =
      (SheafOfModules.overMap R a).map
        (sheafModelAugmentationZero (O.over U) K ε m hm r
          (fun i ↦ ringedSliceSection O U (f i))) ≫
        (SheafOfModules.overMapUnitIso (R := R) a).hom
```

```lean
private theorem ringFamilyComponentEquiv_trans
    (K : RingComplexFamily.{u}) (A : CommRingCat.{u})
    (I L M : {I : Ideal A // I.FG}) (h : I = L) (k : L = M)
    (n : ℤ) (x : ((K A I).X n).val.obj (op ⟨PUnit.unit⟩)) :
    ringFamilyComponentEquiv K A I M (h.trans k) n x =
      ringFamilyComponentEquiv K A L M k n (ringFamilyComponentEquiv K A I L h n x)
```

## New

Corresponding private definitions or theorem signatures:


```lean
private instance overMap_additive
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C} (a : W ⟶ U) :
    (directOverMap.{u} R a).Additive :=
  ⟨fun {_ _} b c ↦ by ext X x; rfl⟩
```

```lean
private theorem restricted_ringFamily_model_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U W : C) (a : W ⟶ U) (r : ℕ) (f : Fin r → O.obj.obj (op U)) :
    ∃ e : (ringFamilySheafModel (O.over W) K ε m hm r
      (commonSpanSections O U W a r f)).1 ≅
      ((directOverMap
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) a).mapHomologicalComplex
          (.up ℤ)).obj (ringFamilySheafModel (O.over U) K ε m hm r
            (fun i ↦ ringedSliceSection O U (f i))).1,
      ∀ (n : ℤ) (X : (Over W)ᵒᵖ)
        (x : ((ringFamilyPresheafComplex (O.over W) K ε m hm r
          (commonSpanSections O U W a r f)).X n).obj X),
        (e.hom.f n).val.app X
          ((modelUnit (O.over W) K ε m hm r
            (commonSpanSections O U W a r f) n).app X x) =
          ((modelUnit (O.over U) K ε m hm r
            (fun i ↦ ringedSliceSection O U (f i)) n).app ((Over.map a).op.obj X) x)
```

```lean
private def sliceUnit
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U : C) (r : ℕ) (f : Fin r → O.obj.obj (op U)) (n : ℤ) :
    (ringFamilyPresheafComplex (O.over U) K ε m hm r
      (fun i ↦ ringedSliceSection O U (f i))).X n ⟶
        ((sliceModelComplex O K ε m hm U r f).X n).val :=
  modelUnit (O.over U) K ε m hm r (fun i ↦ ringedSliceSection O U (f i)) n
```

```lean
private def sliceModelComplex
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U : C) (r : ℕ) (f : Fin r → O.obj.obj (op U)) :
    CochainComplex (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over U)) ℤ :=
  (ringFamilySheafModel (O.over U) K ε m hm r
    (fun i ↦ ringedSliceSection O U (f i))).1
```

```lean
private def restrictedModel
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U W : C) (a : W ⟶ U) (r : ℕ) (f : Fin r → O.obj.obj (op U)) :
    CochainComplex (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over W)) ℤ :=
  ((directOverMap
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) a).mapHomologicalComplex
      (.up ℤ)).obj (sliceModelComplex O K ε m hm U r f)
```

```lean
private def commonSpanCanonical
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U V W : C) (a : W ⟶ U) (b : W ⟶ V)
    (r s : ℕ) (f : Fin r → O.obj.obj (op U)) (g : Fin s → O.obj.obj (op V))
    (q : restrictedModel O K ε m hm U W a r f ≅
      restrictedModel O K ε m hm V W b s g) : Prop :=
  ∀ (n : ℤ) (X : (Over W)ᵒᵖ)
    (h : ringFamilySectionIdeal (O.over W) r (commonSpanSections O U W a r f) X =
      ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) X)
    (x : ((ringFamilyPresheafComplex (O.over W) K ε m hm r
      (commonSpanSections O U W a r f)).X n).obj X),
    (q.hom.f n).val.app X
      ((sliceUnit O K ε m hm U r f n).app ((Over.map a).op.obj X) x) =
      (sliceUnit O K ε m hm V s g n).app ((Over.map b).op.obj X)
        (familyTransport K ((O.over W).obj.obj X) _ _ h n x)
```

```lean
private theorem commonSpanModels_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U V W : C) (a : W ⟶ U) (b : W ⟶ V)
    (r s : ℕ) (f : Fin r → O.obj.obj (op U)) (g : Fin s → O.obj.obj (op V))
    (heq : ∀ (T : C) (h : T ⟶ W), ∃ S ∈ J T,
      ∀ (Z : C) (k : Z ⟶ T), S k →
        Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ h ≫ a).op (f t))) =
          Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ h ≫ b).op (g t)))) :
    ∃ q : restrictedModel O K ε m hm U W a r f ≅
      restrictedModel O K ε m hm V W b s g,
      commonSpanCanonical O K ε m hm U V W a b r s f g q
```

```lean
private def spanEvaluationEquiv
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C} (a : W ⟶ U)
    (M : SheafOfModules.{u} (R.over U)) :
    (sliceValue R ((directOverMap R a).obj M) (𝟙 W)) ≃ₗ[
        R.obj.obj (op W)]
      (sliceValue R M a) :=
  (eqToIso (congrArg (fun b : W ⟶ U ↦
    (sliceValue R M b))
      (Category.id_comp a))).toLinearEquiv
```

```lean
private theorem spanEvaluationEquiv_naturality
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C} (a : W ⟶ U)
    (M N : SheafOfModules.{u} (R.over U)) (g : M ⟶ N)
    (x : ((directOverMap R a).obj M).val.obj (op (Over.mk (𝟙 W)))) :
    spanEvaluationEquiv R a N
        ((((directOverMap R a).map g).val.app (op (Over.mk (𝟙 W)))) x) =
      g.val.app (op (Over.mk a)) (spanEvaluationEquiv R a M x)
```

```lean
private def spanTransitionEquiv
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U V W : C} (a : W ⟶ U) (b : W ⟶ V)
    (M : CochainComplex (SheafOfModules.{u} (R.over U)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (R.over V)) ℤ)
    (q : ((directOverMap R a).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((directOverMap R b).mapHomologicalComplex (.up ℤ)).obj N) (n : ℤ) :
    (show ModuleCat (R.obj.obj (op W)) from (M.X n).val.obj (op (Over.mk a))) ≃ₗ[
      R.obj.obj (op W)]
      (show ModuleCat (R.obj.obj (op W)) from (N.X n).val.obj (op (Over.mk b))) :=
  let e : (show ModuleCat (R.obj.obj (op W)) from
      ((directOverMap R a).obj (M.X n)).val.obj (op (Over.mk (𝟙 W)))) ≃ₗ[
        R.obj.obj (op W)] (show ModuleCat (R.obj.obj (op W)) from
      ((directOverMap R b).obj (N.X n)).val.obj (op (Over.mk (𝟙 W)))) :=
    ((SheafOfModules.evaluation (R.over W) (op (Over.mk (𝟙 W)))).mapIso
      (HomologicalComplex.Hom.isoApp q n)).toLinearEquiv
  (spanEvaluationEquiv R a (M.X n)).symm.trans
    (e.trans (spanEvaluationEquiv R b (N.X n)))
```

```lean
private theorem spanTransitionEquiv_differential
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U V W : C} (a : W ⟶ U) (b : W ⟶ V)
    (M : CochainComplex (SheafOfModules.{u} (R.over U)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (R.over V)) ℤ)
    (q : ((directOverMap R a).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((directOverMap R b).mapHomologicalComplex (.up ℤ)).obj N)
    (n k : ℤ) (x : (M.X n).val.obj (op (Over.mk a))) :
    spanTransitionEquiv R a b M N q k ((M.d n k).val.app (op (Over.mk a)) x) =
      (N.d n k).val.app (op (Over.mk b)) (spanTransitionEquiv R a b M N q n x)
```

```lean
private theorem spanTransitionEquiv_comp
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U V T W : C}
    (a : W ⟶ U) (b : W ⟶ V) (c : W ⟶ T)
    (M : CochainComplex (SheafOfModules.{u} (R.over U)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (R.over V)) ℤ)
    (P : CochainComplex (SheafOfModules.{u} (R.over T)) ℤ)
    (q : ((directOverMap R a).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((directOverMap R b).mapHomologicalComplex (.up ℤ)).obj N)
    (z : ((directOverMap R b).mapHomologicalComplex (.up ℤ)).obj N ≅
      ((directOverMap R c).mapHomologicalComplex (.up ℤ)).obj P)
    (n : ℤ) (x : (M.X n).val.obj (op (Over.mk a))) :
    spanTransitionEquiv R a c M P (q ≪≫ z) n x =
      spanTransitionEquiv R b c N P z n (spanTransitionEquiv R a b M N q n x)
```

```lean
private theorem commonSpanHom_ext
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U W : C) (a : W ⟶ U) (r : ℕ) (f : Fin r → O.obj.obj (op U))
    (E : (Over W)ᵒᵖ → Prop)
    (hcover : ∀ X : Over W, ∃ S ∈ (J.over W) X,
      ∀ (Y : Over W) (k : Y ⟶ X), S k → E (op Y))
    (B : CochainComplex (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over W)) ℤ)
    (τ χ : restrictedModel O K ε m hm U W a r f ⟶ B)
    (h : ∀ (n : ℤ) (X : (Over W)ᵒᵖ), E X →
      ∀ x : ((ringFamilyPresheafComplex (O.over U) K ε m hm r
        (fun i ↦ ringedSliceSection O U (f i))).X n).obj ((Over.map a).op.obj X),
      (τ.f n).val.app X ((sliceUnit O K ε m hm U r f n).app ((Over.map a).op.obj X) x) =
        (χ.f n).val.app X
          ((sliceUnit O K ε m hm U r f n).app ((Over.map a).op.obj X) x)) : τ = χ
```

```lean
private theorem sheafModelAugmentationZero_unit
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (r : ℕ) (f : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (X : Cᵒᵖ) (x : ((ringFamilyPresheafComplex O K ε m hm r f).X 0).obj X) :
    (sheafModelAugmentationZero O K ε m hm r f).val.app X
      ((modelUnit O K ε m hm r f 0).app X x) =
      ringComplexAugmentationValue (ε (O.obj.obj X) (ringFamilySectionIdeal O r f X)) x
```

```lean
private theorem commonSpanCanonical_augmentationZero
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U V W : C) (a : W ⟶ U) (b : W ⟶ V)
    (r s : ℕ) (f : Fin r → O.obj.obj (op U)) (g : Fin s → O.obj.obj (op V))
    (q : restrictedModel O K ε m hm U W a r f ≅ restrictedModel O K ε m hm V W b s g)
    (hq : commonSpanCanonical O K ε m hm U V W a b r s f g q)
    (hcover : ∀ X : Over W, ∃ S ∈ (J.over W) X,
      ∀ (Y : Over W) (k : Y ⟶ X), S k →
        ringFamilySectionIdeal (O.over W) r (commonSpanSections O U W a r f) (op Y) =
          ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) (op Y)) :
    let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
    (q.hom.f 0) ≫ (directOverMap R b).map
        (sliceAugmentationToUnit O K ε m hm V s g) ≫
        (directOverMapUnitIso (R := R) b).hom =
      (directOverMap R a).map
        (sliceAugmentationToUnit O K ε m hm U r f) ≫
        (directOverMapUnitIso (R := R) a).hom
```

```lean
private theorem componentEquiv_trans
    {R : Type u} [Ring R] {ι : Type u} (P : ι → ModuleCat.{u} R)
    {I L M : ι} (h : I = L) (k : L = M) (x : P I) :
    (eqToIso (congrArg P (h.trans k))).toLinearEquiv x =
      (eqToIso (congrArg P k)).toLinearEquiv
        ((eqToIso (congrArg P h)).toLinearEquiv x)
```

## Users

The consumer check used `tools/downstream.py` with `--uses` for every changed private
interface. The whole-word search over-approximates references: the other `restrictedModel`
is declared in its own namespace in the completed-stalk module (line 269) and is unrelated.
Private Lean names cannot be referenced by that unqualified name from another module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FunctorialRingComplexIdealDescent | U3 | All actual users; the proof is adapted and compiled as one file. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Textual hit for its own `restrictedModel`, not a user of this private declaration; unchanged. |

No adaptation of another module is required, and no target statement needs renewed
semantic review. The covering-locus argument also applies to empty index families,
empty generating lists, and the zero ring; it uses no inhabitance or nontriviality premise.

## Status

landed 20261026T002937-L-132644 2026-10-26 (merge of deliver/U3/Sheaf.Paper.FunctorialRingComplexIdealDescent)
