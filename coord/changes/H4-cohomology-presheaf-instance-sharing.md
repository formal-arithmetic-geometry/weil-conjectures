# AlgebraicGeometry.Etale.ModuleSheaf instance sharing in CohomologyPresheaf

## Reason

Reviewer X-f4010 returned the previous implementation because its unchanged direct
importer FreeSheaf exceeded the 60-second limit. The named category had been exported
through the free-sheaf interfaces, forcing callers to compare their raw derived-category
instances with the local cached instances in those interfaces.

Keep the original raw-category implementations and signatures of freeSheaf,
freeSheafSections, freeSheafHomEquiv, its three compatibility lemmas,
freeSheafSections_naturality, upperStarFreeSheafHomEquiv, its composition lemma and
upperStarFreeSheafIso. Also retain the original raw derived-object input types of
higherDirectImagePresheaf and higherDirectImagePresheafToSheaf, so strict callers infer
their original categories. Inside the derived-cohomology argument, use moduleFreeSheaf,
moduleFreeSheafSections and moduleFreeSheafHomEquiv: typed abbreviations of those same
constructions using ModuleSheaf. Their compatibility lemmas apply the original proved
lemmas. The named category's five inferred instances remain local. No new instance is
registered globally and no upstream reducibility or instance attribute is changed.

All 35 original public declarations retain their kind and visibility, and none is
removed. The vanishing criterion retains its original signature verbatim. All changed
expressions below unfold to the original constructions; no mathematical statement or
Challenge.lean target is changed. The generic boundary homotopy and its private
cycle-boundary helper stay fully proved. No object is chosen from an unproved existence
statement. No file is split, no timeout is raised and no compiler check is disabled.

The landed delivery subsequently failed in HigherDirectImageRawTrianglePullbackComposition.
The repair below adapts only its proof application; report.md records the fresh local
dependency check and the reproduced original error.

## Old

Under the original namespace, universes and section variables, these are the changed
signatures, and the original bodies of changed definitions, verbatim:

```lean
noncomputable def Etale.higherDirectImagePresheaf {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Etale.freeSheaf Λ X ⋙ (h)^*[ModuleCat.{u + 1} Λ] ⋙
    DerivedCategory.Plus.singleFunctor _ 0).op ⋙ preadditiveYoneda.obj (K⟦q⟧)

noncomputable def Etale.derivedHomToHomology
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.freeSheaf Λ X ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj L ⟶
      (Etale.freeSheaf Λ X).op ⋙ preadditiveYoneda.obj
        ((DerivedCategory.Plus.homologyFunctor _ 0).obj L) where
  app W := AddCommGrpCat.ofHom <|
    (Preadditive.leftComp _
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _)).comp
      (DerivedCategory.Plus.homologyFunctor _ 0).mapAddHom
  naturality W W' g := by
    have hs := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
      (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).inv.naturality
        ((Etale.freeSheaf Λ X).map g.unop)
    dsimp at hs
    ext f
    revert f
    change ∀ f : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj W.unop) ⟶
        L,
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map ((Etale.freeSheaf Λ X).map g.unop) ≫ f) =
      (Etale.freeSheaf Λ X).map g.unop ≫
        (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app
          ((Etale.freeSheaf Λ X).obj W.unop) ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map f
    intro f
    rw [Functor.map_comp, ← reassoc_of% hs]

lemma Etale.derivedHomToHomology_app_apply
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (W : X.Etaleᵒᵖ)
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj W.unop) ⟶ L) :
    (Etale.derivedHomToHomology L).app W β =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map β

noncomputable abbrev Etale.sectionsMap {G G' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (g : G ⟶ G') :
    ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G).obj ⟶
    ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G').obj :=
  ((sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map g).hom

lemma Etale.derivedHomToHomology_app_eq {W : X.Etaleᵒᵖ}
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj W.unop) ⟶
      DerivedCategory.Plus.Q.obj M)
    (f : (HomologicalComplex.single _ (.up ℤ) 0).obj ((Etale.freeSheaf Λ X).obj W.unop) ⟶ M.obj)
    (hf : DerivedCategory.Plus.ι.map β =
      DerivedCategory.Q.map f ≫ (DerivedCategory.quotientCompQhIso _).inv.app M.obj) :
    (Etale.derivedHomToHomology (DerivedCategory.Plus.Q.obj M)).app W β =
      DerivedCategory.singleCyclesHom _ ≫ HomologicalComplex.cyclesMap f 0 ≫
        M.obj.homologyπ 0 ≫ Etale.homologyComparison M

theorem Etale.isLocallySurjective_derivedHomToHomology [M.obj.IsKInjective] :
    Presheaf.IsLocallySurjective X.smallEtaleTopology
      (Etale.derivedHomToHomology (DerivedCategory.Plus.Q.obj M) ≫
        Etale.freeSheafSections Λ
          ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M)))

noncomputable def Etale.homotopyOfSingle {A : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (f : (HomologicalComplex.single _ (.up ℤ) 0).obj A ⟶ M.obj) (b : A ⟶ M.obj.X (-1))
    (hb : f.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom ≫ b ≫ M.obj.d (-1) 0) :
    Homotopy f 0 :=
  (Homotopy.ofEq (HomologicalComplex.from_single_hom_ext (j := 0) (by
    rw [hb, Homotopy.nullHomotopicMap'_f (k₂ := -1) (k₀ := 1) (by simp) (by simp)]
    simp
    rfl)) :
      Homotopy f (Homotopy.nullHomotopicMap' (fun i j (_ : j + 1 = i) ↦
        if hi : i = 0 then
          (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 A i hi).hom ≫ b ≫
            eqToHom (by congr 1; lia)
        else 0))).trans (Homotopy.nullHomotopy' _)

theorem Etale.isLocallyInjective_derivedHomToHomology [M.obj.IsKInjective] :
    Presheaf.IsLocallyInjective X.smallEtaleTopology
      (Etale.derivedHomToHomology (DerivedCategory.Plus.Q.obj M) ≫
        Etale.freeSheafSections Λ
          ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M)))

theorem Etale.isLocallyBijective_derivedHomToHomology
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology
        (Etale.derivedHomToHomology L ≫
          Etale.freeSheafSections Λ ((DerivedCategory.Plus.homologyFunctor _ 0).obj L)) ∧
      Presheaf.IsLocallySurjective X.smallEtaleTopology
        (Etale.derivedHomToHomology L ≫
          Etale.freeSheafSections Λ ((DerivedCategory.Plus.homologyFunctor _ 0).obj L))

noncomputable def Etale.higherDirectImagePresheafIso {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.higherDirectImagePresheaf Λ h q K ≅
      (Etale.freeSheaf Λ X ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj (R+((h)_*[ModuleCat.{u + 1} Λ]).obj (K⟦q⟧)) :=
  Functor.isoWhiskerRight (NatIso.op (Functor.isoWhiskerLeft (Etale.freeSheaf Λ X)
    (((h)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0)))
      (preadditiveYoneda.obj (K⟦q⟧)) ≪≫
  NatIso.ofComponents (fun W ↦ AddEquiv.toAddCommGrpIso
    ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h).homAddEquiv _ _))
    (fun g ↦ by
      ext f
      exact (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ)
        h).homEquiv_naturality_left _ _)

noncomputable def Etale.higherDirectImagePresheafToHom {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.higherDirectImagePresheaf Λ h q K ⟶
      (Etale.freeSheaf Λ X).op ⋙ preadditiveYoneda.obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K)) :=
  (Etale.higherDirectImagePresheafIso Λ h q K).hom ≫
  Etale.derivedHomToHomology (R+((h)_*[ModuleCat.{u + 1} Λ]).obj (K⟦q⟧)) ≫
  Functor.whiskerLeft (Etale.freeSheaf Λ X).op (preadditiveYoneda.map
    ((DerivedCategory.Plus.homologyFunctor _ 0).map
      ((R+((h)_*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K) ≫
    ((DerivedCategory.Plus.homologyFunctor _ 0).isoShiftZero ℤ).inv.app _ ≫
      ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso q 0 q (add_zero q)).hom.app _))

noncomputable def Etale.higherDirectImagePresheafToSheaf {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.higherDirectImagePresheaf Λ h q K ⟶
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((DerivedCategory.Plus.homologyFunctor _ q).obj
            (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K))) :=
  Etale.higherDirectImagePresheafToHom Λ h q K ≫ Etale.freeSheafSections Λ _

theorem Etale.isLocallyBijective_higherDirectImagePresheafToSheaf {X Y : Scheme.{u}}
    (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology
        (Etale.higherDirectImagePresheafToSheaf Λ h q K) ∧
      Presheaf.IsLocallySurjective X.smallEtaleTopology
        (Etale.higherDirectImagePresheafToSheaf Λ h q K)

theorem Etale.isIso_higherDirectImagePresheafToSheaf {X Y : Scheme.{u}}
    (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h] (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _ _).symm
      (Etale.higherDirectImagePresheafToSheaf Λ h q K))

theorem Etale.isIso_higherDirectImagePresheafToSheaf_singleFunctor
    {X Y : Scheme.{u}} (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h] (q : ℤ)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _ _).symm
      (Etale.higherDirectImagePresheafToSheaf Λ h q
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))

noncomputable def Etale.higherDirectImagePresheafMap {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    {K K' : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ K') :
    Etale.higherDirectImagePresheaf Λ h q K ⟶ Etale.higherDirectImagePresheaf Λ h q K' :=
  Functor.whiskerLeft _ (preadditiveYoneda.map ((shiftFunctor _ q).map φ))

noncomputable abbrev Etale.homologyShiftComparison {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (DerivedCategory.Plus.homologyFunctor _ 0).obj (R+((h)_*[ModuleCat.{u + 1} Λ]).obj (K⟦q⟧)) ⟶
      (DerivedCategory.Plus.homologyFunctor _ q).obj (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K) :=
  (DerivedCategory.Plus.homologyFunctor _ 0).map
      ((R+((h)_*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K) ≫
    ((DerivedCategory.Plus.homologyFunctor _ 0).isoShiftZero ℤ).inv.app _ ≫
      ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso q 0 q (add_zero q)).hom.app _

lemma Etale.higherDirectImagePresheafToHom_app_apply {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (W : X.Etaleᵒᵖ) (β : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W.unop)) ⟶ K⟦q⟧) :
    (Etale.higherDirectImagePresheafToHom Λ h q K).app W β =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map
          ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h).homEquiv _ _
            ((((h)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
              ((Etale.freeSheaf Λ X).obj W.unop) ≫ β)) ≫
        Etale.homologyShiftComparison Λ h q K

lemma Etale.homologyShiftComparison_naturality {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    {K K' : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ K') :
    (DerivedCategory.Plus.homologyFunctor _ 0).map
        (R+((h)_*[ModuleCat.{u + 1} Λ]).map ((shiftFunctor _ q).map φ)) ≫
      Etale.homologyShiftComparison Λ h q K' =
    Etale.homologyShiftComparison Λ h q K ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map (R+((h)_*[ModuleCat.{u + 1} Λ]).map φ)

lemma Etale.higherDirectImagePresheafToSheaf_naturality {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    {K K' : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ K') :
    Etale.higherDirectImagePresheafMap Λ h q φ ≫ Etale.higherDirectImagePresheafToSheaf Λ h q K' =
      Etale.higherDirectImagePresheafToSheaf Λ h q K ≫ Etale.sectionsMap
        ((DerivedCategory.Plus.homologyFunctor _ q).map
          (R+((h)_*[ModuleCat.{u + 1} Λ]).map φ))

noncomputable def Etale.higherDirectImagePresheafFunctor {X Y : Scheme.{u}} (h : Y ⟶ X)
    (q : ℤ) :
    DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  shiftFunctor _ q ⋙ preadditiveYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj
    (Etale.freeSheaf Λ X ⋙ (h)^*[ModuleCat.{u + 1} Λ] ⋙ DerivedCategory.Plus.singleFunctor _ 0).op
```

## New

Under the same namespace, universes and section variables, the new helpers and changed
signatures (with definition bodies) are:

```lean
def Etale.ModuleSheaf (X : Scheme.{u}) : Type (u + 2) :=
  Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)

noncomputable abbrev Etale.moduleUpperStar {X Y : Scheme.{u}} (h : Y ⟶ X) :
    Etale.ModuleSheaf Λ X ⥤ Etale.ModuleSheaf Λ Y :=
  (h)^*[ModuleCat.{u + 1} Λ]

noncomputable abbrev Etale.moduleLowerStar {X Y : Scheme.{u}} (h : Y ⟶ X) :
    Etale.ModuleSheaf Λ Y ⥤ Etale.ModuleSheaf Λ X :=
  (h)_*[ModuleCat.{u + 1} Λ]

noncomputable abbrev Etale.moduleDerivedAdjunction {X Y : Scheme.{u}} (h : Y ⟶ X) :
    D+(Etale.moduleUpperStar Λ h) ⊣ R+(Etale.moduleLowerStar Λ h) :=
  Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h

noncomputable abbrev Etale.moduleFreeSheaf (X : Scheme.{u}) :
    X.Etale ⥤ Etale.ModuleSheaf Λ X := Etale.freeSheaf Λ X

noncomputable abbrev Etale.moduleFreeSheafSections {X : Scheme.{u}}
    (G : Etale.ModuleSheaf Λ X) :
    (Etale.moduleFreeSheaf Λ X).op ⋙ preadditiveYoneda.obj G ⟶
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G).obj :=
  Etale.freeSheafSections Λ G

noncomputable abbrev Etale.moduleFreeSheafHomEquiv (W : X.Etale)
    (G : Etale.ModuleSheaf Λ X) :
    ((Etale.moduleFreeSheaf Λ X).obj W ⟶ G) ≃ G.obj.obj (op W) := Etale.freeSheafHomEquiv Λ W G

lemma Etale.moduleFreeSheafHomEquiv_apply (W : X.Etale)
    (G : Etale.ModuleSheaf Λ X)
    (f : (Etale.moduleFreeSheaf Λ X).obj W ⟶ G) :
    Etale.moduleFreeSheafHomEquiv Λ W G f = (Etale.moduleFreeSheafSections Λ G).app (op W) f

lemma Etale.moduleFreeSheafHomEquiv_comp (W : X.Etale)
    {G G' : Etale.ModuleSheaf Λ X}
    (f : (Etale.moduleFreeSheaf Λ X).obj W ⟶ G) (g : G ⟶ G') :
    Etale.moduleFreeSheafHomEquiv Λ W G' (f ≫ g) =
      g.hom.app (op W) (Etale.moduleFreeSheafHomEquiv Λ W G f)

lemma Etale.moduleFreeSheafHomEquiv_map {W W' : X.Etale} (v : W' ⟶ W)
    (G : Etale.ModuleSheaf Λ X)
    (f : (Etale.moduleFreeSheaf Λ X).obj W ⟶ G) :
    Etale.moduleFreeSheafHomEquiv Λ W' G ((Etale.moduleFreeSheaf Λ X).map v ≫ f) =
      G.obj.map v.op (Etale.moduleFreeSheafHomEquiv Λ W G f)

lemma Etale.moduleFreeSheafSections_naturality
    {G G' : Etale.ModuleSheaf Λ X} (g : G ⟶ G') :
    Etale.moduleFreeSheafSections Λ G ≫ Etale.sectionsMap g =
      Functor.whiskerLeft (Etale.moduleFreeSheaf Λ X).op (preadditiveYoneda.map g) ≫
        Etale.moduleFreeSheafSections Λ G'

noncomputable def Etale.singleBoundaryHomotopy
    {C : Type*} [Category* C] [Abelian C] (N : CochainComplex C ℤ) {A : C}
    (f : (HomologicalComplex.single _ (.up ℤ) 0).obj A ⟶ N) (b : A ⟶ N.X (-1))
    (hb : f.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom ≫ b ≫ N.d (-1) 0) :
    Homotopy f 0 :=
  (Homotopy.ofEq (HomologicalComplex.from_single_hom_ext (j := 0) (by
    rw [hb, Homotopy.nullHomotopicMap'_f (k₂ := -1) (k₀ := 1) (by simp) (by simp)]
    simp
    rfl)) :
      Homotopy f (Homotopy.nullHomotopicMap' (fun i j (_ : j + 1 = i) ↦
        if hi : i = 0 then
          (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 A i hi).hom ≫ b ≫
            eqToHom (by congr 1; lia)
        else 0))).trans (Homotopy.nullHomotopy' _)

private noncomputable def homotopyOfSingleCycles
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (N : CochainComplex C ℤ) {A : C}
    (f : (HomologicalComplex.single C (.up ℤ) 0).obj A ⟶ N) (b : A ⟶ N.X (-1))
    (hb : DerivedCategory.singleCyclesHom A ≫ HomologicalComplex.cyclesMap f 0 =
      b ≫ N.toCycles (-1) 0) : Homotopy f 0 := by
  let τ := DerivedCategory.singleCyclesHom A ≫
    (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 A).hom
  have hτ : DerivedCategory.singleCyclesHom A ≫
      ((HomologicalComplex.single C (.up ℤ) 0).obj A).iCycles 0 =
        τ ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv := by
    simp [τ, HomologicalComplex.singleObjCyclesSelfIso_hom]
  apply Etale.singleBoundaryHomotopy N f (inv τ ≫ b)
  have h := hb =≫ N.iCycles 0
  rw [Category.assoc, HomologicalComplex.cyclesMap_i, Category.assoc,
    HomologicalComplex.toCycles_i, ← Category.assoc, hτ, Category.assoc] at h
  simp only [Category.assoc]
  rw [← h]
  simp

noncomputable def Etale.higherDirectImagePresheaf {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Etale.moduleFreeSheaf Λ X ⋙ (Etale.moduleUpperStar Λ h) ⋙
    DerivedCategory.Plus.singleFunctor _ 0).op ⋙ preadditiveYoneda.obj (K⟦q⟧)

noncomputable def Etale.derivedHomToHomology
    (L : DerivedCategory.Plus (Etale.ModuleSheaf Λ X)) :
    (Etale.moduleFreeSheaf Λ X ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj L ⟶
      (Etale.moduleFreeSheaf Λ X).op ⋙ preadditiveYoneda.obj
        ((DerivedCategory.Plus.homologyFunctor _ 0).obj L) where
  app W := AddCommGrpCat.ofHom <|
    (Preadditive.leftComp _
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _)).comp
      (DerivedCategory.Plus.homologyFunctor _ 0).mapAddHom
  naturality W W' g := by
    have hs := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
      (C := Etale.ModuleSheaf Λ X) 0).inv.naturality
        ((Etale.moduleFreeSheaf Λ X).map g.unop)
    dsimp at hs
    ext f
    revert f
    change ∀ f : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.moduleFreeSheaf Λ X).obj
    W.unop) ⟶
        L,
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map ((Etale.moduleFreeSheaf Λ X).map g.unop)
    ≫ f) =
      (Etale.moduleFreeSheaf Λ X).map g.unop ≫
        (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app
          ((Etale.moduleFreeSheaf Λ X).obj W.unop) ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map f
    intro f
    rw [Functor.map_comp, ← reassoc_of% hs]

lemma Etale.derivedHomToHomology_app_apply
    (L : DerivedCategory.Plus (Etale.ModuleSheaf Λ X))
    (W : X.Etaleᵒᵖ)
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.moduleFreeSheaf Λ X).obj W.unop) ⟶
    L) :
    (Etale.derivedHomToHomology L).app W β =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map β

noncomputable abbrev Etale.sectionsMap {G G' : Etale.ModuleSheaf Λ X}
    (g : G ⟶ G') :
    ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G).obj ⟶
    ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G').obj :=
  ((sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map g).hom

lemma Etale.derivedHomToHomology_app_eq {W : X.Etaleᵒᵖ}
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.moduleFreeSheaf Λ X).obj W.unop) ⟶
      DerivedCategory.Plus.Q.obj M)
    (f : (HomologicalComplex.single _ (.up ℤ) 0).obj ((Etale.moduleFreeSheaf Λ X).obj W.unop) ⟶
    M.obj)
    (hf : DerivedCategory.Plus.ι.map β =
      DerivedCategory.Q.map f ≫ (DerivedCategory.quotientCompQhIso _).inv.app M.obj) :
    (Etale.derivedHomToHomology (DerivedCategory.Plus.Q.obj M)).app W β =
      DerivedCategory.singleCyclesHom _ ≫ HomologicalComplex.cyclesMap f 0 ≫
        M.obj.homologyπ 0 ≫ Etale.homologyComparison M

theorem Etale.isLocallySurjective_derivedHomToHomology [M.obj.IsKInjective] :
    Presheaf.IsLocallySurjective X.smallEtaleTopology
      (Etale.derivedHomToHomology (DerivedCategory.Plus.Q.obj M) ≫
        Etale.moduleFreeSheafSections Λ
          ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M)))

noncomputable def Etale.homotopyOfSingle {A : Etale.ModuleSheaf Λ X}
    (f : (HomologicalComplex.single _ (.up ℤ) 0).obj A ⟶ M.obj) (b : A ⟶ M.obj.X (-1))
    (hb : f.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom ≫ b ≫ M.obj.d (-1) 0) :
    Homotopy f 0 :=
  Etale.singleBoundaryHomotopy M.obj f b hb

theorem Etale.isLocallyInjective_derivedHomToHomology [M.obj.IsKInjective] :
    Presheaf.IsLocallyInjective X.smallEtaleTopology
      (Etale.derivedHomToHomology (DerivedCategory.Plus.Q.obj M) ≫
        Etale.moduleFreeSheafSections Λ
          ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M)))

theorem Etale.isLocallyBijective_derivedHomToHomology
    (L : DerivedCategory.Plus (Etale.ModuleSheaf Λ X)) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology
        (Etale.derivedHomToHomology L ≫
          Etale.moduleFreeSheafSections Λ ((DerivedCategory.Plus.homologyFunctor _ 0).obj L)) ∧
      Presheaf.IsLocallySurjective X.smallEtaleTopology
        (Etale.derivedHomToHomology L ≫
          Etale.moduleFreeSheafSections Λ ((DerivedCategory.Plus.homologyFunctor _ 0).obj L))

noncomputable def Etale.higherDirectImagePresheafIso {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Etale.ModuleSheaf Λ Y)) :
    Etale.higherDirectImagePresheaf Λ h q K ≅
      (Etale.moduleFreeSheaf Λ X ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj (R+((Etale.moduleLowerStar Λ h)).obj (K⟦q⟧)) :=
  Functor.isoWhiskerRight (NatIso.op (Functor.isoWhiskerLeft (Etale.moduleFreeSheaf Λ X)
    (((Etale.moduleUpperStar Λ h)).mapDerivedCategoryPlusSingleFunctor 0)))
      (preadditiveYoneda.obj (K⟦q⟧)) ≪≫
  NatIso.ofComponents (fun W ↦ AddEquiv.toAddCommGrpIso
    ((Etale.moduleDerivedAdjunction Λ h).homAddEquiv _ _))
    (fun g ↦ by
      ext f
      exact (Etale.moduleDerivedAdjunction Λ h).homEquiv_naturality_left _ _)

noncomputable def Etale.higherDirectImagePresheafToHom {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Etale.ModuleSheaf Λ Y)) :
    Etale.higherDirectImagePresheaf Λ h q K ⟶
      (Etale.moduleFreeSheaf Λ X).op ⋙ preadditiveYoneda.obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj (R+((Etale.moduleLowerStar Λ h)).obj K)) :=
  (Etale.higherDirectImagePresheafIso Λ h q K).hom ≫
  Etale.derivedHomToHomology (R+((Etale.moduleLowerStar Λ h)).obj (K⟦q⟧)) ≫
  Functor.whiskerLeft (Etale.moduleFreeSheaf Λ X).op (preadditiveYoneda.map
    ((DerivedCategory.Plus.homologyFunctor _ 0).map
      ((R+((Etale.moduleLowerStar Λ h)).commShiftIso q).hom.app K) ≫
    ((DerivedCategory.Plus.homologyFunctor _ 0).isoShiftZero ℤ).inv.app _ ≫
      ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso q 0 q (add_zero q)).hom.app _))

noncomputable def Etale.higherDirectImagePresheafToSheaf {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.higherDirectImagePresheaf Λ h q K ⟶
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((DerivedCategory.Plus.homologyFunctor _ q).obj
            (R+((Etale.moduleLowerStar Λ h)).obj K))) :=
  Etale.higherDirectImagePresheafToHom Λ h q K ≫ Etale.moduleFreeSheafSections Λ _

theorem Etale.isLocallyBijective_higherDirectImagePresheafToSheaf {X Y : Scheme.{u}}
    (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Etale.ModuleSheaf Λ Y)) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology
        (Etale.higherDirectImagePresheafToSheaf Λ h q K) ∧
      Presheaf.IsLocallySurjective X.smallEtaleTopology
        (Etale.higherDirectImagePresheafToSheaf Λ h q K)

theorem Etale.isIso_higherDirectImagePresheafToSheaf {X Y : Scheme.{u}}
    (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h] (q : ℤ)
    (K : DerivedCategory.Plus (Etale.ModuleSheaf Λ Y)) :
    IsIso (((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _ _).symm
      (Etale.higherDirectImagePresheafToSheaf Λ h q K))

theorem Etale.isIso_higherDirectImagePresheafToSheaf_singleFunctor
    {X Y : Scheme.{u}} (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h] (q : ℤ)
    (F : Etale.ModuleSheaf Λ Y) :
    IsIso (((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _ _).symm
      (Etale.higherDirectImagePresheafToSheaf Λ h q
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))

noncomputable def Etale.higherDirectImagePresheafMap {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    {K K' : DerivedCategory.Plus (Etale.ModuleSheaf Λ Y)}
    (φ : K ⟶ K') :
    Etale.higherDirectImagePresheaf Λ h q K ⟶ Etale.higherDirectImagePresheaf Λ h q K' :=
  Functor.whiskerLeft _ (preadditiveYoneda.map ((shiftFunctor _ q).map φ))

noncomputable abbrev Etale.homologyShiftComparison {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Etale.ModuleSheaf Λ Y)) :
    (DerivedCategory.Plus.homologyFunctor _ 0).obj (R+((Etale.moduleLowerStar Λ h)).obj (K⟦q⟧)) ⟶
      (DerivedCategory.Plus.homologyFunctor _ q).obj (R+((Etale.moduleLowerStar Λ h)).obj K) :=
  (DerivedCategory.Plus.homologyFunctor _ 0).map
      ((R+((Etale.moduleLowerStar Λ h)).commShiftIso q).hom.app K) ≫
    ((DerivedCategory.Plus.homologyFunctor _ 0).isoShiftZero ℤ).inv.app _ ≫
      ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso q 0 q (add_zero q)).hom.app _

lemma Etale.higherDirectImagePresheafToHom_app_apply {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Etale.ModuleSheaf Λ Y))
    (W : X.Etaleᵒᵖ) (β : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((Etale.moduleUpperStar Λ h).obj ((Etale.moduleFreeSheaf Λ X).obj W.unop)) ⟶ K⟦q⟧) :
    (Etale.higherDirectImagePresheafToHom Λ h q K).app W β =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map
          ((Etale.moduleDerivedAdjunction Λ h).homEquiv _ _
            ((((Etale.moduleUpperStar Λ h)).mapDerivedCategoryPlusSingleFunctor 0).hom.app
              ((Etale.moduleFreeSheaf Λ X).obj W.unop) ≫ β)) ≫
        Etale.homologyShiftComparison Λ h q K

lemma Etale.homologyShiftComparison_naturality {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    {K K' : DerivedCategory.Plus (Etale.ModuleSheaf Λ Y)}
    (φ : K ⟶ K') :
    (DerivedCategory.Plus.homologyFunctor _ 0).map
        (R+((Etale.moduleLowerStar Λ h)).map ((shiftFunctor _ q).map φ)) ≫
      Etale.homologyShiftComparison Λ h q K' =
    Etale.homologyShiftComparison Λ h q K ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map (R+((Etale.moduleLowerStar Λ h)).map φ)

lemma Etale.higherDirectImagePresheafToSheaf_naturality {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    {K K' : DerivedCategory.Plus (Etale.ModuleSheaf Λ Y)}
    (φ : K ⟶ K') :
    Etale.higherDirectImagePresheafMap Λ h q φ ≫ Etale.higherDirectImagePresheafToSheaf Λ h q K' =
      Etale.higherDirectImagePresheafToSheaf Λ h q K ≫ Etale.sectionsMap
        ((DerivedCategory.Plus.homologyFunctor _ q).map
          (R+((Etale.moduleLowerStar Λ h)).map φ))

noncomputable def Etale.higherDirectImagePresheafFunctor {X Y : Scheme.{u}} (h : Y ⟶ X)
    (q : ℤ) :
    DerivedCategory.Plus (Etale.ModuleSheaf Λ Y) ⥤
      X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  shiftFunctor _ q ⋙ preadditiveYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj
    (Etale.moduleFreeSheaf Λ X ⋙ (Etale.moduleUpperStar Λ h) ⋙ DerivedCategory.Plus.singleFunctor
    _ 0).op
```

The original instance values are shared locally. The four data instances are reducible
so downstream strict instance comparisons can unfold them; EnoughInjectives is a proposition
and stays an ordinary local instance. Their inferred values are unchanged:

```lean
@[reducible]
noncomputable local instance Etale.moduleSheafCategory (X : Scheme.{u}) :
    Category.{u + 1} (Etale.ModuleSheaf Λ X) :=
  inferInstanceAs (Category.{u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

@[reducible]
noncomputable local instance Etale.moduleSheafPreadditive (X : Scheme.{u}) :
    Preadditive (Etale.ModuleSheaf Λ X) :=
  inferInstanceAs (Preadditive (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

@[reducible]
noncomputable local instance Etale.moduleSheafAbelian (X : Scheme.{u}) :
    Abelian (Etale.ModuleSheaf Λ X) :=
  inferInstanceAs (Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

@[reducible]
noncomputable local instance Etale.moduleSheafHasDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory (Etale.ModuleSheaf Λ X) :=
  inferInstanceAs (HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

noncomputable local instance Etale.moduleSheafEnoughInjectives (X : Scheme.{u}) :
    EnoughInjectives (Etale.ModuleSheaf Λ X) :=
  inferInstanceAs (EnoughInjectives (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
```

The named category is made reducible only after this file has been elaborated,
so callers can infer the original category instances for objects whose types
contain `ModuleSheaf`. No instance is registered globally.

```lean
attribute [reducible] Etale.ModuleSheaf
```

The redundant direct FullyFaithful import is removed: the retained public
DerivabilityStructureInjectives import already publicly imports it. The two added
Sheaf imports are proof-only;
all other original public imports are retained.

## Users

The source-only downstream scan gives the following users of changed names and direct importers. Each
accepts the same mathematical statement, by unfolding the named category and functors;
Only HigherDirectImageRawTrianglePullbackComposition is adapted in this repair.
Holders are the local coordination snapshot.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleFreeSheafDerivedSections | unclaimed | Definitionally equal category/functor expressions; no signature or statement change in this user. |
| Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi | unclaimed | Definitionally equal category/functor expressions; no signature or statement change in this user. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalClassVanishing | unclaimed | Definitionally equal category/functor expressions; no signature or statement change in this user. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep | P1 | Definitionally equal category/functor expressions; no signature or statement change in this user. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality | P3 | Unchanged; retaining the original raw K input categories allows its strict instance inference. Full-file validation passes. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHom | X2 | Definitionally equal category/functor expressions; no signature or statement change in this user. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback | C2 | Definitionally equal category/functor expressions; no signature or statement change in this user. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullbackComposition | unclaimed | Forced proof adaptation: allow alias unfolding only in the final rawTriangleMap_comp application; signature and visibility unchanged. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageLargeFilteredColimit | unclaimed | Definitionally equal category/functor expressions; no signature or statement change in this user. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit | unclaimed | Definitionally equal category/functor expressions; no signature or statement change in this user. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf | unclaimed | Definitionally equal category/functor expressions; no signature or statement change in this user. |
| WeilConjectures | unclaimed | Direct importer; existing instance search is preserved. No source adaptation. |

The earlier source-only transitive import scan lists 226 downstream modules. This repair
adapts only HigherDirectImageRawTrianglePullbackComposition. The original free-sheaf
interfaces preserve their inferred raw instances; the other interfaces use
definitionally equal category/functor aliases.
The maintainer's global build verifies the transitive closure.


## Repair validation

The second reader found category instance inference failures in unchanged
HigherDirectImageRawTransitionToHom and in the raw-signature check against a
fresh artifact. Making ModuleSheaf reducible at the end restores downstream
instance synthesis while retaining local cached instances within this module.
The global build later exposed the additional failure documented below.


## Forced adaptation in repair XRfef4bc449ceae451

The original consumer fails at line 114 against the freshly compiled landed dependency:

```text
failed to synthesize instance of type class
  D+((b)^*[ModuleCat Λ]).CommShift ℤ
```

The final application of `rawTriangleMap_comp` compares raw derived-category structures
with those exposed through `higherDirectImagePresheaf` and its ModuleSheaf aliases.
The theorem's existing `backward.isDefEq.respectTransparency true` setting prevents
Lean's backward elaborator from identifying these definitionally equal structures
while it resolves the derived pullback's shift-commutation instance.

Allow that unfolding only for this final proof application. All supplied functors,
comparisons, coefficient maps, the class and the source coherence proof are unchanged.
This option controls elaboration; kernel checking remains enabled and unchanged.
There is no new instance, lemma, import, mathematical argument or hole.

Old proof application begins:

```lean
  exact rawTriangleMap_comp
    (freeSheaf Λ S) (h)^*[ModuleCat.{u + 1} Λ]
```

New proof application begins:

```lean
  set_option backward.isDefEq.respectTransparency false in
  exact rawTriangleMap_comp
    (freeSheaf Λ S) (h)^*[ModuleCat.{u + 1} Λ]
```

The only source edit is this added line, at line 114 of
Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullbackComposition (unclaimed).
All existing signatures, visibility and docstrings remain byte-for-byte unchanged.
CohomologyPresheaf and both existing node records remain unchanged from the broken tip.
The route and proof dependencies are unchanged, so no DAG update is required.

Fresh local validation through lcompile.py, one module per invocation:
CohomologyPresheaf compiled in 43.7 seconds; the unchanged consumer reproduced the
reported failure in 21.8 seconds; the repaired consumer compiled in 27.0 seconds.
The original 60-second per-file limit remains in force. See report.md.

## Status

landed 20261013T201813-L-3978570 2026-10-13 (merge of deliver/XRfef4bc449ceae451/WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf)

Original delivery: landed 20261013T190141-L-3216641 2026-10-13 (merge of deliver/H4/WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf)
