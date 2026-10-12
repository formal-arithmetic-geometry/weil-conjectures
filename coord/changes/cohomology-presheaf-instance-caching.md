# AlgebraicGeometry.Etale.ModuleSheaf and cohomology-presheaf category instances

## Reason

The original assigned file and the earlier reduction both exceed the required 60-second
single-file limit. Profiling found repeated kernel checking of the large sheaf-category
instances in derived constructions. A named specialization `Etale.ModuleSheaf` caches the
existing Category, Preadditive, Abelian, HasDerivedCategory and EnoughInjectives instances.
The inverse/direct image abbreviations fix their source and target category instances;
the derived adjunction is an abbreviation of the existing adjunction. All these values
are the original values, not replacement mathematical constructions.

`ModuleSheaf` is a semireducible `def`, rather than an `abbrev`, to retain the instance
sharing during elaboration. Making it an abbreviation in the diagnostic full file again
exceeded 60 seconds. The general `Sheaf` construction is unchanged; this is its named
specialization for the small etale site and ModuleCat coefficients. Inverse image,
direct image, and the derived adjunction are all abbreviations of the original operations.

The existing boundary-homotopy construction is generalized to an arbitrary abelian
category as `singleBoundaryHomotopy`; `homotopyOfSingle` abbreviates its original
specialization. A proved private helper converts a cycle boundary into the degree-zero
boundary needed by that construction. The local-injectivity proof uses injectivity of the
free-sheaf section equivalence and cancels the homology comparison explicitly.
No new mathematical assumption is introduced.

The old long public import of DerivabilityStructureInjectives is now proof-only: its
three lemmas are used only by proofs here, and repository search found no downstream
uses. FullyFaithful is imported publicly for the cycle comparison in the public
derivedHomToHomology_app_eq signature. Both imports remain genuine dependencies. This also fixes the old
102-character import line without using import syntax the tools cannot recognize.

No declaration in Challenge.lean is edited. The changed signatures below unfold to the
same categories and functors, so no hypothesis or conclusion changes. The five targets
use none of these names in their statements or their defining base-change operations.
The maintainer should include this definitional-equality check in any reopened target
statement review required by AGENTS.md section 4.

## Old

These are verbatim old declarations or signatures under the unchanged namespace,
universe and variables of the assigned module. Definitions include their bodies;
proof-only theorem changes are described above.

```lean
noncomputable def Etale.freeSheaf (X : Scheme.{u}) :
    X.Etale ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  uliftYoneda.{u + 1} ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free Λ) ⋙
    presheafToSheaf _ _

noncomputable def Etale.higherDirectImagePresheaf {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Etale.freeSheaf Λ X ⋙ (h)^*[ModuleCat.{u + 1} Λ] ⋙
    DerivedCategory.Plus.singleFunctor _ 0).op ⋙ preadditiveYoneda.obj (K⟦q⟧)

noncomputable def Etale.freeSheafSections {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.freeSheaf Λ X).op ⋙ preadditiveYoneda.obj G ⟶
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G).obj where
  app W := AddCommGrpCat.ofHom
    { toFun f := (f.hom.app W).hom (((toSheafify X.smallEtaleTopology
        (uliftYoneda.{u + 1}.obj W.unop ⋙ ModuleCat.free Λ)).app W).hom
          (ModuleCat.freeMk (ULift.up (𝟙 W.unop))))
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality W W' g := by
    ext f
    have h₁ := congr_arg (fun k ↦ (k.app W').hom (ModuleCat.freeMk (ULift.up (𝟙 W'.unop))))
      (toSheafify_naturality X.smallEtaleTopology
        (Functor.whiskerRight (uliftYoneda.{u + 1}.map g.unop) (ModuleCat.free Λ)))
    have h₂ := congr_arg (fun k ↦ k.hom (ModuleCat.freeMk (ULift.up (𝟙 W.unop))))
      ((toSheafify X.smallEtaleTopology
        (uliftYoneda.{u + 1}.obj W.unop ⋙ ModuleCat.free Λ)).naturality g)
    have h₃ := congr_arg (fun k ↦ k.hom (((toSheafify X.smallEtaleTopology
        (uliftYoneda.{u + 1}.obj W.unop ⋙ ModuleCat.free Λ)).app W).hom
          (ModuleCat.freeMk (ULift.up (𝟙 W.unop))))) (f.hom.naturality g)
    have h₀ : ((ModuleCat.free Λ).map ((uliftYoneda.{u + 1}.map g.unop).app W')).hom
        (ModuleCat.freeMk (ULift.up (𝟙 W'.unop))) =
        ((ModuleCat.free Λ).map ((uliftYoneda.{u + 1}.obj W.unop).map g)).hom
          (ModuleCat.freeMk (ULift.up (𝟙 W.unop))) := by
      simp
    dsimp at h₁ h₂ h₃
    exact (congr_arg (f.hom.app W').hom h₁.symm).trans
      ((congr_arg (fun x ↦ (f.hom.app W').hom
        (((toSheafify X.smallEtaleTopology
          (uliftYoneda.{u + 1}.obj W.unop ⋙ ModuleCat.free Λ)).app W').hom x)) h₀).trans
        ((congr_arg (f.hom.app W').hom h₂).trans h₃))

noncomputable def Etale.freeSheafHomEquiv (W : X.Etale)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((Etale.freeSheaf Λ X).obj W ⟶ G) ≃ G.obj.obj (op W) :=
  ((sheafificationAdjunction _ _).homEquiv _ _).trans <|
    (((ModuleCat.adj Λ).whiskerRight X.Etaleᵒᵖ).homEquiv _ _).trans uliftYonedaEquiv

lemma Etale.freeSheafHomEquiv_apply (W : X.Etale)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (f : (Etale.freeSheaf Λ X).obj W ⟶ G) :
    Etale.freeSheafHomEquiv Λ W G f = (Etale.freeSheafSections Λ G).app (op W) f

lemma Etale.freeSheafHomEquiv_comp (W : X.Etale)
    {G G' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (f : (Etale.freeSheaf Λ X).obj W ⟶ G) (g : G ⟶ G') :
    Etale.freeSheafHomEquiv Λ W G' (f ≫ g) =
      g.hom.app (op W) (Etale.freeSheafHomEquiv Λ W G f)

lemma Etale.freeSheafHomEquiv_map {W W' : X.Etale} (v : W' ⟶ W)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (f : (Etale.freeSheaf Λ X).obj W ⟶ G) :
    Etale.freeSheafHomEquiv Λ W' G ((Etale.freeSheaf Λ X).map v ≫ f) =
      G.obj.map v.op (Etale.freeSheafHomEquiv Λ W G f)

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

lemma Etale.freeSheafSections_naturality
    {G G' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (g : G ⟶ G') :
    Etale.freeSheafSections Λ G ≫ Etale.sectionsMap g =
      Functor.whiskerLeft (Etale.freeSheaf Λ X).op (preadditiveYoneda.map g) ≫
        Etale.freeSheafSections Λ G'

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

noncomputable def Etale.upperStarFreeSheafHomEquiv {X Y : Scheme.{u}} (h : Y ⟶ X) (W : X.Etale)
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W) ⟶ G) ≃
      ((Etale.freeSheaf Λ Y).obj ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W) ⟶ G) :=
  ((Etale.upperStarLowerStarAdjunction _ h).homEquiv _ _).trans
    ((Etale.freeSheafHomEquiv Λ W _).trans (Etale.freeSheafHomEquiv Λ _ G).symm)

lemma Etale.upperStarFreeSheafHomEquiv_comp {X Y : Scheme.{u}} (h : Y ⟶ X) (W : X.Etale)
    {G G' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (a : (h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W) ⟶ G) (g : G ⟶ G') :
    Etale.upperStarFreeSheafHomEquiv Λ h W G' (a ≫ g) =
      Etale.upperStarFreeSheafHomEquiv Λ h W G a ≫ g

noncomputable def Etale.upperStarFreeSheafIso {X Y : Scheme.{u}} (h : Y ⟶ X) (W : X.Etale) :
    (h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W) ≅
      (Etale.freeSheaf Λ Y).obj ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W) :=
  Coyoneda.ext _ _ (fun f ↦ Etale.upperStarFreeSheafHomEquiv Λ h W _ f)
    (fun g ↦ (Etale.upperStarFreeSheafHomEquiv Λ h W _).symm g) (by simp) (by simp) (by
      intro Z Z' f g
      apply (Etale.upperStarFreeSheafHomEquiv Λ h W _).injective
      rw [Etale.upperStarFreeSheafHomEquiv_comp]
      simp)

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

The additional named category specialization, cached instances, functor abbreviations,
generic boundary homotopy and private cycle-boundary helper did not previously exist.
The old public DerivabilityStructureInjectives import becomes the same proof-only import.

## New

These are the corresponding new definitions and signatures in that same context.
The assigned vanishing theorem's signature is unchanged and its two-step reduction
is recorded by lem-sbc-constant-module-higher-direct-image-local-vanishing.

```lean
def Etale.ModuleSheaf (X : Scheme.{u}) : Type (u + 2) :=
  Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)

noncomputable instance Etale.moduleSheafCategory (X : Scheme.{u}) :
    Category.{u + 1} (Etale.ModuleSheaf Λ X) :=
  inferInstanceAs (Category.{u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

noncomputable instance Etale.moduleSheafPreadditive (X : Scheme.{u}) :
    Preadditive (Etale.ModuleSheaf Λ X) :=
  inferInstanceAs (Preadditive (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

noncomputable instance Etale.moduleSheafAbelian (X : Scheme.{u}) :
    Abelian (Etale.ModuleSheaf Λ X) :=
  inferInstanceAs (Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

noncomputable instance Etale.moduleSheafHasDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory (Etale.ModuleSheaf Λ X) :=
  inferInstanceAs (HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

noncomputable instance Etale.moduleSheafEnoughInjectives (X : Scheme.{u}) :
    EnoughInjectives (Etale.ModuleSheaf Λ X) :=
  inferInstanceAs (EnoughInjectives (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

noncomputable abbrev Etale.moduleUpperStar {X Y : Scheme.{u}} (h : Y ⟶ X) :
    Etale.ModuleSheaf Λ X ⥤ Etale.ModuleSheaf Λ Y :=
  (h)^*[ModuleCat.{u + 1} Λ]

noncomputable abbrev Etale.moduleLowerStar {X Y : Scheme.{u}} (h : Y ⟶ X) :
    Etale.ModuleSheaf Λ Y ⥤ Etale.ModuleSheaf Λ X :=
  (h)_*[ModuleCat.{u + 1} Λ]

instance Etale.moduleUpperStarAdditive {X Y : Scheme.{u}} (h : Y ⟶ X) :
    (Etale.moduleUpperStar Λ h).Additive :=
  inferInstanceAs ((h)^*[ModuleCat.{u + 1} Λ]).Additive

instance Etale.moduleLowerStarAdditive {X Y : Scheme.{u}} (h : Y ⟶ X) :
    (Etale.moduleLowerStar Λ h).Additive :=
  inferInstanceAs ((h)_*[ModuleCat.{u + 1} Λ]).Additive

instance Etale.moduleUpperStarPreservesFiniteLimits {X Y : Scheme.{u}} (h : Y ⟶ X) :
    PreservesFiniteLimits (Etale.moduleUpperStar Λ h) :=
  inferInstanceAs (PreservesFiniteLimits ((h)^*[ModuleCat.{u + 1} Λ]))

instance Etale.moduleUpperStarPreservesFiniteColimits {X Y : Scheme.{u}} (h : Y ⟶ X) :
    PreservesFiniteColimits (Etale.moduleUpperStar Λ h) :=
  inferInstanceAs (PreservesFiniteColimits ((h)^*[ModuleCat.{u + 1} Λ]))

noncomputable abbrev Etale.moduleDerivedAdjunction {X Y : Scheme.{u}} (h : Y ⟶ X) :
    D+(Etale.moduleUpperStar Λ h) ⊣ R+(Etale.moduleLowerStar Λ h) :=
  Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h

noncomputable def Etale.freeSheaf (X : Scheme.{u}) :
    X.Etale ⥤ Etale.ModuleSheaf Λ X :=
  uliftYoneda.{u + 1} ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free Λ) ⋙
    presheafToSheaf _ _

noncomputable def Etale.higherDirectImagePresheaf {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Etale.ModuleSheaf Λ Y)) :
    X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Etale.freeSheaf Λ X ⋙ (Etale.moduleUpperStar Λ h) ⋙
    DerivedCategory.Plus.singleFunctor _ 0).op ⋙ preadditiveYoneda.obj (K⟦q⟧)

noncomputable def Etale.freeSheafSections {X : Scheme.{u}}
    (G : Etale.ModuleSheaf Λ X) :
    (Etale.freeSheaf Λ X).op ⋙ preadditiveYoneda.obj G ⟶
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G).obj where
  app W := AddCommGrpCat.ofHom
    { toFun f := (f.hom.app W).hom (((toSheafify X.smallEtaleTopology
        (uliftYoneda.{u + 1}.obj W.unop ⋙ ModuleCat.free Λ)).app W).hom
          (ModuleCat.freeMk (ULift.up (𝟙 W.unop))))
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality W W' g := by
    ext f
    have h₁ := congr_arg (fun k ↦ (k.app W').hom (ModuleCat.freeMk (ULift.up (𝟙 W'.unop))))
      (toSheafify_naturality X.smallEtaleTopology
        (Functor.whiskerRight (uliftYoneda.{u + 1}.map g.unop) (ModuleCat.free Λ)))
    have h₂ := congr_arg (fun k ↦ k.hom (ModuleCat.freeMk (ULift.up (𝟙 W.unop))))
      ((toSheafify X.smallEtaleTopology
        (uliftYoneda.{u + 1}.obj W.unop ⋙ ModuleCat.free Λ)).naturality g)
    have h₃ := congr_arg (fun k ↦ k.hom (((toSheafify X.smallEtaleTopology
        (uliftYoneda.{u + 1}.obj W.unop ⋙ ModuleCat.free Λ)).app W).hom
          (ModuleCat.freeMk (ULift.up (𝟙 W.unop))))) (f.hom.naturality g)
    have h₀ : ((ModuleCat.free Λ).map ((uliftYoneda.{u + 1}.map g.unop).app W')).hom
        (ModuleCat.freeMk (ULift.up (𝟙 W'.unop))) =
        ((ModuleCat.free Λ).map ((uliftYoneda.{u + 1}.obj W.unop).map g)).hom
          (ModuleCat.freeMk (ULift.up (𝟙 W.unop))) := by
      simp
    dsimp at h₁ h₂ h₃
    exact (congr_arg (f.hom.app W').hom h₁.symm).trans
      ((congr_arg (fun x ↦ (f.hom.app W').hom
        (((toSheafify X.smallEtaleTopology
          (uliftYoneda.{u + 1}.obj W.unop ⋙ ModuleCat.free Λ)).app W').hom x)) h₀).trans
        ((congr_arg (f.hom.app W').hom h₂).trans h₃))

noncomputable def Etale.freeSheafHomEquiv (W : X.Etale)
    (G : Etale.ModuleSheaf Λ X) :
    ((Etale.freeSheaf Λ X).obj W ⟶ G) ≃ G.obj.obj (op W) :=
  ((sheafificationAdjunction _ _).homEquiv _ _).trans <|
    (((ModuleCat.adj Λ).whiskerRight X.Etaleᵒᵖ).homEquiv _ _).trans uliftYonedaEquiv

lemma Etale.freeSheafHomEquiv_apply (W : X.Etale)
    (G : Etale.ModuleSheaf Λ X)
    (f : (Etale.freeSheaf Λ X).obj W ⟶ G) :
    Etale.freeSheafHomEquiv Λ W G f = (Etale.freeSheafSections Λ G).app (op W) f

lemma Etale.freeSheafHomEquiv_comp (W : X.Etale)
    {G G' : Etale.ModuleSheaf Λ X}
    (f : (Etale.freeSheaf Λ X).obj W ⟶ G) (g : G ⟶ G') :
    Etale.freeSheafHomEquiv Λ W G' (f ≫ g) =
      g.hom.app (op W) (Etale.freeSheafHomEquiv Λ W G f)

lemma Etale.freeSheafHomEquiv_map {W W' : X.Etale} (v : W' ⟶ W)
    (G : Etale.ModuleSheaf Λ X)
    (f : (Etale.freeSheaf Λ X).obj W ⟶ G) :
    Etale.freeSheafHomEquiv Λ W' G ((Etale.freeSheaf Λ X).map v ≫ f) =
      G.obj.map v.op (Etale.freeSheafHomEquiv Λ W G f)

noncomputable def Etale.derivedHomToHomology
    (L : DerivedCategory.Plus (Etale.ModuleSheaf Λ X)) :
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
      (C := Etale.ModuleSheaf Λ X) 0).inv.naturality
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
    (L : DerivedCategory.Plus (Etale.ModuleSheaf Λ X))
    (W : X.Etaleᵒᵖ)
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj W.unop) ⟶ L) :
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

lemma Etale.freeSheafSections_naturality
    {G G' : Etale.ModuleSheaf Λ X} (g : G ⟶ G') :
    Etale.freeSheafSections Λ G ≫ Etale.sectionsMap g =
      Functor.whiskerLeft (Etale.freeSheaf Λ X).op (preadditiveYoneda.map g) ≫
        Etale.freeSheafSections Λ G'

noncomputable def Etale.singleBoundaryHomotopy
    {C : Type*} [Category* C] [Abelian C] (M : CochainComplex C ℤ) {A : C}
    (f : (HomologicalComplex.single _ (.up ℤ) 0).obj A ⟶ M) (b : A ⟶ M.X (-1))
    (hb : f.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom ≫ b ≫ M.d (-1) 0) :
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

noncomputable abbrev Etale.homotopyOfSingle {A : Etale.ModuleSheaf Λ X}
    (f : (HomologicalComplex.single _ (.up ℤ) 0).obj A ⟶ M.obj) (b : A ⟶ M.obj.X (-1))
    (hb : f.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom ≫ b ≫ M.obj.d (-1) 0) :
    Homotopy f 0 :=
  Etale.singleBoundaryHomotopy M.obj f b hb

private noncomputable def homotopyOfSingleCycles
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (M : CochainComplex C ℤ) {A : C}
    (f : (HomologicalComplex.single C (.up ℤ) 0).obj A ⟶ M) (b : A ⟶ M.X (-1))
    (hb : DerivedCategory.singleCyclesHom A ≫ HomologicalComplex.cyclesMap f 0 =
      b ≫ M.toCycles (-1) 0) : Homotopy f 0 := by
  let τ := DerivedCategory.singleCyclesHom A ≫
    (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 A).hom
  have hτ : DerivedCategory.singleCyclesHom A ≫
      ((HomologicalComplex.single C (.up ℤ) 0).obj A).iCycles 0 =
        τ ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv := by
    simp [τ, HomologicalComplex.singleObjCyclesSelfIso_hom]
  apply Etale.singleBoundaryHomotopy M f (inv τ ≫ b)
  have h := hb =≫ M.iCycles 0
  rw [Category.assoc, HomologicalComplex.cyclesMap_i, Category.assoc,
    HomologicalComplex.toCycles_i, ← Category.assoc, hτ, Category.assoc] at h
  simp only [Category.assoc]
  rw [← h]
  simp

theorem Etale.isLocallyBijective_derivedHomToHomology
    (L : DerivedCategory.Plus (Etale.ModuleSheaf Λ X)) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology
        (Etale.derivedHomToHomology L ≫
          Etale.freeSheafSections Λ ((DerivedCategory.Plus.homologyFunctor _ 0).obj L)) ∧
      Presheaf.IsLocallySurjective X.smallEtaleTopology
        (Etale.derivedHomToHomology L ≫
          Etale.freeSheafSections Λ ((DerivedCategory.Plus.homologyFunctor _ 0).obj L))

noncomputable def Etale.higherDirectImagePresheafIso {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Etale.ModuleSheaf Λ Y)) :
    Etale.higherDirectImagePresheaf Λ h q K ≅
      (Etale.freeSheaf Λ X ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj (R+((Etale.moduleLowerStar Λ h)).obj (K⟦q⟧)) :=
  Functor.isoWhiskerRight (NatIso.op (Functor.isoWhiskerLeft (Etale.freeSheaf Λ X)
    (((Etale.moduleUpperStar Λ h)).mapDerivedCategoryPlusSingleFunctor 0)))
      (preadditiveYoneda.obj (K⟦q⟧)) ≪≫
  NatIso.ofComponents (fun W ↦ AddEquiv.toAddCommGrpIso
    ((Etale.moduleDerivedAdjunction Λ h).homAddEquiv _ _))
    (fun g ↦ by
      ext f
      exact (Etale.moduleDerivedAdjunction Λ
        h).homEquiv_naturality_left _ _)

noncomputable def Etale.higherDirectImagePresheafToHom {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Etale.ModuleSheaf Λ Y)) :
    Etale.higherDirectImagePresheaf Λ h q K ⟶
      (Etale.freeSheaf Λ X).op ⋙ preadditiveYoneda.obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj (R+((Etale.moduleLowerStar Λ h)).obj K)) :=
  (Etale.higherDirectImagePresheafIso Λ h q K).hom ≫
  Etale.derivedHomToHomology (R+((Etale.moduleLowerStar Λ h)).obj (K⟦q⟧)) ≫
  Functor.whiskerLeft (Etale.freeSheaf Λ X).op (preadditiveYoneda.map
    ((DerivedCategory.Plus.homologyFunctor _ 0).map
      ((R+((Etale.moduleLowerStar Λ h)).commShiftIso q).hom.app K) ≫
    ((DerivedCategory.Plus.homologyFunctor _ 0).isoShiftZero ℤ).inv.app _ ≫
      ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso q 0 q (add_zero q)).hom.app _))

noncomputable def Etale.higherDirectImagePresheafToSheaf {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Etale.ModuleSheaf Λ Y)) :
    Etale.higherDirectImagePresheaf Λ h q K ⟶
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((DerivedCategory.Plus.homologyFunctor _ q).obj
            (R+((Etale.moduleLowerStar Λ h)).obj K))) :=
  Etale.higherDirectImagePresheafToHom Λ h q K ≫ Etale.freeSheafSections Λ _

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

noncomputable def Etale.upperStarFreeSheafHomEquiv {X Y : Scheme.{u}} (h : Y ⟶ X) (W : X.Etale)
    (G : Etale.ModuleSheaf Λ Y) :
    ((Etale.moduleUpperStar Λ h).obj ((Etale.freeSheaf Λ X).obj W) ⟶ G) ≃
      ((Etale.freeSheaf Λ Y).obj ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W) ⟶ G) :=
  ((Etale.upperStarLowerStarAdjunction _ h).homEquiv _ _).trans
    ((Etale.freeSheafHomEquiv Λ W _).trans (Etale.freeSheafHomEquiv Λ _ G).symm)

lemma Etale.upperStarFreeSheafHomEquiv_comp {X Y : Scheme.{u}} (h : Y ⟶ X) (W : X.Etale)
    {G G' : Etale.ModuleSheaf Λ Y}
    (a : (Etale.moduleUpperStar Λ h).obj ((Etale.freeSheaf Λ X).obj W) ⟶ G) (g : G ⟶ G') :
    Etale.upperStarFreeSheafHomEquiv Λ h W G' (a ≫ g) =
      Etale.upperStarFreeSheafHomEquiv Λ h W G a ≫ g

noncomputable def Etale.upperStarFreeSheafIso {X Y : Scheme.{u}} (h : Y ⟶ X) (W : X.Etale) :
    (Etale.moduleUpperStar Λ h).obj ((Etale.freeSheaf Λ X).obj W) ≅
      (Etale.freeSheaf Λ Y).obj ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W) :=
  Coyoneda.ext _ _ (fun f ↦ Etale.upperStarFreeSheafHomEquiv Λ h W _ f)
    (fun g ↦ (Etale.upperStarFreeSheafHomEquiv Λ h W _).symm g) (by simp) (by simp) (by
      intro Z Z' f g
      apply (Etale.upperStarFreeSheafHomEquiv Λ h W _).injective
      rw [Etale.upperStarFreeSheafHomEquiv_comp]
      simp)

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
      ((Etale.moduleUpperStar Λ h).obj ((Etale.freeSheaf Λ X).obj W.unop)) ⟶ K⟦q⟧) :
    (Etale.higherDirectImagePresheafToHom Λ h q K).app W β =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map
          ((Etale.moduleDerivedAdjunction Λ h).homEquiv _ _
            ((((Etale.moduleUpperStar Λ h)).mapDerivedCategoryPlusSingleFunctor 0).hom.app
              ((Etale.freeSheaf Λ X).obj W.unop) ≫ β)) ≫
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
    (Etale.freeSheaf Λ X ⋙ (Etale.moduleUpperStar Λ h) ⋙ DerivedCategory.Plus.singleFunctor _ 0).op
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit` | none | Uses `freeSheaf`, `sectionsMap`, `higherDirectImagePresheafToSheaf`, `isLocallyBijective_higherDirectImagePresheafToSheaf`, `higherDirectImagePresheafToSheaf_naturality`, `higherDirectImagePresheafFunctor`. The new types unfold to the original types, with the original functors and instances; no source adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf` | J1 | Uses `freeSheaf`, `freeSheafHomEquiv`, `freeSheafHomEquiv_comp`, `upperStarFreeSheafIso`. The new types unfold to the original types, with the original functors and instances; no source adaptation is required. |
| `Sheaf.AlgebraicGeometry.EtaleFreeSheafDerivedSections` | none | Uses `freeSheaf` in its derived-sections theorem signature. The named category and cached instances unfold to the original category; no source adaptation is required. A fresh scratch copy of the whole module compiles against the rebuilt sandbox module in 3.7 seconds. |

All occurrences listed by the downstream scan were read. FreeSheaf uses the free-sheaf
corepresenting equivalence and the inverse-image isomorphism. FilteredColimit uses those
same underlying sheaf categories, the presheaf functor, section maps and their naturality.
Direct API conversion checks cover these uses and compile without warnings in 4.7 seconds
against the rebuilt sandbox module, using the old raw Sheaf-category types. The full unchanged FreeSheaf module times
out both against the original cached library and against this delivery, so those full-file
attempts do not establish compatibility; this is a pre-existing compile limitation.
No adapted downstream source file is included or needed for the definitionally equal API.

## Status

landed 20261012T070548-L-3475998 2026-10-12 (merge of deliver/Q1/WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf)
