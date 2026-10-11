module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Morphisms out of `h^* Λ[W]` are morphisms out of `Λ[W ×_X Y]`. -/
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
      Etale.upperStarFreeSheafHomEquiv Λ h W G a ≫ g := by
  apply (Etale.freeSheafHomEquiv Λ _ G').injective
  simp only [Etale.upperStarFreeSheafHomEquiv, Equiv.trans_apply, Etale.freeSheafHomEquiv_comp,
    Adjunction.homEquiv_naturality_right]
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- The pullback of the free sheaf `Λ[W]` along `h : Y ⟶ X` is the free sheaf on `W ×_X Y`:
both corepresent the sections over `W ×_X Y`. -/
noncomputable def Etale.upperStarFreeSheafIso {X Y : Scheme.{u}} (h : Y ⟶ X) (W : X.Etale) :
    (h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W) ≅
      (Etale.freeSheaf Λ Y).obj ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W) :=
  Coyoneda.ext _ _ (fun f ↦ Etale.upperStarFreeSheafHomEquiv Λ h W _ f)
    (fun g ↦ (Etale.upperStarFreeSheafHomEquiv Λ h W _).symm g) (by simp) (by simp) (by
      intro Z Z' f g
      apply (Etale.upperStarFreeSheafHomEquiv Λ h W _).injective
      rw [Etale.upperStarFreeSheafHomEquiv_comp]
      simp)

/-- The map of hypercohomology presheaves `W ↦ Hᵠ(W ×_X Y, K|)` induced by `φ : K ⟶ K'`. -/
noncomputable def Etale.higherDirectImagePresheafMap {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    {K K' : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ K') :
    Etale.higherDirectImagePresheaf Λ h q K ⟶ Etale.higherDirectImagePresheaf Λ h q K' :=
  Functor.whiskerLeft _ (preadditiveYoneda.map ((shiftFunctor _ q).map φ))


/-- The shift identification `H⁰((Rh_* K)[q]) ≅ Hᵠ(Rh_* K)`. -/
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
        Etale.homologyShiftComparison Λ h q K := by
  simp only [Etale.higherDirectImagePresheafToHom, NatTrans.comp_app, ConcreteCategory.comp_apply,
    Etale.derivedHomToHomology_app_apply, Category.assoc]
  rfl

lemma Etale.homologyShiftComparison_naturality {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    {K K' : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ K') :
    (DerivedCategory.Plus.homologyFunctor _ 0).map
        (R+((h)_*[ModuleCat.{u + 1} Λ]).map ((shiftFunctor _ q).map φ)) ≫
      Etale.homologyShiftComparison Λ h q K' =
    Etale.homologyShiftComparison Λ h q K ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map (R+((h)_*[ModuleCat.{u + 1} Λ]).map φ) := by
  simp only [Etale.homologyShiftComparison]
  rw [← Functor.map_comp_assoc, Functor.commShiftIso_hom_naturality, Functor.map_comp_assoc]
  simp only [Category.assoc]
  congr 1
  have n₁ := ((DerivedCategory.Plus.homologyFunctor _ 0).isoShiftZero ℤ).inv.naturality
    ((shiftFunctor _ q).map (R+((h)_*[ModuleCat.{u + 1} Λ]).map φ))
  have n₂ := ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso q 0 q (add_zero q)).hom.naturality
    (R+((h)_*[ModuleCat.{u + 1} Λ]).map φ)
  erw [reassoc_of% n₁, n₂]
  rfl

lemma Etale.higherDirectImagePresheafToSheaf_naturality {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    {K K' : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ K') :
    Etale.higherDirectImagePresheafMap Λ h q φ ≫ Etale.higherDirectImagePresheafToSheaf Λ h q K' =
      Etale.higherDirectImagePresheafToSheaf Λ h q K ≫ Etale.sectionsMap
        ((DerivedCategory.Plus.homologyFunctor _ q).map (R+((h)_*[ModuleCat.{u + 1} Λ]).map φ)) := by
  have h₁ : ∀ L, Etale.higherDirectImagePresheafToSheaf Λ h q L =
      Etale.higherDirectImagePresheafToHom Λ h q L ≫ Etale.freeSheafSections Λ _ := fun _ ↦ rfl
  have h₂ : Etale.higherDirectImagePresheafMap Λ h q φ ≫ Etale.higherDirectImagePresheafToHom Λ h q K' =
      Etale.higherDirectImagePresheafToHom Λ h q K ≫ Functor.whiskerLeft (Etale.freeSheaf Λ X).op
        (preadditiveYoneda.map ((DerivedCategory.Plus.homologyFunctor _ q).map
          (R+((h)_*[ModuleCat.{u + 1} Λ]).map φ))) := by
    ext W β
    have e₁ : (Etale.higherDirectImagePresheafMap Λ h q φ).app W β =
        β ≫ (shiftFunctor _ q).map φ := rfl
    rw [NatTrans.comp_app, NatTrans.comp_app, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, e₁, Etale.higherDirectImagePresheafToHom_app_apply,
      Etale.higherDirectImagePresheafToHom_app_apply]
    change _ = _ ≫ _
    rw [← Category.assoc _ β, Adjunction.homEquiv_naturality_right, Functor.map_comp]
    simp only [Category.assoc]
    congr 2
    exact Etale.homologyShiftComparison_naturality Λ h q φ
  rw [h₁, h₁, Category.assoc, Etale.freeSheafSections_naturality, ← Category.assoc,
    ← Category.assoc, h₂]

/-- Blueprint `lem-weil-pbc-cohomology-filtered-colimit` (subsection `sk-prop-h2`): Filtered
colimits of étale cohomology. Let `V` be an étale `Y`-scheme whose underlying scheme is
quasi-compact and quasi-separated. Then `F ↦ Hᵠ(V, F|_V) = Hom(Λ[V][0], F[q])`, cohomology of
the restriction to `V` computed on the site of `Y` as in
`AlgebraicGeometry.Etale.higherDirectImagePresheaf`, commutes with filtered colimits of sheaves
of `Λ`-modules. -/
theorem Etale.preservesColimitsOfShape_cohomology {Y : Scheme.{u}} (V : Y.Etale)
    [CompactSpace V.left] [QuasiSeparatedSpace V.left] (q : ℤ) (J : Type) [SmallCategory J]
    [IsFiltered J] :
    PreservesColimitsOfShape J
      (DerivedCategory.Plus.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
        shiftFunctor _ q ⋙ preadditiveCoyoneda.obj
          (op ((DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ Y).obj V)))) :=
  sorry

/-- The hypercohomology presheaves `W ↦ Hᵠ(W ×_X Y, K|)` as a functor of `K`. -/
noncomputable def Etale.higherDirectImagePresheafFunctor {X Y : Scheme.{u}} (h : Y ⟶ X)
    (q : ℤ) :
    DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  shiftFunctor _ q ⋙ preadditiveYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj
    (Etale.freeSheaf Λ X ⋙ (h)^*[ModuleCat.{u + 1} Λ] ⋙ DerivedCategory.Plus.singleFunctor _ 0).op

lemma Etale.higherDirectImagePresheafFunctor_obj {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ) (K) :
    (Etale.higherDirectImagePresheafFunctor Λ h q).obj K = Etale.higherDirectImagePresheaf Λ h q K :=
  rfl

lemma Etale.higherDirectImagePresheafFunctor_map {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    {K K'} (φ : K ⟶ K') :
    (Etale.higherDirectImagePresheafFunctor Λ h q).map φ =
      Etale.higherDirectImagePresheafMap Λ h q φ :=
  rfl

/-- On an étale `X`-scheme `W` whose base change `W ×_X Y` is quasi-compact and
quasi-separated, the hypercohomology presheaves of single sheaves commute with filtered
colimits. -/
theorem Etale.preservesColimitsOfShape_higherDirectImagePresheaf_app {X Y : Scheme.{u}}
    (h : Y ⟶ X) (q : ℤ) (W : X.Etale)
    [CompactSpace ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).left]
    [QuasiSeparatedSpace ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).left]
    (J : Type) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J
      (DerivedCategory.Plus.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
        Etale.higherDirectImagePresheafFunctor Λ h q ⋙ (evaluation _ _).obj (op W)) := by
  have := Etale.preservesColimitsOfShape_cohomology Λ
    ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W) q J
  have : PreservesColimitsOfShape J
      ((DerivedCategory.Plus.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
        shiftFunctor _ q) ⋙ preadditiveCoyoneda.obj (op ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((Etale.freeSheaf Λ Y).obj ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W))))) := this
  refine preservesColimitsOfShape_of_natIso (Functor.isoWhiskerLeft
    (DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ q)
    (preadditiveCoyoneda.mapIso ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
      (Etale.upperStarFreeSheafIso Λ h W)).op))

end AlgebraicGeometry
