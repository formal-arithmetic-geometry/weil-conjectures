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

lemma Etale.higherDirectImagePresheafToSheaf_naturality {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    {K K' : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ K') :
    Etale.higherDirectImagePresheafMap Λ h q φ ≫ Etale.higherDirectImagePresheafToSheaf Λ h q K' =
      Etale.higherDirectImagePresheafToSheaf Λ h q K ≫ Etale.sectionsMap
        ((DerivedCategory.Plus.homologyFunctor _ q).map (R+((h)_*[ModuleCat.{u + 1} Λ]).map φ)) := by
  simp only [Etale.higherDirectImagePresheafToSheaf, Etale.higherDirectImagePresheafToHom,
    Category.assoc, Etale.freeSheafSections_naturality]
  simp only [← Category.assoc]
  congr 1
  ext W β
  dsimp [Etale.higherDirectImagePresheafMap, Etale.higherDirectImagePresheafIso,
    Etale.derivedHomToHomology, preadditiveYoneda]
  have key : ∀ x : (h)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryPlus.obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj W.unop)) ⟶ K⟦q⟧,
      (DerivedCategory.Plus.homologyFunctor _ 0).map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h).homEquiv _ _
          (x ≫ (shiftFunctor _ q).map φ)) ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map
            ((R+((h)_*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K') ≫
          ((DerivedCategory.Plus.homologyFunctor _ 0).isoShiftZero ℤ).inv.app _ ≫
            ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso q 0 q (add_zero q)).hom.app _ =
      ((DerivedCategory.Plus.homologyFunctor _ 0).map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h).homEquiv _ _ x) ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map
            ((R+((h)_*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K) ≫
          ((DerivedCategory.Plus.homologyFunctor _ 0).isoShiftZero ℤ).inv.app _ ≫
            ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso q 0 q (add_zero q)).hom.app _) ≫
        (DerivedCategory.Plus.homologyFunctor _ q).map (R+((h)_*[ModuleCat.{u + 1} Λ]).map φ) := by
    intro x
    rw [Adjunction.homEquiv_naturality_right]
    simp only [Functor.map_comp, Category.assoc]
    congr 1
    rw [← Functor.map_comp_assoc, Functor.commShiftIso_hom_naturality, Functor.map_comp_assoc]
    congr 1
    have n₁ := ((DerivedCategory.Plus.homologyFunctor _ 0).isoShiftZero ℤ).inv.naturality
      ((shiftFunctor _ q).map (R+((h)_*[ModuleCat.{u + 1} Λ]).map φ))
    have n₂ := ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso q 0 q (add_zero q)).hom.naturality
      (R+((h)_*[ModuleCat.{u + 1} Λ]).map φ)
    erw [reassoc_of% n₁, n₂]
    rfl
  have k₂ := congrArg (fun t ↦ (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
    (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).inv.app
      ((Etale.freeSheaf Λ X).obj W.unop) ≫ t)
    (key (((NatIso.op ((Etale.freeSheaf Λ X).isoWhiskerLeft
      ((h)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryPlusSingleFunctor 0))).hom.app W).unop ≫ β))
  simp only [Category.assoc] at k₂
  refine Eq.trans ?_ (k₂.trans ?_)
  · simp only [Category.assoc]
    rfl
  · simp only [Category.assoc]
    rfl
end AlgebraicGeometry
