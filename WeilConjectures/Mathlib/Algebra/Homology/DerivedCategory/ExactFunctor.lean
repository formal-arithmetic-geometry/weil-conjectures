/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso

/-!
# Functoriality of `mapDerivedCategory`

For exact functors between abelian categories, the induced functor
`Functor.mapDerivedCategory` on derived categories is functorial:

- `CategoryTheory.Functor.mapDerivedCategoryNatIso`: an isomorphism `F ≅ G` of exact
  functors induces an isomorphism `F.mapDerivedCategory ≅ G.mapDerivedCategory`.
- `CategoryTheory.Functor.mapDerivedCategoryCompIso`: the composition isomorphism
  `(F ⋙ G).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory`.
- `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso`: the commutation
  `H^n(-) ⋙ F ≅ F.mapDerivedCategory ⋙ H^n(-)` with the homology functors, with the
  bounded below variant `CategoryTheory.Functor.mapDerivedCategoryPlusHomologyFunctorIso`.
- `CategoryTheory.Functor.mapDerivedCategoryPlus`: the restriction of
  `F.mapDerivedCategory` to the bounded below derived categories, with the compatibility
  isomorphism `CategoryTheory.Functor.mapDerivedCategoryPlusCompatibility` and the
  factorization `CategoryTheory.Functor.mapDerivedCategoryPlusFactorsh` through the
  localization functors from the bounded below homotopy categories.
- `CategoryTheory.Functor.mapDerivedCategoryPlusNatIso` and
  `CategoryTheory.Functor.mapDerivedCategoryPlusCompIso`: the corresponding
  functoriality of `mapDerivedCategoryPlus`, obtained by cancelling the fully faithful
  inclusions `DerivedCategory.Plus.ι`.
- `CategoryTheory.Functor.mapDerivedCategoryCompIso_fac`,
  `CategoryTheory.Functor.mapDerivedCategoryCompIso_fach` and
  `CategoryTheory.Functor.mapDerivedCategoryPlusCompIso_fac`: the composition isomorphisms
  are characterized by their compatibility with the factorizations of the induced functors
  through the localization functors.
- `CategoryTheory.Functor.mapDerivedCategoryPlusSingleFunctor`: the compatibility of
  `mapDerivedCategoryPlus` with the single functors of the bounded below derived
  categories.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

/-- An isomorphism `F ≅ G` of exact functors between abelian categories induces an
isomorphism `F.mapDerivedCategory ≅ G.mapDerivedCategory` of the functors induced on
derived categories, compatibly with the localization functors. -/
noncomputable def mapDerivedCategoryNatIso {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (isoWhiskerRight (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)) DerivedCategory.Q)

/-- The composition isomorphism
`(F ⋙ G).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory` for exact
functors between abelian categories: both sides are induced by
`(F ⋙ G).mapHomologicalComplex` on the localizations. -/
noncomputable def mapDerivedCategoryCompIso (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (F ⋙ G).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory :=
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (F.mapDerivedCategory ⋙ G.mapDerivedCategory) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight F.mapDerivedCategoryFactors G.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
        (ComplexShape.up ℤ)) DerivedCategory.Q⟩
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (F ⋙ G).mapDerivedCategory (F.mapDerivedCategory ⋙ G.mapDerivedCategory)
    (Iso.refl _)

/-- The composition isomorphism `Functor.mapDerivedCategoryCompIso` is characterized by its
compatibility with the factorizations `Functor.mapDerivedCategoryFactors` through the
localization functors `DerivedCategory.Q`. -/
@[reassoc]
lemma mapDerivedCategoryCompIso_fac (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : CochainComplex C ℤ) :
    (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
        (ComplexShape.up ℤ)).hom.app K) =
    (F ⋙ G).mapDerivedCategoryFactors.hom.app K := by
  dsimp [mapDerivedCategoryCompIso]
  rw [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  dsimp
  simp
  rfl

/-- The homotopy category counterpart of `Functor.mapDerivedCategoryCompIso_fac`: the
composition isomorphism `Functor.mapDerivedCategoryCompIso` is compatible with the
factorizations `Functor.mapDerivedCategoryFactorsh` through the localization functors
`DerivedCategory.Qh` and with `Functor.mapHomotopyCategoryCompIso`. -/
@[reassoc]
lemma mapDerivedCategoryCompIso_fach (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Qh.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
      G.mapDerivedCategoryFactorsh.hom.app
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G))
        (ComplexShape.up ℤ)).hom.app K) =
    (F ⋙ G).mapDerivedCategoryFactorsh.hom.app K := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  have hG : G.mapDerivedCategoryFactorsh.hom.app
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) =
      G.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso D).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (DerivedCategory.quotientCompQhIso E).inv.app _ ≫
        DerivedCategory.Qh.map ((G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
    G.mapDerivedCategoryFactorsh_hom_app _
  have hCI : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G))
        (ComplexShape.up ℤ)).hom.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient E (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
          (ComplexShape.up ℤ)).hom.app K) := rfl
  rw [mapDerivedCategoryFactorsh_hom_app, hG, hCI, mapDerivedCategoryFactorsh_hom_app]
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv, Functor.map_comp,
    Category.assoc]
  simp only [comp_obj, map_id, Category.id_comp, cancelIso, Category.comp_id]
  rw [← Functor.comp_map F.mapDerivedCategory G.mapDerivedCategory,
    ← NatTrans.naturality_assoc, ← DerivedCategory.quotientCompQhIso_inv_naturality,
    mapDerivedCategoryCompIso_fac_assoc]

/-- An exact functor commutes with the homology functors of the derived categories:
the canonical isomorphism
`H^n(-) ⋙ F ≅ F.mapDerivedCategory ⋙ H^n(-)` of functors
`DerivedCategory C ⥤ D`, induced by the commutation of `F` with homology of complexes. -/
noncomputable def mapDerivedCategoryHomologyFunctorIso (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n : ℤ) :
    DerivedCategory.homologyFunctor C n ⋙ F ≅
      F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n :=
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n ⋙ F)
      (DerivedCategory.homologyFunctor C n ⋙ F) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (DerivedCategory.homologyFunctorFactors C n) F⟩
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n ⋙ F)
      (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight F.mapDerivedCategoryFactors (DerivedCategory.homologyFunctor D n) ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactors D n) ≪≫
      F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n⟩
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n ⋙ F)
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n ⋙ F)
    (DerivedCategory.homologyFunctor C n ⋙ F)
    (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n)
    (Iso.refl _)

section Plus

variable (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- An exact functor between abelian categories preserves bounded below objects of the
derived categories: an object isomorphic to a complex concentrated in degrees `≥ n` is
sent to an object with the same property. -/
lemma isGE_mapDerivedCategory_obj (X : DerivedCategory C) (n : ℤ) [X.IsGE n] :
    (F.mapDerivedCategory.obj X).IsGE n := by
  obtain ⟨K, hK, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isGE n
  have : DerivedCategory.TStructure.t.IsGE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).obj K) n :=
    inferInstanceAs (DerivedCategory.IsGE (DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) n)
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app K).symm n

/-- The functor induced on the bounded below derived categories by an exact functor
between abelian categories: the restriction of `F.mapDerivedCategory` to
`DerivedCategory.Plus`, which is well defined since an exact functor preserves bounded
below objects. -/
noncomputable def mapDerivedCategoryPlus :
    DerivedCategory.Plus C ⥤ DerivedCategory.Plus D :=
  DerivedCategory.TStructure.t.plus.lift
    (DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory) (by
      rintro ⟨X, n, hn⟩
      exact ⟨n, F.isGE_mapDerivedCategory_obj X n⟩)

/-- The restriction `F.mapDerivedCategoryPlus` of `F.mapDerivedCategory` to the bounded
below derived categories is compatible with the inclusions. -/
noncomputable def mapDerivedCategoryPlusCompatibility :
    F.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory :=
  Iso.refl _

/-- The functor `F.mapDerivedCategoryPlus` induced on the bounded below derived categories
by an exact functor `F` factors the functor `F.mapHomotopyCategoryPlus` on the bounded
below homotopy categories through the localization functors: the bounded below counterpart
of `Functor.mapDerivedCategoryFactorsh`. -/
noncomputable def mapDerivedCategoryPlusFactorsh :
    DerivedCategory.Plus.Qh ⋙ F.mapDerivedCategoryPlus ≅
      F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh :=
  fullyFaithfulCancelRight DerivedCategory.Plus.ι
    (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft DerivedCategory.Plus.Qh F.mapDerivedCategoryPlusCompatibility ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (DerivedCategory.Plus.QhCompιIsoιCompQh C) F.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (HomotopyCategory.Plus.ι C) F.mapDerivedCategoryFactorsh ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (Iso.refl (HomotopyCategory.Plus.ι C ⋙
        F.mapHomotopyCategory (ComplexShape.up ℤ))).symm DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft F.mapHomotopyCategoryPlus
        (DerivedCategory.Plus.QhCompιIsoιCompQh D).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- The factorization `Functor.mapDerivedCategoryPlusFactorsh` is the restriction of
`Functor.mapDerivedCategoryFactorsh` along the fully faithful inclusion
`DerivedCategory.Plus.ι`. -/
@[simp]
lemma ι_map_mapDerivedCategoryPlusFactorsh_hom_app (K : HomotopyCategory.Plus C) :
    DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlusFactorsh.hom.app K) =
      F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.Plus.ι C).obj K) := by
  rw [mapDerivedCategoryPlusFactorsh, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage]
  simp [mapDerivedCategoryPlusCompatibility, DerivedCategory.Plus.QhCompιIsoιCompQh,
    DerivedCategory.Plus.Qh, mapDerivedCategoryPlus, mapHomotopyCategoryPlus,
    ObjectProperty.lift]

/-- An exact functor commutes with the homology functors of the bounded below derived
categories: the restriction of `Functor.mapDerivedCategoryHomologyFunctorIso` along the
inclusion `DerivedCategory.Plus.ι`. -/
noncomputable def mapDerivedCategoryPlusHomologyFunctorIso (n : ℤ) :
    DerivedCategory.Plus.homologyFunctor C n ⋙ F ≅
      F.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.homologyFunctor D n :=
  Functor.associator DerivedCategory.Plus.ι (DerivedCategory.homologyFunctor C n) F ≪≫
    isoWhiskerLeft DerivedCategory.Plus.ι (F.mapDerivedCategoryHomologyFunctorIso n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight F.mapDerivedCategoryPlusCompatibility.symm
      (DerivedCategory.homologyFunctor D n) ≪≫
    Functor.associator _ _ _

/-- An isomorphism `F ≅ G` of exact functors between abelian categories induces an
isomorphism `F.mapDerivedCategoryPlus ≅ G.mapDerivedCategoryPlus` of the functors
induced on the bounded below derived categories: the restriction of
`Functor.mapDerivedCategoryNatIso` along the inclusions `DerivedCategory.Plus.ι`. -/
noncomputable def mapDerivedCategoryPlusNatIso {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    F.mapDerivedCategoryPlus ≅ G.mapDerivedCategoryPlus :=
  fullyFaithfulCancelRight DerivedCategory.Plus.ι
    (F.mapDerivedCategoryPlusCompatibility ≪≫
      isoWhiskerLeft DerivedCategory.Plus.ι (mapDerivedCategoryNatIso e) ≪≫
      G.mapDerivedCategoryPlusCompatibility.symm)

/-- The composition isomorphism
`(F ⋙ G).mapDerivedCategoryPlus ≅ F.mapDerivedCategoryPlus ⋙ G.mapDerivedCategoryPlus`
for exact functors between abelian categories: the restriction of
`Functor.mapDerivedCategoryCompIso` along the inclusions `DerivedCategory.Plus.ι`. -/
noncomputable def mapDerivedCategoryPlusCompIso (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (F ⋙ G).mapDerivedCategoryPlus ≅
      F.mapDerivedCategoryPlus ⋙ G.mapDerivedCategoryPlus :=
  fullyFaithfulCancelRight DerivedCategory.Plus.ι
    ((F ⋙ G).mapDerivedCategoryPlusCompatibility ≪≫
      isoWhiskerLeft DerivedCategory.Plus.ι (mapDerivedCategoryCompIso F G) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight F.mapDerivedCategoryPlusCompatibility.symm G.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft F.mapDerivedCategoryPlus
        G.mapDerivedCategoryPlusCompatibility.symm ≪≫
      (Functor.associator _ _ _).symm)

section Comp

variable (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The composition isomorphism `Functor.mapDerivedCategoryPlusCompIso` is the restriction of
`Functor.mapDerivedCategoryCompIso` along the fully faithful inclusion
`DerivedCategory.Plus.ι`. -/
@[simp]
lemma ι_map_mapDerivedCategoryPlusCompIso_hom_app (X : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusCompIso F G).hom.app X) =
      (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Plus.ι.obj X) := by
  rw [mapDerivedCategoryPlusCompIso, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage]
  simp [mapDerivedCategoryPlusCompatibility, mapDerivedCategoryPlus, ObjectProperty.lift]

/-- The composition isomorphism `Functor.mapDerivedCategoryPlusCompIso` is characterized by
its compatibility with the factorizations `Functor.mapDerivedCategoryPlusFactorsh` through
the localization functors `DerivedCategory.Plus.Qh`. -/
@[reassoc]
lemma mapDerivedCategoryPlusCompIso_fac (K : HomotopyCategory.Plus C) :
    (mapDerivedCategoryPlusCompIso F G).hom.app (DerivedCategory.Plus.Qh.obj K) ≫
      G.mapDerivedCategoryPlus.map (F.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      G.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj K) ≫
      DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app K) =
    (F ⋙ G).mapDerivedCategoryPlusFactorsh.hom.app K := by
  apply DerivedCategory.Plus.ι.map_injective
  have hmap : ∀ {X Y : DerivedCategory.Plus D} (f : X ⟶ Y),
      DerivedCategory.Plus.ι.map (G.mapDerivedCategoryPlus.map f) =
        G.mapDerivedCategory.map (DerivedCategory.Plus.ι.map f) := fun _ => rfl
  have hqh : ∀ {X Y : HomotopyCategory.Plus E} (f : X ⟶ Y),
      DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map f) =
        DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι E).map f) := fun _ => rfl
  have hci : (HomotopyCategory.Plus.ι E).map
      ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app K) =
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.Plus.ι C).obj K) := rfl
  simp only [Functor.map_comp, hmap, hqh, hci,
    ι_map_mapDerivedCategoryPlusFactorsh_hom_app, ι_map_mapDerivedCategoryPlusCompIso_hom_app]
  exact mapDerivedCategoryCompIso_fach F G ((HomotopyCategory.Plus.ι C).obj K)

/-- The isomorphism version of `Functor.mapDerivedCategoryPlusCompIso_fac`: the factorization
of `(F ⋙ G).mapDerivedCategoryPlus` through the localization functors
`DerivedCategory.Plus.Qh` is the composite of the composition isomorphism, the factorizations
of `F` and `G`, and the composition isomorphism of `mapHomotopyCategoryPlus`. -/
lemma mapDerivedCategoryPlusFactorsh_comp :
    (F ⋙ G).mapDerivedCategoryPlusFactorsh =
      isoWhiskerLeft DerivedCategory.Plus.Qh (mapDerivedCategoryPlusCompIso F G) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight F.mapDerivedCategoryPlusFactorsh G.mapDerivedCategoryPlus ≪≫
        Functor.associator _ _ _ ≪≫
        isoWhiskerLeft F.mapHomotopyCategoryPlus G.mapDerivedCategoryPlusFactorsh ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G)))
          DerivedCategory.Plus.Qh := by
  ext K : 3
  simpa using (mapDerivedCategoryPlusCompIso_fac F G K).symm

end Comp

/-- `DerivedCategory.Plus.singleFunctor` commutes with an exact functor `F` and
`F.mapDerivedCategoryPlus`: the restriction of `Functor.mapDerivedCategorySingleFunctor`
along the inclusions `DerivedCategory.Plus.ι`. -/
noncomputable def mapDerivedCategoryPlusSingleFunctor (n : ℤ) :
    DerivedCategory.Plus.singleFunctor C n ⋙ F.mapDerivedCategoryPlus ≅
      F ⋙ DerivedCategory.Plus.singleFunctor D n :=
  fullyFaithfulCancelRight DerivedCategory.Plus.ι
    (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C n)
        F.mapDerivedCategoryPlusCompatibility ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (DerivedCategory.Plus.singleFunctorιIso C n)
        F.mapDerivedCategory ≪≫
      F.mapDerivedCategorySingleFunctor n ≪≫
      isoWhiskerLeft F (DerivedCategory.Plus.singleFunctorιIso D n).symm ≪≫
      (Functor.associator _ _ _).symm)

end Plus

end CategoryTheory.Functor
