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
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

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
- `CategoryTheory.Functor.isGE_mapDerivedCategory_obj`,
  `CategoryTheory.Functor.isLE_mapDerivedCategory_obj`,
  `CategoryTheory.Functor.homologyConcentratedIn_mapDerivedCategory_obj` and
  `CategoryTheory.Functor.bounded_mapDerivedCategory_obj`: `F.mapDerivedCategory` preserves
  the bounds of the canonical t-structure.
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
- `CategoryTheory.Functor.mapDerivedCategoryNatIso_fac`,
  `CategoryTheory.Functor.mapDerivedCategoryNatIso_fach` and
  `CategoryTheory.Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh`: likewise, the
  isomorphism induced by `e : F ≅ G` is characterized by its compatibility with the
  factorizations; on the image of a complex it is `e` itself.
- `CategoryTheory.Functor.mapDerivedCategoryPlusSingleFunctor`: the compatibility of
  `mapDerivedCategoryPlus` with the single functors of the bounded below derived
  categories.
- `CategoryTheory.Functor.mapDerivedCategoryIdIso` and
  `CategoryTheory.Functor.mapDerivedCategoryPlusIdIso`: the identity isomorphisms
  `(𝟭 C).mapDerivedCategory ≅ 𝟭` and `(𝟭 C).mapDerivedCategoryPlus ≅ 𝟭`, together with
  their characterizations `CategoryTheory.Functor.mapDerivedCategoryIdIso_factorsh` and
  `CategoryTheory.Functor.mapDerivedCategoryPlusIdIso_factorsh` at the level of the
  homotopy categories.
- `CategoryTheory.Functor.mapDerivedCategoryPlusCompIso_id_comp`,
  `CategoryTheory.Functor.mapDerivedCategoryPlusCompIso_comp_id` and
  `CategoryTheory.Functor.mapDerivedCategoryPlusCompIso_assoc`: the unit and associativity
  laws relating `mapDerivedCategoryPlusCompIso` and `mapDerivedCategoryPlusIdIso`.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

@[inherit_doc mapDerivedCategory]
scoped notation "D(" F ")" => mapDerivedCategory F

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

/-- The isomorphism `Functor.mapDerivedCategoryNatIso` is characterized by its
compatibility with the factorizations `Functor.mapDerivedCategoryFactors` through the
localization functors `DerivedCategory.Q`: on the image of a complex it is the levelwise
image of `e`. -/
@[reassoc]
lemma mapDerivedCategoryNatIso_fac {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (K : CochainComplex C ℤ) :
    (mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K) := by
  have hF : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      F.mapDerivedCategory = F.mapDerivedCategoryFactors := rfl
  have hG : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      G.mapDerivedCategory = G.mapDerivedCategoryFactors := rfl
  simp only [mapDerivedCategoryNatIso, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app, hF, hG, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id, isoWhiskerRight_hom, whiskerRight_app]
  rfl

/-- The homotopy category counterpart of `Functor.mapDerivedCategoryNatIso_fac`: the
isomorphism `Functor.mapDerivedCategoryNatIso` is compatible with the factorizations
`Functor.mapDerivedCategoryFactorsh` through the localization functors
`DerivedCategory.Qh`. -/
@[reassoc]
lemma mapDerivedCategoryNatIso_fach {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Qh.obj K) ≫
        G.mapDerivedCategoryFactorsh.hom.app K =
      F.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  have hnt : (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K) := rfl
  rw [mapDerivedCategoryFactorsh_hom_app, mapDerivedCategoryFactorsh_hom_app, hnt,
    ← NatTrans.naturality_assoc, mapDerivedCategoryNatIso_fac_assoc,
    reassoc_of% (DerivedCategory.quotientCompQhIso_inv_naturality
      ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K))]
  simp only [mapHomotopyCategoryFactors, Quotient.lift.isLift_inv, Category.assoc]
  rw [← DerivedCategory.Qh.map_comp, ← DerivedCategory.Qh.map_comp]
  simp

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

/-- An exact functor between abelian categories sends an object of the derived category
whose `n`-th homology vanishes to an object whose `n`-th homology vanishes. -/
lemma isZero_homologyFunctor_mapDerivedCategory_obj {X : DerivedCategory C} {n : ℤ}
    (hX : IsZero ((DerivedCategory.homologyFunctor C n).obj X)) :
    IsZero ((DerivedCategory.homologyFunctor D n).obj (F.mapDerivedCategory.obj X)) :=
  (F.map_isZero hX).of_iso ((F.mapDerivedCategoryHomologyFunctorIso n).symm.app X)

/-- An exact functor between abelian categories preserves bounded above objects of the
derived categories: an object with homology concentrated in degrees `≤ n` is sent to an
object with the same property. -/
lemma isLE_mapDerivedCategory_obj (X : DerivedCategory C) (n : ℤ) [X.IsLE n] :
    (F.mapDerivedCategory.obj X).IsLE n :=
  (DerivedCategory.isLE_iff _ n).2 fun i hi ↦
    F.isZero_homologyFunctor_mapDerivedCategory_obj ((DerivedCategory.isLE_iff X n).1 ‹_› i hi)

/-- An exact functor between abelian categories preserves homology concentration in an
interval `[a, b]`. -/
lemma homologyConcentratedIn_mapDerivedCategory_obj {a b : ℤ} {X : DerivedCategory C}
    (hX : DerivedCategory.homologyConcentratedIn a b X) :
    DerivedCategory.homologyConcentratedIn a b (F.mapDerivedCategory.obj X) := by
  obtain ⟨_, _⟩ := (DerivedCategory.homologyConcentratedIn_iff a b X).1 hX
  exact (DerivedCategory.homologyConcentratedIn_iff a b _).2
    ⟨F.isGE_mapDerivedCategory_obj X a, F.isLE_mapDerivedCategory_obj X b⟩

/-- An exact functor between abelian categories preserves objects of the derived categories
that are bounded for the canonical t-structure. -/
lemma bounded_mapDerivedCategory_obj {X : DerivedCategory C}
    (hX : DerivedCategory.TStructure.t.bounded X) :
    DerivedCategory.TStructure.t.bounded (F.mapDerivedCategory.obj X) := by
  obtain ⟨a, b, hab⟩ := (DerivedCategory.exists_homologyConcentratedIn_iff_bounded X).2 hX
  exact (DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).1
    ⟨a, b, F.homologyConcentratedIn_mapDerivedCategory_obj hab⟩

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

@[inherit_doc mapDerivedCategoryPlus]
scoped notation "D+(" F ")" => mapDerivedCategoryPlus F

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

/-- The isomorphism `Functor.mapDerivedCategoryPlusNatIso` is the restriction of
`Functor.mapDerivedCategoryNatIso` along the fully faithful inclusion
`DerivedCategory.Plus.ι`. -/
@[simp]
lemma ι_map_mapDerivedCategoryPlusNatIso_hom_app {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (X : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusNatIso e).hom.app X) =
      (mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Plus.ι.obj X) := by
  rw [mapDerivedCategoryPlusNatIso, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage]
  simp [mapDerivedCategoryPlusCompatibility, mapDerivedCategoryPlus, ObjectProperty.lift]

/-- The isomorphism `Functor.mapDerivedCategoryPlusNatIso` is characterized by its
compatibility with the factorizations `Functor.mapDerivedCategoryPlusFactorsh` through the
localization functors `DerivedCategory.Plus.Qh`: on the image of a bounded below complex it
is the levelwise image of `e`. -/
@[reassoc]
lemma mapDerivedCategoryPlusNatIso_hom_app_factorsh {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (K : HomotopyCategory.Plus C) :
    (mapDerivedCategoryPlusNatIso e).hom.app (DerivedCategory.Plus.Qh.obj K) ≫
        G.mapDerivedCategoryPlusFactorsh.hom.app K =
      F.mapDerivedCategoryPlusFactorsh.hom.app K ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e.hom).app K) := by
  apply DerivedCategory.Plus.ι.map_injective
  have hqh : ∀ {X Y : HomotopyCategory.Plus D} (g : X ⟶ Y),
      DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map g) =
        DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι D).map g) := fun _ => rfl
  have hnt : (HomotopyCategory.Plus.ι D).map
      ((NatTrans.mapHomotopyCategoryPlus e.hom).app K) =
      (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app
        ((HomotopyCategory.Plus.ι C).obj K) := rfl
  simp only [Functor.map_comp, hqh, hnt, ι_map_mapDerivedCategoryPlusFactorsh_hom_app,
    ι_map_mapDerivedCategoryPlusNatIso_hom_app]
  exact mapDerivedCategoryNatIso_fach e ((HomotopyCategory.Plus.ι C).obj K)

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

/-- The form of `Functor.mapDerivedCategoryPlusCompIso_fac` in which the comparison
isomorphism `Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))` on the bounded
below homotopy categories has been cancelled, it being the identity. -/
@[reassoc]
lemma mapDerivedCategoryPlusCompIso_hom_app_factorsh (K : HomotopyCategory.Plus C) :
    (mapDerivedCategoryPlusCompIso F G).hom.app (DerivedCategory.Plus.Qh.obj K) ≫
        G.mapDerivedCategoryPlus.map (F.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        G.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj K) =
      (F ⋙ G).mapDerivedCategoryPlusFactorsh.hom.app K := by
  have hqc : DerivedCategory.Plus.Qh.map
      ((mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app K) =
      𝟙 ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj
        (F.mapHomotopyCategoryPlus.obj K)) := by
    rw [mapHomotopyCategoryPlusCompIso_refl_hom_app]
    exact DerivedCategory.Plus.Qh.map_id _
  have key := mapDerivedCategoryPlusCompIso_fac F G K
  rwa [hqc, Category.comp_id] at key

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

section Identity

variable (C)

/-- The functor induced on derived categories by the identity functor is isomorphic to the
identity functor: the derived category counterpart of
`CategoryTheory.Functor.mapHomologicalComplexIdIso`. -/
noncomputable def mapDerivedCategoryIdIso :
    (𝟭 C).mapDerivedCategory ≅ 𝟭 (DerivedCategory C) :=
  Localization.liftNatIso DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    ((𝟭 C).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) DerivedCategory.Qh
    (𝟭 C).mapDerivedCategory (𝟭 (DerivedCategory C))
    (isoWhiskerRight (mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)) DerivedCategory.Qh ≪≫
      DerivedCategory.Qh.leftUnitor)

/-- The characterization of `Functor.mapDerivedCategoryIdIso` at the level of the homotopy
category: the isomorphism `DerivedCategory.Qh ⋙ (𝟭 C).mapDerivedCategory ≅ DerivedCategory.Qh`
it induces is the one coming from `Functor.mapDerivedCategoryFactorsh` and
`Functor.mapHomotopyCategoryIdIso`. -/
lemma mapDerivedCategoryIdIso_factorsh :
    isoWhiskerLeft DerivedCategory.Qh (mapDerivedCategoryIdIso C) ≪≫
        DerivedCategory.Qh.rightUnitor =
      (𝟭 C).mapDerivedCategoryFactorsh ≪≫
        isoWhiskerRight (mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)) DerivedCategory.Qh ≪≫
        DerivedCategory.Qh.leftUnitor := by
  have h : Localization.Lifting.iso DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      ((𝟭 C).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (𝟭 C).mapDerivedCategory = (𝟭 C).mapDerivedCategoryFactorsh := rfl
  ext X
  simp [mapDerivedCategoryIdIso, h]

/-- The functor induced on the bounded below derived categories by the identity functor is
isomorphic to the identity functor: the restriction of `Functor.mapDerivedCategoryIdIso`
along the inclusion `DerivedCategory.Plus.ι`. -/
noncomputable def mapDerivedCategoryPlusIdIso :
    (𝟭 C).mapDerivedCategoryPlus ≅ 𝟭 (DerivedCategory.Plus C) :=
  fullyFaithfulCancelRight DerivedCategory.Plus.ι
    ((𝟭 C).mapDerivedCategoryPlusCompatibility ≪≫
      isoWhiskerLeft DerivedCategory.Plus.ι (mapDerivedCategoryIdIso C) ≪≫
      DerivedCategory.Plus.ι.rightUnitor ≪≫ DerivedCategory.Plus.ι.leftUnitor.symm)

@[simp]
lemma ι_map_mapDerivedCategoryPlusIdIso_hom_app (X : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusIdIso C).hom.app X) =
      (mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Plus.ι.obj X) := by
  rw [mapDerivedCategoryPlusIdIso, fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  simp [mapDerivedCategoryPlusCompatibility]

/-- The characterization of `Functor.mapDerivedCategoryPlusIdIso` at the level of the bounded
below homotopy category: the isomorphism
`DerivedCategory.Plus.Qh ⋙ (𝟭 C).mapDerivedCategoryPlus ≅ DerivedCategory.Plus.Qh` it induces
is the one coming from `Functor.mapDerivedCategoryPlusFactorsh` and
`Functor.mapHomotopyCategoryPlusIdIso`. -/
lemma mapDerivedCategoryPlusIdIso_factorsh :
    isoWhiskerLeft DerivedCategory.Plus.Qh (mapDerivedCategoryPlusIdIso C) ≪≫
        DerivedCategory.Plus.Qh.rightUnitor =
      (𝟭 C).mapDerivedCategoryPlusFactorsh ≪≫
        isoWhiskerRight (mapHomotopyCategoryPlusIdIso C) DerivedCategory.Plus.Qh ≪≫
        DerivedCategory.Plus.Qh.leftUnitor := by
  apply Iso.ext
  ext K : 2
  apply DerivedCategory.Plus.ι.map_injective
  have h := congr_app (congr_arg Iso.hom (mapDerivedCategoryIdIso_factorsh C))
    ((HomotopyCategory.Plus.ι C).obj K)
  have h' : DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusIdIso C).hom.app K)) =
      DerivedCategory.Qh.map
        ((mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom.app K.obj) :=
    congrArg DerivedCategory.Qh.map (ι_map_mapHomotopyCategoryPlusIdIso_hom_app C K)
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.rightUnitor_hom_app,
    Functor.leftUnitor_hom_app, Functor.map_comp, h',
    ι_map_mapDerivedCategoryPlusIdIso_hom_app, ι_map_mapDerivedCategoryPlusFactorsh_hom_app] at h ⊢
  exact h

/-- The pointwise form of `Functor.mapDerivedCategoryPlusIdIso_factorsh`: on the image of a
bounded below homotopy category object, the identity isomorphism
`Functor.mapDerivedCategoryPlusIdIso` is the factorization
`Functor.mapDerivedCategoryPlusFactorsh` of `𝟭 C` followed by
`Functor.mapHomotopyCategoryPlusIdIso`. -/
@[reassoc]
lemma mapDerivedCategoryPlusIdIso_fac_app (K : HomotopyCategory.Plus C) :
    (mapDerivedCategoryPlusIdIso C).hom.app (DerivedCategory.Plus.Qh.obj K) =
      (𝟭 C).mapDerivedCategoryPlusFactorsh.hom.app K ≫
        DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusIdIso C).hom.app K) := by
  have := congr_app (congr_arg Iso.hom (mapDerivedCategoryPlusIdIso_factorsh C)) K
  simpa using this

/-- The form of `Functor.mapDerivedCategoryPlusIdIso_fac_app` in which the comparison
isomorphism `Functor.mapHomotopyCategoryPlusIdIso` on the bounded below homotopy categories
has been cancelled, it being the identity. -/
@[reassoc]
lemma mapDerivedCategoryPlusIdIso_hom_app_factorsh (K : HomotopyCategory.Plus C) :
    (mapDerivedCategoryPlusIdIso C).hom.app (DerivedCategory.Plus.Qh.obj K) =
      (𝟭 C).mapDerivedCategoryPlusFactorsh.hom.app K := by
  have hq : DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusIdIso C).hom.app K) =
      𝟙 (((𝟭 C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj K) := by
    rw [mapHomotopyCategoryPlusIdIso_hom_app_eq_id]
    exact DerivedCategory.Plus.Qh.map_id _
  rw [mapDerivedCategoryPlusIdIso_fac_app, hq, Category.comp_id]

end Identity

section Coherence

/-- The left unit law for `Functor.mapDerivedCategoryPlusCompIso`: composing with the
identity isomorphism `Functor.mapDerivedCategoryPlusIdIso` in the first variable gives the
identity. -/
lemma mapDerivedCategoryPlusCompIso_id_comp (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (mapDerivedCategoryPlusCompIso (𝟭 C) F).hom ≫
        Functor.whiskerRight (mapDerivedCategoryPlusIdIso C).hom F.mapDerivedCategoryPlus =
      𝟙 F.mapDerivedCategoryPlus := by
  refine Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso C) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app]
  rw [← cancel_mono (F.mapDerivedCategoryPlusFactorsh.hom.app K),
    mapDerivedCategoryPlusIdIso_hom_app_factorsh, Category.assoc]
  exact (mapDerivedCategoryPlusCompIso_hom_app_factorsh (𝟭 C) F K).trans
    (Category.id_comp _).symm

/-- The right unit law for `Functor.mapDerivedCategoryPlusCompIso`: composing with the
identity isomorphism `Functor.mapDerivedCategoryPlusIdIso` in the second variable gives the
identity. -/
lemma mapDerivedCategoryPlusCompIso_comp_id (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (mapDerivedCategoryPlusCompIso F (𝟭 D)).hom ≫
        Functor.whiskerLeft F.mapDerivedCategoryPlus (mapDerivedCategoryPlusIdIso D).hom =
      𝟙 F.mapDerivedCategoryPlus := by
  refine Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso C) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app]
  have hnat : (mapDerivedCategoryPlusIdIso D).hom.app
        (F.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj K)) ≫
      F.mapDerivedCategoryPlusFactorsh.hom.app K =
      (𝟭 D).mapDerivedCategoryPlus.map (F.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        (mapDerivedCategoryPlusIdIso D).hom.app
          (DerivedCategory.Plus.Qh.obj (F.mapHomotopyCategoryPlus.obj K)) :=
    ((mapDerivedCategoryPlusIdIso D).hom.naturality _).symm
  rw [← cancel_mono (F.mapDerivedCategoryPlusFactorsh.hom.app K), Category.assoc, hnat,
    mapDerivedCategoryPlusIdIso_hom_app_factorsh]
  exact (mapDerivedCategoryPlusCompIso_hom_app_factorsh F (𝟭 D) K).trans
    (Category.id_comp _).symm

variable {E' : Type*} [Category E'] [Abelian E'] [HasDerivedCategory E']

/-- The associativity law for `Functor.mapDerivedCategoryPlusCompIso`: the two ways of
comparing `(F ⋙ G ⋙ H).mapDerivedCategoryPlus` with
`F.mapDerivedCategoryPlus ⋙ G.mapDerivedCategoryPlus ⋙ H.mapDerivedCategoryPlus` agree. -/
lemma mapDerivedCategoryPlusCompIso_assoc (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E')
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] :
    (mapDerivedCategoryPlusCompIso F (G ⋙ H)).hom ≫
        Functor.whiskerLeft F.mapDerivedCategoryPlus
          (mapDerivedCategoryPlusCompIso G H).hom =
      (mapDerivedCategoryPlusCompIso (F ⋙ G) H).hom ≫
        Functor.whiskerRight (mapDerivedCategoryPlusCompIso F G).hom
          H.mapDerivedCategoryPlus := by
  refine Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso C) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have hnat : (mapDerivedCategoryPlusCompIso G H).hom.app
        (F.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj K)) ≫
      H.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlus.map
        (F.mapDerivedCategoryPlusFactorsh.hom.app K)) =
      (G ⋙ H).mapDerivedCategoryPlus.map (F.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        (mapDerivedCategoryPlusCompIso G H).hom.app
          (DerivedCategory.Plus.Qh.obj (F.mapHomotopyCategoryPlus.obj K)) :=
    ((mapDerivedCategoryPlusCompIso G H).hom.naturality _).symm
  rw [← cancel_mono (H.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlus.map
      (F.mapDerivedCategoryPlusFactorsh.hom.app K)) ≫
    H.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app
      (F.mapHomotopyCategoryPlus.obj K)) ≫
    H.mapDerivedCategoryPlusFactorsh.hom.app
      (G.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj K)))]
  trans (F ⋙ G ⋙ H).mapDerivedCategoryPlusFactorsh.hom.app K
  · rw [Category.assoc, reassoc_of% hnat,
      mapDerivedCategoryPlusCompIso_hom_app_factorsh G H (F.mapHomotopyCategoryPlus.obj K)]
    exact mapDerivedCategoryPlusCompIso_hom_app_factorsh F (G ⋙ H) K
  · symm
    rw [Category.assoc]
    simp only [← Functor.map_comp_assoc]
    rw [mapDerivedCategoryPlusCompIso_hom_app_factorsh F G K]
    exact mapDerivedCategoryPlusCompIso_hom_app_factorsh (F ⋙ G) H K

end Coherence

end CategoryTheory.Functor
