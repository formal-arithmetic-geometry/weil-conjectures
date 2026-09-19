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
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Functoriality of `mapDerivedCategory`

For exact functors between abelian categories, the induced functor
`Functor.mapDerivedCategory` on derived categories is functorial:

- `CategoryTheory.Functor.mapDerivedCategoryIdIso`: the identity functor induces the
  identity functor, `(𝟭 C).mapDerivedCategory ≅ 𝟭 (DerivedCategory C)`.
- `CategoryTheory.Functor.mapDerivedCategoryNatIso`: an isomorphism `F ≅ G` of exact
  functors induces an isomorphism `F.mapDerivedCategory ≅ G.mapDerivedCategory`.
- `CategoryTheory.Functor.mapDerivedCategoryCompIso`: the composition isomorphism
  `(F ⋙ G).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory`.
- `CategoryTheory.Functor.mapDerivedCategoryIdFactors`,
  `CategoryTheory.Functor.mapDerivedCategoryCompFactors` and
  `CategoryTheory.Functor.mapDerivedCategoryNatIsoFactors`: the corresponding
  isomorphisms one level down, between the functors
  `_.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q` and
  `DerivedCategory.Q ⋙ _`, which commute with the shift. The three isomorphisms above
  are the descents of these along the localization functor, as recorded by
  `whiskerLeft_mapDerivedCategoryIdIso_hom`, `whiskerLeft_mapDerivedCategoryCompIso_hom`
  and `whiskerLeft_mapDerivedCategoryNatIso_inv`.
- `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso`: the commutation
  `H^n(-) ⋙ F ≅ F.mapDerivedCategory ⋙ H^n(-)` with the homology functors, with the
  bounded below variant `CategoryTheory.Functor.mapDerivedCategoryPlusHomologyFunctorIso`.
- `CategoryTheory.Functor.mapDerivedCategoryPlus`: the restriction of
  `F.mapDerivedCategory` to the bounded below derived categories, with the compatibility
  isomorphism `CategoryTheory.Functor.mapDerivedCategoryPlusCompatibility`.
- `CategoryTheory.Functor.mapDerivedCategoryPlusNatIso` and
  `CategoryTheory.Functor.mapDerivedCategoryPlusCompIso`: the corresponding
  functoriality of `mapDerivedCategoryPlus`, obtained by cancelling the fully faithful
  inclusions `DerivedCategory.Plus.ι`.
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

section Factors

/-- The naturality of the inverse of `Functor.mapDerivedCategoryFactors`, in the form in
which `Mathlib` states `Functor.mapDerivedCategoryFactors_hom_naturality`. -/
@[reassoc]
lemma mapDerivedCategoryFactors_inv_naturality (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) ≫
        F.mapDerivedCategoryFactors.inv.app L =
      F.mapDerivedCategoryFactors.inv.app K ≫
        F.mapDerivedCategory.map (DerivedCategory.Q.map f) :=
  F.mapDerivedCategoryFactors.inv.naturality f

/-- The shift of `Functor.mapDerivedCategoryFactors_hom_naturality`. -/
@[reassoc]
lemma shift_mapDerivedCategoryFactors_hom_naturality (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (m : ℤ) :
    (F.mapDerivedCategory.map (DerivedCategory.Q.map f))⟦m⟧' ≫
        (F.mapDerivedCategoryFactors.hom.app L)⟦m⟧' =
      (F.mapDerivedCategoryFactors.hom.app K)⟦m⟧' ≫
        (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f))⟦m⟧' := by
  rw [← Functor.map_comp, ← Functor.map_comp, F.mapDerivedCategoryFactors_hom_naturality]

variable (C) in
/-- The functor on cochain complexes induced by `𝟭 C` becomes the identity functor after
localization: the identification of `(𝟭 C).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q`
with `Q ⋙ 𝟭 (DerivedCategory C)`. -/
noncomputable def mapDerivedCategoryIdFactors :
    (𝟭 C).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q (C := C) ≅
      DerivedCategory.Q (C := C) ⋙ 𝟭 (DerivedCategory C) :=
  isoWhiskerRight (Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ))
      DerivedCategory.Q ≪≫
    (DerivedCategory.Q (C := C)).leftUnitor ≪≫
    (DerivedCategory.Q (C := C)).rightUnitor.symm

instance : NatTrans.CommShift (mapDerivedCategoryIdFactors C).hom ℤ := by
  have h : (mapDerivedCategoryIdFactors C).hom =
      Functor.whiskerRight (Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ)).hom
          DerivedCategory.Q ≫
        (DerivedCategory.Q (C := C)).leftUnitor.hom ≫
        (DerivedCategory.Q (C := C)).rightUnitor.inv := rfl
  rw [h]
  infer_instance

/-- The functor on cochain complexes induced by `F ⋙ G` becomes the composition of the
functors induced by `F` and by `G` after localization: the identification of
`(F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q` with
`Q ⋙ (F.mapDerivedCategory ⋙ G.mapDerivedCategory)`. -/
noncomputable def mapDerivedCategoryCompFactors (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q (C := E) ≅
      DerivedCategory.Q (C := C) ⋙ (F.mapDerivedCategory ⋙ G.mapDerivedCategory) :=
  isoWhiskerRight (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
      (ComplexShape.up ℤ)).symm DerivedCategory.Q ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
      G.mapDerivedCategoryFactors.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight F.mapDerivedCategoryFactors.symm G.mapDerivedCategory ≪≫
    Functor.associator _ _ _

instance (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    NatTrans.CommShift (mapDerivedCategoryCompFactors F G).hom ℤ := by
  have h : (mapDerivedCategoryCompFactors F G).hom =
      Functor.whiskerRight (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
          (ComplexShape.up ℤ)).inv DerivedCategory.Q ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
          G.mapDerivedCategoryFactors.inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight F.mapDerivedCategoryFactors.inv G.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom := rfl
  rw [h]
  infer_instance

/-- An isomorphism `α : F ≅ G` of exact functors identifies the functor on cochain
complexes induced by `G` with the functor induced by `F` after localization: the
identification of `G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q` with
`Q ⋙ F.mapDerivedCategory`. -/
noncomputable def mapDerivedCategoryNatIsoFactors {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (α : F ≅ G) :
    G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q (C := D) ≅
      DerivedCategory.Q (C := C) ⋙ F.mapDerivedCategory :=
  isoWhiskerRight (NatIso.mapHomologicalComplex α (ComplexShape.up ℤ)).symm
      DerivedCategory.Q ≪≫
    F.mapDerivedCategoryFactors.symm

instance {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (α : F ≅ G) :
    NatTrans.CommShift (mapDerivedCategoryNatIsoFactors α).hom ℤ := by
  have h : (mapDerivedCategoryNatIsoFactors α).hom =
      Functor.whiskerRight (NatIso.mapHomologicalComplex α (ComplexShape.up ℤ)).inv
          DerivedCategory.Q ≫ F.mapDerivedCategoryFactors.inv := rfl
  rw [h]
  infer_instance

end Factors

variable (C) in
/-- The identity functor of an abelian category induces the identity functor of its
derived category. -/
noncomputable def mapDerivedCategoryIdIso :
    (𝟭 C).mapDerivedCategory ≅ 𝟭 (DerivedCategory C) :=
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      ((𝟭 C).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (𝟭 (DerivedCategory C)) := ⟨(mapDerivedCategoryIdFactors C).symm⟩
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    ((𝟭 C).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    ((𝟭 C).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (𝟭 C).mapDerivedCategory (𝟭 (DerivedCategory C)) (Iso.refl _)

variable (C) in
/-- `Functor.mapDerivedCategoryIdIso` is the descent of
`Functor.mapDerivedCategoryIdFactors` along the localization functor. -/
lemma whiskerLeft_mapDerivedCategoryIdIso_hom :
    Functor.whiskerLeft DerivedCategory.Q (mapDerivedCategoryIdIso C).hom =
      (𝟭 C).mapDerivedCategoryFactors.hom ≫ (mapDerivedCategoryIdFactors C).hom := by
  ext K
  simp [mapDerivedCategoryIdIso]
  rfl

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

/-- `Functor.mapDerivedCategoryNatIso` is the descent of
`Functor.mapDerivedCategoryNatIsoFactors` along the localization functor. -/
lemma whiskerLeft_mapDerivedCategoryNatIso_inv {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    Functor.whiskerLeft DerivedCategory.Q (mapDerivedCategoryNatIso e).inv =
      G.mapDerivedCategoryFactors.hom ≫ (mapDerivedCategoryNatIsoFactors e).hom := by
  ext K
  simp [mapDerivedCategoryNatIso, mapDerivedCategoryNatIsoFactors]
  rfl

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

/-- `Functor.mapDerivedCategoryCompIso` is the descent of
`Functor.mapDerivedCategoryCompFactors` along the localization functor. -/
lemma whiskerLeft_mapDerivedCategoryCompIso_hom (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    Functor.whiskerLeft DerivedCategory.Q (mapDerivedCategoryCompIso F G).hom =
      (F ⋙ G).mapDerivedCategoryFactors.hom ≫ (mapDerivedCategoryCompFactors F G).hom := by
  ext K
  simp [mapDerivedCategoryCompIso, mapDerivedCategoryCompFactors]
  rfl

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
