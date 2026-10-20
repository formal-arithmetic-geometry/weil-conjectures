/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M7
-/
module

public import Sheaf.CategoryTheory.RightDerivedSingleH0
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Sheaf.CategoryTheory.RightDerivedSingleCounit
import Sheaf.CategoryTheory.AdjunctionComparisonSquare
import Sheaf.CategoryTheory.DerivedSingleConstantsComparison

/-! # Adjunction comparisons on single complexes

Source: Stacks Project, Tag 07A6, composition of derived adjunctions.
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Adjunction

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Composing normalized single-object counit squares preserves the comparison
of right adjoints through a specified exact-left-adjoint isomorphism.
Source: Stacks Project, Tag 07A6.
(blueprint: lem-kun-single-adjunction-comparison).

Proof: compose the two single counit equations, using naturality of the first
counit. The single comparisons for exact functors form a commutative square with
the descended constants isomorphism. Apply the counit characterization of the
unique right-adjoint comparison to this square. -/
theorem single_adjunction_comparison
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions E]
    {L : C ⥤ D} {S : D ⥤ C} {U : D ⥤ E} {R : E ⥤ D}
    {K : C ⥤ E} {T : E ⥤ C}
    [L.Additive] [S.Additive] [U.Additive] [R.Additive] [K.Additive] [T.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (a : L ⊣ S) (p : U ⊣ R) (b : K ⊣ T)
    (a' : L.mapDerivedCategory ⊣ S.mapDerivedCategory)
    (p' : U.mapDerivedCategory ⊣ R.rightDerivedFunctor)
    (b' : K.mapDerivedCategory ⊣ T.rightDerivedFunctor)
    (ha : ∀ X, L.mapDerivedCategory.map
        ((S.mapDerivedCategorySingleFunctor 0).inv.app X) ≫
      a'.counit.app ((DerivedCategory.singleFunctor D 0).obj X) =
        (L.mapDerivedCategorySingleFunctor 0).hom.app (S.obj X) ≫
          (DerivedCategory.singleFunctor D 0).map (a.counit.app X))
    (hp : ∀ X, U.mapDerivedCategory.map (R.singleRightDerivedUnit.app X) ≫
      p'.counit.app ((DerivedCategory.singleFunctor E 0).obj X) =
        (U.mapDerivedCategorySingleFunctor 0).hom.app (R.obj X) ≫
          (DerivedCategory.singleFunctor E 0).map (p.counit.app X))
    (hb : ∀ X, K.mapDerivedCategory.map (T.singleRightDerivedUnit.app X) ≫
      b'.counit.app ((DerivedCategory.singleFunctor E 0).obj X) =
        (K.mapDerivedCategorySingleFunctor 0).hom.app (T.obj X) ≫
          (DerivedCategory.singleFunctor E 0).map (b.counit.app X))
    (e : L ⋙ U ≅ K) (X : E) :
    (S.mapDerivedCategorySingleFunctor 0).inv.app (R.obj X) ≫
      S.mapDerivedCategory.map (R.singleRightDerivedUnit.app X) ≫
      (((a'.comp p').ofNatIsoLeft
        ((Functor.mapDerivedCategoryCompIso L U).symm ≪≫
          Functor.mapDerivedCategoryNatIso e)).rightAdjointUniq b').hom.app
            ((DerivedCategory.singleFunctor E 0).obj X) =
    (DerivedCategory.singleFunctor C 0).map
      ((((a.comp p).ofNatIsoLeft e).rightAdjointUniq b).hom.app X) ≫
        T.singleRightDerivedUnit.app X := by
  let i : DerivedCategory.singleFunctor C 0 ⋙
      (L.mapDerivedCategory ⋙ U.mapDerivedCategory) ≅
        (L ⋙ U) ⋙ DerivedCategory.singleFunctor E 0 :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (L.mapDerivedCategorySingleFunctor 0) U.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft L (U.mapDerivedCategorySingleFunctor 0) ≪≫
      (Functor.associator _ _ _).symm
  have hi (M : C) : i.hom.app M =
      U.mapDerivedCategory.map ((L.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
        (U.mapDerivedCategorySingleFunctor 0).hom.app (L.obj M) := by
    simp [i]
  have hc (Y : E) :
      (L.mapDerivedCategory ⋙ U.mapDerivedCategory).map
        ((S.mapDerivedCategorySingleFunctor 0).inv.app (R.obj Y) ≫
          S.mapDerivedCategory.map (R.singleRightDerivedUnit.app Y)) ≫
        (a'.comp p').counit.app ((DerivedCategory.singleFunctor E 0).obj Y) =
      i.hom.app ((R ⋙ S).obj Y) ≫
        (DerivedCategory.singleFunctor E 0).map ((a.comp p).counit.app Y) := by
    simp only [Functor.comp_map, comp_counit_app]
    rw [← U.mapDerivedCategory.map_comp_assoc]
    rw [L.mapDerivedCategory.map_comp, Category.assoc]
    have hn := a'.counit.naturality (R.singleRightDerivedUnit.app Y)
    simp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hn
    erw [hn]
    rw [← Category.assoc, ha, Functor.map_comp, Category.assoc, hp]
    simp only [U.mapDerivedCategory.map_comp, Category.assoc]
    erw [(U.mapDerivedCategorySingleFunctor 0).hom.naturality_assoc]
    simp only [Functor.comp_map, ← Functor.map_comp, hi]
    simp only [Category.assoc]
    rfl
  have h := rightAdjointUniq_square (a.comp p) b (a'.comp p') b'
    (DerivedCategory.singleFunctor C 0) (DerivedCategory.singleFunctor E 0)
    i (K.mapDerivedCategorySingleFunctor 0)
    (fun Y ↦ (S.mapDerivedCategorySingleFunctor 0).inv.app (R.obj Y) ≫
      S.mapDerivedCategory.map (R.singleRightDerivedUnit.app Y))
    (fun Y ↦ T.singleRightDerivedUnit.app Y) hc hb e
    ((Functor.mapDerivedCategoryCompIso L U).symm ≪≫
      Functor.mapDerivedCategoryNatIso e) (fun M ↦ by
        rw [hi]
        simpa only [Category.assoc] using
          (Functor.derived_single_constants_comparison L U K e M).symm) X
  simpa only [Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Zeroth homology of a normalized derived right-adjoint comparison is the ordinary
right-adjoint comparison, under the canonical augmentation isomorphisms.
Source: Stacks Tags 07A6 and 05TD (blueprint: lem-kun-single-adjunction-comparison).

Proof: the single-object counit equations give the square for the composed
right-adjoint comparison. Apply zeroth homology and the canonical augmentation
normalization to that square. Naturality and cancellation identify its map with
the ordinary comparison. -/
theorem single_adjunction_comparison_h0
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions E] [EnoughInjectives E]
    {L : C ⥤ D} {S : D ⥤ C} {U : D ⥤ E} {R : E ⥤ D}
    {K : C ⥤ E} {T : E ⥤ C}
    [L.Additive] [S.Additive] [U.Additive] [R.Additive] [K.Additive] [T.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits R] [PreservesFiniteLimits T]
    (a : L ⊣ S) (p : U ⊣ R) (b : K ⊣ T)
    (a' : L.mapDerivedCategory ⊣ S.mapDerivedCategory)
    (p' : U.mapDerivedCategory ⊣ R.rightDerivedFunctor)
    (b' : K.mapDerivedCategory ⊣ T.rightDerivedFunctor)
    (ha : ∀ X, L.mapDerivedCategory.map
        ((S.mapDerivedCategorySingleFunctor 0).inv.app X) ≫
      a'.counit.app ((DerivedCategory.singleFunctor D 0).obj X) =
        (L.mapDerivedCategorySingleFunctor 0).hom.app (S.obj X) ≫
          (DerivedCategory.singleFunctor D 0).map (a.counit.app X))
    (hp : ∀ X, U.mapDerivedCategory.map (R.singleRightDerivedUnit.app X) ≫
      p'.counit.app ((DerivedCategory.singleFunctor E 0).obj X) =
        (U.mapDerivedCategorySingleFunctor 0).hom.app (R.obj X) ≫
          (DerivedCategory.singleFunctor E 0).map (p.counit.app X))
    (hb : ∀ X, K.mapDerivedCategory.map (T.singleRightDerivedUnit.app X) ≫
      b'.counit.app ((DerivedCategory.singleFunctor E 0).obj X) =
        (K.mapDerivedCategorySingleFunctor 0).hom.app (T.obj X) ≫
          (DerivedCategory.singleFunctor E 0).map (b.counit.app X))
    (e : L ⋙ U ≅ K) (X : E) :
    (R.mapSingleRightDerivedH0Iso S X).inv ≫
        (DerivedCategory.homologyFunctor C 0).map
          ((((a'.comp p').ofNatIsoLeft
            ((Functor.mapDerivedCategoryCompIso L U).symm ≪≫
              Functor.mapDerivedCategoryNatIso e)).rightAdjointUniq b').hom.app
                ((DerivedCategory.singleFunctor E 0).obj X)) ≫
      (T.singleRightDerivedH0Iso X).hom =
    ((((a.comp p).ofNatIsoLeft e).rightAdjointUniq b).hom.app X) := by
  have h := single_adjunction_comparison a p b a' p' b' ha hp hb e X
  apply Functor.mapSingleRightDerivedH0Iso_conjugate R S T X
  simpa only [Category.assoc] using h

section Canonical
open MonoidalCategory
variable
  {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [Abelian.HasKInjectiveResolutions D] [Abelian.HasKInjectiveResolutions E]
  {L : C ⥤ D} {S : D ⥤ C} {U : D ⥤ E} {R : E ⥤ D}
  {K : C ⥤ E} {T : E ⥤ C}
  [L.Additive] [S.Additive] [U.Additive] [R.Additive] [K.Additive] [T.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits K] [PreservesFiniteColimits K]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]

/-- The canonical composite right-adjoint comparison obtained from exact termwise
left adjoints and their canonical derived adjunctions.
Source: Stacks Tag 07A6 (blueprint: lem-kun-single-adjunction-comparison). -/
@[irreducible]
noncomputable def normalizedDerivedRightAdjointIso
    (a : L ⊣ S) (p : U ⊣ R) (b : K ⊣ T) (e : L ⋙ U ≅ K) :
    R.rightDerivedFunctor ⋙ S.mapDerivedCategory ≅ T.rightDerivedFunctor :=
  (((a.mapDerivedCategoryAdjunction.comp
      (p.derivedAdjunction.ofNatIsoLeft U.leftDerivedFunctorIsoMapDerivedCategory)).ofNatIsoLeft
        ((Functor.mapDerivedCategoryCompIso L U).symm ≪≫
          Functor.mapDerivedCategoryNatIso e)).rightAdjointUniq
            (b.derivedAdjunction.ofNatIsoLeft K.leftDerivedFunctorIsoMapDerivedCategory))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical composite comparison is characterized by compatibility with the
transported derived counits. Source: Stacks Tag 07A6
(blueprint: lem-kun-single-adjunction-comparison).

Proof: apply the counit characterization of uniqueness of right adjoints, expand the
transported composite counit, and cancel the constants isomorphism and its inverse. -/
theorem normalizedDerivedRightAdjointIso_counit
    (a : L ⊣ S) (p : U ⊣ R) (b : K ⊣ T) (e : L ⋙ U ≅ K)
    (Y : DerivedCategory E) :
    ((Functor.mapDerivedCategoryCompIso L U).symm ≪≫
      Functor.mapDerivedCategoryNatIso e).hom.app
        ((R.rightDerivedFunctor ⋙ S.mapDerivedCategory).obj Y) ≫
      K.mapDerivedCategory.map ((normalizedDerivedRightAdjointIso a p b e).hom.app Y) ≫
        (b.derivedAdjunction.ofNatIsoLeft
          K.leftDerivedFunctorIsoMapDerivedCategory).counit.app Y =
    U.mapDerivedCategory.map (a.mapDerivedCategoryAdjunction.counit.app
      (R.rightDerivedFunctor.obj Y)) ≫
        (p.derivedAdjunction.ofNatIsoLeft
          U.leftDerivedFunctorIsoMapDerivedCategory).counit.app Y := by
  delta normalizedDerivedRightAdjointIso
  rw [rightAdjointUniq_hom_app_counit]
  simp only [ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.hom_inv_id_app_assoc, comp_counit_app]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical derived composite comparison has the ordinary comparison as normalized
zeroth homology. Source: Stacks Tags 07A6 and 05TD
(blueprint: lem-kun-single-adjunction-comparison).

Proof: the canonical derived counits satisfy the single-object normalization, including
for the exact stalk-side right adjoint. The single comparison square followed by the
zeroth-homology augmentation rule gives the asserted equality. -/
theorem normalizedDerivedRightAdjointIso_h0 [EnoughInjectives E]
    [PreservesFiniteLimits R] [PreservesFiniteLimits T]
    (a : L ⊣ S) (p : U ⊣ R) (b : K ⊣ T) (e : L ⋙ U ≅ K) (X : E) :
    (R.mapSingleRightDerivedH0Iso S X).inv ≫
        (DerivedCategory.homologyFunctor C 0).map
          ((normalizedDerivedRightAdjointIso a p b e).hom.app
            ((DerivedCategory.singleFunctor E 0).obj X)) ≫
      (T.singleRightDerivedH0Iso X).hom =
    ((((a.comp p).ofNatIsoLeft e).rightAdjointUniq b).hom.app X) := by
  delta normalizedDerivedRightAdjointIso
  exact single_adjunction_comparison_h0 a p b _ _ _
    (single_mapDerivedCategory_counit a) (single_rightDerived_counit p)
    (single_rightDerived_counit b) e X

end Canonical

end CategoryTheory.Adjunction
