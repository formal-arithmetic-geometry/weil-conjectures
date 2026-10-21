/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.AlgebraicGeometry.SupportedLocalizationComparisons
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedCategories

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import Sheaf.AlgebraicGeometry.SupportedExteriorProductSupportMaps
import Sheaf.AlgebraicGeometry.SupportedExteriorProductBoundary
import Sheaf.AlgebraicGeometry.SupportedCoefficientSecondOpenTensor
import Sheaf.CategoryTheory.UnboundedInjectiveModel
import WeilConjectures.SixFunctors.BaseChange.GlobalSections
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap

/-!
# Supported exterior products and localization triangles

Source: Stacks Tags 09XP and 0F1E, and the refinement in the complete proof of
lem-pur-supported-product-localization (blueprint: lem-pur-supported-product-localization).
The third components are the supported exterior products on the actual open product
schemes, transported through the canonical ambient and coefficient comparisons.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry.Etale

/-- The support triangle tensored in the first variable, using the canonical
exact tensor functor and its signed shift comparison.
Source: Tag 09XP (blueprint: lem-pur-supported-product-localization). -/
noncomputable def supportedFirstLocalizationSource (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (_f : X ⟶ S) (_g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    Triangle (DerivedCategory (ModuleCat.{u + 1} A)) :=
  (tensorRight ((supportedSectionsDerived A d).obj L)).mapTriangle.obj
    (normalizedSupportTriangle A b c K)

/-- The product support triangle, with the normalized injective-resolution boundary.
Source: Tag 09XP (blueprint: lem-pur-supported-product-localization). -/
noncomputable def supportedFirstLocalizationTarget (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    Triangle (DerivedCategory (ModuleCat.{u + 1} A)) :=
  normalizedSupportTriangle A (supportedProductImmersion f g b d) (supportedProductImmersion f g
    c (𝟙 Y))
    (externalProduct (ModuleCat.{u + 1} A) f g K L)

/-- The first specified supported exterior-product component.
Source: Tag 0F1E (blueprint: lem-pur-supported-product-localization). -/
noncomputable def supportedFirstLocalizationComponent₁ (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    (supportedFirstLocalizationSource A f g b c d K L).obj₁ ⟶
      (supportedFirstLocalizationTarget A f g b c d K L).obj₁ :=
  supportedExteriorProduct A f g (supportIntersection b c) d K L ≫
    (derivedSupportCongruence A (supportedProductImmersion f g (supportIntersection b c) d)
      (supportIntersection (supportedProductImmersion f g b d) (supportedProductImmersion f g c
        (𝟙 Y)))
      (supportedFirstIntersection_complement f g b c d)).hom.app
        (externalProduct (ModuleCat.{u + 1} A) f g K L)

/-- The second specified supported exterior-product component.
Source: Tag 0F1E (blueprint: lem-pur-supported-product-localization). -/
noncomputable def supportedFirstLocalizationComponent₂ (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    (supportedFirstLocalizationSource A f g b c d K L).obj₂ ⟶
      (supportedFirstLocalizationTarget A f g b c d K L).obj₂ :=
  supportedExteriorProduct A f g b d K L

/-- The third component is the prescribed supported exterior product on the open
product, transported back by the canonical ambient comparison.
Source: Tags 09XP and 0F1E (blueprint: lem-pur-supported-product-localization). -/
noncomputable def supportedFirstLocalizationComponent₃ (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    (supportedFirstLocalizationSource A f g b c d K L).obj₃ ⟶
      (supportedFirstLocalizationTarget A f g b c d K L).obj₃ :=
  supportedExteriorProduct A (c.openComplement.ι ≫ f) g
      (supportOnOpen b c.openComplement) d
      ((upperStar (ModuleCat.{u + 1} A) c.openComplement.ι).mapDerivedCategory.obj K) L ≫
    (supportedFirstLocalizationThirdIso A f g b c d K L).inv

/-- The support triangle tensored in the second variable, using the canonical
exact tensor functor and its signed shift comparison.
Source: Tag 09XP (blueprint: lem-pur-supported-product-localization). -/
noncomputable def supportedSecondLocalizationSource (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (_f : X ⟶ S) (_g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ Y) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    Triangle (DerivedCategory (ModuleCat.{u + 1} A)) :=
  (tensorLeft ((supportedSectionsDerived A b).obj K)).mapTriangle.obj (normalizedSupportTriangle
    A d c L)

/-- The product support triangle, with the normalized injective-resolution boundary.
Source: Tag 09XP (blueprint: lem-pur-supported-product-localization). -/
noncomputable def supportedSecondLocalizationTarget (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ Y) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    Triangle (DerivedCategory (ModuleCat.{u + 1} A)) :=
  normalizedSupportTriangle A (supportedProductImmersion f g b d) (supportedProductImmersion f g
    (𝟙 X) c)
    (externalProduct (ModuleCat.{u + 1} A) f g K L)

/-- The first specified supported exterior-product component.
Source: Tag 0F1E (blueprint: lem-pur-supported-product-localization). -/
noncomputable def supportedSecondLocalizationComponent₁ (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ Y) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    (supportedSecondLocalizationSource A f g b c d K L).obj₁ ⟶
      (supportedSecondLocalizationTarget A f g b c d K L).obj₁ :=
  supportedExteriorProduct A f g b (supportIntersection d c) K L ≫
    (derivedSupportCongruence A (supportedProductImmersion f g b (supportIntersection d c))
      (supportIntersection (supportedProductImmersion f g b d) (supportedProductImmersion f g (𝟙
        X) c))
      (supportedSecondIntersection_complement f g b c d)).hom.app
        (externalProduct (ModuleCat.{u + 1} A) f g K L)

/-- The second specified supported exterior-product component.
Source: Tag 0F1E (blueprint: lem-pur-supported-product-localization). -/
noncomputable def supportedSecondLocalizationComponent₂ (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ Y) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    (supportedSecondLocalizationSource A f g b c d K L).obj₂ ⟶
      (supportedSecondLocalizationTarget A f g b c d K L).obj₂ :=
  supportedExteriorProduct A f g b d K L

/-- The third component is the prescribed supported exterior product on the open
product, transported back by the canonical ambient comparison.
Source: Tags 09XP and 0F1E (blueprint: lem-pur-supported-product-localization). -/
noncomputable def supportedSecondLocalizationComponent₃ (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ Y) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    (supportedSecondLocalizationSource A f g b c d K L).obj₃ ⟶
      (supportedSecondLocalizationTarget A f g b c d K L).obj₃ :=
  supportedExteriorProduct A f (c.openComplement.ι ≫ g)
      b (supportOnOpen d c.openComplement) K
      ((upperStar (ModuleCat.{u + 1} A) c.openComplement.ι).mapDerivedCategory.obj L) ≫
    (supportedSecondLocalizationThirdIso A f g b c d K L).inv

/-- Map the derived external product in both coefficient objects using its bifunctor.
Source: Tag 0F1E (blueprint: lem-pur-supported-product-localization). -/
noncomputable def supportedExternalProductMap (A : Type (u + 1)) [CommRing A]
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    {K K' : DerivedCategoryModule A X} {L L' : DerivedCategoryModule A Y}
    (a : K ⟶ K') (e : L ⟶ L') :
    externalProduct (ModuleCat.{u + 1} A) f g K L ⟶
      externalProduct (ModuleCat.{u + 1} A) f g K' L' :=
  (supportedExternalProductIso (ModuleCat.{u + 1} A) f g K L).hom ≫
    supportedDerivedTensorMap A (pullback f g)
    ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.map a)
    ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.map e) ≫
    (supportedExternalProductIso (ModuleCat.{u + 1} A) f g K' L').inv

private theorem evaluation_natural
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (R : D ⥤ C) (G G' : D ⥤ E) (H : C ⥤ E)
    (σ : H ≅ F ⋙ G) (ε : R ⋙ F ⟶ 𝟭 D) (τ : G' ≅ G)
    {K K' : D} (a : K ⟶ K') :
    H.map (R.map a) ≫
        (σ.hom.app (R.obj K') ≫ G.map (ε.app K') ≫ τ.inv.app K') =
      (σ.hom.app (R.obj K) ≫ G.map (ε.app K) ≫ τ.inv.app K) ≫ G'.map a := by
  exact (Functor.whiskerLeft R σ.hom ≫ Functor.whiskerRight ε G ≫ τ.inv).naturality a

private def bifunctorMap {D : Type*} [Category D] (T : D ⥤ D ⥤ D)
    {U U' V V' : D} (a : U ⟶ U') (b : V ⟶ V') :
    (T.obj U).obj V ⟶ (T.obj U').obj V' :=
  (T.map a).app V ≫ (T.obj U').map b

private theorem bifunctorMap_comp {D : Type*} [Category D] (T : D ⥤ D ⥤ D)
    {U U' U'' V V' V'' : D} (a : U ⟶ U') (b : V ⟶ V')
    (a' : U' ⟶ U'') (b' : V' ⟶ V'') :
    bifunctorMap T a b ≫ bifunctorMap T a' b' = bifunctorMap T (a ≫ a') (b ≫ b') := by
  simp only [bifunctorMap, Category.assoc, Functor.map_comp, NatTrans.comp_app]
  rw [(T.map a').naturality_assoc b]

private theorem adjunct_bifunctor_pairing_natural
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    {F : C ⥤ D} {R : D ⥤ C} (adj : F ⊣ R) (T : D ⥤ D ⥤ D)
    {M M' N N' : C} {U U' V V' P P' Q Q' : D}
    (a : M ⟶ M') (b : N ⟶ N') (x : U ⟶ U') (y : V ⟶ V')
    (t : F.obj (M ⊗ N) ⟶ (T.obj U).obj V)
    (t' : F.obj (M' ⊗ N') ⟶ (T.obj U').obj V')
    (v : U ⟶ P) (v' : U' ⟶ P') (w : V ⟶ Q) (w' : V' ⟶ Q')
    (p : P ⟶ P') (q : Q ⟶ Q')
    (ht : F.map (a ⊗ₘ b) ≫ t' = t ≫ bifunctorMap T x y)
    (hv : x ≫ v' = v ≫ p) (hw : y ≫ w' = w ≫ q) :
    (a ⊗ₘ b) ≫ adj.homEquiv _ _ (t' ≫ bifunctorMap T v' w') =
      adj.homEquiv _ _ (t ≫ bifunctorMap T v w) ≫ R.map (bifunctorMap T p q) := by
  apply adj.homEquiv_naturality_left_square
  rw [← Category.assoc, ht, Category.assoc, bifunctorMap_comp, hv, hw,
    ← bifunctorMap_comp, ← Category.assoc]

private theorem schemeComparison_natural
    (E : Type (u + 2)) [Category.{u + 1} E] [Abelian E]
    [IsGrothendieckAbelian.{u + 1} E] [HasDerivedCategory.{u + 1} E]
    [MonoidalCategory E] [MonoidalPreadditive E] [SymmetricCategory E] [MonoidalClosed E]
    [Abelian.HasFunctorialFlatResolution E] (T : Scheme.{u})
    (G F₁ F₂ : E ⥤ Sheaf T.smallEtaleTopology E)
    [G.Additive] [F₁.Additive] [F₂.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂] [G.IsLeftAdjoint]
    (τ : (Functor.postcompose₂.obj G).obj (curriedTensor E) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁).obj F₂).obj
        (supportedSheafTensorGeneric E T))
    (t : supportedSchemeDerivedHom E T G F₁ F₂)
    (ht : supportedSchemeDerivedCondition E T G F₁ F₂ τ t)
    {M M' N N' : DerivedCategory E} (a : M ⟶ M') (b : N ⟶ N') :
    G.mapDerivedCategory.map (a ⊗ₘ b) ≫ supportedSchemeDerivedApply E T G F₁ F₂ t M' N' =
      supportedSchemeDerivedApply E T G F₁ F₂ t M N ≫
        bifunctorMap (derivedTensor E T) (F₁.mapDerivedCategory.map a)
          (F₂.mapDerivedCategory.map b) := by
  exact ht.1 M M' N N' a b

private theorem firstEvaluation_natural (A : Type (u + 1)) [CommRing A]
    {S X Y B : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X)
    [IsClosedImmersion b] {K K' : DerivedCategoryModule A X} (a : K ⟶ K') :
    (supportedFirstCoefficients A f g b).mapDerivedCategory.map
        ((supportedSectionsDerived A b).map a) ≫ supportedFirstEvaluation A f g b K' =
      supportedFirstEvaluation A f g b K ≫
        (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.map a := by
  exact evaluation_natural (supportedCoefficients A b).mapDerivedCategory
    (supportedSectionsDerived A b)
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor
    (supportedFirstCoefficients A f g b).mapDerivedCategory
    (Functor.mapDerivedCategoryCompIso (supportedCoefficients A b)
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)))
    (supportedCoefficientDerivedAdjunction A b).counit
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (pullback.fst f g)) a

private theorem secondEvaluation_natural (A : Type (u + 1)) [CommRing A]
    {S X Y D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y)
    [IsClosedImmersion d] {L L' : DerivedCategoryModule A Y} (e : L ⟶ L') :
    (supportedSecondCoefficients A f g d).mapDerivedCategory.map
        ((supportedSectionsDerived A d).map e) ≫ supportedSecondEvaluation A f g d L' =
      supportedSecondEvaluation A f g d L ≫
        (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.map e := by
  exact evaluation_natural (supportedCoefficients A d).mapDerivedCategory
    (supportedSectionsDerived A d)
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor
    (supportedSecondCoefficients A f g d).mapDerivedCategory
    (Functor.mapDerivedCategoryCompIso (supportedCoefficients A d)
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)))
    (supportedCoefficientDerivedAdjunction A d).counit
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (pullback.snd f g)) e

private theorem externalProductMap_eq (A : Type (u + 1)) [CommRing A]
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    {K K' : DerivedCategoryModule A X} {L L' : DerivedCategoryModule A Y}
    (a : K ⟶ K') (e : L ⟶ L') :
    supportedExternalProductMap A f g a e =
      supportedDerivedTensorMap A (pullback f g)
        ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.map a)
        ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.map e) := by
  change 𝟙 _ ≫ _ ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

/-- Naturality of every specified exterior-product component under coefficient morphisms.
Source: Tag 0F1E (blueprint: lem-pur-supported-product-localization).
Proof: evaluation and the coefficient tensor map are natural in both variables. Apply
that naturality to their composite and then the natural supported-coefficient adjunction.
The argument applies also on each open product, hence to all three triangle components. -/
theorem supportedProductLocalization_naturality (A : Type (u + 1)) [CommRing A]
    {S X Y B D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d]
    {K K' : DerivedCategoryModule A X} {L L' : DerivedCategoryModule A Y}
    (a : K ⟶ K') (e : L ⟶ L') :
    ((supportedSectionsDerived A b).map a ⊗ₘ (supportedSectionsDerived A d).map e) ≫
        supportedExteriorProduct A f g b d K' L' =
      supportedExteriorProduct A f g b d K L ≫
        (supportedSectionsDerived A (supportedProductImmersion f g b d)).map
          (supportedExternalProductMap A f g a e) := by
  rw [externalProductMap_eq]
  have ht := schemeComparison_natural (ModuleCat.{u + 1} A) (pullback f g)
    (supportedCoefficients A (supportedProductImmersion f g b d))
    (supportedFirstCoefficients A f g b) (supportedSecondCoefficients A f g d)
    (supportedCoefficientTensorNatTrans A f g b d)
    (exists_unique_supportedCoefficientTensorDerived A f g b d).choose
    (exists_unique_supportedCoefficientTensorDerived A f g b d).choose_spec.1
    ((supportedSectionsDerived A b).map a) ((supportedSectionsDerived A d).map e)
  have h := adjunct_bifunctor_pairing_natural
    (supportedCoefficientDerivedAdjunction A (supportedProductImmersion f g b d))
    (derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
    ((supportedSectionsDerived A b).map a) ((supportedSectionsDerived A d).map e)
    _ _ _ _ _ _ _ _ _ _ ht
    (firstEvaluation_natural A f g b a) (secondEvaluation_natural A f g d e)
  exact h

private theorem coefficientMate_counit
    {B C D : Type*} [Category B] [Category C] [Category D]
    {F : B ⥤ C} {R : C ⥤ B} {F' : B ⥤ D} {R' : D ⥤ B}
    (adj : F ⊣ R) (adj' : F' ⊣ R') (H : C ⥤ D) (r : R ⟶ H ⋙ R') (K : C) :
    F'.map (r.app K) ≫ adj'.counit.app (H.obj K) =
      (supportCoefficientMate adj adj' H r).app (R.obj K) ≫ H.map (adj.counit.app K) := by
  simpa [supportCoefficientMate] using mateEquiv_counit_symm adj adj'
    (TwoSquare.mk _ _ _ _ ((Functor.rightUnitor R).hom ≫ r)) K

private theorem coefficientMate_transpose
    {B C D : Type*} [Category B] [Category C] [Category D]
    {F : B ⥤ C} {R : C ⥤ B} {F' : B ⥤ D} {R' : D ⥤ B}
    (adj : F ⊣ R) (adj' : F' ⊣ R') (H : C ⥤ D) (r : R ⟶ H ⋙ R')
    {M : B} {K : C} (t : F.obj M ⟶ K) :
    adj'.homEquiv _ _ ((supportCoefficientMate adj adj' H r).app M ≫ H.map t) =
      adj.homEquiv _ _ t ≫ r.app K := by
  apply (adj'.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_symm_apply, Functor.map_comp,
    Category.assoc, coefficientMate_counit adj adj' H r K,
    (supportCoefficientMate adj adj' H r).naturality_assoc]
  change _ = (supportCoefficientMate adj adj' H r).app M ≫
    H.map (F.map (adj.homEquiv _ _ t)) ≫ H.map (adj.counit.app K)
  rw [← H.map_comp]
  have ht := (adj.homEquiv M K).symm_apply_apply t
  change F.map (adj.homEquiv M K t) ≫ adj.counit.app K = t at ht
  rw [ht]

private theorem coefficientEvaluation_eq
    {B C D : Type*} [Category B] [Category C] [Category D]
    (F : B ⥤ C) (R : C ⥤ B) (P Q : C ⥤ D) (G : B ⥤ D)
    (σ : G ≅ F ⋙ P) (τ : Q ≅ P) (ε : R ⋙ F ⟶ 𝟭 C) (K : C) :
    σ.hom.app (R.obj K) ≫ P.map (ε.app K) ≫ τ.inv.app K =
      (σ ≪≫ Functor.isoWhiskerLeft F τ.symm).hom.app (R.obj K) ≫ Q.map (ε.app K) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc]
  congr 1
  exact τ.inv.naturality (ε.app K)

private theorem evaluation_transport
    {B C C' D D' : Type*}
    [Category B] [Category C] [Category C'] [Category D] [Category D']
    {F : B ⥤ C} {R : C ⥤ B} {F' : B ⥤ C'} {R' : C' ⥤ B}
    (adj : F ⊣ R) (adj' : F' ⊣ R') (J : C ⥤ C') (r : R ⟶ J ⋙ R')
    (P : C ⥤ D) (P' : C' ⥤ D') (H : D ⥤ D')
    (G : B ⥤ D) (G' : B ⥤ D')
    (σ : G ≅ F ⋙ P) (σ' : G' ≅ F' ⋙ P')
    (K : C) (e : H.obj (P.obj K) ≅ P'.obj (J.obj K))
    (eF : H.obj (P.obj (F.obj (R.obj K))) ≅ P'.obj (J.obj (F.obj (R.obj K))))
    (he : H.map (P.map (adj.counit.app K)) ≫ e.hom =
      eF.hom ≫ P'.map (J.map (adj.counit.app K))) :
    (σ'.hom.app (R.obj K) ≫
      P'.map ((supportCoefficientMate adj adj' J r).app (R.obj K)) ≫
      eF.inv ≫ H.map (σ.inv.app (R.obj K))) ≫
      H.map (σ.hom.app (R.obj K) ≫ P.map (adj.counit.app K)) ≫ e.hom =
    G'.map (r.app K) ≫
      (σ'.hom.app (R'.obj (J.obj K)) ≫ P'.map (adj'.counit.app (J.obj K))) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, σ.inv_hom_id_app]
  erw [H.map_id, Category.id_comp]
  rw [he, Iso.inv_hom_id_assoc, ← P'.map_comp, ← coefficientMate_counit adj adj' J r K]
  rw [P'.map_comp]
  simpa only [Category.assoc, Functor.comp_map, Functor.comp_obj, Functor.id_obj] using congrArg
    (fun t ↦ t ≫ P'.map (adj'.counit.app (J.obj K)))
    (σ'.hom.naturality (r.app K)).symm

private theorem evaluation_pullback
    {B C D D' : Type*} [Category B] [Category C] [Category D] [Category D']
    (F : B ⥤ C) (R : C ⥤ B) (ε : R ⋙ F ⟶ 𝟭 C)
    (P : C ⥤ D) (P' : C ⥤ D') (H : D ⥤ D') (G : B ⥤ D) (G' : B ⥤ D')
    (σ : G ≅ F ⋙ P) (σ' : G' ≅ F ⋙ P') (K : C)
    (e : H.obj (P.obj K) ≅ P'.obj K)
    (eF : H.obj (P.obj (F.obj (R.obj K))) ≅ P'.obj (F.obj (R.obj K)))
    (he : H.map (P.map (ε.app K)) ≫ e.hom = eF.hom ≫ P'.map (ε.app K)) :
    (σ'.hom.app (R.obj K) ≫ eF.inv ≫ H.map (σ.inv.app (R.obj K))) ≫
      H.map (σ.hom.app (R.obj K) ≫ P.map (ε.app K)) ≫ e.hom =
    σ'.hom.app (R.obj K) ≫ P'.map (ε.app K) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, σ.inv_hom_id_app]
  erw [H.map_id, Category.id_comp]
  rw [he, Iso.inv_hom_id_assoc]

private theorem bifunctorComparison_natural
    {C D : Type*} [Category C] [Category D] (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
    (F : C ⥤ D)
    (δ : (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj T')
    {M M' N N' : C} (v : M ⟶ M') (w : N ⟶ N') :
    F.map (bifunctorMap T v w) ≫ (δ.app M').app N' =
      (δ.app M).app N ≫ bifunctorMap T' (F.map v) (F.map w) := by
  dsimp only [bifunctorMap]
  have h₁ : F.map ((T.obj M').map w) ≫ (δ.app M').app N' =
      (δ.app M').app N ≫ (T'.obj (F.obj M')).map (F.map w) :=
    (δ.app M').naturality w
  have h₂ : F.map ((T.map v).app N) ≫ (δ.app M').app N =
      (δ.app M).app N ≫ (T'.map (F.map v)).app (F.obj N) :=
    NatTrans.congr_app (δ.naturality v) N
  rw [F.map_comp, Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc]

private theorem exactPullbackTensor_natural (A : Type (u + 1)) [CommRing A]
    {P Q : Scheme.{u}} (h : Q ⟶ P)
    {M M' N N' : DerivedCategoryModule A P} (v : M ⟶ M') (w : N ⟶ N') :
    (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.map
        (supportedDerivedTensorMap A P v w) ≫
      (supportExactPullbackTensorIso (ModuleCat.{u + 1} A) h M' N').hom =
    (supportExactPullbackTensorIso (ModuleCat.{u + 1} A) h M N).hom ≫
      supportedDerivedTensorMap A Q
        ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.map v)
        ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.map w) := by
  let H := (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory
  let J := (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor
  let τ := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) h
  let T := derivedTensor (ModuleCat.{u + 1} A) P
  let T' := derivedTensor (ModuleCat.{u + 1} A) Q
  let δ := (Functor.postcompose₂.mapIso τ.symm).app T ≪≫
    leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) h ≪≫
    (((Functor.whiskeringLeft₂ (DerivedCategoryModule A Q)).mapIso τ).app J).app T' ≪≫
    (((Functor.whiskeringLeft₂ (DerivedCategoryModule A Q)).obj H).mapIso τ).app T'
  exact bifunctorComparison_natural T T' H δ.hom v w

private theorem adjunct_pairing_transport
    {B C C' : Type*} [Category B] [MonoidalCategory B] [Category C] [Category C']
    {F : B ⥤ C} {R : C ⥤ B} {F' : B ⥤ C'} {R' : C' ⥤ B}
    (adj : F ⊣ R) (adj' : F' ⊣ R') (H : C ⥤ C') (r : R ⟶ H ⋙ R')
    (T : C ⥤ C ⥤ C) (T' : C' ⥤ C' ⥤ C')
    {M M' N N' : B} {V W P Q : C} {V₀ W₀ V' W' P' Q' : C'}
    (a : M ⟶ M') (b : N ⟶ N')
    (t : F.obj (M ⊗ N) ⟶ (T.obj V).obj W)
    (t₀ : F'.obj (M ⊗ N) ⟶ (T'.obj V₀).obj W₀)
    (t' : F'.obj (M' ⊗ N') ⟶ (T'.obj V').obj W')
    (x : V₀ ⟶ H.obj V) (y : W₀ ⟶ H.obj W)
    (v : V ⟶ P) (w : W ⟶ Q) (v' : V' ⟶ P') (w' : W' ⟶ Q')
    (a' : V₀ ⟶ V') (b' : W₀ ⟶ W')
    (e : H.obj P ⟶ P') (d : H.obj Q ⟶ Q')
    (δ₀ : H.obj ((T.obj V).obj W) ⟶ (T'.obj (H.obj V)).obj (H.obj W))
    (δ₁ : H.obj ((T.obj P).obj Q) ⟶ (T'.obj (H.obj P)).obj (H.obj Q))
    (hc : (supportCoefficientMate adj adj' H r).app (M ⊗ N) ≫ H.map t ≫ δ₀ =
      t₀ ≫ bifunctorMap T' x y)
    (hδ : H.map (bifunctorMap T v w) ≫ δ₁ =
      δ₀ ≫ bifunctorMap T' (H.map v) (H.map w))
    (hv : x ≫ H.map v ≫ e = a' ≫ v') (hw : y ≫ H.map w ≫ d = b' ≫ w')
    (ht : F'.map (a ⊗ₘ b) ≫ t' = t₀ ≫ bifunctorMap T' a' b') :
    adj.homEquiv _ _ (t ≫ bifunctorMap T v w) ≫ r.app ((T.obj P).obj Q) ≫
      R'.map (δ₁ ≫ bifunctorMap T' e d) =
    (a ⊗ₘ b) ≫ adj'.homEquiv _ _ (t' ≫ bifunctorMap T' v' w') := by
  rw [← Category.assoc, ← coefficientMate_transpose adj adj' H r,
    ← adj'.homEquiv_naturality_right, ← adj'.homEquiv_naturality_left]
  congr 1
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hδ, reassoc_of% hc]
  rw [← Category.assoc (bifunctorMap T' x y), bifunctorMap_comp, bifunctorMap_comp,
    Category.assoc x, Category.assoc y, hv, hw, ← bifunctorMap_comp,
    ← Category.assoc, ← ht, Category.assoc]

private theorem openRestriction_eq_transport (A : Type (u + 1)) [CommRing A]
    {X B : Scheme.{u}} (b : B ⟶ X) [IsClosedImmersion b] (U : X.Opens) :
    derivedSupportOpenRestriction A b U =
      derivedSupportTransport A U.ι b (supportOnOpen b U)
        (supportOnOpen_complement b U) := by
  rfl

private theorem pullbackSquare_natural (A : Type (u + 1)) [CommRing A]
    {P Q X X' : Scheme.{u}} (h : Q ⟶ P) (p : P ⟶ X) (q : Q ⟶ X')
    (a : X' ⟶ X) (hp : h ≫ p = q ≫ a)
    {K L : DerivedCategoryModule A X} (t : K ⟶ L) :
    (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.map
        ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.map t) ≫
      (supportPullbackSquareIso (ModuleCat.{u + 1} A) h p q a hp L).hom =
    (supportPullbackSquareIso (ModuleCat.{u + 1} A) h p q a hp K).hom ≫
      (upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.map
        ((upperStar (ModuleCat.{u + 1} A) a).mapDerivedCategory.map t) := by
  let e := Functor.isoWhiskerLeft
      (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) h).symm ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) h p).symm ≪≫
    leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q a (h ≫ p) hp ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) a)
      (upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor
  exact e.hom.naturality t

private theorem pullbackProjection_natural (A : Type (u + 1)) [CommRing A]
    {P Q X : Scheme.{u}} (h : Q ⟶ P) (p : P ⟶ X) (q : Q ⟶ X)
    (hp : h ≫ p = q) {K L : DerivedCategoryModule A X} (t : K ⟶ L) :
    (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.map
        ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.map t) ≫
      (supportPullbackProjectionIso (ModuleCat.{u + 1} A) h p q hp L).hom =
    (supportPullbackProjectionIso (ModuleCat.{u + 1} A) h p q hp K).hom ≫
      (upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.map t := by
  let e := Functor.isoWhiskerLeft
      (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) h).symm ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) h p q hp.symm).symm
  exact e.hom.naturality t

private theorem firstEvaluation_eq (A : Type (u + 1)) [CommRing A]
    {S X Y B : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X)
    [IsClosedImmersion b] (K : DerivedCategoryModule A X) :
    supportedFirstEvaluation A f g b K =
      (supportFirstCoefficientProjectionIso A f g b).hom.app
        ((supportedSectionsDerived A b).obj K) ≫
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.map
        ((supportedCoefficientDerivedAdjunction A b).counit.app K) := by
  exact coefficientEvaluation_eq _ _ _ _ _ _ _ _ _

private theorem secondEvaluation_eq (A : Type (u + 1)) [CommRing A]
    {S X Y D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y)
    [IsClosedImmersion d] (L : DerivedCategoryModule A Y) :
    supportedSecondEvaluation A f g d L =
      (supportSecondCoefficientProjectionIso A f g d).hom.app
        ((supportedSectionsDerived A d).obj L) ≫
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.map
        ((supportedCoefficientDerivedAdjunction A d).counit.app L) := by
  exact coefficientEvaluation_eq _ _ _ _ _ _ _ _ _

private theorem firstEvaluation_openFirst (A : Type (u + 1)) [CommRing A]
    {S X Y B : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X)
    [IsClosedImmersion b] (U : X.Opens) (K : DerivedCategoryModule A X) :
    supportFirstOpenCoefficientMap A f g b U ((supportedSectionsDerived A b).obj K) ≫
      (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)).mapDerivedCategory.map
        (supportedFirstEvaluation A f g b K) ≫
      (supportPullbackSquareIso (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)
        (pullback.fst f g) (pullback.fst (U.ι ≫ f) g) U.ι
        (supportedFirstOpenMap_fst f g U) K).hom =
    (supportedFirstCoefficients A (U.ι ≫ f) g (supportOnOpen b U)).mapDerivedCategory.map
        ((derivedSupportTransport A U.ι b (supportOnOpen b U)
          (supportOnOpen_complement b U)).app K) ≫
      supportedFirstEvaluation A (U.ι ≫ f) g (supportOnOpen b U)
        ((upperStar (ModuleCat.{u + 1} A) U.ι).mapDerivedCategory.obj K) := by
  rw [firstEvaluation_eq, firstEvaluation_eq]
  exact evaluation_transport
    (supportedCoefficientDerivedAdjunction A b)
    (supportedCoefficientDerivedAdjunction A (supportOnOpen b U))
    (upperStar (ModuleCat.{u + 1} A) U.ι).mapDerivedCategory _ _ _ _ _ _ _ _ _ _ _
    (pullbackSquare_natural A _ _ _ _ _ _)

private theorem secondEvaluation_openFirst (A : Type (u + 1)) [CommRing A]
    {S X Y D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y)
    [IsClosedImmersion d] (U : X.Opens) (L : DerivedCategoryModule A Y) :
    supportFirstOpenSecondCoefficientMap A f g d U ((supportedSectionsDerived A d).obj L) ≫
      (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)).mapDerivedCategory.map
        (supportedSecondEvaluation A f g d L) ≫
      (supportPullbackProjectionIso (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)
        (pullback.snd f g) (pullback.snd (U.ι ≫ f) g)
        (supportedFirstOpenMap_snd f g U) L).hom =
    supportedSecondEvaluation A (U.ι ≫ f) g d L := by
  rw [secondEvaluation_eq, secondEvaluation_eq]
  exact evaluation_pullback _ _ _ _ _ _ _ _ _ _ _ _ _
    (pullbackProjection_natural A _ _ _ _ _)

private theorem firstExternalOpenIso_hom_eq (A : Type (u + 1)) [CommRing A]
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (U : X.Opens)
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    (supportedFirstExternalOpenIso (ModuleCat.{u + 1} A) f g U K L).hom =
    (supportExactPullbackTensorIso (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)
      ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.obj K)
      ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.obj L)).hom ≫
    supportedDerivedTensorMap A (pullback (U.ι ≫ f) g)
      (supportPullbackSquareIso (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)
        (pullback.fst f g) (pullback.fst (U.ι ≫ f) g) U.ι
        (supportedFirstOpenMap_fst f g U) K).hom
      (supportPullbackProjectionIso (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)
        (pullback.snd f g) (pullback.snd (U.ι ≫ f) g)
        (supportedFirstOpenMap_snd f g U) L).hom := by
  change (upperStar (ModuleCat.{u + 1} A)
      (supportedFirstOpenMap f g U)).mapDerivedCategory.map (𝟙 _) ≫ _ ≫ 𝟙 _ = _
  dsimp only [externalProduct]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

/-- Naturality under open restriction of the first ambient scheme, for every
support, hence for all three components of each localization diagram.
Source: Tags 09XP and 0F1E (blueprint: lem-pur-supported-product-localization).
Proof: the ordinary kernel restriction commutes with pulling back and tensoring sections.
The uniquely normalized coefficient maps preserve this equality on each tensor bidegree.
Use K-flat models, injective support resolutions and their canonical comparisons to derive
that equality. The product-open comparison is exactly the one used in the third component. -/
theorem supportedProductLocalization_openFirst (A : Type (u + 1)) [CommRing A]
    {S X Y B D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d] (U : X.Opens)
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    supportedExteriorProduct A f g b d K L ≫
        supportedFirstExternalRestriction A f g b d U K L =
      ((derivedSupportOpenRestriction A b U).app K ⊗ₘ 𝟙 _) ≫
        supportedExteriorProduct A (U.ι ≫ f) g (supportOnOpen b U) d ((upperStar (ModuleCat.{u +
          1} A) U.ι).mapDerivedCategory.obj K) L := by
  unfold supportedExteriorProduct supportedFirstExternalRestriction
    supportedRestrictionWithComparison
  rw [openRestriction_eq_transport, firstExternalOpenIso_hom_eq]
  dsimp only [externalProduct]
  refine adjunct_pairing_transport
    (supportedCoefficientDerivedAdjunction A (supportedProductImmersion f g b d))
    (supportedCoefficientDerivedAdjunction A
      (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U) d))
    (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)).mapDerivedCategory
    (derivedSupportTransport A (supportedFirstOpenMap f g U)
      (supportedProductImmersion f g b d)
      (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U) d)
      (supportedFirstOpenSupport_complement f g b d U))
    (derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
    (derivedTensor (ModuleCat.{u + 1} A) (pullback (U.ι ≫ f) g))
    ((derivedSupportTransport A U.ι b (supportOnOpen b U)
      (supportOnOpen_complement b U)).app K) (𝟙 _)
    _ (supportedCoefficientTensorDerived A (U.ι ≫ f) g (supportOnOpen b U) d _ _) _
    (supportFirstOpenCoefficientMap A f g b U _)
    (supportFirstOpenSecondCoefficientMap A f g d U _)
    _ _ _ _
    ((supportedFirstCoefficients A (U.ι ≫ f) g
      (supportOnOpen b U)).mapDerivedCategory.map
        ((derivedSupportTransport A U.ι b (supportOnOpen b U)
          (supportOnOpen_complement b U)).app K))
    ((supportedSecondCoefficients A (U.ι ≫ f) g d).mapDerivedCategory.map (𝟙 _))
    _ _
    (supportExactPullbackTensorIso (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)
      ((supportedFirstCoefficients A f g b).mapDerivedCategory.obj
        ((supportedSectionsDerived A b).obj K))
      ((supportedSecondCoefficients A f g d).mapDerivedCategory.obj
        ((supportedSectionsDerived A d).obj L))).hom
    _ ?_ ?_ ?_ ?_ ?_
  · exact supportedCoefficientTensor_openFirst A f g b d U _ _
  · exact exactPullbackTensor_natural A _ _ _
  · exact firstEvaluation_openFirst A f g b U K
  · rw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact secondEvaluation_openFirst A f g d U L
  · exact schemeComparison_natural (ModuleCat.{u + 1} A) (pullback (U.ι ≫ f) g)
      (supportedCoefficients A
        (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U) d))
      (supportedFirstCoefficients A (U.ι ≫ f) g (supportOnOpen b U))
      (supportedSecondCoefficients A (U.ι ≫ f) g d)
      (supportedCoefficientTensorNatTrans A (U.ι ≫ f) g (supportOnOpen b U) d)
      (exists_unique_supportedCoefficientTensorDerived A
        (U.ι ≫ f) g (supportOnOpen b U) d).choose
      (exists_unique_supportedCoefficientTensorDerived A
        (U.ι ≫ f) g (supportOnOpen b U) d).choose_spec.1 _ _


private theorem firstEvaluation_openSecond (A : Type (u + 1)) [CommRing A]
    {S X Y B : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X)
    [IsClosedImmersion b] (V : Y.Opens) (K : DerivedCategoryModule A X) :
    supportSecondOpenFirstCoefficientMap A f g b V ((supportedSectionsDerived A b).obj K) ≫
      (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)).mapDerivedCategory.map
        (supportedFirstEvaluation A f g b K) ≫
      (supportPullbackProjectionIso (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)
        (pullback.fst f g) (pullback.fst f (V.ι ≫ g))
        (supportedSecondOpenMap_fst f g V) K).hom =
    supportedFirstEvaluation A f (V.ι ≫ g) b K := by
  rw [firstEvaluation_eq, firstEvaluation_eq]
  exact evaluation_pullback _ _ _ _ _ _ _ _ _ _ _ _ _
    (pullbackProjection_natural A _ _ _ _ _)

private theorem secondEvaluation_openSecond (A : Type (u + 1)) [CommRing A]
    {S X Y D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y)
    [IsClosedImmersion d] (V : Y.Opens) (L : DerivedCategoryModule A Y) :
    supportSecondOpenCoefficientMap A f g d V ((supportedSectionsDerived A d).obj L) ≫
      (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)).mapDerivedCategory.map
        (supportedSecondEvaluation A f g d L) ≫
      (supportPullbackSquareIso (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)
        (pullback.snd f g) (pullback.snd f (V.ι ≫ g)) V.ι
        (supportedSecondOpenMap_snd f g V) L).hom =
    (supportedSecondCoefficients A f (V.ι ≫ g) (supportOnOpen d V)).mapDerivedCategory.map
        ((derivedSupportTransport A V.ι d (supportOnOpen d V)
          (supportOnOpen_complement d V)).app L) ≫
      supportedSecondEvaluation A f (V.ι ≫ g) (supportOnOpen d V)
        ((upperStar (ModuleCat.{u + 1} A) V.ι).mapDerivedCategory.obj L) := by
  rw [secondEvaluation_eq, secondEvaluation_eq]
  exact evaluation_transport
    (supportedCoefficientDerivedAdjunction A d)
    (supportedCoefficientDerivedAdjunction A (supportOnOpen d V))
    (upperStar (ModuleCat.{u + 1} A) V.ι).mapDerivedCategory _ _ _ _ _ _ _ _ _ _ _
    (pullbackSquare_natural A _ _ _ _ _ _)

private theorem secondExternalOpenIso_hom_eq (A : Type (u + 1)) [CommRing A]
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (V : Y.Opens)
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    (supportedSecondExternalOpenIso (ModuleCat.{u + 1} A) f g V K L).hom =
    (supportExactPullbackTensorIso (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)
      ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.obj K)
      ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.obj L)).hom ≫
    supportedDerivedTensorMap A (pullback f (V.ι ≫ g))
      (supportPullbackProjectionIso (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)
        (pullback.fst f g) (pullback.fst f (V.ι ≫ g))
        (supportedSecondOpenMap_fst f g V) K).hom
      (supportPullbackSquareIso (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)
        (pullback.snd f g) (pullback.snd f (V.ι ≫ g)) V.ι
        (supportedSecondOpenMap_snd f g V) L).hom := by
  change (upperStar (ModuleCat.{u + 1} A)
      (supportedSecondOpenMap f g V)).mapDerivedCategory.map (𝟙 _) ≫ _ ≫ 𝟙 _ = _
  dsimp only [externalProduct]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

/-- Naturality under open restriction of the second ambient scheme, for every
support, hence for all three components of each localization diagram.
Source: Tags 09XP and 0F1E (blueprint: lem-pur-supported-product-localization).
Proof: the ordinary kernel restriction commutes with pulling back and tensoring sections.
The uniquely normalized coefficient maps preserve this equality on each tensor bidegree.
Use K-flat models, injective support resolutions and their canonical comparisons to derive
that equality. The product-open comparison is exactly the one used in the third component. -/
theorem supportedProductLocalization_openSecond (A : Type (u + 1)) [CommRing A]
    {S X Y B D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d] (V : Y.Opens)
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    supportedExteriorProduct A f g b d K L ≫
        supportedSecondExternalRestriction A f g b d V K L =
      (𝟙 _ ⊗ₘ (derivedSupportOpenRestriction A d V).app L) ≫
        supportedExteriorProduct A f (V.ι ≫ g) b (supportOnOpen d V) K ((upperStar (ModuleCat.{u
          + 1} A) V.ι).mapDerivedCategory.obj L) := by
  unfold supportedExteriorProduct supportedSecondExternalRestriction
    supportedRestrictionWithComparison
  rw [openRestriction_eq_transport, secondExternalOpenIso_hom_eq]
  dsimp only [externalProduct]
  refine adjunct_pairing_transport
    (supportedCoefficientDerivedAdjunction A (supportedProductImmersion f g b d))
    (supportedCoefficientDerivedAdjunction A
      (supportedProductImmersion f (V.ι ≫ g) b (supportOnOpen d V)))
    (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)).mapDerivedCategory
    (derivedSupportTransport A (supportedSecondOpenMap f g V)
      (supportedProductImmersion f g b d)
      (supportedProductImmersion f (V.ι ≫ g) b (supportOnOpen d V))
      (supportedSecondOpenSupport_complement f g b d V))
    (derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
    (derivedTensor (ModuleCat.{u + 1} A) (pullback f (V.ι ≫ g)))
    (𝟙 _) ((derivedSupportTransport A V.ι d (supportOnOpen d V)
      (supportOnOpen_complement d V)).app L)
    _ (supportedCoefficientTensorDerived A f (V.ι ≫ g) b (supportOnOpen d V) _ _) _
    (supportSecondOpenFirstCoefficientMap A f g b V _)
    (supportSecondOpenCoefficientMap A f g d V _)
    _ _ _ _
    ((supportedFirstCoefficients A f (V.ι ≫ g) b).mapDerivedCategory.map (𝟙 _))
    ((supportedSecondCoefficients A f (V.ι ≫ g)
      (supportOnOpen d V)).mapDerivedCategory.map
        ((derivedSupportTransport A V.ι d (supportOnOpen d V)
          (supportOnOpen_complement d V)).app L))
    _ _
    (supportExactPullbackTensorIso (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)
      ((supportedFirstCoefficients A f g b).mapDerivedCategory.obj
        ((supportedSectionsDerived A b).obj K))
      ((supportedSecondCoefficients A f g d).mapDerivedCategory.obj
        ((supportedSectionsDerived A d).obj L))).hom
    _ ?_ ?_ ?_ ?_ ?_
  · exact supportedCoefficientTensor_openSecond A f g b d V _ _
  · exact exactPullbackTensor_natural A _ _ _
  · rw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact firstEvaluation_openSecond A f g b V K
  · exact secondEvaluation_openSecond A f g d V L
  · exact schemeComparison_natural (ModuleCat.{u + 1} A) (pullback f (V.ι ≫ g))
      (supportedCoefficients A
        (supportedProductImmersion f (V.ι ≫ g) b (supportOnOpen d V)))
      (supportedFirstCoefficients A f (V.ι ≫ g) b)
      (supportedSecondCoefficients A f (V.ι ≫ g) (supportOnOpen d V))
      (supportedCoefficientTensorNatTrans A f (V.ι ≫ g) b (supportOnOpen d V))
      (exists_unique_supportedCoefficientTensorDerived A
        f (V.ι ≫ g) b (supportOnOpen d V)).choose
      (exists_unique_supportedCoefficientTensorDerived A
        f (V.ι ≫ g) b (supportOnOpen d V)).choose_spec.1 _ _


private instance support_kernel_mono (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (W : T.Opens)
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    Mono ((supportedEtaleSectionsι A T W).app M) := by
  dsimp [supportedEtaleSectionsι]
  infer_instance


private theorem transport_spec (A : Type (u + 1)) [CommRing A]
    {T S B D : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (d : D ⟶ S) [IsClosedImmersion b] [IsClosedImmersion d]
    (hd : d.openComplement = h ⁻¹ᵁ b.openComplement)
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (supportTransport A h b d hd).app M ≫
        (supportedEtaleSectionsι A S d.openComplement).app
          ((upperStar (ModuleCat.{u + 1} A) h).obj M) =
      (supportedEtaleSectionsι A T b.openComplement).app M ≫
        globalSectionsUpperStarMap (ModuleCat.{u + 1} A) h M :=
  (exists_unique_supportTransport A h b d hd).choose_spec.1 M

private theorem inclusion_spec (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c]
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (supportInclusion A b c).app M ≫ (supportedEtaleSectionsι A T b.openComplement).app M =
      (supportedEtaleSectionsι A T (supportIntersection b c).openComplement).app M :=
  congr_app (exists_unique_supportInclusion A b c).choose_spec.1 M

private theorem restriction_spec (A : Type (u + 1)) [CommRing A]
    {T B : Scheme.{u}} (b : B ⟶ T) [IsClosedImmersion b] (U : T.Opens)
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (supportOpenRestriction A b U).app M ≫
        (supportedEtaleSectionsι A U (supportOnOpen b U).openComplement).app
          ((upperStar (ModuleCat.{u + 1} A) U.ι).obj M) =
      (supportedEtaleSectionsι A T b.openComplement).app M ≫
        globalSectionsUpperStarMap (ModuleCat.{u + 1} A) U.ι M :=
  (exists_unique_supportOpenRestriction A b U).choose_spec.1 M

private theorem support_inclusion_transport (A : Type (u + 1)) [CommRing A]
    {T S B C B' C' : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (c : C ⟶ T) (b' : B' ⟶ S) (c' : C' ⟶ S)
    [IsClosedImmersion b] [IsClosedImmersion c]
    [IsClosedImmersion b'] [IsClosedImmersion c']
    (hb : b'.openComplement = h ⁻¹ᵁ b.openComplement)
    (hc : c'.openComplement = h ⁻¹ᵁ c.openComplement) :
    supportInclusion A b c ≫ supportTransport A h b b' hb =
      supportTransport A h (supportIntersection b c) (supportIntersection b' c')
          (supportRestrictedIntersection_complement h b c b' c' hb hc) ≫
        Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) h)
          (supportInclusion A b' c') := by
  apply NatTrans.ext
  funext M
  apply (cancel_mono ((supportedEtaleSectionsι A S b'.openComplement).app
    ((upperStar (ModuleCat.{u + 1} A) h).obj M))).1
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  simp only [Category.assoc, transport_spec, inclusion_spec]
  rw [← Category.assoc, inclusion_spec]

private noncomputable def support_cut_square (A : Type (u + 1)) [CommRing A]
    {T S C C' : Scheme.{u}}
    (h : S ⟶ T) [IsOpenImmersion h] (c : C ⟶ T) (c' : C' ⟶ S)
    [IsClosedImmersion c] [IsClosedImmersion c']
    (hc : c'.openComplement = h ⁻¹ᵁ c.openComplement) :=
  squareUpperStarIso (ModuleCat.{u + 1} A)
    (show CommSq c'.openComplement.ι (supportCutOpenMap h c c' hc) h
      c.openComplement.ι from ⟨(supportCutOpenMap_over h c c' hc).symm⟩)

private noncomputable def support_third_ordinary (A : Type (u + 1)) [CommRing A]
    {T S B C B' C' : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (c : C ⟶ T) (b' : B' ⟶ S) (c' : C' ⟶ S)
    [IsClosedImmersion b] [IsClosedImmersion c]
    [IsClosedImmersion b'] [IsClosedImmersion c']
    (hb : b'.openComplement = h ⁻¹ᵁ b.openComplement)
    (hc : c'.openComplement = h ⁻¹ᵁ c.openComplement) :
    supportOpenComposite A b c.openComplement ⟶
      upperStar (ModuleCat.{u + 1} A) h ⋙ supportOpenComposite A b' c'.openComplement :=
  Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) c.openComplement.ι)
      (supportTransport A (supportCutOpenMap h c c' hc)
        (supportOnOpen b c.openComplement) (supportOnOpen b' c'.openComplement)
        (supportRestrictedCut_complement h b c b' c' hb hc)) ≫
    Functor.whiskerRight (support_cut_square A h c c' hc).hom
      (supportedEtaleSections A c'.openComplement
        (supportOnOpen b' c'.openComplement).openComplement)

private theorem support_restriction_transport (A : Type (u + 1)) [CommRing A]
    {T S B C B' C' : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (c : C ⟶ T) (b' : B' ⟶ S) (c' : C' ⟶ S)
    [IsClosedImmersion b] [IsClosedImmersion c]
    [IsClosedImmersion b'] [IsClosedImmersion c']
    (hb : b'.openComplement = h ⁻¹ᵁ b.openComplement)
    (hc : c'.openComplement = h ⁻¹ᵁ c.openComplement) :
    supportOpenRestriction A b c.openComplement ≫ support_third_ordinary A h b c b' c' hb hc =
      supportTransport A h b b' hb ≫
        Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) h)
          (supportOpenRestriction A b' c'.openComplement) := by
  set_option backward.isDefEq.respectTransparency false in
    apply NatTrans.ext
    funext M
    let N := (upperStar (ModuleCat.{u + 1} A) h).obj M
    let e := (support_cut_square A h c c' hc).hom.app M
    let ι := supportedEtaleSectionsι A c'.openComplement
      (supportOnOpen b' c'.openComplement).openComplement
    apply (cancel_mono (ι.app ((upperStar (ModuleCat.{u + 1} A)
      c'.openComplement.ι).obj N))).1
    have he := ι.naturality e
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, support_third_ordinary,
      Functor.whiskerRight_app]
    dsimp only [N, ι, e, Functor.comp_obj] at he ⊢
    rw [Category.assoc, Category.assoc, he]
    simp only [← Category.assoc, transport_spec, restriction_spec]
    simp only [Category.assoc, support_cut_square]
    rw [globalSectionsUpperStarMap_comp_squareUpperStarIso, restriction_spec]
    simp only [← Category.assoc, transport_spec]

private theorem composite_unit_eq
    {C C' D : Type*} [Category C] [Category C'] [Category D]
    [Abelian C] [Abelian C'] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C']
    (P : C ⥤ C') [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (G : C' ⥤ D) [G.Additive] :
    Functor.rightDerivedFunctorCompUnit P G ≫
        Functor.whiskerLeft DerivedCategory.Qh (Functor.whiskerRight
          P.rightDerivedFunctorIsoMapDerivedCategory.hom G.rightDerivedFunctor) =
      Functor.mapDerivedCategoryCompRightDerivedFunctorUnit P G := by
  apply NatTrans.ext
  funext X
  have h := congr_app P.rightDerivedFunctorIsoMapDerivedCategory_hom_fac X
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  simp only [Functor.rightDerivedFunctorCompUnit,
    Functor.mapDerivedCategoryCompRightDerivedFunctorUnit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc]
  rw [← Functor.map_comp, h]

private theorem pullback_eq_comparison
    {C C' D : Type*} [Category C] [Category C'] [Category D]
    [Abelian C] [Abelian C'] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C']
    (P : C ⥤ C') [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (F : C ⥤ D) (G : C' ⥤ D) [F.Additive] [G.Additive]
    (α : F ⟶ P ⋙ G)
    (e : (P ⋙ G).rightDerivedFunctor ≅ P.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (he : (P ⋙ G).rightDerivedFunctorUnit ≫ Functor.whiskerLeft DerivedCategory.Qh e.hom =
      Functor.mapDerivedCategoryCompRightDerivedFunctorUnit P G) :
    Functor.rightDerivedPullback P α = Functor.rightDerivedFunctorNatTrans α ≫ e.hom := by
  apply Functor.rightDerived_ext F.rightDerivedFunctor F.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ))
  simp only [Functor.whiskerLeft_comp, ← Category.assoc]
  rw [show F.rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh (Functor.rightDerivedPullback P α) =
      Functor.rightDerivedPullbackAux P α by simp [Functor.rightDerivedPullback]]
  rw [show F.rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh (Functor.rightDerivedFunctorNatTrans α) =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory α (.up ℤ)) DerivedCategory.Qh ≫
        (P ⋙ G).rightDerivedFunctorUnit by
      exact Functor.rightDerivedNatTrans_fac _ _ _ _ _ _]
  rw [Category.assoc, he]
  apply NatTrans.ext
  funext X
  simp [Functor.rightDerivedPullbackAux,
    Functor.mapDerivedCategoryCompRightDerivedFunctorUnit]

private theorem pullback_id_eq_comparison
    {C C' D : Type*} [Category C] [Category C'] [Category D]
    [Abelian C] [Abelian C'] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C']
    (P : C ⥤ C') [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (G : C' ⥤ D) [G.Additive]
    (e : (P ⋙ G).rightDerivedFunctor ≅ P.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (he : (P ⋙ G).rightDerivedFunctorUnit ≫ Functor.whiskerLeft DerivedCategory.Qh e.hom =
      Functor.mapDerivedCategoryCompRightDerivedFunctorUnit P G) :
    Functor.rightDerivedPullback P (𝟙 (P ⋙ G)) = e.hom := by
  rw [pullback_eq_comparison P (P ⋙ G) G (𝟙 _) e he]
  simp [Functor.rightDerivedFunctorNatTrans]

private theorem mapDerived_refl
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (P : C ⥤ D) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P] :
    (Functor.mapDerivedCategoryNatIso (Iso.refl P)).hom = 𝟙 P.mapDerivedCategory := by
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  apply (cancel_mono (P.mapDerivedCategoryFactors.hom.app K)).1
  rw [Functor.mapDerivedCategoryNatIso_fac]
  simp

private theorem mapDerived_nat_comp
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ≅ G) (e' : G ≅ H) :
    (Functor.mapDerivedCategoryNatIso (e ≪≫ e')).hom =
      (Functor.mapDerivedCategoryNatIso e).hom ≫ (Functor.mapDerivedCategoryNatIso e').hom := by
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  apply (cancel_mono (H.mapDerivedCategoryFactors.hom.app K)).1
  simp only [NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_fac, Functor.mapDerivedCategoryNatIso_fac,
    ← Category.assoc, Functor.mapDerivedCategoryNatIso_fac, Category.assoc,
    ← DerivedCategory.Q.map_comp]
  congr 2

private theorem mapDerived_nat_inv
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    (Functor.mapDerivedCategoryNatIso e.symm).hom =
      (Functor.mapDerivedCategoryNatIso e).inv := by
  apply (cancel_epi (Functor.mapDerivedCategoryNatIso e).hom).1
  rw [← mapDerived_nat_comp, Iso.self_symm_id, mapDerived_refl, Iso.hom_inv_id]

private instance private_comp_preservesFiniteLimits
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteLimits F] [PreservesFiniteLimits G] :
    PreservesFiniteLimits (F ⋙ G) := comp_preservesFiniteLimits F G

private instance private_comp_preservesFiniteColimits
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteColimits F] [PreservesFiniteColimits G] :
    PreservesFiniteColimits (F ⋙ G) := comp_preservesFiniteColimits F G

private theorem pullback_square
    {C₀ C₁ C₂ C₃ D : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃] [Category D]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian D]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory C₃] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₀]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₁]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₂]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₃]
    (P : C₀ ⥤ C₁) (Q : C₁ ⥤ C₂) (R : C₀ ⥤ C₃) (S : C₃ ⥤ C₂)
    [P.Additive] [Q.Additive] [R.Additive] [S.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [P.PreservesKInjectiveComplexes] [S.PreservesKInjectiveComplexes]
    (G : C₁ ⥤ D) (G' : C₂ ⥤ D) [G.Additive] [G'.Additive]
    (α : G ⟶ Q ⋙ G') (ε : P ⋙ Q ≅ R ⋙ S) (M : DerivedCategory C₀) :
    (Functor.mapDerivedCategoryCompRightDerivedFunctorIso P G).inv.app M ≫
        (Functor.rightDerivedPullback R
          (Functor.whiskerLeft P α ≫ (Functor.associator P Q G').inv ≫
            Functor.whiskerRight ε.hom G' ≫ (Functor.associator R S G').hom)).app M ≫
        (Functor.mapDerivedCategoryCompRightDerivedFunctorIso S G').hom.app
          (R.mapDerivedCategory.obj M) =
      (Functor.rightDerivedPullback Q α).app (P.mapDerivedCategory.obj M) ≫
        G'.rightDerivedFunctor.map
          ((Functor.mapDerivedCategoryCompIso P Q).inv.app M ≫
            (Functor.mapDerivedCategoryNatIso ε).hom.app M ≫
            (Functor.mapDerivedCategoryCompIso R S).hom.app M) := by
  have hP := pullback_id_eq_comparison P G
    (Functor.mapDerivedCategoryCompRightDerivedFunctorIso P G)
    (by ext X; exact Functor.mapDerivedCategoryCompRightDerivedFunctorIso_hom_fac_app P G X)
  have hS := pullback_id_eq_comparison S G'
    (Functor.mapDerivedCategoryCompRightDerivedFunctorIso S G')
    (by ext X; exact Functor.mapDerivedCategoryCompRightDerivedFunctorIso_hom_fac_app S G' X)
  have h₁ := Functor.rightDerivedPullback_comp P Q (P ⋙ Q) (Iso.refl _)
    (𝟙 (P ⋙ G)) α
    (Functor.whiskerLeft P α ≫ (Functor.associator P Q G').inv) (by ext; simp) M
  have h₂ := Functor.rightDerivedPullback_comp R S (P ⋙ Q) ε
    (Functor.whiskerLeft P α ≫ (Functor.associator P Q G').inv ≫
            Functor.whiskerRight ε.hom G' ≫ (Functor.associator R S G').hom) (𝟙 (S ⋙ G'))
    (Functor.whiskerLeft P α ≫ (Functor.associator P Q G').inv) (by ext; simp) M
  simp only [Iso.trans_hom, NatTrans.comp_app, mapDerived_refl, Category.id_comp,
    hP, hS] at h₁ h₂
  have h₁' := congrArg (fun t ↦ t ≫
    G'.rightDerivedFunctor.map ((Functor.mapDerivedCategoryCompIso P Q).inv.app M)) h₁
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id] at h₁'
  erw [Category.comp_id] at h₁'
  rw [← h₂, h₁']
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]

private theorem support_pullback_eq (A : Type (u + 1)) [CommRing A]
    {T S B D : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (d : D ⟶ S) [IsClosedImmersion b] [IsClosedImmersion d]
    (hd : d.openComplement = h ⁻¹ᵁ b.openComplement) :
    Functor.rightDerivedPullback (upperStar (ModuleCat.{u + 1} A) h)
      (supportTransport A h b d hd) = derivedSupportTransport A h b d hd := by
  apply pullback_eq_comparison
  exact (exists_unique_supportTransportComparison A h d).choose_spec.1 |>.trans
    (composite_unit_eq _ _)

private theorem cut_derived_square (A : Type (u + 1)) [CommRing A]
    {T S C C' : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (c : C ⟶ T) (c' : C' ⟶ S) [IsClosedImmersion c] [IsClosedImmersion c']
    (hc : c'.openComplement = h ⁻¹ᵁ c.openComplement) (K : DerivedCategoryModule A T) :
    (Functor.mapDerivedCategoryCompIso
        (upperStar (ModuleCat.{u + 1} A) c.openComplement.ι)
        (upperStar (ModuleCat.{u + 1} A) (supportCutOpenMap h c c' hc))).inv.app K ≫
      (Functor.mapDerivedCategoryNatIso (support_cut_square A h c c' hc)).hom.app K ≫
      (Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} A) h)
        (upperStar (ModuleCat.{u + 1} A) c'.openComplement.ι)).hom.app K =
    ((supportExactPullbackCompIso (ModuleCat.{u + 1} A) (supportCutOpenMap h c c' hc)
        c.openComplement.ι (c'.openComplement.ι ≫ h)
        (supportCutOpenMap_over h c c' hc).symm).symm ≪≫
      supportExactPullbackCompIso (ModuleCat.{u + 1} A) c'.openComplement.ι h
        (c'.openComplement.ι ≫ h) rfl).hom.app K := by
  simp only [support_cut_square, squareUpperStarIso, supportExactPullbackCompIso,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app]
  rw [mapDerived_nat_comp, mapDerived_nat_inv]
  simp only [NatTrans.comp_app, Category.assoc]

private theorem support_open_comparison_pullback (A : Type (u + 1)) [CommRing A]
    {T B : Scheme.{u}} (b : B ⟶ T) [IsClosedImmersion b] (U : T.Opens) :
    Functor.rightDerivedPullback (upperStar (ModuleCat.{u + 1} A) U.ι)
        (𝟙 (supportOpenComposite A b U)) = (supportOpenDerivedComparison A b U).hom := by
  apply pullback_id_eq_comparison
  exact (exists_unique_supportOpenDerivedComparison A b U).choose_spec.1 |>.trans
    (composite_unit_eq _ _)

private theorem third_pullback (A : Type (u + 1)) [CommRing A]
    {T S B C B' C' : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (c : C ⟶ T) (b' : B' ⟶ S) (c' : C' ⟶ S)
    [IsClosedImmersion b] [IsClosedImmersion c]
    [IsClosedImmersion b'] [IsClosedImmersion c']
    (hb : b'.openComplement = h ⁻¹ᵁ b.openComplement)
    (hc : c'.openComplement = h ⁻¹ᵁ c.openComplement) (K : DerivedCategoryModule A T) :
    (supportOpenDerivedComparison A b c.openComplement).inv.app K ≫
        (Functor.rightDerivedPullback (upperStar (ModuleCat.{u + 1} A) h)
          (support_third_ordinary A h b c b' c' hb hc)).app K ≫
        (supportOpenDerivedComparison A b' c'.openComplement).hom.app
          ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj K) =
      supportTriangleRestrictionThird A h b c b' c' hb hc K := by
  let P := upperStar (ModuleCat.{u + 1} A) c.openComplement.ι
  let Q := upperStar (ModuleCat.{u + 1} A) (supportCutOpenMap h c c' hc)
  let R := upperStar (ModuleCat.{u + 1} A) h
  let S' := upperStar (ModuleCat.{u + 1} A) c'.openComplement.ι
  let G := supportedEtaleSections A c.openComplement
    (supportOnOpen b c.openComplement).openComplement
  let G' := supportedEtaleSections A c'.openComplement
    (supportOnOpen b' c'.openComplement).openComplement
  let : P.PreservesKInjectiveComplexes :=
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c.openComplement.ι
      inferInstance).preservesKInjectiveComplexes
  let : S'.PreservesKInjectiveComplexes :=
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c'.openComplement.ι
      inferInstance).preservesKInjectiveComplexes
  have hP : Functor.mapDerivedCategoryCompRightDerivedFunctorIso P G =
      supportOpenDerivedComparison A b c.openComplement := by
    apply Iso.ext
    rw [← support_open_comparison_pullback]
    exact (pullback_id_eq_comparison P G _
      (by ext X; exact Functor.mapDerivedCategoryCompRightDerivedFunctorIso_hom_fac_app P G X)).symm
  have hS : Functor.mapDerivedCategoryCompRightDerivedFunctorIso S' G' =
      supportOpenDerivedComparison A b' c'.openComplement := by
    apply Iso.ext
    rw [← support_open_comparison_pullback]
    exact (pullback_id_eq_comparison S' G' _
      (by
        ext X
        exact Functor.mapDerivedCategoryCompRightDerivedFunctorIso_hom_fac_app S' G' X)).symm
  have hs := pullback_square P Q R S' G G'
    (supportTransport A (supportCutOpenMap h c c' hc)
      (supportOnOpen b c.openComplement) (supportOnOpen b' c'.openComplement)
      (supportRestrictedCut_complement h b c b' c' hb hc))
    (support_cut_square A h c c' hc) K
  rw [hP, hS] at hs
  change _ ≫ (Functor.rightDerivedPullback R
    (support_third_ordinary A h b c b' c' hb hc)).app K ≫ _ = _ at hs
  rw [cut_derived_square, support_pullback_eq] at hs
  exact hs

/- The upstream pullback boundary API is bounded below. The normalized support
triangles in this file are unbounded, so use termwise injective K-injective models
to prove the corresponding comparison directly. -/
private theorem boundary_formula
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (S : ShortComplex (C ⥤ D)) [S.X₁.Additive] [S.X₂.Additive] [S.X₃.Additive]
    (hS : S.ShortExactOnInjectives)
    (δ : S.X₃.rightDerivedFunctor ⟶
      S.X₁.rightDerivedFunctor ⋙ shiftFunctor (DerivedCategory D) (1 : ℤ))
    (hδ : ∀ (I : CochainComplex C ℤ) [I.IsKInjective] [∀ n : ℤ, Injective (I.X n)],
      δ.app (DerivedCategory.Q.obj I) ≫
          (S.X₁.rightDerivedFunctorObjQIso I).hom⟦(1 : ℤ)⟧' =
        (S.X₃.rightDerivedFunctorObjQIso I).hom ≫
          DerivedCategory.triangleOfSESδ (hS.shortExact_mapCochainComplex I))
    (M : DerivedCategory C) (R : M.InjectiveModel) :
    δ.app M = ShortComplex.rightDerivedδAux hS M R := by
  have hI : δ.app (DerivedCategory.Q.obj R.I) =
      ShortComplex.rightDerivedδQObj hS R.I := by
    apply (cancel_mono ((S.X₁.rightDerivedFunctorObjQIso R.I).hom⟦(1 : ℤ)⟧')).1
    rw [hδ]
    simp [ShortComplex.rightDerivedδQObj, Category.assoc, ← Functor.map_comp]
  have h := δ.naturality R.iso.hom
  dsimp at h
  rw [hI] at h
  apply (cancel_epi (S.X₃.rightDerivedFunctor.map R.iso.hom)).1
  rw [h]
  simp [ShortComplex.rightDerivedδAux, ← Functor.map_comp_assoc]

private theorem boundary_pullback.{uc, uc', ud, vc, vc', vd}
    {C : Type uc} {C' : Type uc'} {D : Type ud}
    [Category.{vc} C] [Category.{vc'} C'] [Category.{vd} D]
    [Abelian C] [Abelian C'] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D]
    [IsGrothendieckAbelian.{vc} C] [IsGrothendieckAbelian.{vc'} C']
    (P : C ⥤ C') [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (S : ShortComplex (C ⥤ D)) (S' : ShortComplex (C' ⥤ D))
    [S.X₁.Additive] [S.X₂.Additive] [S.X₃.Additive]
    [S'.X₁.Additive] [S'.X₂.Additive] [S'.X₃.Additive]
    (hS : S.ShortExactOnInjectives) (hS' : S'.ShortExactOnInjectives)
    (δ : S.X₃.rightDerivedFunctor ⟶
      S.X₁.rightDerivedFunctor ⋙ shiftFunctor (DerivedCategory D) (1 : ℤ))
    (δ' : S'.X₃.rightDerivedFunctor ⟶
      S'.X₁.rightDerivedFunctor ⋙ shiftFunctor (DerivedCategory D) (1 : ℤ))
    (hδ : ∀ (I : CochainComplex C ℤ) [I.IsKInjective] [∀ n : ℤ, Injective (I.X n)],
      δ.app (DerivedCategory.Q.obj I) ≫
          (S.X₁.rightDerivedFunctorObjQIso I).hom⟦(1 : ℤ)⟧' =
        (S.X₃.rightDerivedFunctorObjQIso I).hom ≫
          DerivedCategory.triangleOfSESδ (hS.shortExact_mapCochainComplex I))
    (hδ' : ∀ (I : CochainComplex C' ℤ) [I.IsKInjective] [∀ n : ℤ, Injective (I.X n)],
      δ'.app (DerivedCategory.Q.obj I) ≫
          (S'.X₁.rightDerivedFunctorObjQIso I).hom⟦(1 : ℤ)⟧' =
        (S'.X₃.rightDerivedFunctorObjQIso I).hom ≫
          DerivedCategory.triangleOfSESδ (hS'.shortExact_mapCochainComplex I))
    (α₁ : S.X₁ ⟶ P ⋙ S'.X₁) (α₂ : S.X₂ ⟶ P ⋙ S'.X₂)
    (α₃ : S.X₃ ⟶ P ⋙ S'.X₃)
    (h₁₂ : S.f ≫ α₂ = α₁ ≫ Functor.whiskerLeft P S'.f)
    (h₂₃ : S.g ≫ α₃ = α₂ ≫ Functor.whiskerLeft P S'.g)
    (M : DerivedCategory C) :
    δ.app M ≫ ((Functor.rightDerivedPullback P α₁).app M)⟦(1 : ℤ)⟧' =
      (Functor.rightDerivedPullback P α₃).app M ≫ δ'.app (P.mapDerivedCategory.obj M) := by
  let R := Classical.choice (DerivedCategory.nonempty_injectiveModel C M)
  let R' := Classical.choice (DerivedCategory.nonempty_injectiveModel C'
    (P.mapDerivedCategory.obj M))
  obtain ⟨φ, hφ⟩ := CochainComplex.IsKInjective.exists_Q_map_eq
    ((P.mapHomologicalComplex _).obj R.I) R'.I
    (P.mapDerivedCategoryFactors.inv.app R.I ≫ P.mapDerivedCategory.map R.iso.hom ≫ R'.iso.inv)
  have hφ' : P.mapDerivedCategory.map R.iso.hom ≫ R'.iso.inv =
      P.mapDerivedCategoryFactors.hom.app R.I ≫ DerivedCategory.Q.map φ := by
    rw [hφ, Iso.hom_inv_id_app_assoc]
  have k₁ := Functor.rightDerivedPullback_app_Q_obj P α₁ R.I R'.I φ
  have k₃ := Functor.rightDerivedPullback_app_Q_obj P α₃ R.I R'.I φ
  rw [← hφ'] at k₁ k₃
  have n₁ := (Functor.rightDerivedPullback P α₁).naturality R.iso.hom
  have n₃ := (Functor.rightDerivedPullback P α₃).naturality R.iso.inv
  dsimp at n₁ n₃
  have m₁ : S.X₁.rightDerivedFunctor.map R.iso.hom ≫
      (Functor.rightDerivedPullback P α₁).app M =
      (S.X₁.rightDerivedFunctorObjQIso R.I).hom ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α₁ _).app R.I ≫
          (S'.X₁.mapHomologicalComplex _).map φ) ≫
        (S'.X₁.rightDerivedFunctorObjQIso R'.I).inv ≫
          S'.X₁.rightDerivedFunctor.map R'.iso.hom := by
    rw [n₁, ← reassoc_of% k₁, ← Functor.map_comp, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have m₃ : (Functor.rightDerivedPullback P α₃).app M ≫
      S'.X₃.rightDerivedFunctor.map R'.iso.inv =
      S.X₃.rightDerivedFunctor.map R.iso.inv ≫ (S.X₃.rightDerivedFunctorObjQIso R.I).hom ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α₃ _).app R.I ≫
          (S'.X₃.mapHomologicalComplex _).map φ) ≫
        (S'.X₃.rightDerivedFunctorObjQIso R'.I).inv := by
    rw [← k₃, reassoc_of% n₃, ← Functor.map_comp, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hb := DerivedCategory.triangleOfSESδ_naturality (hS.shortExact_mapCochainComplex R.I)
    (hS'.shortExact_mapCochainComplex R'.I)
    (ShortComplex.mapCochainComplexPullback P α₁ α₂ α₃ h₁₂ h₂₃ R.I R'.I φ)
  simp only [ShortComplex.mapCochainComplexPullback_τ₁,
    ShortComplex.mapCochainComplexPullback_τ₃] at hb
  rw [boundary_formula S hS δ hδ M R, boundary_formula S' hS' δ' hδ' _ R']
  simp only [ShortComplex.rightDerivedδAux, ShortComplex.rightDerivedδQObj, Category.assoc]
  rw [reassoc_of% m₃]
  simp only [← Functor.map_comp, m₁, Iso.inv_hom_id_assoc]
  rw [(shiftFunctor _ (1 : ℤ)).map_comp (DerivedCategory.Q.map _), reassoc_of% hb]

private theorem support_sequence_exact (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c] :
    (supportLocalizationSequence A b c).ShortExactOnInjectives := by
  intro J _
  let I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ := {
    X _ := J
    d _ _ := 0 }
  let : ∀ n : ℤ, Injective (I.X n) := fun _ ↦ inferInstance
  exact (supportLocalizationComplex_shortExact A b c I).map_of_exact
    (HomologicalComplex.eval _ (.up ℤ) 0)

private noncomputable def raw_support_triangle (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c] (K : DerivedCategoryModule A T) :=
  Triangle.mk ((Functor.rightDerivedFunctorNatTrans (supportInclusion A b c)).app K)
    ((Functor.rightDerivedFunctorNatTrans (supportOpenRestriction A b c.openComplement)).app K)
    ((supportLocalizationBoundary A b c).app K)

private noncomputable def support_triangle_rawIso (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c] (K : DerivedCategoryModule A T) :
    normalizedSupportTriangle A b c K ≅ raw_support_triangle A b c K := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ((supportOpenDerivedComparison A b c.openComplement).symm.app K) ?_ ?_ ?_
  · change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp only [Category.comp_id, Category.id_comp]
    rfl
  · change (_ ≫ (supportOpenDerivedComparison A b c.openComplement).hom.app K) ≫
      (supportOpenDerivedComparison A b c.openComplement).inv.app K = 𝟙 _ ≫ _
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id, Category.id_comp]
    rfl
  · change (_ ≫ _) ≫ (𝟙 _)⟦(1 : ℤ)⟧' = _
    rw [(shiftFunctor (DerivedCategory (ModuleCat.{u + 1} A)) (1 : ℤ)).map_id]
    exact Category.comp_id _

/-- The support localization rows themselves are natural under open restriction,
including their connecting maps. The three components are the canonical restrictions,
with the third coefficient comparison fixed by the commuting square of cut complements.
Together with supportedProductLocalization_openFirst and _openSecond this gives
naturality of the complete exterior-product diagrams, rather than just their pairings.
Source: Tags 09XP and 0F1E; proof step 9 of the node
(blueprint: lem-pur-supported-product-localization).
Proof: restrict a termwise injective K-injective representative to the open immersion.
Exact extension by zero is left adjoint to restriction, so restriction preserves both
injective objects and K-injectivity. Ordinary support restrictions give a morphism
between the two degreewise short exact support sequences. Naturality of triangleOfSESδ
makes its boundary square commute. The unique boundary normalization and canonical
right-derived composition units identify all three components with the displayed maps.
Apply this on X, on Y, and on the product open to obtain the row restriction morphisms.
The exterior-product restriction identities identify the three squares between rows. -/
theorem supportedProductLocalization_openRows (A : Type (u + 1)) [CommRing A]
    {T S B C B' C' : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (c : C ⟶ T) (b' : B' ⟶ S) (c' : C' ⟶ S)
    [IsClosedImmersion b] [IsClosedImmersion c]
    [IsClosedImmersion b'] [IsClosedImmersion c']
    (hb : b'.openComplement = h ⁻¹ᵁ b.openComplement)
    (hc : c'.openComplement = h ⁻¹ᵁ c.openComplement)
    (K : DerivedCategoryModule A T) :
    ∃ m : normalizedSupportTriangle A b c K ⟶
        normalizedSupportTriangle A b' c'
          ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj K),
      m.hom₁ = (derivedSupportTransport A h (supportIntersection b c)
        (supportIntersection b' c')
        (supportRestrictedIntersection_complement h b c b' c' hb hc)).app K ∧
      m.hom₂ = (derivedSupportTransport A h b b' hb).app K ∧
      m.hom₃ = supportTriangleRestrictionThird A h b c b' c' hb hc K := by
  let P := upperStar (ModuleCat.{u + 1} A) h
  let α₁ := supportTransport A h (supportIntersection b c) (supportIntersection b' c')
    (supportRestrictedIntersection_complement h b c b' c' hb hc)
  let α₂ := supportTransport A h b b' hb
  let α₃ := support_third_ordinary A h b c b' c' hb hc
  have h₁₂ := support_inclusion_transport A h b c b' c' hb hc
  have h₂₃ := support_restriction_transport A h b c b' c' hb hc
  let : (supportLocalizationSequence A b c).X₁.Additive := inferInstanceAs
    (supportedEtaleSections A T (supportIntersection b c).openComplement).Additive
  let : (supportLocalizationSequence A b c).X₂.Additive := inferInstanceAs
    (supportedEtaleSections A T b.openComplement).Additive
  let : (supportLocalizationSequence A b c).X₃.Additive := inferInstanceAs
    (supportOpenComposite A b c.openComplement).Additive
  let : (supportLocalizationSequence A b' c').X₁.Additive := inferInstanceAs
    (supportedEtaleSections A S (supportIntersection b' c').openComplement).Additive
  let : (supportLocalizationSequence A b' c').X₂.Additive := inferInstanceAs
    (supportedEtaleSections A S b'.openComplement).Additive
  let : (supportLocalizationSequence A b' c').X₃.Additive := inferInstanceAs
    (supportOpenComposite A b' c'.openComplement).Additive
  let m : raw_support_triangle A b c K ⟶
      raw_support_triangle A b' c' (P.mapDerivedCategory.obj K) := {
    hom₁ := (Functor.rightDerivedPullback P α₁).app K
    hom₂ := (Functor.rightDerivedPullback P α₂).app K
    hom₃ := (Functor.rightDerivedPullback P α₃).app K
    comm₁ := congr_app (Functor.rightDerivedFunctorNatTrans_comp_rightDerivedPullback P
      (supportInclusion A b c) (supportInclusion A b' c') α₁ α₂ h₁₂) K
    comm₂ := congr_app (Functor.rightDerivedFunctorNatTrans_comp_rightDerivedPullback P
      (supportOpenRestriction A b c.openComplement)
      (supportOpenRestriction A b' c'.openComplement) α₂ α₃ h₂₃) K
    comm₃ := boundary_pullback P (supportLocalizationSequence A b c)
      (supportLocalizationSequence A b' c') (support_sequence_exact A b c)
      (support_sequence_exact A b' c') (supportLocalizationBoundary A b c)
      (supportLocalizationBoundary A b' c')
      (exists_unique_supportLocalizationBoundary A b c).choose_spec.1
      (exists_unique_supportLocalizationBoundary A b' c').choose_spec.1
      α₁ α₂ α₃ h₁₂ h₂₃ K }
  refine ⟨(support_triangle_rawIso A b c K).hom ≫ m ≫
    (support_triangle_rawIso A b' c' (P.mapDerivedCategory.obj K)).inv, ?_, ?_, ?_⟩
  · change 𝟙 _ ≫ (Functor.rightDerivedPullback P α₁).app K ≫ 𝟙 _ = _
    simpa only [Category.id_comp, Category.comp_id] using congr_app
      (support_pullback_eq A h (supportIntersection b c) (supportIntersection b' c')
        (supportRestrictedIntersection_complement h b c b' c' hb hc)) K
  · change 𝟙 _ ≫ (Functor.rightDerivedPullback P α₂).app K ≫ 𝟙 _ = _
    simpa only [Category.id_comp, Category.comp_id] using
      congr_app (support_pullback_eq A h b b' hb) K
  · change (supportOpenDerivedComparison A b c.openComplement).inv.app K ≫
      (Functor.rightDerivedPullback P α₃).app K ≫
      (supportOpenDerivedComparison A b' c'.openComplement).hom.app
        (P.mapDerivedCategory.obj K) = _
    simpa only [Category.assoc] using third_pullback A h b c b' c' hb hc K

private theorem support_transport_comp (A : Type (u + 1)) [CommRing A]
    {T S R B C D : Scheme.{u}} (h : S ⟶ T) (e : R ⟶ S) (a : R ⟶ T)
    [IsOpenImmersion h] [IsOpenImmersion e] [IsOpenImmersion a]
    (ha : a = e ≫ h) (b : B ⟶ T) (c : C ⟶ S) (d : D ⟶ R)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (hc : c.openComplement = h ⁻¹ᵁ b.openComplement)
    (hd : d.openComplement = e ⁻¹ᵁ c.openComplement)
    (hda : d.openComplement = a ⁻¹ᵁ b.openComplement)
    (K : DerivedCategoryModule A T) :
    (derivedSupportTransport A a b d hda).app K ≫
        (supportedSectionsDerived A d).map
          ((supportExactPullbackCompIso (ModuleCat.{u + 1} A) e h a ha).hom.app K) =
      (derivedSupportTransport A h b c hc).app K ≫
        (derivedSupportTransport A e c d hd).app
          ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj K) := by
  have hs : supportTransport A a b d hda ≫
      Functor.whiskerRight (upperStarComp (ModuleCat.{u + 1} A) e h a ha).hom
        (supportedEtaleSections A R d.openComplement) =
      supportTransport A h b c hc ≫
        Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) h)
          (supportTransport A e c d hd) := by
    apply NatTrans.ext
    funext F
    apply (cancel_mono ((supportedEtaleSectionsι A R d.openComplement).app
      ((upperStar (ModuleCat.{u + 1} A) e).obj
        ((upperStar (ModuleCat.{u + 1} A) h).obj F)))).1
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    rw [Category.assoc]
    erw [(supportedEtaleSectionsι A R d.openComplement).naturality]
    simp only [Category.assoc]
    erw [reassoc_of% transport_spec A a b d hda F,
      transport_spec A e c d hd ((upperStar (ModuleCat.{u + 1} A) h).obj F),
      reassoc_of% transport_spec A h b c hc F]
    rw [globalSectionsUpperStarMap_comp']
  have ht := Functor.rightDerivedPullback_comp
    (upperStar (ModuleCat.{u + 1} A) h) (upperStar (ModuleCat.{u + 1} A) e)
    (upperStar (ModuleCat.{u + 1} A) a)
    (upperStarComp (ModuleCat.{u + 1} A) e h a ha)
    (supportTransport A h b c hc) (supportTransport A e c d hd)
    (supportTransport A a b d hda) hs K
  rw [support_pullback_eq, support_pullback_eq, support_pullback_eq] at ht
  exact ht

private theorem supported_restriction_ambient (A : Type (u + 1)) [CommRing A]
    {T S R B C D : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (e : R ≅ S) (a : R ⟶ T) [IsOpenImmersion a] (ha : a = e.hom ≫ h)
    (b : B ⟶ T) (c : C ⟶ S) (d : D ⟶ R)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (hc : c.openComplement = h ⁻¹ᵁ b.openComplement)
    (hd : d.openComplement = e.hom ⁻¹ᵁ c.openComplement)
    (hda : d.openComplement = a ⁻¹ᵁ b.openComplement)
    (K : DerivedCategoryModule A T) (L : DerivedCategoryModule A R)
    (q : (upperStar (ModuleCat.{u + 1} A) a).mapDerivedCategory.obj K ≅ L) :
    (derivedSupportTransport A h b c hc).app K ≫
        (supportedAmbientComparison A e c d hd h a ha K L q).hom =
      supportedRestrictionWithComparison A a b d hda K L q := by
  have ht := support_transport_comp A h e.hom a ha b c d hc hd hda K
  change (derivedSupportTransport A h b c hc).app K ≫
      ((derivedSupportTransport A e.hom c d hd).app
        ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj K) ≫
        (supportedSectionsDerived A d).map
          ((supportExactPullbackCompIso (ModuleCat.{u + 1} A) e.hom h a ha).inv.app K ≫
            q.hom)) =
    (derivedSupportTransport A a b d hda).app K ≫ (supportedSectionsDerived A d).map q.hom
  rw [← Category.assoc, ← ht, Category.assoc,
    ← CategoryTheory.Functor.map_comp]
  congr 2
  exact Iso.hom_inv_id_app_assoc _ _ _

private theorem first_restriction_third (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    (supportedFirstLocalizationTarget A f g b c d K L).mor₂ ≫
        (supportedFirstLocalizationThirdIso A f g b c d K L).hom =
      supportedFirstExternalRestriction A f g b d c.openComplement K L := by
  change (derivedSupportOpenRestriction A (supportedProductImmersion f g b d)
    (supportedProductImmersion f g c (𝟙 Y)).openComplement).app _ ≫ _ = _
  rw [openRestriction_eq_transport]
  exact supported_restriction_ambient A _ (supportedFirstProductComplementIso f g c) _
    (supportedFirstProductComplementIso_over f g c).symm _ _ _
    (supportOnOpen_complement _ _) (supportedFirstProductComplement_support f g b c d)
    (supportedFirstOpenSupport_complement f g b d c.openComplement) _ _ _

private theorem second_restriction_third (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ Y) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    (supportedSecondLocalizationTarget A f g b c d K L).mor₂ ≫
        (supportedSecondLocalizationThirdIso A f g b c d K L).hom =
      supportedSecondExternalRestriction A f g b d c.openComplement K L := by
  change (derivedSupportOpenRestriction A (supportedProductImmersion f g b d)
    (supportedProductImmersion f g (𝟙 X) c).openComplement).app _ ≫ _ = _
  rw [openRestriction_eq_transport]
  exact supported_restriction_ambient A _ (supportedSecondProductComplementIso f g c) _
    (supportedSecondProductComplementIso_over f g c).symm _ _ _
    (supportOnOpen_complement _ _) (supportedSecondProductComplement_support f g b c d)
    (supportedSecondOpenSupport_complement f g b d c.openComplement) _ _ _

private theorem first_square_two (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    (supportedFirstLocalizationSource A f g b c d K L).mor₂ ≫
        supportedFirstLocalizationComponent₃ A f g b c d K L =
      supportedFirstLocalizationComponent₂ A f g b c d K L ≫
        (supportedFirstLocalizationTarget A f g b c d K L).mor₂ := by
  apply (cancel_mono (supportedFirstLocalizationThirdIso A f g b c d K L).hom).1
  dsimp only [supportedFirstLocalizationComponent₂, supportedFirstLocalizationComponent₃]
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, first_restriction_third]
  dsimp only [supportedFirstLocalizationSource, Functor.mapTriangle,
    normalizedSupportTriangle, CategoryTheory.Pretriangulated.Triangle.mk, tensorRight,
    tensorLeft, curriedTensor, Functor.flip]
  simpa only [tensorHom_id] using
    (supportedProductLocalization_openFirst A f g b d c.openComplement K L).symm

private theorem second_square_two (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ Y) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    (supportedSecondLocalizationSource A f g b c d K L).mor₂ ≫
        supportedSecondLocalizationComponent₃ A f g b c d K L =
      supportedSecondLocalizationComponent₂ A f g b c d K L ≫
        (supportedSecondLocalizationTarget A f g b c d K L).mor₂ := by
  apply (cancel_mono (supportedSecondLocalizationThirdIso A f g b c d K L).hom).1
  dsimp only [supportedSecondLocalizationComponent₂, supportedSecondLocalizationComponent₃]
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, second_restriction_third]
  dsimp only [supportedSecondLocalizationSource, Functor.mapTriangle,
    normalizedSupportTriangle, CategoryTheory.Pretriangulated.Triangle.mk, tensorRight,
    tensorLeft, curriedTensor, Functor.flip]
  simpa only [id_tensorHom] using
    (supportedProductLocalization_openSecond A f g b d c.openComplement K L).symm

private theorem support_congruence_spec (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (U V : T.Opens) (h : U = V) :
    (eqToIso (congrArg (supportedEtaleSections A T) h)).hom ≫
        supportedEtaleSectionsι A T V = supportedEtaleSectionsι A T U := by
  subst V
  simp

private theorem support_derived_identity (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (U : T.Opens) :
    Functor.rightDerivedFunctorNatTrans (𝟙 (supportedEtaleSections A T U)) = 𝟙 _ := by
  simp [Functor.rightDerivedFunctorNatTrans]

private theorem support_inclusion_specNat (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c] :
    supportInclusion A b c ≫ supportedEtaleSectionsι A T b.openComplement =
      supportedEtaleSectionsι A T (supportIntersection b c).openComplement :=
  (exists_unique_supportInclusion A b c).choose_spec.1

private theorem support_congruence_hom (A : Type (u + 1)) [CommRing A]
    {T B D : Scheme.{u}} (b : B ⟶ T) (d : D ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion d]
    (h : b.openComplement = d.openComplement) :
    (derivedSupportCongruence A b d h).hom =
      Functor.rightDerivedFunctorNatTrans
        (eqToIso (congrArg (supportedEtaleSections A T) h)).hom := by
  rfl

private theorem first_square_one (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    (supportedFirstLocalizationSource A f g b c d K L).mor₁ ≫
        supportedFirstLocalizationComponent₂ A f g b c d K L =
      supportedFirstLocalizationComponent₁ A f g b c d K L ≫
        (supportedFirstLocalizationTarget A f g b c d K L).mor₁ := by
  let e := eqToIso (congrArg (supportedEtaleSections A (pullback f g))
    (supportedFirstIntersection_complement f g b c d))
  let r := e.hom ≫ supportInclusion A (supportedProductImmersion f g b d)
    (supportedProductImmersion f g c (𝟙 Y))
  have hr : r ≫ supportedEtaleSectionsι A (pullback f g)
        (supportedProductImmersion f g b d).openComplement =
      supportedEtaleSectionsι A (pullback f g)
        (supportedProductImmersion f g (supportIntersection b c) d).openComplement := by
    dsimp only [r]
    rw [Category.assoc]
    rw [support_inclusion_specNat]
    exact support_congruence_spec A _ _ _
      (supportedFirstIntersection_complement f g b c d)
  have h := supportedExteriorProduct_supportMaps A f g (supportIntersection b c) b d d
    (supportInclusion A b c) (𝟙 _) r
    (exists_unique_supportInclusion A b c).choose_spec.1 (Category.id_comp _) hr K L
  rw [support_derived_identity, NatTrans.id_app, tensorHom_id] at h
  dsimp only [r] at h
  rw [Functor.rightDerivedFunctorNatTrans_comp, NatTrans.comp_app] at h
  dsimp only [supportedFirstLocalizationSource, supportedFirstLocalizationTarget,
    supportedFirstLocalizationComponent₁, supportedFirstLocalizationComponent₂,
    Functor.mapTriangle, normalizedSupportTriangle, CategoryTheory.Pretriangulated.Triangle.mk,
    tensorRight, curriedTensor, Functor.flip]
  simpa only [Category.assoc, support_congruence_hom, e] using h.symm

private theorem second_square_one (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ Y) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    (supportedSecondLocalizationSource A f g b c d K L).mor₁ ≫
        supportedSecondLocalizationComponent₂ A f g b c d K L =
      supportedSecondLocalizationComponent₁ A f g b c d K L ≫
        (supportedSecondLocalizationTarget A f g b c d K L).mor₁ := by
  let e := eqToIso (congrArg (supportedEtaleSections A (pullback f g))
    (supportedSecondIntersection_complement f g b c d))
  let r := e.hom ≫ supportInclusion A (supportedProductImmersion f g b d)
    (supportedProductImmersion f g (𝟙 X) c)
  have hr : r ≫ supportedEtaleSectionsι A (pullback f g)
        (supportedProductImmersion f g b d).openComplement =
      supportedEtaleSectionsι A (pullback f g)
        (supportedProductImmersion f g b (supportIntersection d c)).openComplement := by
    dsimp only [r]
    rw [Category.assoc]
    rw [support_inclusion_specNat]
    exact support_congruence_spec A _ _ _
      (supportedSecondIntersection_complement f g b c d)
  have h := supportedExteriorProduct_supportMaps A f g b b (supportIntersection d c) d
    (𝟙 _) (supportInclusion A d c) r
    (Category.id_comp _) (exists_unique_supportInclusion A d c).choose_spec.1 hr K L
  rw [support_derived_identity, NatTrans.id_app, id_tensorHom] at h
  dsimp only [r] at h
  rw [Functor.rightDerivedFunctorNatTrans_comp, NatTrans.comp_app] at h
  dsimp only [supportedSecondLocalizationSource, supportedSecondLocalizationTarget,
    supportedSecondLocalizationComponent₁, supportedSecondLocalizationComponent₂,
    Functor.mapTriangle, normalizedSupportTriangle, CategoryTheory.Pretriangulated.Triangle.mk,
    tensorLeft, curriedTensor]
  simpa only [Category.assoc, support_congruence_hom, e] using h.symm


/-- The component maps extend to a triangle morphism in the first variable.
Source: Tags 09XP and 0F1E (blueprint: lem-pur-supported-product-localization).
This is the component-extension part of the localization theorem; the distinguishedness
of the source and target triangles is handled by `normalizedSupportTriangle_distinguished`.
(blueprint: lem-pur-supported-product-localization-first-map). -/
theorem supportedProductLocalizationFirst_map (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y B C D : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
    (b : B ⟶ X) (c : C ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hF : ∃ n : ℤ,
      (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj).IsGE n) :
    ∃ m : supportedFirstLocalizationSource A f g b c d K.obj L.obj ⟶
        supportedFirstLocalizationTarget A f g b c d K.obj L.obj,
      m.hom₁ = supportedFirstLocalizationComponent₁ A f g b c d K.obj L.obj ∧
        m.hom₂ = supportedFirstLocalizationComponent₂ A f g b c d K.obj L.obj ∧
        m.hom₃ = supportedFirstLocalizationComponent₃ A f g b c d K.obj L.obj := by
  refine ⟨
    { hom₁ := supportedFirstLocalizationComponent₁ A f g b c d K.obj L.obj
      hom₂ := supportedFirstLocalizationComponent₂ A f g b c d K.obj L.obj
      hom₃ := supportedFirstLocalizationComponent₃ A f g b c d K.obj L.obj
      comm₁ := first_square_one A f g b c d K.obj L.obj
      comm₂ := first_square_two A f g b c d K.obj L.obj
      comm₃ := ?_ }, rfl, rfl, rfl⟩
  simpa only [supportedFirstLocalizationSource, supportedFirstLocalizationTarget,
    supportedFirstLocalizationComponent₁, supportedFirstLocalizationComponent₃] using
    (supportedExteriorProduct_boundary k A f g K L _hF).1 b c d

/-- The three specified supported exterior products form a morphism of distinguished
localization triangles in the first variable. The third morphism equation in
`TriangleMorphism` includes the connecting maps and the canonical tensor shift iso.
For the first variable that iso has no additional sign on homogeneous tensors; for the
second variable it is multiplication by (-1) to the degree of the first tensor factor.
No component is asserted invertible.

Source: Tags 09XP and 0F1E (blueprint: lem-pur-supported-product-localization).
Proof plan:
1. Identify the product and intersection supports on affine product charts by sums of
   extended ideals; identify the product open with the complement of the cut support.
2. Apply the exact K-flat right tensor functor to the support restriction triangle,
   using lem-pc-derived-tensor-second-factor-functor.
3. Use a bounded-below injective representative and the open-closed coefficient sequence
   to identify supported sections with Hom from the closed supported constant sheaf.
4. Apply the open-closed coefficient sequence to the support sheaf of B. Its three
   coefficient terms are flat on geometric stalks. Their external tensors are exactly
   the corresponding three product support coefficient sheaves.
5. Pull back and tensor the two evaluation maps. The adjoint pairing on Hom complexes
   has formula (e tensor d) maps to (-1)^(degree(g) degree(e)) f(e) tensor g(d).
   Naturality under precomposition checks both cone summands and the off-diagonal entry,
   so this is the prescribed third pairing as well as the first two pairings.
6. Apply Hom into injectives to the two coefficient sequences. The degreewise short
   exact sequences compute the two support triangles. The normalized boundaries are
   their actual short-exact-complex connecting maps.
7. The total differential is d tensor 1 + (-1)^p 1 tensor d. Its shift comparisons give
   respectively no extra sign and (-1)^p; these are the imported tensor CommShift maps.
8. For the second variable repeat the coefficient-sequence argument in that variable.
   Pullback, evaluation and restriction commute with coefficient morphisms and open
   restrictions; hence all three squares are natural in both senses. -/
theorem supportedProductLocalizationFirst (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y B C D : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
    (b : B ⟶ X) (c : C ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hF : ∃ n : ℤ,
      (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj).IsGE n) :
    supportedFirstLocalizationSource A f g b c d K.obj L.obj ∈
        distTriang (DerivedCategory (ModuleCat.{u + 1} A)) ∧
      supportedFirstLocalizationTarget A f g b c d K.obj L.obj ∈
        distTriang (DerivedCategory (ModuleCat.{u + 1} A)) ∧
      ∃ m : supportedFirstLocalizationSource A f g b c d K.obj L.obj ⟶
          supportedFirstLocalizationTarget A f g b c d K.obj L.obj,
        m.hom₁ = supportedFirstLocalizationComponent₁ A f g b c d K.obj L.obj ∧
        m.hom₂ = supportedFirstLocalizationComponent₂ A f g b c d K.obj L.obj ∧
        m.hom₃ = supportedFirstLocalizationComponent₃ A f g b c d K.obj L.obj := by
  refine ⟨?_, ?_, ?_⟩
  · exact (tensorRight ((supportedSectionsDerived A d).obj L.obj)).map_distinguished _
      (normalizedSupportTriangle_distinguished A b c K)
  · obtain ⟨n, hn⟩ := _hF
    let Fplus : DerivedCategory.Plus
        (Sheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} A)) :=
      ⟨externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj, ⟨n, hn⟩⟩
    exact normalizedSupportTriangle_distinguished A
      (supportedProductImmersion f g b d)
      (supportedProductImmersion f g c (𝟙 Y)) Fplus
  · exact supportedProductLocalizationFirst_map k A f g b c d K L _hF

/-- The component maps extend to a triangle morphism in the second variable.
Source: Tags 09XP and 0F1E (blueprint: lem-pur-supported-product-localization).
This is the component-extension part of the localization theorem; the distinguishedness
of the source and target triangles is handled by `normalizedSupportTriangle_distinguished`.
(blueprint: lem-pur-supported-product-localization-second-map). -/
theorem supportedProductLocalizationSecond_map (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y B C D : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
    (b : B ⟶ X) (c : C ⟶ Y) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hF : ∃ n : ℤ,
      (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj).IsGE n) :
    ∃ m : supportedSecondLocalizationSource A f g b c d K.obj L.obj ⟶
        supportedSecondLocalizationTarget A f g b c d K.obj L.obj,
      m.hom₁ = supportedSecondLocalizationComponent₁ A f g b c d K.obj L.obj ∧
        m.hom₂ = supportedSecondLocalizationComponent₂ A f g b c d K.obj L.obj ∧
        m.hom₃ = supportedSecondLocalizationComponent₃ A f g b c d K.obj L.obj := by
  refine ⟨
    { hom₁ := supportedSecondLocalizationComponent₁ A f g b c d K.obj L.obj
      hom₂ := supportedSecondLocalizationComponent₂ A f g b c d K.obj L.obj
      hom₃ := supportedSecondLocalizationComponent₃ A f g b c d K.obj L.obj
      comm₁ := second_square_one A f g b c d K.obj L.obj
      comm₂ := second_square_two A f g b c d K.obj L.obj
      comm₃ := ?_ }, rfl, rfl, rfl⟩
  simpa only [supportedSecondLocalizationSource, supportedSecondLocalizationTarget,
    supportedSecondLocalizationComponent₁, supportedSecondLocalizationComponent₃] using
    (supportedExteriorProduct_boundary k A f g K L _hF).2 b c d

/-- The three specified supported exterior products form a morphism of distinguished
localization triangles in the second variable. The third morphism equation in
`TriangleMorphism` includes the connecting maps and the canonical tensor shift iso.
For the first variable that iso has no additional sign on homogeneous tensors; for the
second variable it is multiplication by (-1) to the degree of the first tensor factor.
No component is asserted invertible.

Source: Tags 09XP and 0F1E (blueprint: lem-pur-supported-product-localization).
Proof plan:
1. Identify the product and intersection supports on affine product charts by sums of
   extended ideals; identify the product open with the complement of the cut support.
2. Apply the exact K-flat right tensor functor to the support restriction triangle,
   using lem-pc-derived-tensor-second-factor-functor.
3. Use a bounded-below injective representative and the open-closed coefficient sequence
   to identify supported sections with Hom from the closed supported constant sheaf.
4. Apply the open-closed coefficient sequence to the support sheaf of B. Its three
   coefficient terms are flat on geometric stalks. Their external tensors are exactly
   the corresponding three product support coefficient sheaves.
5. Pull back and tensor the two evaluation maps. The adjoint pairing on Hom complexes
   has formula (e tensor d) maps to (-1)^(degree(g) degree(e)) f(e) tensor g(d).
   Naturality under precomposition checks both cone summands and the off-diagonal entry,
   so this is the prescribed third pairing as well as the first two pairings.
6. Apply Hom into injectives to the two coefficient sequences. The degreewise short
   exact sequences compute the two support triangles. The normalized boundaries are
   their actual short-exact-complex connecting maps.
7. The total differential is d tensor 1 + (-1)^p 1 tensor d. Its shift comparisons give
   respectively no extra sign and (-1)^p; these are the imported tensor CommShift maps.
8. For the second variable repeat the coefficient-sequence argument in that variable.
   Pullback, evaluation and restriction commute with coefficient morphisms and open
   restrictions; hence all three squares are natural in both senses. -/
theorem supportedProductLocalizationSecond (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y B C D : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
    (b : B ⟶ X) (c : C ⟶ Y) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hF : ∃ n : ℤ,
      (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj).IsGE n) :
    supportedSecondLocalizationSource A f g b c d K.obj L.obj ∈
        distTriang (DerivedCategory (ModuleCat.{u + 1} A)) ∧
      supportedSecondLocalizationTarget A f g b c d K.obj L.obj ∈
        distTriang (DerivedCategory (ModuleCat.{u + 1} A)) ∧
      ∃ m : supportedSecondLocalizationSource A f g b c d K.obj L.obj ⟶
          supportedSecondLocalizationTarget A f g b c d K.obj L.obj,
        m.hom₁ = supportedSecondLocalizationComponent₁ A f g b c d K.obj L.obj ∧
        m.hom₂ = supportedSecondLocalizationComponent₂ A f g b c d K.obj L.obj ∧
        m.hom₃ = supportedSecondLocalizationComponent₃ A f g b c d K.obj L.obj := by
  refine ⟨?_, ?_, ?_⟩
  · exact (tensorLeft ((supportedSectionsDerived A b).obj K.obj)).map_distinguished _
      (normalizedSupportTriangle_distinguished A d c L)
  · obtain ⟨n, hn⟩ := _hF
    let Fplus : DerivedCategory.Plus
        (Sheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} A)) :=
      ⟨externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj, ⟨n, hn⟩⟩
    exact normalizedSupportTriangle_distinguished A
      (supportedProductImmersion f g b d)
      (supportedProductImmersion f g (𝟙 X) c) Fplus
  · exact supportedProductLocalizationSecond_map k A f g b c d K L _hF


end AlgebraicGeometry.Etale
