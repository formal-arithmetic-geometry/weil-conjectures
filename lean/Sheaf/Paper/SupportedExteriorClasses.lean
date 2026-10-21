/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.PurityConventions
public import Sheaf.Paper.SupportedCupFunctoriality
public import Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.Paper.SupportedHomAdjunctionTranspose

/-!
# Exterior pairing on individual supported cohomology classes

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-regular, Step 5;
the induced cohomology pairing uses the specified pro-etale derived exterior map.
(blueprint: def-pur-supported-exterior-classes).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w v₁ w₁

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

/-- The standard derived category of scalar modules. Source: Step 5, supported
adjunction (blueprint: def-pur-supported-exterior-classes). -/
instance exteriorFrameScalarHasDerived (P : PurityFiniteSetting.{u}) :
    HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} P.Coefficient) :=
  HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{u + 1} P.Coefficient)


/-- The coefficient comparison for the exact supported adjunction, including the
published comparison from P.constant to the site constant sheaf.
Source: Step 5, supported adjunction transpose
(blueprint: def-pur-supported-exterior-classes). -/
def exteriorFrameSupportIso (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X] :
    (supportedCoefficients P.Coefficient i).mapDerivedCategory.{u + 1, u + 1}.obj
        ((DerivedCategory.singleFunctor.{u + 1} (ModuleCat.{u + 1} P.Coefficient) 0).obj
          (ModuleCat.of P.Coefficient P.Coefficient)) ≅
      (P.functorialCupSingle true X).obj (P.functorialCupSource true i) :=
  ((supportedCoefficients P.Coefficient i).mapDerivedCategorySingleFunctor.{u + 1, u + 1}
    0).app _ ≪≫
    (P.functorialCupSingle true X).mapIso
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).mapIso (cupConstantIso P Z).symm)

/-- A supported Hom class as a map from A[0] to derived supported sections of
its already shifted coefficient object. Source: Step 5, adjunction
(blueprint: def-pur-supported-exterior-classes). -/
def exteriorFrameTranspose (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X] (a r : ℤ)
    (α : P.FunctorialCupH true i a r) :
    (DerivedCategory.singleFunctor.{u + 1} (ModuleCat.{u + 1} P.Coefficient) 0).obj
        (ModuleCat.of P.Coefficient P.Coefficient) ⟶
      (supportedSectionsDerived P.Coefficient i).obj
        (((P.functorialCupSingle true X).obj
          (P.functorialCupTwist true X r))⟦a⟧) :=
  (supportedCoefficientDerivedAdjunction P.Coefficient i).homEquiv _ _
    ((P.exteriorFrameSupportIso i).hom ≫ α)

/-- The canonical diagonal A[0] → A[0] tensor A[0], carrying 1 to 1 tensor 1.
Source: Step 5, exterior product on individual classes
(blueprint: def-pur-supported-exterior-classes). -/
def exteriorFrameUnit (P : PurityFiniteSetting.{u}) :
    (DerivedCategory.singleFunctor.{u + 1} (ModuleCat.{u + 1} P.Coefficient) 0).obj
        (ModuleCat.of P.Coefficient P.Coefficient) ⟶
      (DerivedCategory.singleFunctor.{u + 1} (ModuleCat.{u + 1} P.Coefficient) 0).obj
        (ModuleCat.of P.Coefficient P.Coefficient) ⊗
      (DerivedCategory.singleFunctor.{u + 1} (ModuleCat.{u + 1} P.Coefficient) 0).obj
        (ModuleCat.of P.Coefficient P.Coefficient) :=
  (DerivedCategory.singleFunctorObjUnitIso.{u + 1} (ModuleCat.{u + 1} P.Coefficient)).hom ≫
    (λ_ (𝟙_ (DerivedCategory.{u + 1} (ModuleCat.{u + 1} P.Coefficient)))).inv ≫
    tensorHom (DerivedCategory.singleFunctorObjUnitIso.{u + 1}
      (ModuleCat.{u + 1} P.Coefficient)).inv
      (DerivedCategory.singleFunctorObjUnitIso.{u + 1} (ModuleCat.{u + 1} P.Coefficient)).inv

/-- Assemble the tensor of two shifted morphisms before specializing the category.
Sharing the localization and tensor instances keeps all comparisons on the same
native derived tensor. Source: Step 5, right-shift-first convention
(blueprint: def-pur-supported-exterior-classes). -/
def exteriorFrameTensorTarget {C : Type v} [Category.{w} C]
    [MonoidalCategory C] [HasShift C ℤ]
    [∀ K : C, ((curriedTensor C).obj K).CommShift ℤ]
    [∀ K : C, ((curriedTensor C).flip.obj K).CommShift ℤ]
    {L M F G H : C} (a b : ℤ)
    (α : L ⟶ F⟦a⟧) (β : M ⟶ G⟦b⟧) (γ : F ⊗ G ⟶ H) :
    L ⊗ M ⟶ H⟦a + b⟧ :=
  tensorHom α β ≫ (cupTensorShiftIso F G a b).hom ≫ γ⟦a + b⟧'

/-- The exact inverse-image comparison on a degree-zero object, followed by
its specified ordinary coefficient map. Source: Step 5, projection comparisons
(blueprint: def-pur-supported-exterior-classes). -/
def exteriorFrameSingleMap {C : Type v} {D : Type w}
    [Category.{v₁} C] [Abelian C] [hC : HasDerivedCategory.{v₁} C]
    [Category.{w₁} D] [Abelian D] [hD : HasDerivedCategory.{w₁} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : DerivedCategory C ⥤ DerivedCategory D) (e : G ≅ F.mapDerivedCategory)
    {L : C} {M : D} (t : F.obj L ⟶ M) :
    G.obj ((DerivedCategory.singleFunctor C 0).obj L) ⟶
      (DerivedCategory.singleFunctor D 0).obj M :=
  e.hom.app _ ≫ (F.mapDerivedCategorySingleFunctor 0).hom.app L ≫
    (DerivedCategory.singleFunctor D 0).map t

/-- Assemble a tensor of two comparisons followed by a coefficient map before
specializing the categories. Source: Step 5, coefficient comparisons
(blueprint: def-pur-supported-exterior-classes). -/
def exteriorFrameTensorMap {C : Type v} [Category.{v₁} C] [MonoidalCategory C]
    {L M F G H : C} (α : L ⟶ F) (β : M ⟶ G) (μ : F ⊗ G ⟶ H) :
    L ⊗ M ⟶ H :=
  tensorHom α β ≫ μ

/-- Assemble both exact inverse-image comparisons and the single tensor comparison
before specializing the sheaf categories. Source: Step 5, coefficient comparison
(blueprint: def-pur-supported-exterior-classes). -/
def exteriorFrameCoefficientCore {A B C : Type v}
    [Category.{w} A] [Abelian A] [HasDerivedCategory.{w} A]
    [Category.{w} B] [Abelian B] [HasDerivedCategory.{w} B]
    [Category.{w} C] [Abelian C] [HasDerivedCategory.{w} C]
    [HasColimitsOfSize.{0, 0} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C]
    [MonoidalCategory (DerivedCategory C)] [(DerivedCategory.Q (C := C)).LaxMonoidal]
    (F : A ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (DF : DerivedCategory A ⥤ DerivedCategory C)
    (DG : DerivedCategory B ⥤ DerivedCategory C)
    (eF : DF ≅ F.mapDerivedCategory) (eG : DG ≅ G.mapDerivedCategory)
    {L : A} {M : B} {U V H : C} (α : F.obj L ⟶ U) (β : G.obj M ⟶ V)
    (μ : U ⊗ V ⟶ H) :
    DF.obj ((DerivedCategory.singleFunctor A 0).obj L) ⊗
        DG.obj ((DerivedCategory.singleFunctor B 0).obj M) ⟶
      (DerivedCategory.singleFunctor C 0).obj H :=
  exteriorFrameTensorMap (exteriorFrameSingleMap F DF eF α)
    (exteriorFrameSingleMap G DG eG β) (cupDerivedCoefficientMap μ)

/-- The canonical coefficient map on an external product, before specializing
its sheaves. It is the exact inverse-image comparison, the degree-zero tensor
comparison and the indicated ordinary multiplication. Source: Step 5,
coefficient identifications (blueprint: def-pur-supported-exterior-classes). -/
def exteriorFrameProjectionCoefficientMap (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    {T X Y : Scheme.{u}} (pX : T ⟶ X) (pY : T ⟶ Y)
    (F : Sheaf (Scheme.ProEt.topology X) C)
    (G : Sheaf (Scheme.ProEt.topology Y) C)
    (H₁ H₂ H : Sheaf (Scheme.ProEt.topology T) C)
    (α : (upperStar C pX).obj F ⟶ H₁)
    (β : (upperStar C pY).obj G ⟶ H₂)
    (μ : H₁ ⊗ H₂ ⟶ H) :
    ((derivedTensor C T).obj
      ((upperStar C pX).leftDerivedFunctor.obj
        ((DerivedCategory.singleFunctor.{u + 1} _ 0).obj F))).obj
      ((upperStar C pY).leftDerivedFunctor.obj
        ((DerivedCategory.singleFunctor.{u + 1} _ 0).obj G)) ⟶
      (DerivedCategory.singleFunctor.{u + 1} _ 0).obj H :=
  exteriorFrameCoefficientCore
    (upperStar C pX) (upperStar C pY) _ _
    (leftDerivedUpperStarIsoMapDerivedCategory C pX)
    (leftDerivedUpperStarIsoMapDerivedCategory C pY) α β μ


/-- Change the source of a morphism using the specified equality.
Source: Step 5, tensor presentation (blueprint: def-pur-supported-exterior-classes). -/
def exteriorFrameChangeSource {C : Type v} [Category.{w} C] {L M N : C}
    (h : L = M) (f : M ⟶ N) : L ⟶ N :=
  eqToHom h ≫ f

/-- Transport the explicit tensor presentation to the published external product.
Source: Step 5, the canonical coefficient identification
(blueprint: def-pur-supported-exterior-classes). -/
def exteriorFrameCoefficientMap (A : Type (u + 1)) [CommRing A]
    {B X Y : Scheme.{u}} (aX : X ⟶ B) (aY : Y ⟶ B)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    (G : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))
    (H₁ H₂ H : Sheaf (Scheme.ProEt.topology (pullback aX aY)) (ModuleCat.{u + 1} A))
    (α : (upperStar (ModuleCat.{u + 1} A) (pullback.fst aX aY)).obj F ⟶ H₁)
    (β : (upperStar (ModuleCat.{u + 1} A) (pullback.snd aX aY)).obj G ⟶ H₂)
    (μ : H₁ ⊗ H₂ ⟶ H) :=
  exteriorFrameChangeSource (supportedExternalProduct_eq A aX aY
    ((DerivedCategory.singleFunctor _ 0).obj F)
    ((DerivedCategory.singleFunctor _ 0).obj G)).symm
    (exteriorFrameProjectionCoefficientMap (ModuleCat.{u + 1} A)
        (pullback.fst aX aY) (pullback.snd aX aY) F G H₁ H₂ H α β μ)

/-- Specialize the canonical external coefficient map to the normalized twist
pullbacks and multiplication. Source: Step 5, coefficient identifications
(blueprint: def-pur-supported-exterior-classes). -/
def exteriorFrameTarget (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k)) (r s : ℤ) :=
  exteriorFrameCoefficientMap P.Coefficient aX aY
    (P.functorialCupTwist true X r) (P.functorialCupTwist true Y s)
    (P.functorialCupTwist true (pullback aX aY) r)
    (P.functorialCupTwist true (pullback aX aY) s)
    (P.functorialCupTwist true (pullback aX aY) (r + s))
    (P.functorialCupTwistPullback true (pullback.fst aX aY) aX r).hom
    (P.functorialCupTwistPullback true (pullback.snd aX aY) aY s).hom
    (P.functorialCupTwistProduct true (pullback aX aY) (pullback.fst aX aY ≫ aX) r s).hom


/-- Transpose after the specified coefficient-source identification.
Source: Step 5, normalized supported adjunction
(blueprint: def-pur-supported-exterior-classes). -/
def exteriorFrameAdjoint {C : Type v} {D : Type w}
    [Category.{v₁} C] [Category.{w₁} D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {L : C} {M N : D} (s : N ⟶ F.obj L) (α : L ⟶ G.obj M) :
    N ⟶ M :=
  s ≫ (adj.homEquiv _ _).symm α

/-- Assemble the shifted exterior pairing through its normalized adjunction.
Source: Step 5, exterior pairing and adjunction
(blueprint: def-pur-supported-exterior-classes). -/
def exteriorFramePairing {C : Type v} {D : Type w}
    [Category.{v₁} C] [MonoidalCategory C] [HasShift C ℤ]
    [∀ K : C, ((curriedTensor C).obj K).CommShift ℤ]
    [∀ K : C, ((curriedTensor C).flip.obj K).CommShift ℤ]
    [Category.{w₁} D] [HasShift D ℤ]
    {F : C ⥤ D} {G : D ⥤ C} [G.CommShift ℤ]
    (adj : F ⊣ G) {L M N U V : C} {S T : D} (s : T ⟶ F.obj L)
    (δ : L ⟶ M ⊗ N) (a b : ℤ)
    (α : M ⟶ U⟦a⟧) (β : N ⟶ V⟦b⟧) (γ : U ⊗ V ⟶ G.obj S) : T ⟶ S⟦a + b⟧ :=
  exteriorFrameAdjoint adj s
    (δ ≫ exteriorFrameTensorTarget a b α β γ ≫ (G.commShiftIso (a + b)).inv.app S)

/-- The specified pro-etale exterior map on the two classes. Their adjunction
transposes are identified with shifted supported sections; the tensor-shift
comparison is then taken in the coefficient-module derived category. Apply
kappa to the unshifted coefficient objects and transpose back.
Source: Step 5, last equality (blueprint: def-pur-supported-exterior-classes). -/
def exteriorFrameExternal (P : PurityFiniteSetting.{u}) {X Y Z W : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [LocallyOfFiniteType aY]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (a b r s : ℤ) (α : P.FunctorialCupH true i a r) (β : P.FunctorialCupH true j b s) :
    P.FunctorialCupH true (Etale.supportedProductImmersion aX aY i j) (a + b) (r + s) :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  exteriorFramePairing
    (supportedCoefficientDerivedAdjunction P.Coefficient
      (Etale.supportedProductImmersion aX aY i j))
    (P.exteriorFrameSupportIso (Etale.supportedProductImmersion aX aY i j)).inv
    P.exteriorFrameUnit a b
          (P.exteriorFrameTranspose i a r α ≫
            ((supportedSectionsDerived P.Coefficient i).commShiftIso a).hom.app
              ((cupSingle P X).obj (P.functorialCupTwist true X r)))
          (P.exteriorFrameTranspose j b s β ≫
            ((supportedSectionsDerived P.Coefficient j).commShiftIso b).hom.app
              ((cupSingle P Y).obj (P.functorialCupTwist true Y s)))
          (supportedExteriorProductOverField P.Coefficient P.field.k aX aY i j _ _ ≫
            (supportedSectionsDerived P.Coefficient
              (Etale.supportedProductImmersion aX aY i j)).map
                (P.exteriorFrameTarget aX aY r s))


end WeilConjectures.PurityFiniteSetting
