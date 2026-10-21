/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.AlgebraicGeometry.ProperSupportCompactMaps
public import Sheaf.AlgebraicGeometry.CompactProductArrows
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import Sheaf.Paper.SupportedClassGeometry

/-! # Compact products, proper support and excision

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-proper-support-laws).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry AlgebraicGeometry.Etale


/-- The kunneth clause, with the same quantified inputs and canonical maps.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-proper-support-laws). -/
def compactProductProperSupportKunnethLaw (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Spec (.of P.field.k))
    (g : Y ⟶ Spec (.of P.field.k)),
    IsSeparated f → LocallyOfFiniteType f → QuasiCompact f →
    IsSeparated g → LocallyOfFiniteType g → QuasiCompact g →
    ∀ (c : Compactification f) (d : Compactification g)
      (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))),
      P.CompactProductInput X K → P.CompactProductInput Y L →
      IsIso (compactProductMap (ModuleCat.{u + 1} P.Coefficient) c d K L)

/-- The naturality clause, with the same quantified inputs and canonical maps.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-proper-support-laws). -/
def compactProductProperSupportNaturalityLaw (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Spec (.of P.field.k))
    (g : Y ⟶ Spec (.of P.field.k)),
    IsSeparated f → LocallyOfFiniteType f → QuasiCompact f →
    IsSeparated g → LocallyOfFiniteType g → QuasiCompact g →
    ∀ (c : Compactification f) (d : Compactification g)
      (K K' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (L L' : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (α : K ⟶ K') (β : L ⟶ L'),
      P.CompactProductInput X K → P.CompactProductInput X K' →
      P.CompactProductInput Y L → P.CompactProductInput Y L' →
      tensorHom ((compactProductSections (ModuleCat.{u + 1} P.Coefficient) c).map α)
          ((compactProductSections (ModuleCat.{u + 1} P.Coefficient) d).map β) ≫
        compactProductMap (ModuleCat.{u + 1} P.Coefficient) c d K' L' =
      compactProductMap (ModuleCat.{u + 1} P.Coefficient) c d K L ≫
        (compactProductSections (ModuleCat.{u + 1} P.Coefficient)
          (compactProductCompactification c d)).map
          (compactProductExternalMap (ModuleCat.{u + 1} P.Coefficient) f g α β)

/-- The proper support clause, with the same quantified inputs and canonical maps.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-proper-support-laws). -/
def compactProductProperSupportProperSupportLaw (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Y Z W : Scheme.{u}} (f : X ⟶ Spec (.of P.field.k))
    (g : Y ⟶ Spec (.of P.field.k)),
    IsSeparated f → LocallyOfFiniteType f → QuasiCompact f →
    IsSeparated g → LocallyOfFiniteType g → QuasiCompact g →
    ∀ (c : Compactification f) (d : Compactification g)
      (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
      [IsProper (i ≫ f)] [IsProper (j ≫ g)]
      (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))),
      P.CompactProductInput X K → P.CompactProductInput Y L →
      supportedExteriorProduct P.Coefficient f g i j K L ≫
        compactSupportFromProperSupport P.Coefficient (compactProductCompactification c d)
          (supportedProductImmersion f g i j)
          (externalProduct (ModuleCat.{u + 1} P.Coefficient) f g K L) =
      tensorHom (compactSupportFromProperSupport P.Coefficient c i K)
          (compactSupportFromProperSupport P.Coefficient d j L) ≫
        compactProductMap (ModuleCat.{u + 1} P.Coefficient) c d K L

/-- The supported classes clause, with the same quantified inputs and canonical maps.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-proper-support-laws). -/
def compactProductProperSupportSupportedClassesLaw (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Z : Scheme.{u}} (f : X ⟶ Spec (.of P.field.k)),
    IsSeparated f → LocallyOfFiniteType f → QuasiCompact f →
    ∀ (c : Compactification f) (i : Z ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ f)]
      (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (a : ℤ)
      (α : (supportedCoefficients P.Coefficient i).mapDerivedCategory.obj
        P.compactProductUnit ⟶ K⟦a⟧),
      P.CompactProductInput X K →
      (supportedCoefficientDerivedAdjunction P.Coefficient i).homEquiv _ _ α ≫
        compactSupportFromProperSupport P.Coefficient c i (K⟦a⟧) =
      compactSupportClassImage P.Coefficient c i α

/-- The excision clause, with the same quantified inputs and canonical maps.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-proper-support-laws). -/
def compactProductProperSupportExcisionLaw (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Z : Scheme.{u}} (f : X ⟶ Spec (.of P.field.k)),
    IsSeparated f → LocallyOfFiniteType f → QuasiCompact f →
    ∀ (c : Compactification f) (i : Z ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ f)]
      (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (F : DerivedCategory.Plus
        (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (e : (compactProductPullback (ModuleCat.{u + 1} P.Coefficient) c.i).obj F.obj ≅ K),
      P.CompactProductInput X K →
      ∃ h : IsIso (compactSupportExcisionMap P.Coefficient c i K F.obj e),
        compactSupportFromProperSupport P.Coefficient c i K ≫
          compactSupportToExtension P.Coefficient c K F.obj e =
        @inv _ _ _ _ (compactSupportExcisionMap P.Coefficient c i K F.obj e) h ≫
          (compactProductForget P.Coefficient (i ≫ c.i)).app F.obj

/-- The complete conjunction of the named universally quantified clauses above.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-proper-support-laws). -/
structure CompactProductProperSupportLaws (P : PurityFiniteSetting.{u}) : Prop where
  kunneth : P.compactProductProperSupportKunnethLaw
  naturality : P.compactProductProperSupportNaturalityLaw
  proper_support : P.compactProductProperSupportProperSupportLaw
  supported_classes : P.compactProductProperSupportSupportedClassesLaw
  excision : P.compactProductProperSupportExcisionLaw

end WeilConjectures.PurityFiniteSetting
