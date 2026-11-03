/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.MorphismProperty.Limits
import all WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSquare
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryRestrictionPullbackSquare
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.CategoryTheory.ExactCube

/-! Scalar restriction and the ordinary ringed inverse-image square.
Source: Stacks Project, Tags 03D7, 03D8 and 0D6D.
(blueprint: lem-weil-pbc-ring-restriction-pullback-square) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  proEtaleRingInverseImageComp LocallyRingedSpace.comp PresheafedSpace.comp
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  proEtaleRingCompositeCoefficients exchangeModuleComposition

section
variable {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RW SW : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (RZ SZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (aV : RV ⟶ SV) (aW : RW ⟶ SW) (aZ : RZ ⟶ SZ)
    (ckR : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj RV ≅ RW)
    (chR : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RW ≅ RZ)
    (ckS : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj SV ≅ SW)
    (chS : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj SW ≅ SZ)
    (hk : ckR.hom ≫ aW = (proEtaleSheafInverseImage k CommRingCat.{u + 1}).map aV ≫ ckS.hom)
    (hh : chR.hom ≫ aZ = (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map aW ≫ chS.hom)

include hk hh in
end

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}

set_option linter.defProp false in
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

private theorem derivedCube_nat
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
  [Category C₀] [Category C₁] [Category C₂] [Category C₃]
  [Category D₀] [Category D₁] [Category D₂] [Category D₃]
  [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
  [Abelian D₀] [Abelian D₁] [Abelian D₂] [Abelian D₃]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁]
  [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁]
  [HasDerivedCategory D₂] [HasDerivedCategory D₃]
  {R₀ : D₀ ⥤ C₀} {R₁ : D₁ ⥤ C₁} {R₂ : D₂ ⥤ C₂} {R₃ : D₃ ⥤ C₃}
  {J : C₀ ⥤ C₁} {H : C₁ ⥤ C₃} {G : C₀ ⥤ C₂} {I : C₂ ⥤ C₃}
  {J' : D₀ ⥤ D₁} {H' : D₁ ⥤ D₃} {G' : D₀ ⥤ D₂} {I' : D₂ ⥤ D₃}
  [R₀.Additive] [R₁.Additive] [R₂.Additive] [R₃.Additive]
  [J.Additive] [H.Additive] [G.Additive] [I.Additive]
  [J'.Additive] [H'.Additive] [G'.Additive] [I'.Additive]
  [PreservesFiniteLimits R₀] [PreservesFiniteColimits R₀]
  [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  [PreservesFiniteLimits R₃] [PreservesFiniteColimits R₃]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
  [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
  [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits I'] [PreservesFiniteColimits I']
    (qJ : R₀ ⋙ J ≅ J' ⋙ R₁) (qH : R₁ ⋙ H ≅ H' ⋙ R₃)
    (qG : R₀ ⋙ G ≅ G' ⋙ R₂) (qI : R₂ ⋙ I ≅ I' ⋙ R₃)
    (c : J ⋙ H ≅ G ⋙ I) (d : J' ⋙ H' ≅ G' ⋙ I')
    (hc : Functor.whiskerLeft R₀ c.hom ≫ Functor.whiskerRight qG.hom I ≫
        Functor.whiskerLeft G' qI.hom =
      Functor.whiskerRight qJ.hom H ≫ Functor.whiskerLeft J' qH.hom ≫
        Functor.whiskerRight d.hom R₃) :
    Functor.whiskerLeft R₀.mapDerivedCategory (Functor.mapDerivedCategorySquareIso c).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso qG).hom I.mapDerivedCategory ≫
      Functor.whiskerLeft G'.mapDerivedCategory (Functor.mapDerivedCategorySquareIso qI).hom =
    Functor.whiskerRight (Functor.mapDerivedCategorySquareIso qJ).hom H.mapDerivedCategory ≫
      Functor.whiskerLeft J'.mapDerivedCategory (Functor.mapDerivedCategorySquareIso qH).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso d).hom R₃.mapDerivedCategory := by
  apply NatTrans.ext
  funext M
  exact CategoryTheory.Functor.exactDerivedCube qJ qH qG qI c d
    (fun N ↦ congrArg (fun z ↦ z.app N) hc) M

end AlgebraicGeometry.Scheme
