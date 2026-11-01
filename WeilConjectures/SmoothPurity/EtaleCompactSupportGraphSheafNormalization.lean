/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
import WeilConjectures.SixFunctors.BaseChange.Etale
import WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent

/-!
# The graph map into the compactification sheaf

Source: Stacks Project Tag 0F4L (lemma-shriek-into-star-separated-etale),
and SGA 4 XVII 6.2.11 (blueprint: lem-asd-compact-support-graph-sheaf-normalization).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.all false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
namespace GraphNormalization
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (A : Type (u + 1)) [CommRing A]
  {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f] (c : Compactification f)
private noncomputable abbrev sectionMap : U ⟶ pullback c.g f :=
  pullback.lift c.i (𝟙 U) (by simpa using c.comm.symm)
attribute [local instance] section_open

attribute [local instance] section_closed

attribute [local instance] section_comparison_iso

private noncomputable def sectionIso :
    upperStar (ModuleCat.{u + 1} A) (pullback.snd c.g f) ⋙
      upperStar (ModuleCat.{u + 1} A) (sectionMap f c) ≅ 𝟭 _ :=
  (upperStarComp (ModuleCat.{u + 1} A) (sectionMap f c) (pullback.snd c.g f) (𝟙 U)
    (pullback.lift_snd c.i (𝟙 U) (by simpa using c.comm.symm)).symm).symm ≪≫ upperStarId _ U
attribute [local irreducible] sectionIso
private noncomputable def projection :
    upperStar (ModuleCat.{u + 1} A) (pullback.snd c.g f) ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) (sectionMap f c) :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (upperStarLowerStarAdjunction _ (sectionMap f c)).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (sectionIso A f c).hom _ ≫ (Functor.leftUnitor _).hom ≫
    (asIso (openImmersionLowerShriekToLowerStar _ (sectionMap f c))).inv
private noncomputable def composition :
    openImmersionLowerShriek (ModuleCat.{u + 1} A) (sectionMap f c) ⋙
      etaleLowerShriek (ModuleCat.{u + 1} A) (pullback.fst c.g f) inferInstance ≅
        openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i :=
  (((openImmersionLowerShriekUpperStarAdjunction _ (sectionMap f c)).comp
    (etaleLowerShriekUpperStarAdjunction _ (pullback.fst c.g f) inferInstance)).ofNatIsoRight
      (upperStarComp (ModuleCat.{u + 1} A) (sectionMap f c) (pullback.fst c.g f) c.i
        (pullback.lift_fst c.i (𝟙 U) (by simpa using c.comm.symm)).symm).symm).leftAdjointUniq
    (openImmersionLowerShriekUpperStarAdjunction _ c.i)
attribute [local irreducible] projection
  composition
  etaleLowerShriek
  openImmersionLowerShriek
attribute [local irreducible] transfer
private noncomputable def delta :
    etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⋙
      upperStar (ModuleCat.{u + 1} A) c.g ⟶
        openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i :=
  (etaleLowerShriekBaseChangeIso A (IsPullback.of_hasPullback c.g f)).hom ≫
    Functor.whiskerRight (projection A f c) _ ≫ (composition A f c).hom
attribute [local irreducible] delta
set_option maxRecDepth 4000 in
attribute [local irreducible] normalizedTransfer

attribute [local instance] siteBC_iso

attribute [local instance] restrictionBC_iso

attribute [local irreducible] upperStarLowerStarAdjunction

attribute [local instance] toTest_open

attribute [local irreducible] toTest

end GraphNormalization

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
end AlgebraicGeometry.Etale
