/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.BaseChangeCube
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# The graph comparison under geometric base change

Source: SGA 4 XVII 5.2.2 and 6.2.11; Stacks Project Tags 03S6 and 07A7
(blueprint: lem-asd-compact-support-graph-geometric-base-change).
-/

section
set_option autoImplicit false
set_option linter.all false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
attribute [local irreducible] AlgebraicGeometry.Etale.upperStar
  AlgebraicGeometry.Etale.lowerStar
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.leftDerivedFunctor
  AlgebraicGeometry.Etale.leftDerivedUpperStarComp
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorCounit
  CategoryTheory.Functor.rightDerivedFunctorUnit
  CategoryTheory.Functor.mapDerivedCategoryFactorsh
  CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
universe u u' v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry

open Scheme

namespace Etale.GraphExchange

variable (Λ : Type u') [Category.{u + 1} Λ] [Abelian Λ]
  [IsGrothendieckAbelian.{u + 1} Λ] [HasSmallSiteSheafify Λ]
  [MonoidalCategory Λ] [MonoidalPreadditive Λ] [SymmetricCategory Λ]
  [MonoidalClosed Λ] [Abelian.HasFunctorialFlatResolution Λ]

attribute [local irreducible] graphOpenAdjunction

section BaseChange

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

end BaseChange

section Clopen

variable {X W : Scheme.{u}} (σ : X ⟶ W) [IsOpenImmersion σ] [IsClosedImmersion σ]

attribute [local irreducible] sheafClopenAdjunction

attribute [local irreducible] clopenUpperStarLowerShriekAdjunction

variable {σ} in
attribute [local irreducible] clopenTransfer

set_option maxHeartbeats 800000 in
-- the base change of the unit of `Lσ^* ⊣ Dσ_!` unfolds large derived functors
end Clopen

end Etale.GraphExchange

end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme

namespace Compactification

variable {X Y : Scheme.{u}} {e : X ⟶ Y} (c : Compactification e)

/-- The graph `(j, 𝟙) : X ⟶ Z ×_Y X` of the open immersion `j : X ⟶ Z` of a compactification
of `e`. -/
private noncomputable def graphExchangeSection : X ⟶ pullback c.g e :=
  pullback.lift c.i (𝟙 X) (by rw [Category.id_comp, ← c.comm])

end Compactification

namespace Etale.GraphExchange

variable (Λ : Type u') [Category.{u + 1} Λ] [Abelian Λ]
  [IsGrothendieckAbelian.{u + 1} Λ] [HasSmallSiteSheafify Λ]
  [MonoidalCategory Λ] [MonoidalPreadditive Λ] [SymmetricCategory Λ]
  [MonoidalClosed Λ] [Abelian.HasFunctorialFlatResolution Λ]

section Construction

variable {X Y : Scheme.{u}} (e : X ⟶ Y) [_root_.AlgebraicGeometry.Etale e]
  (c : Compactification e)

end Construction
end Etale.GraphExchange
end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme

namespace Compactification

variable {X Y X' Y' : Scheme.{u}} {e : X ⟶ Y} {g : Y' ⟶ Y} {e' : X' ⟶ Y'} {g' : X' ⟶ X}
  (sq : IsPullback g' e' e g) (c : Compactification e)

end Compactification
namespace Etale.GraphExchange

section Coherence

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

end Coherence

variable (Λ : Type u') [Category.{u + 1} Λ] [Abelian Λ]
  [IsGrothendieckAbelian.{u + 1} Λ] [HasSmallSiteSheafify Λ]
  [MonoidalCategory Λ] [MonoidalPreadditive Λ] [SymmetricCategory Λ]
  [MonoidalClosed Λ] [Abelian.HasFunctorialFlatResolution Λ]

section Unfold

variable {X Y : Scheme.{u}} (e : X ⟶ Y) [_root_.AlgebraicGeometry.Etale e]
  (c : Compactification e)

omit [_root_.AlgebraicGeometry.Etale e] in
by
  unfold compactificationEtaleGraphMap
  rw [transfer_natTrans_app]
  unfold clopenTransfer
  rfl

end Unfold
section BaseChange

variable {X Y X' Y' : Scheme.{u}} {e : X ⟶ Y} {g : Y' ⟶ Y} {e' : X' ⟶ Y'} {g' : X' ⟶ X}
  (sq : IsPullback g' e' e g) (c : Compactification e) [_root_.AlgebraicGeometry.Etale e]
  [_root_.AlgebraicGeometry.Etale e']

attribute [local irreducible] compactificationEtaleGraphIso
  compactificationEtaleGraphMap
set_option maxHeartbeats 1000000 in
-- the derived functors involved are large terms
omit [_root_.AlgebraicGeometry.Etale e] [_root_.AlgebraicGeometry.Etale e'] in
end BaseChange
end Etale.GraphExchange
end AlgebraicGeometry

attribute [local irreducible] AlgebraicGeometry.Etale.GraphExchange.graphOpenAdjunction
  AlgebraicGeometry.Etale.GraphExchange.clopenUpperStarLowerShriekAdjunction
  AlgebraicGeometry.Etale.GraphExchange.compactificationEtaleGraphIso
  AlgebraicGeometry.Etale.GraphExchange.compactificationEtaleGraphMap

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
namespace GraphSheaf
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f] (c : Compactification f)
private noncomputable abbrev sectionMap : U ⟶ pullback c.g f :=
  c.graphExchangeSection
private theorem section_fst : sectionMap f c ≫ pullback.fst c.g f = c.i :=
  pullback.lift_fst _ _ _
private theorem section_snd : sectionMap f c ≫ pullback.snd c.g f = 𝟙 U :=
  pullback.lift_snd _ _ _
private noncomputable def sectionIso :
    upperStar (A) (pullback.snd c.g f) ⋙
      upperStar (A) (sectionMap f c) ≅ 𝟭 _ :=
  (upperStarComp _ _ _ (𝟙 U) (section_snd f c).symm).symm ≪≫ upperStarId _ U
attribute [local irreducible] sectionIso
private noncomputable def projection :
    upperStar (A) (pullback.snd c.g f) ⟶
      openImmersionLowerShriek (A) (sectionMap f c) :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (upperStarLowerStarAdjunction _ (sectionMap f c)).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (sectionIso A f c).hom _ ≫ (Functor.leftUnitor _).hom ≫
    (asIso (openImmersionLowerShriekToLowerStar _ (sectionMap f c))).inv
private noncomputable def composition :
    openImmersionLowerShriek (A) (sectionMap f c) ⋙
      etaleLowerShriek (A) (pullback.fst c.g f) inferInstance ≅
        openImmersionLowerShriek (A) c.i :=
  (((openImmersionLowerShriekUpperStarAdjunction _ (sectionMap f c)).comp
    (etaleLowerShriekUpperStarAdjunction _ (pullback.fst c.g f) inferInstance)).ofNatIsoRight
      (upperStarComp _ _ _ c.i (section_fst f c).symm).symm).leftAdjointUniq
    (openImmersionLowerShriekUpperStarAdjunction _ c.i)
attribute [local irreducible] projection
  composition
  etaleLowerShriek
  openImmersionLowerShriek
attribute [local irreducible] transfer
attribute [local irreducible] clopenAdjunction
end GraphSheaf
namespace GraphSheaf
variable (A : Type (u + 1)) [CommRing A]
  {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f] (c : Compactification f)
private noncomputable def delta :
    etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⋙
      upperStar (ModuleCat.{u + 1} A) c.g ⟶
        openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i :=
  (etaleLowerShriekBaseChangeIso A (IsPullback.of_hasPullback c.g f)).hom ≫
    Functor.whiskerRight (projection (ModuleCat.{u + 1} A) f c) _ ≫ (composition (ModuleCat.{u +
      1} A) f c).hom
attribute [local irreducible] delta
  projection
  composition
  etaleLowerShriek
  openImmersionLowerShriek
set_option maxRecDepth 4000 in
end GraphSheaf
end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.GraphExchange
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
end AlgebraicGeometry.Etale.GraphExchange
namespace AlgebraicGeometry.Etale.GraphExchange
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
end AlgebraicGeometry.Etale.GraphExchange
namespace AlgebraicGeometry.Etale
variable (A : Type (u + 1)) [CommRing A]
end AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale.GraphExchange
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
end AlgebraicGeometry.Etale.GraphExchange
namespace AlgebraicGeometry.Etale
variable (A : Type (u + 1)) [CommRing A]
attribute [local irreducible] derivedEtaleLowerShriekAdjunction
  derivedUpperStarLowerStarAdjunction
  derivedBaseChangeMap


end AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

end AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale.GraphExchange
attribute [local irreducible] AlgebraicGeometry.Etale.derivedUpperStarLowerStarAdjunction
  AlgebraicGeometry.Etale.mapDerivedUpperStarLowerStarAdjunction
variable (Λ : Type u') [Category.{u + 1} Λ] [Abelian Λ]
  [IsGrothendieckAbelian.{u + 1} Λ] [HasSmallSiteSheafify Λ]
  [MonoidalCategory Λ] [MonoidalPreadditive Λ] [SymmetricCategory Λ]
  [MonoidalClosed Λ] [Abelian.HasFunctorialFlatResolution Λ] [Fact (GraphProperBaseChange Λ)]
section Construction
variable {X Y : Scheme.{u}} (e : X ⟶ Y) [_root_.AlgebraicGeometry.Etale e]
  (c : Compactification e)
end Construction
section Unfold
variable {X Y : Scheme.{u}} (e : X ⟶ Y) [_root_.AlgebraicGeometry.Etale e]
  (c : Compactification e)
end Unfold
section BaseChange
variable {X Y X' Y' : Scheme.{u}} {e : X ⟶ Y} {g : Y' ⟶ Y}
  {e' : X' ⟶ Y'} {g' : X' ⟶ X}
  (sq : IsPullback g' e' e g) (c : Compactification e)
  [_root_.AlgebraicGeometry.Etale e] [_root_.AlgebraicGeometry.Etale e']
omit [Fact (GraphProperBaseChange Λ)] [_root_.AlgebraicGeometry.Etale e]
  [_root_.AlgebraicGeometry.Etale e'] in
set_option maxHeartbeats 1000000 in
-- the derived functors involved are large terms
end BaseChange
section Transpose
variable {X Y : Scheme.{u}} (e : X ⟶ Y) [_root_.AlgebraicGeometry.Etale e]
  (c : Compactification e)
end Transpose
section BaseChange
variable {X Y X' Y' : Scheme.{u}} {e : X ⟶ Y} {g : Y' ⟶ Y}
  {e' : X' ⟶ Y'} {g' : X' ⟶ X}
  (sq : IsPullback g' e' e g) (c : Compactification e)
  [_root_.AlgebraicGeometry.Etale e] [_root_.AlgebraicGeometry.Etale e']
end BaseChange
end AlgebraicGeometry.Etale.GraphExchange

namespace AlgebraicGeometry.Etale.GraphExchange
end AlgebraicGeometry.Etale.GraphExchange

namespace AlgebraicGeometry.Etale.GraphExchange
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

end AlgebraicGeometry.Etale.GraphExchange
namespace AlgebraicGeometry.Etale.GraphExchange

end AlgebraicGeometry.Etale.GraphExchange

namespace AlgebraicGeometry.Etale.GraphExchange
end AlgebraicGeometry.Etale.GraphExchange
attribute [-instance] AlgebraicGeometry.Etale.GraphExchange.graphUpperAdditive
  AlgebraicGeometry.Etale.GraphExchange.graphUpperPreservesFiniteLimits
  AlgebraicGeometry.Etale.GraphExchange.graphUpperPreservesFiniteColimits
  AlgebraicGeometry.Etale.GraphExchange.graphLowerAdditive
  AlgebraicGeometry.Etale.GraphExchange.graphLowerPreservesFiniteLimits
  AlgebraicGeometry.Etale.GraphExchange.graphOpenAdditive
  AlgebraicGeometry.Etale.GraphExchange.graphOpenPreservesFiniteLimits
  AlgebraicGeometry.Etale.GraphExchange.graphOpenPreservesFiniteColimits
  AlgebraicGeometry.Etale.GraphExchange.graphEtaleAdditive
  AlgebraicGeometry.Etale.GraphExchange.graphEtalePreservesFiniteLimits
  AlgebraicGeometry.Etale.GraphExchange.graphEtalePreservesFiniteColimits
  AlgebraicGeometry.Etale.GraphExchange.graphSheafLocalization
attribute [-instance] AlgebraicGeometry.Etale.GraphExchange.graphSheafColimits
  AlgebraicGeometry.Etale.GraphExchange.graphSheafCountableCoproducts
  AlgebraicGeometry.Etale.GraphExchange.graphSheafExactColimits
  AlgebraicGeometry.Etale.GraphExchange.graphSheafFlatResolution
  AlgebraicGeometry.Etale.GraphExchange.graphSheafKInjective
  AlgebraicGeometry.Etale.GraphExchange.graphSheafGrothendieck
  AlgebraicGeometry.Etale.cachedColimits
  AlgebraicGeometry.Etale.cachedCoproducts
  AlgebraicGeometry.Etale.cachedExactColimits
end

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
