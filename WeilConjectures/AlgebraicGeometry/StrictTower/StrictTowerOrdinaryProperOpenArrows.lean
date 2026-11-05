/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
public import WeilConjectures.CategoryTheory.SmoothPurity.TermwiseCompositeTransformation
public import WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenClopenProjector
public import WeilConjectures.AlgebraicGeometry.StrictTower.TowerOpenBetaNormalization
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows

/-! # Ordinary clopen arrows for constant-coefficient strict towers

Source: Stacks Project, Tags 09BN, 0F7B, and the underived refinement of the blueprint.
(blueprint: def-cbc-strict-tower-ordinary-proper-open-arrows)

These are the ordinary constructions underlying the recorded derived arrows. All
functors and adjunctions are the already specified constant-ring module operations.
The open unit, its direct-image transpose, and the clopen projector are imported
from ProperOpenClopenProjector. Cartesian beta and the open-extension compositor
are imported from TowerOpenBetaNormalization.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

attribute [local irreducible] Functor.leftAdjoint modulePullback

/-- Unit-preserving open-adjoint transport along equality of scheme morphisms.
Source: Stacks, Tag 09BN
(blueprint: def-cbc-strict-tower-ordinary-proper-open-arrows). -/
def singleJCongr {U X : Scheme.{u}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) : moduleJ B f ≅ moduleJ B g :=
  ((moduleJAdj B f).ofNatIsoRight
    (eqToIso (congrArg (modulePullback B) h))).leftAdjointUniq (moduleJAdj B g)

/-- The intrinsic ordinary alpha: cartesian beta, clopen projection, and compositors.
Source: Stacks, Tag 0F7B and the blueprint's underived refinement
(blueprint: def-cbc-strict-tower-ordinary-proper-open-arrows). -/
def singleAlpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : moduleJ B i ⋙ modulePullback B p ⟶
      modulePullback B r ⋙ moduleJ B k :=
  (openBetaModule B (pullback.snd p i) (pullback.fst p i) i p
    (pullback.condition.symm) (IsPullback.of_hasPullback p i).flip).hom ≫
  Functor.whiskerRight (Functor.whiskerLeft (modulePullback B (pullback.snd p i))
    (clopenModulePi B (squareLift k r p i h))) (moduleJ B (pullback.fst p i)) ≫
  Functor.whiskerRight
    (Functor.associator (modulePullback B (pullback.snd p i))
      (modulePullback B (squareLift k r p i h)) (moduleJ B (squareLift k r p i h))).inv
      (moduleJ B (pullback.fst p i)) ≫
  (Functor.associator
    (modulePullback B (pullback.snd p i) ⋙ modulePullback B (squareLift k r p i h))
    (moduleJ B (squareLift k r p i h)) (moduleJ B (pullback.fst p i))).hom ≫
  Functor.whiskerLeft
    (modulePullback B (pullback.snd p i) ⋙ modulePullback B (squareLift k r p i h))
    ((openBetaModuleJComp B (squareLift k r p i h) (pullback.fst p i)).hom ≫
      (singleJCongr B (pullback.lift_fst k r h)).hom) ≫
  Functor.whiskerRight
    ((moduleGComp B (squareLift k r p i h) (pullback.snd p i)).inv ≫
      (eqToIso (congrArg (modulePullback B) (pullback.lift_snd k r h))).hom) (moduleJ B k)

section DescentCalculus

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe v₁ v₂ v₃ u₁ u₂ u₃ w₁ w₂ w₃
variable {A : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} A] [Category.{v₂} D] [Category.{v₃} E]
  [aA : Abelian A] [aD : Abelian D] [aE : Abelian E]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} D]
  [HasDerivedCategory.{w₃} E]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance] clopenTowerAbelian

omit [Abelian A] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E] in
@[irreducible] private def termwiseCompHom (f : A ⥤ D) (g : D ⥤ E) (h : A ⥤ E)
    (t : f ⋙ g ⟶ h) :
    (Functor.whiskeringRight ℕᵒᵖ A D).obj f ⋙
      (Functor.whiskeringRight ℕᵒᵖ D E).obj g ⟶
      (Functor.whiskeringRight ℕᵒᵖ A E).obj h :=
  (Functor.whiskeringRightObjCompIso f g).inv ≫
    (Functor.whiskeringRight ℕᵒᵖ A E).map t

end DescentCalculus

end AlgebraicGeometry.ProEtale.StrictTower
