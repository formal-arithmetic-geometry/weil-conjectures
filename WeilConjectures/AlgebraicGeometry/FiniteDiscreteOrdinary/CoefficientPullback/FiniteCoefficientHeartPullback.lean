/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientOperationEncoding
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingPullbackFixed

/-! # The constructed inverse-image comparison on coefficient hearts -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.CoefficientPullback

section Mate
variable {C D E F : Type*}
  [Category C] [Category D] [Category E] [Category F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
  {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

end Mate

variable (A : Type u) [CommRing A]
  [TopologicalSpace A] [IsTopologicalRing A]
variable (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj R] [IsCommMonObj R]

/-- The direct-image comparison is restriction of scalars followed by the identity
on normalized sections. Source: coefficient-map naturality and normalized section actions
(blueprint: lem-sfb-finite-coefficient-heart-pullback). -/
@[irreducible] def heartPush (e : Mon.mk R ≅ Mon.mk (coefficient A))
    {X Y : Scheme.{u}} (f : X ⟶ Y) (EX : Encoding A X) (EY : Encoding A Y) :
    CondensedRing.lowerStar R f ⋙ heart A R e Y EY ≅
      heart A R e X EX ⋙ lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f := by
  unfold heart
  exact
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CondensedRing.comapLowerStarIso e.inv.hom f)
        (sectionEncoding A Y EY.ringIso ⋙ fixedRestriction A Y) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (Mod.comap (coefficientMap e.inv.hom X))
        (encodingHeartPush A Y X f EY EX) ≪≫
      (Functor.associator _ _ _).symm

/-- Conjugate the specified direct-image comparison under the geometric adjunctions.
The construction uses only proved equivalences and the identity-on-sections comparison.
Source: Stacks 03D3; uniqueness of adjoints
(blueprint: lem-sfb-finite-coefficient-heart-pullback). -/
@[irreducible] def heartPull (e : Mon.mk R ≅ Mon.mk (coefficient A))
    {X Y : Scheme.{u}} (f : X ⟶ Y) (EX : Encoding A X) (EY : Encoding A Y) :
    CondensedRing.upperStar R f ⋙ heart A R e X EX ≅
      heart A R e Y EY ⋙ upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f := by
  let β : TwoSquare (CondensedRing.lowerStar R f) (heart A R e X EX)
      (heart A R e Y EY) (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f) :=
    (heartPush A R e f EX EY).hom
  have : IsIso β.natTrans := inferInstanceAs (IsIso (heartPush A R e f EX EY).hom)
  have := inverseMate_isIso (CondensedRing.upperStarLowerStarAdjunction R f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f) β
  exact (asIso ((mateEquiv (CondensedRing.upperStarLowerStarAdjunction R f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)).symm
      β).natTrans).symm

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.CoefficientPullback
