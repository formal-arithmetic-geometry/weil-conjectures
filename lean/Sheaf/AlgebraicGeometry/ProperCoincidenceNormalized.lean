/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper

/-! # Proper coincidence with the identity-open normalization

Source: Stacks Project, more-etale.tex, proper compactification and Tag 0F7L;
blueprint cor-cbc-proper-coincidence
(blueprint: cor-cbc-proper-coincidence).
The identifications are constructed from the identity-open adjunction, rather than
selected from the recorded Nonempty isomorphism.

## Main definitions

* `Etale.properCoincidenceIdentityOpenPlus`, `ProEtale.properCoincidenceIdentityOpenPlus`:
  the specified identity-open identifications.
* `Etale.properCoincidenceCandidatePlus`, `Etale.properCoincidenceBaseChangedPlus`:
  their canonical candidate and base-change transports.

## Main statement

* `Etale.properCoincidence_exchange`: equality with the proper-base-change exchange.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Identity-open normalization of ordinary etale compact support for a proper map.
Source: Stacks, the proper compactification convention, Tag 0F7L
(blueprint: cor-cbc-proper-coincidence). -/
def Etale.properCoincidenceIdentityOpenPlus (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
        (Compactification.ofIsProper f) ≅
      (Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus :=
  Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryPlusNatIso
          (Adjunction.leftAdjointIdIso
            (Etale.openImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} A) (𝟙 X))
            (Etale.upperStarId (ModuleCat.{u + 1} A) X)) ≪≫
        Functor.mapDerivedCategoryPlusIdIso _) _ ≪≫
    Functor.leftUnitor _

/-- The same identity-open normalization for pro-etale constant-module sheaves.
Source: blueprint proper coincidence, identity-open compactification
(blueprint: cor-cbc-proper-coincidence). -/
def ProEtale.properCoincidenceIdentityOpenPlus (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    ProEtale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
        (Compactification.ofIsProper f) ≅
      (ProEtale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus :=
  Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryPlusNatIso
          (Adjunction.leftAdjointIdIso
            (ProEtale.openImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} A) (𝟙 X))
            (ProEtale.upperStarId (ModuleCat.{u + 1} A) X)) ≪≫
        Functor.mapDerivedCategoryPlusIdIso _) _ ≪≫
    Functor.leftUnitor _

/-- Canonical proper coincidence for any ordinary etale candidate, compared to the
identity-open model by the recorded compactification comparison.
Source: Stacks 0F7I and proper compactification convention
(blueprint: cor-cbc-proper-coincidence). -/
def Etale.properCoincidenceCandidatePlus (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (c : Compactification f) :=
  Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c
      (Compactification.ofIsProper f) ≪≫
    Etale.properCoincidenceIdentityOpenPlus A f

/-- The canonical proper identification of the base-changed identity-open model.
Properness of the base-changed morphism follows from the supplied cartesian square.
Source: Stacks 0F7L, base change of a proper compactification
(blueprint: cor-cbc-proper-coincidence). -/
def Etale.properCoincidenceBaseChangedPlus (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [IsProper f] (sq : IsPullback g' f' f g) :=
  letI : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) sq inferInstance
  Etale.properCoincidenceCandidatePlus A f' ((Compactification.ofIsProper f).ofIsPullback sq)

/-- Under the identity-open identifications, the specified compact-support exchange
is the ordinary proper-base-change exchange. Consequently it is invertible.
Source: Stacks 0F7L and blueprint cor-cbc-proper-coincidence
(blueprint: cor-cbc-proper-coincidence).

Proof: use the identity-open compactification of f. Its candidate is Rf_* after the
identity-open adjunction isomorphism displayed above. Base change gives the proper
identity-open model on X', canonically compared with its displayed pullback model.
In the definition of Ex_!, the first factor is the proper unit--square--counit
exchange applied after identity extension. The second factor is the identity-open
extension base-change isomorphism. Its unit normalization cancels the identity
extension identifications. The remaining map is precisely the derived proper
exchange, with no automorphism ambiguity. The finite-torsion compact-support theorem
applies to this model, so the equal map is invertible. Equivalently apply ordinary
proper base change with the same finite ring. These constructions also cover the
empty scheme, identity base change and zero coefficient ring. -/
theorem Etale.properCoincidence_exchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [IsProper f] (sq : IsPullback g' f' f g) :
    (Functor.whiskerRight (Etale.properCoincidenceIdentityOpenPlus A f).hom
        (Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus ≫
      Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} A) sq.toCommSq =
    Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap A sq
        (Compactification.ofIsProper f) ≫
      Functor.whiskerLeft (Etale.upperStar (ModuleCat.{u + 1} A) g').mapDerivedCategoryPlus
        (Etale.properCoincidenceBaseChangedPlus A sq).hom) ∧
      IsIso (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} A) sq.toCommSq) := by
  sorry

end AlgebraicGeometry
