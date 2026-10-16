/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2 -/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Sheaf.Paper.FiniteDiscreteRealizationFunctor

/-! # Derived functor interfaces for condensed coefficient comparisons

Source: the existing internal-module derived adjunction and pullback composition
isomorphisms (blueprint: def-weil-pbc-coefficient-derived-functor-api).
The four functor definitions are moved verbatim from FiniteDiscreteDerivedCoefficientData.
The partial comparison record keeps only inverse-image data and square coherence.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance coefficientProfiniteEssentiallySmall :
    EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section DerivedFunctorAPI

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {S T : Scheme.{u}} (h : S ⟶ T)

/-- The derived pullback with its derivability instances fixed at a generic coefficient ring. -/
noncomputable def coefficientDerivedUpperStar :
    DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :=
  L((h)^*⟦Λ⟧)

/-- The derived pushforward with its derivability instances fixed at a generic coefficient ring. -/
noncomputable def coefficientDerivedLowerStar :
    DerivedCategory (Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :=
  R((h)_*⟦Λ⟧)

/-- The derived coefficient adjunction, with the cached derived functor interfaces. -/
@[irreducible] noncomputable def coefficientDerivedAdjunction :
    coefficientDerivedUpperStar Λ h ⊣ coefficientDerivedLowerStar Λ h :=
  derivedUpperStarLowerStarAdjunction Λ h

end DerivedFunctorAPI

/-- The ambient derived pullback comparison, before restricting to constructible objects. -/
@[irreducible] noncomputable def coefficientAmbientSquare
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g) :
    coefficientDerivedUpperStar Λ g ⋙
        coefficientDerivedUpperStar Λ f' ≅
      coefficientDerivedUpperStar Λ f ⋙
        coefficientDerivedUpperStar Λ g' :=
  (leftDerivedUpperStarComp Λ f' g).symm ≪≫
    eqToIso (by rw [← sq.w]) ≪≫
    leftDerivedUpperStarComp Λ g' f

/-- Inverse-image data and square coherence, without a condition on right mates. -/
structure CoefficientCoherentPullbackData (B : Type) [CommRing B]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T))) where
  pullback : ∀ {S T : Scheme.{u}} (h : S ⟶ T),
    D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h) ⋙
        F S ≅
      F T ⋙
        coefficientDerivedUpperStar Λ h
  square : ∀ {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
      {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
      (K : FiniteDiscreteEtalePlus B Y),
    (F X').map
        ((Etale.pullbackSquareComparison (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq).hom.app K) ≫
      (pullback g').hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f).obj K) ≫
      (coefficientDerivedUpperStar Λ g').map
        ((pullback f).hom.app K) =
    (pullback f').hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).obj K) ≫
      (coefficientDerivedUpperStar Λ f').map
        ((pullback g).hom.app K) ≫
      (coefficientAmbientSquare Λ sq).hom.app
        ((F Y).obj K)

/-- Coherent inverse-image data for a finite-discrete realization family. -/
abbrev FiniteDiscreteCoherentPullbacks (B : Type) [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B]
    (E : ∀ T : Scheme.{u},
      FiniteDiscreteProEtaleSheaves B T ≌ FiniteDiscreteInternalModules B T) :=
  CoefficientCoherentPullbackData B (Profinite.continuousMapRingObj B)
    (fun T ↦ finiteDiscreteRealization B T (E T))

end AlgebraicGeometry.ProEtale.CondensedRing
