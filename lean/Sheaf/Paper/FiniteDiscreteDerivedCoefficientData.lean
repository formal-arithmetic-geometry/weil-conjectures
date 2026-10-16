/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2 -/
module

public import Sheaf.Paper.FiniteDiscreteCoefficientEncoding
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.LowerShriek.Defs

/-! # Coherent inverse-image comparisons for the common coefficient encoding -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

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

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- Pullback comparisons with invertible right mates and coherent composition. -/
structure CoefficientComparisonData
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
  pushforward : ∀ {S T : Scheme.{u}} (h : S ⟶ T) [QuasiCompact h] [QuasiSeparated h],
    R+(Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h) ⋙
        F T ≅
      F S ⋙
        coefficientDerivedLowerStar Λ h
  unit : ∀ {S T : Scheme.{u}} (h : S ⟶ T) [QuasiCompact h] [QuasiSeparated h]
      (K : FiniteDiscreteEtalePlus B T),
    (F T).map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus
          (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).unit.app K) ≫
      (pushforward h).hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).obj K) ≫
      (coefficientDerivedLowerStar Λ h).map
        ((pullback h).hom.app K) =
    (coefficientDerivedAdjunction Λ h).unit.app
      ((F T).obj K)
  counit : ∀ {S T : Scheme.{u}} (h : S ⟶ T) [QuasiCompact h] [QuasiSeparated h]
      (K : FiniteDiscreteEtalePlus B S),
    (coefficientDerivedUpperStar Λ h).map
        ((pushforward h).hom.app K) ≫
      (coefficientDerivedAdjunction Λ h).counit.app
        ((F S).obj K) =
    (pullback h).inv.app
        (R+(Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).obj K) ≫
      (F S).map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus
          (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).counit.app K)
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

/-- Coherent inverse-image comparisons whose canonical right mates are invertible. -/
structure CoefficientPullbackData
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
  rightMate : ∀ {S T : Scheme.{u}} (h : S ⟶ T) [QuasiCompact h] [QuasiSeparated h],
    IsIso (mateEquiv
      (Etale.derivedUpperStarLowerStarAdjunctionPlus
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) h)
      (coefficientDerivedAdjunction Λ h)
      (TwoSquare.mk _ _ _ _ (pullback h).inv)).natTrans
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

/-- Form the direct-image isomorphisms by taking canonical mates. -/
noncomputable def CoefficientPullbackData.toComparisonData
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ]
    {F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T))} (P : CoefficientPullbackData B Λ F) :
    CoefficientComparisonData B Λ F where
  pullback := P.pullback
  pushforward h _ _ := by
    let := P.rightMate h
    exact asIso (mateEquiv
      (Etale.derivedUpperStarLowerStarAdjunctionPlus
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) h)
      (coefficientDerivedAdjunction Λ h)
      (TwoSquare.mk _ _ _ _ (P.pullback h).inv)).natTrans
  unit h _ _ K := by
    let := P.rightMate h
    dsimp only [asIso_hom]
    rw [reassoc_of% (unit_mateEquiv
      (Etale.derivedUpperStarLowerStarAdjunctionPlus
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) h)
      (coefficientDerivedAdjunction Λ h)
      (TwoSquare.mk _ _ _ _ (P.pullback h).inv) K)]
    simp only [← Functor.map_comp, Iso.inv_hom_id_app]
    change (coefficientDerivedAdjunction Λ h).unit.app ((F _).obj K) ≫
      (coefficientDerivedLowerStar Λ h).map
        (𝟙 ((coefficientDerivedUpperStar Λ h).obj ((F _).obj K))) = _
    rw [(coefficientDerivedLowerStar Λ h).map_id]
    exact Category.comp_id _
  counit h _ _ K := by
    let := P.rightMate h
    exact mateEquiv_counit
      (Etale.derivedUpperStarLowerStarAdjunctionPlus
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) h)
      (coefficientDerivedAdjunction Λ h)
      (TwoSquare.mk _ _ _ _ (P.pullback h).inv) K
  square := P.square

/-- The comparison interface for the concrete finite-discrete realization family. -/
abbrev FiniteDiscreteCoefficientComparisonData
    (E : ∀ T : Scheme.{u},
      FiniteDiscreteProEtaleSheaves B T ≌ FiniteDiscreteInternalModules B T) :=
  CoefficientPullbackData B (Profinite.continuousMapRingObj B)
    (fun T ↦ finiteDiscreteRealization B T (E T))

variable
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
  [IsMonHom eR.hom]
  (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
    Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))

/-- The common sectionwise encoding intertwines pullback, with invertible canonical
right mates on qcqs morphisms.
Source: Bhatt--Scholze, Proposition 5.3.2 and Lemmas 5.4.1 and 5.4.3
(blueprint: lem-weil-pbc-finite-discrete-derived-coefficient-data).

Proof in words. First work with ordinary module-valued pro-etale sheaves. Restriction
commutes with the etale/pro-etale comparison pushforward. Conjugating its natural
isomorphism gives the inverse-image comparison. The restriction identity is coherent
with composition; conjugation, exact derivation, and the canonical composition
isomorphisms preserve this coherence. This proves the displayed square equation,
including the equality transport supplied by sq.w. Encode internal modules using the
same functor G on every object of every site. Its forgetful equality ensures that its
maps on sections and restrictions are the original additive maps. The constant ring
identifications are all pulled back from eR at the profinite point. Their monoidal
pullback compatibility therefore identifies the scalar actions in these comparisons.
Transport the comparison through the coefficient equivalences and apply the exact
functors on derived categories, identifying the total left derived internal pullback
with its levelwise functor. For a qcqs morphism, the canonical right mate is the
bounded-below direct-image comparison, transported through those same equivalences.
It is invertible by the finite coefficient direct-image comparison. Restriction to D+
and its inclusion into the full derived category preserve the mate equation. Empty
schemes and the zero ring cause no exception: all identities come from adjunctions. -/
theorem finiteDiscreteCoefficient_derivedComparisonData [DiscreteTopology B] [Finite B] :
    Nonempty (FiniteDiscreteCoefficientComparisonData B
      (finiteDiscreteCoefficientEquivalence B eR G hG)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
