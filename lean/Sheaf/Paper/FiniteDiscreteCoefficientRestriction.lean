/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4 -/
module

public import Sheaf.Paper.FiniteDiscreteCoefficientEncoding
public import Sheaf.Paper.CoefficientDerivedFunctorAPI

/-! # Restriction comparison for the finite discrete coefficient realization -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [local instance] coefficientProfiniteEssentiallySmall

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

variable
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
  [IsMonHom eR.hom]
  (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
    Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))

/-- The canonical additive comparison for restriction under the coefficient encoding. -/
noncomputable def finiteDiscreteCoefficientRestrictionForgetIso
    {S T : Scheme.{u}} (h : S ⟶ T) :
    (finiteDiscreteCoefficientEquivalence B eR G hG S).functor ⋙
        lowerStar (Profinite.continuousMapRingObj B) h ⋙ Mod.forget _ ≅
      ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h ⋙
        (finiteDiscreteCoefficientEquivalence B eR G hG T).functor ⋙ Mod.forget _ := by
  let E (X : Scheme.{u}) := finiteDiscreteCoefficientEquivalence B eR G hG X
  let U (X : Scheme.{u}) := sheafCompose (ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})
  let F := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h
  let H := ProEtale.lowerStar Ab.{u + 1} h
  let e : U S ⋙ H ≅ F ⋙ U T := Iso.refl _
  exact Functor.isoWhiskerLeft (E S).functor
      (eqToIso (lowerStar_comp_forget (Profinite.continuousMapRingObj B) h)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (finiteDiscreteCoefficientEquivalenceForgetIso B eR G hG S) H ≪≫
    e ≪≫ Functor.isoWhiskerLeft F
      (finiteDiscreteCoefficientEquivalenceForgetIso B eR G hG T).symm

/-- The normalized additive restriction comparison is linear over the coefficient ring.
Source: Bhatt--Scholze, Proposition 5.3.2, sectionwise module encoding
(blueprint: lem-weil-pbc-finite-discrete-restriction-linearity).

Proof in words. Under the sectionwise encoding, the action of the sheafified constant
ring is the original module action; the equality hG identifies every underlying additive
map. Restriction evaluates at the base-changed object and therefore preserves this action.
The ring identifications at S and T are pulled back from the same eR. Naturality of the
constant-sheaf pullback comparison identifies the restriction of the ring identification
at S with that at T, followed by the coefficient unit condensedPushforwardHom. Thus the
additive comparison intertwines the two scalar actions, giving the displayed equation.
-/
theorem finiteDiscreteCoefficientRestrictionForgetIso_linear
    {S T : Scheme.{u}} (h : S ⟶ T) (N : FiniteDiscreteProEtaleSheaves B S) :
    let M := (lowerStar (Profinite.continuousMapRingObj B) h).obj
      ((finiteDiscreteCoefficientEquivalence B eR G hG S).functor.obj N)
    let P := (finiteDiscreteCoefficientEquivalence B eR G hG T).functor.obj
      ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).obj N)
    let e := (finiteDiscreteCoefficientRestrictionForgetIso B eR G hG h).app N
    Mod.act M.X ≫ e.hom = (condensedRingObj (Profinite.continuousMapRingObj B) T) ◁
      e.hom ≫ Mod.act P.X := by sorry

/-- The sectionwise encoding commutes with ordinary pro-etale restriction. -/
@[irreducible] noncomputable def finiteDiscreteCoefficientRestrictionIso
    {S T : Scheme.{u}} (h : S ⟶ T) :
    (finiteDiscreteCoefficientEquivalence B eR G hG S).functor ⋙
        lowerStar (Profinite.continuousMapRingObj B) h ≅
      ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h ⋙
        (finiteDiscreteCoefficientEquivalence B eR G hG T).functor :=
  NatIso.ofComponents (fun N ↦ Mod.isoMk
      ((finiteDiscreteCoefficientRestrictionForgetIso B eR G hG h).app N)
      (finiteDiscreteCoefficientRestrictionForgetIso_linear B eR G hG h N))
    (fun φ ↦ Mod.hom_ext _ _
      ((finiteDiscreteCoefficientRestrictionForgetIso B eR G hG h).hom.naturality φ))

end AlgebraicGeometry.ProEtale.CondensedRing
