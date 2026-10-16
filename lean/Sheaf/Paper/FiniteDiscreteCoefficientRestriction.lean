/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4 -/
module

public import Sheaf.Paper.FiniteDiscreteCoefficientEncoding
public import Sheaf.Paper.CoefficientDerivedFunctorAPI
import all Sheaf.Paper.FiniteDiscreteRestrictionEncoding

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

attribute [local semireducible] finiteDiscreteCoefficientEquivalence

open CategoryTheory.ConstantInternalModuleSheafEncoding

private theorem proEtMonoidalW (T : Scheme.{u}) :
    ((ProEt.topology T).W (A := Ab.{u + 1})).IsMonoidal :=
  GrothendieckTopology.W.monoidal (J := ProEt.topology T) (A := Ab.{u + 1})

attribute [local instance] proEtMonoidalW

-- The inverse encoding has the sectionwise forgetful comparison used in its construction.
private noncomputable def inverseForgetIso (T : Scheme.{u}) :
    (finiteDiscreteCoefficientEquivalence B eR G hG T).inverse ⋙
      sheafCompose (ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}) ≅ Mod.forget _ := by
  letI : ((ProEt.topology T).W (A := Ab.{u + 1})).IsMonoidal :=
    GrothendieckTopology.W.monoidal (J := ProEt.topology T) (A := Ab.{u + 1})
  exact Functor.isoWhiskerLeft (Mod.comap (finiteDiscreteSchemeRingIso B T eR).hom)
    (sheafEncodingForgetIso (ProEt.topology T) (ULift.{u + 1} B) G hG)

private lemma compositeInverseUnit {C D E : Type*} [Category C] [Category D] [Category E]
    (H : C ≌ D) (K : E ≌ C) (N : D) :
    (H.symm.trans K.symm).unitIso.inv.app N =
      H.functor.map (K.counitIso.hom.app (H.inverse.obj N)) ≫ H.counitIso.hom.app N := by
  simp [CategoryTheory.Equivalence.trans]

private lemma inverseForgetIso_unit (T : Scheme.{u}) (N : FiniteDiscreteProEtaleSheaves B T) :
    (inverseForgetIso B eR G hG T).inv.app
        ((finiteDiscreteCoefficientEquivalence B eR G hG T).functor.obj N) ≫
      (sheafCompose (ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})).map
        ((finiteDiscreteCoefficientEquivalence B eR G hG T).unitIso.inv.app N) =
      (finiteDiscreteCoefficientEquivalenceForgetIso B eR G hG T).hom.app N := by
  let : ((ProEt.topology T).W (A := Ab.{u + 1})).IsMonoidal :=
    GrothendieckTopology.W.monoidal (J := ProEt.topology T) (A := Ab.{u + 1})
  let H := (sheafEncoding (ProEt.topology T) (ULift.{u + 1} B) G hG).asEquivalence
  let C := Mod.comapEquivalenceOfIsIso (finiteDiscreteSchemeRingIso B T eR).hom
  let U := sheafCompose (ProEt.topology T)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})
  let p : H.functor ⋙ U ≅ Mod.forget _ :=
    sheafEncodingForgetIso (ProEt.topology T) (ULift.{u + 1} B) G hG
  change p.inv.app (C.functor.obj (C.inverse.obj (H.inverse.obj N))) ≫
    U.map ((H.symm.trans C.symm).unitIso.inv.app N) =
      p.inv.app (H.inverse.obj N) ≫ U.map (H.counitIso.hom.app N)
  let c := C.counitIso.hom.app (H.inverse.obj N)
  have hc : c.hom = 𝟙 _ := by
    simp [c, C, Mod.comapEquivalenceOfIsIso, CategoryTheory.Equivalence.mk,
      Mod.comapComp, Mod.comapCongr, Mod.comapId]
    rfl
  have hu : U.map ((H.symm.trans C.symm).unitIso.inv.app N) =
      U.map (H.functor.map c) ≫ U.map (H.counitIso.hom.app N) :=
    (congrArg U.map (compositeInverseUnit H C N)).trans (U.map_comp _ _)
  have hn : c.hom ≫ p.inv.app (H.inverse.obj N) =
      p.inv.app (C.functor.obj (C.inverse.obj (H.inverse.obj N))) ≫
        U.map (H.functor.map c) := p.inv.naturality c
  calc
    _ = p.inv.app (C.functor.obj (C.inverse.obj (H.inverse.obj N))) ≫
        (U.map (H.functor.map c) ≫ U.map (H.counitIso.hom.app N)) :=
      congrArg (p.inv.app (C.functor.obj (C.inverse.obj (H.inverse.obj N))) ≫ ·) hu
    _ = (p.inv.app (C.functor.obj (C.inverse.obj (H.inverse.obj N))) ≫
        U.map (H.functor.map c)) ≫ U.map (H.counitIso.hom.app N) :=
      (Category.assoc _ _ _).symm
    _ = (c.hom ≫ p.inv.app (H.inverse.obj N)) ≫ U.map (H.counitIso.hom.app N) :=
      congrArg (· ≫ U.map (H.counitIso.hom.app N)) hn.symm
    _ = _ := by rw [hc, Category.id_comp]

private lemma sheafPreimage_hom {C A : Type*} [Category C] [Category A]
    (J : GrothendieckTopology C) (hF : (sheafToPresheaf J A).FullyFaithful)
    {X Y : Sheaf J A} (f : X.obj ⟶ Y.obj) : (hF.preimage f).hom = f :=
  hF.map_preimage f

private noncomputable abbrev rawModule (T : Scheme.{u})
    (M : FiniteDiscreteInternalModules B T) (V : T.ProEtᵒᵖ) :
    Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) :=
  ((presheafToFunctor (C := T.ProEtᵒᵖ) (ULift.{u + 1} B)).obj
    ((moduleLocalizationRight (ProEt.topology T)
      (A (C := T.ProEtᵒᵖ) (ULift.{u + 1} B))).obj
      ((Mod.comap (finiteDiscreteSchemeRingIso B T eR).hom).obj M))).obj V

-- The existing comparison is G applied to identity additive maps. Naturality of hG
-- identifies those maps after forgetting, including the equality transports.
private lemma inverseForgetIso_pushforward (T S : Scheme.{u}) (h : S ⟶ T)
    (M : FiniteDiscreteInternalModules B S) :
    (sheafCompose (ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})).map
        (encodingPushforwardIso B eR G hG T S h M).hom ≫
      (ProEtale.lowerStar Ab.{u + 1} h).map ((inverseForgetIso B eR G hG S).hom.app M) =
    (inverseForgetIso B eR G hG T).hom.app
      ((lowerStar (Profinite.continuousMapRingObj B) h).obj M) := by
  apply (sheafToPresheaf (ProEt.topology T) Ab.{u + 1}).map_injective
  apply NatTrans.ext
  funext V
  simp only [Functor.map_comp, NatTrans.comp_app]
  unfold inverseForgetIso sheafEncodingForgetIso encodingPushforwardIso
  simp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.FullyFaithful.preimageIso_hom]
  simp only [Functor.FullyFaithful.whiskeringRight_preimage_app,
    Functor.FullyFaithful.map_preimage]
  dsimp only [sheafCompose, ObjectProperty.lift, Functor.comp_map,
    Functor.whiskeringRight_obj_map, Functor.whiskerRight_app, ObjectProperty.ι_map,
    ProEtale.lowerStar]
  simp only [Functor.sheafPushforwardContinuous_map_hom_app]
  simp only [id_eq, ObjectProperty.homMk_hom, Functor.whiskerRight_app,
    Functor.FullyFaithful.preimageIso_hom, sheafPreimage_hom,
    NatIso.ofComponents_hom_app, Functor.mapIso_hom]
  simp only [eqToIso.hom, eqToHom_app]
  let W : S.ProEtᵒᵖ := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).op.obj V
  let a : rawModule B eR T ((lowerStar (Profinite.continuousMapRingObj B) h).obj M) V ≅
      rawModule B eR S M W := Mod.isoMk (Iso.refl _) (by
    simp only [Iso.refl_hom, Category.comp_id, whiskerLeft_id, Category.id_comp]
    exact push_action B eR T S h M V)
  change (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}).map
    (G.map a.hom) ≫ eqToHom _ = eqToHom _
  have ha := (eqToIso hG).hom.naturality a.hom
  change (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}).map
    (G.map a.hom) ≫ (eqToIso hG).hom.app _ =
      (eqToIso hG).hom.app _ ≫ a.hom.hom at ha
  have hid : a.hom.hom = 𝟙 _ := rfl
  rw [hid] at ha
  have ha' := ha.trans (Category.comp_id _)
  simpa only [eqToIso.hom, eqToHom_app] using ha'

private lemma inverseForgetIso_unit_hom (T : Scheme.{u})
    (N : FiniteDiscreteProEtaleSheaves B T) :
    (inverseForgetIso B eR G hG T).hom.app
        ((finiteDiscreteCoefficientEquivalence B eR G hG T).functor.obj N) ≫
      (finiteDiscreteCoefficientEquivalenceForgetIso B eR G hG T).hom.app N =
    (sheafCompose (ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})).map
        ((finiteDiscreteCoefficientEquivalence B eR G hG T).unitIso.inv.app N) := by
  rw [← inverseForgetIso_unit B eR G hG T N, Iso.hom_inv_id_app_assoc]

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
      e.hom ≫ Mod.act P.X := by
  let ES := finiteDiscreteCoefficientEquivalence B eR G hG S
  let ET := finiteDiscreteCoefficientEquivalence B eR G hG T
  let US := sheafCompose (ProEt.topology S)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})
  let UT := sheafCompose (ProEt.topology T)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})
  let F := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h
  let H := ProEtale.lowerStar Ab.{u + 1} h
  let M := (lowerStar (Profinite.continuousMapRingObj B) h).obj (ES.functor.obj N)
  let P := ET.functor.obj (F.obj N)
  let rS : ES.inverse ⋙ US ≅ Mod.forget _ := inverseForgetIso B eR G hG S
  let rT : ET.inverse ⋙ UT ≅ Mod.forget _ := inverseForgetIso B eR G hG T
  let qS : ES.functor ⋙ Mod.forget _ ≅ US :=
    finiteDiscreteCoefficientEquivalenceForgetIso B eR G hG S
  let qT : ET.functor ⋙ Mod.forget _ ≅ UT :=
    finiteDiscreteCoefficientEquivalenceForgetIso B eR G hG T
  let k : ET.inverse.obj M ≅ F.obj (ES.inverse.obj (ES.functor.obj N)) :=
    encodingPushforwardIso B eR G hG T S h (ES.functor.obj N)
  let a : ET.inverse.obj M ⟶ ET.inverse.obj P :=
    k.hom ≫ F.map (ES.unitIso.inv.app N) ≫ ET.unitIso.hom.app (F.obj N)
  -- Full faithfulness gives a linear map; its normalization is checked below.
  let φ : M ⟶ P := ET.inverse.preimage a
  have hφ : ET.inverse.map φ = a := ET.inverse.map_preimage a
  have hn : UT.map (ET.inverse.map φ) ≫ rT.hom.app P =
      rT.hom.app M ≫ φ.hom := rT.hom.naturality φ
  have hs : rS.hom.app (ES.functor.obj N) ≫ qS.hom.app N =
      US.map (ES.unitIso.inv.app N) := inverseForgetIso_unit_hom B eR G hG S N
  have ht : rT.hom.app P ≫ qT.hom.app (F.obj N) =
      UT.map (ET.unitIso.inv.app (F.obj N)) :=
    inverseForgetIso_unit_hom B eR G hG T (F.obj N)
  have hk : UT.map k.hom ≫ H.map (rS.hom.app (ES.functor.obj N)) = rT.hom.app M :=
    inverseForgetIso_pushforward B eR G hG T S h (ES.functor.obj N)
  have he : φ.hom ≫ qT.hom.app (F.obj N) = H.map (qS.hom.app N) := by
    apply (cancel_epi (rT.hom.app M)).mp
    calc
      _ = UT.map (ET.inverse.map φ) ≫ rT.hom.app P ≫ qT.hom.app (F.obj N) := by
        rw [← Category.assoc, ← hn, Category.assoc]
      _ = UT.map a ≫ UT.map (ET.unitIso.inv.app (F.obj N)) := by
        rw [hφ, ht]
      _ = UT.map k.hom ≫ UT.map (F.map (ES.unitIso.inv.app N)) := by
        dsimp only [a]
        rw [UT.map_comp, UT.map_comp]
        simp only [Category.assoc, ← UT.map_comp, Iso.hom_inv_id_app]
        exact congrArg UT.map (congrArg (k.hom ≫ ·) (Category.comp_id _))
      _ = UT.map k.hom ≫ H.map (US.map (ES.unitIso.inv.app N)) := rfl
      _ = UT.map k.hom ≫ H.map (rS.hom.app (ES.functor.obj N) ≫ qS.hom.app N) := by
        rw [hs]
      _ = _ := by rw [H.map_comp, ← Category.assoc, hk]
  have he0 : ((finiteDiscreteCoefficientRestrictionForgetIso B eR G hG h).app N).hom =
      H.map (qS.hom.app N) ≫ qT.inv.app (F.obj N) := by
    simp only [Functor.comp_obj, finiteDiscreteCoefficientRestrictionForgetIso, eqToIso_refl,
      Functor.isoWhiskerLeft_refl, Iso.refl_trans, NatIso.trans_app, Iso.trans_hom,
      Iso.app_hom, Iso.symm_hom, Functor.associator_inv_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      H, F, qS, qT]
    exact Category.id_comp _
  have he' : ((finiteDiscreteCoefficientRestrictionForgetIso B eR G hG h).app N).hom =
      φ.hom := by
    rw [he0, ← he, Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  change Mod.act M.X ≫ _ = _
  rw [he']
  exact Mod.act_hom φ

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
