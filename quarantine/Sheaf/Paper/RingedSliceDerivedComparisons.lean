/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q7
-/
module

public import Sheaf.Paper.RingedDerivedSliceData
import Sheaf.Paper.RingedSliceDerivedMate
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized

/-!
# Derived slice proof obligations

Source: Stacks Project, algebraization.tex, Tag 099J; Modules on Sites, Tag 04J0;
Cohomology on Sites, Tag 07A6
(blueprint: lem-weil-pbc-ringed-slice-derived-comparisons).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 256

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

variable {D C : Type u} [SmallCategory D] [SmallCategory C]
  {K : GrothendieckTopology D} {J : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous K J]
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf J CommRingCat.{u}}
  (a : R ⟶ (u.sheafPushforwardContinuous CommRingCat.{u} K J).obj S)
  [HasDerivedCategory.{w} (SheafOfModules.{u}
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))]
  [HasDerivedCategory.{w} (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rightComparisonGeneric
    {A B Av Bv : Type*} [Category A] [Category B] [Category Av] [Category Bv]
    [Abelian A] [Abelian B] [Abelian Av] [Abelian Bv]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} Av] [HasDerivedCategory.{w} Bv]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions Bv]
    (F : B ⥤ A) (Fv : Bv ⥤ Av) (rR : A ⥤ Av) (rS : B ⥤ Bv)
    [F.Additive] [Fv.Additive] [rR.Additive] [rS.Additive]
    (jR : DerivedCategory A ⥤ DerivedCategory Av)
    (jS : DerivedCategory B ⥤ DerivedCategory Bv)
    (cR : DerivedCategory.Q ⋙ jR ≅ rR.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (cS : DerivedCategory.Q ⋙ jS ≅ rS.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (c : F.mapHomologicalComplex (.up ℤ) ⋙ rR.mapHomologicalComplex (.up ℤ) ≅
      rS.mapHomologicalComplex (.up ℤ) ⋙ Fv.mapHomologicalComplex (.up ℤ))
    (hrS : ∀ I : CochainComplex B ℤ, I.IsKInjective →
      CochainComplex.IsKInjective ((rS.mapHomologicalComplex (.up ℤ)).obj I))
    (RF : DerivedCategory B ⥤ DerivedCategory A)
    (RFv : DerivedCategory Bv ⥤ DerivedCategory Av)
    (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (ηv : Fv.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RFv)
    [RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso B (.up ℤ))]
    [RFv.IsRightDerivedFunctor ηv (HomologicalComplex.quasiIso Bv (.up ℤ))] :
    ∃ beta : RF ⋙ jR ≅ jS ⋙ RFv, ∀ I : CochainComplex B ℤ,
      jR.map (η.app I) ≫ beta.hom.app (DerivedCategory.Q.obj I) ≫
        RFv.map (cS.hom.app I) =
      cR.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map (c.hom.app I) ≫
        ηv.app ((rS.mapHomologicalComplex (.up ℤ)).obj I) := by
  let cc := (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ rR)) (.up ℤ)).symm
  let etaR : (F ⋙ rR).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (RF ⋙ jR) :=
    Functor.whiskerRight cc.hom DerivedCategory.Q ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ)) cR.inv ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight η jR ≫
      (Functor.associator _ _ _).hom
  let etaS : (F ⋙ rR).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (jS ⋙ RFv) :=
    Functor.whiskerRight cc.hom DerivedCategory.Q ≫
      Functor.whiskerRight c.hom DerivedCategory.Q ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (rS.mapHomologicalComplex (.up ℤ)) ηv ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight cS.inv RFv ≫
      (Functor.associator _ _ _).hom
  have hR : (RF ⋙ jR).IsRightDerivedFunctor etaR
      (HomologicalComplex.quasiIso B (.up ℤ)) := by
    apply (CategoryTheory.derives (F ⋙ rR)).isRightDerivedFunctor_of_isIso etaR
    intro I
    have : IsIso (η.app I.obj) :=
      (CategoryTheory.derives F).isIso_of_isRightDerivedFunctor η I
    change IsIso (etaR.app I.obj)
    dsimp only [etaR, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app]
    infer_instance
  have hS : (jS ⋙ RFv).IsRightDerivedFunctor etaS
      (HomologicalComplex.quasiIso B (.up ℤ)) := by
    apply (CategoryTheory.derives (F ⋙ rR)).isRightDerivedFunctor_of_isIso etaS
    intro I
    have : CochainComplex.IsKInjective ((rS.mapHomologicalComplex (.up ℤ)).obj I.obj) :=
      hrS I.obj I.property
    have : IsIso (ηv.app ((rS.mapHomologicalComplex (.up ℤ)).obj I.obj)) :=
      (CategoryTheory.derives Fv).isIso_of_isRightDerivedFunctor ηv
        (CochainComplex.KInjectives.mk ((rS.mapHomologicalComplex (.up ℤ)).obj I.obj))
    change IsIso (etaS.app I.obj)
    dsimp only [etaS, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app]
    simp only [Category.id_comp, Category.comp_id]
    infer_instance
  let beta := Functor.rightDerivedUnique (RF ⋙ jR) (jS ⋙ RFv) etaR etaS
    (HomologicalComplex.quasiIso B (.up ℤ))
  refine ⟨beta, ?_⟩
  intro I
  have hb := Functor.rightDerivedNatTrans_app (RF ⋙ jR) (jS ⋙ RFv) etaR etaS
    (HomologicalComplex.quasiIso B (.up ℤ)) (𝟙 _) I
  simp only [NatTrans.id_app, Category.id_comp] at hb
  change etaR.app I ≫ beta.hom.app (DerivedCategory.Q.obj I) = etaS.app I at hb
  dsimp only [etaR, etaS, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app] at hb
  have hcc : cc.hom.app I = 𝟙 _ := rfl
  rw [hcc, DerivedCategory.Q.map_id] at hb
  dsimp only [Functor.comp_obj] at hb
  simp only [Category.id_comp, Category.comp_id] at hb
  have hc := congrArg (fun f ↦ cR.hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫ f ≫ RFv.map (cS.hom.app I)) hb
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app] at hc
  erw [RFv.map_id] at hc
  dsimp only [Functor.comp_obj] at hc
  simpa only [Category.assoc, Category.id_comp,
    Category.comp_id, Iso.hom_inv_id_app_assoc] using hc

set_option backward.isDefEq.respectTransparency.types false in
/-- The direct-image slice comparison is normalized on all complexes, and its
inverse adjunction mate is invertible.
Source: Stacks Tags 04J0, 08FI and 07A6
(blueprint: lem-weil-pbc-ringed-slice-derived-comparisons).
Proof:
1. The K-injective derivability structure applies to ordinary pushforward followed
by restriction. Its comparison to derived pushforward followed by derived
restriction is invertible on K-injectives. Restriction preserves K-injectives,
so the comparison to restriction followed by local derived pushforward is also
invertible there. The good-object criterion proves both derived universal
properties. Right-derived uniqueness supplies beta, and its factorization
equation, conjugated by the restriction factorizations, gives the required
normalization on every complex.
2. Apply ringedSliceDerivedMate_isIso to this normalized beta. -/
theorem ringedSliceDerivedComparisons
    [PreservesFiniteLimits (u.sheafPullback (Type u) K J)] (V : D)
    [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]
    [PreservesFiniteLimits
      ((Over.post (X := V) u).sheafPullback (Type u) (K.over V) (J.over (u.obj V)))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose K (forget₂ CommRingCat RingCat)).obj R).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).over (u.obj V)))]
    (e : RingedSliceDerivedImage.{u, w} u a)
    (l : RingedSliceDerivedImage.{u, w} (Over.post (X := V) u)
      (localizedRingedSiteMap u a V)) :
    ∃ beta : e.right ⋙ ringedSliceRestriction.{u, w} R V ≅
        ringedSliceRestriction.{u, w} S (u.obj V) ⋙ l.right,
      IsIso (((mateEquiv e.adjunction l.adjunction).symm
        (TwoSquare.mk _ _ _ _ beta.hom)).natTrans) ∧
      (∀ (I : CochainComplex (SheafOfModules.{u}
              ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) ℤ),
            (ringedSliceRestriction.{u, w} R V).map
                (X := DerivedCategory.Q.{w}.obj
                  (((ringedSliceModulePushforward u a).mapHomologicalComplex (.up ℤ)).obj I))
                (Y := e.right.obj (DerivedCategory.Q.{w}.obj I)) (e.eta.app I) ≫
              beta.hom.app (DerivedCategory.Q.{w}.obj I) ≫
              l.right.map
                (X := (ringedSliceRestriction.{u, w} S (u.obj V)).obj
                  (DerivedCategory.Q.{w}.obj I))
                (Y := DerivedCategory.Q.{w}.obj
                  ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} J S (u.obj V)).obj I))
                ((ringedSliceRestrictionFactors.{u, w} S (u.obj V)).hom.app I) =
            (ringedSliceRestrictionFactors.{u, w} R V).hom.app
              (((ringedSliceModulePushforward u a).mapHomologicalComplex (.up ℤ)).obj I) ≫
              DerivedCategory.Q.{w}.map (ringedSlicePushforwardComplexIso u a V I).hom ≫
              l.eta.app
              ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} J S (u.obj V)).obj I)) := by
  let := e.isRightDerived
  let := l.isRightDerived
  let := (grothendieckAbelian_and_functorial_kInjective_resolutions J S).1
  let := (grothendieckAbelian_and_functorial_kInjective_resolutions
    (J.over (u.obj V)) (S.over (u.obj V))).1
  let := (ringedOverFunctor_exactGeneral.{u, u, u, u}
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R) V).1
  let := (ringedOverFunctor_exactGeneral.{u, u, u, u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (u.obj V)).1
  obtain ⟨beta, hb⟩ := rightComparisonGeneric
    (ringedSliceModulePushforward u a)
    (ringedSliceModulePushforward (Over.post (X := V) u) (localizedRingedSiteMap u a V))
    (overFunctor ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R) V)
    (overFunctor ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (u.obj V))
    (ringedSliceRestriction R V) (ringedSliceRestriction S (u.obj V))
    (ringedSliceRestrictionFactors R V) (ringedSliceRestrictionFactors S (u.obj V))
    (NatIso.ofComponents (fun I ↦ ringedSlicePushforwardComplexIso u a V I) (by
      intro I I' f
      ext n
      rfl)) (by
      intro I hI
      let := hI
      exact isKInjective_restrict_localized.{u, u} _ _ inferInstance I)
    e.right l.right e.eta l.eta
  refine ⟨beta, ringedSliceDerivedMate_isIso u a V e l beta ?_, ?_⟩
  · exact hb
  · exact hb

end SheafOfModules
