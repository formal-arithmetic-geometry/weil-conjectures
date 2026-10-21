/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.RingedToposBinaryDescentDefs
import Sheaf.CategoryTheory.RingedToposCrossDirectImageRestriction
import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
import Sheaf.Algebra.Homology.SitePerfectModelRestriction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Restriction of direct images for subterminals

Source: Stacks Project, Cohomology, Tag 08DG.
-/

@[expose] public section
universe u v r w s m
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
set_option autoImplicit false
set_option synthInstance.maxSize 4096

set_option backward.isDefEq.respectTransparency false

private theorem module_hasKInjective
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J RingCat.{r}) :
    Abelian.HasKInjectiveResolutions (SheafOfModules.{max u v r} R) := by
  let : IsGrothendieckAbelian.{max u v r} (SheafOfModules.{max u v r} R) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u, v, r, 0} J R
  infer_instance

private theorem over_forget_full
    {C : Type u} [Category.{v} C] [HasTerminal C]
    (U : C) [Mono (terminal.from U)] : (Over.forget U).Full := by
  constructor
  intro X Y f
  refine ⟨Over.homMk f ?_, rfl⟩
  apply (cancel_mono (terminal.from U)).mp
  simp

private theorem open_counit_iso
    {C : Type u} [Category.{v} C] [HasTerminal C] [HasBinaryProducts C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r}) (U : C)
    [Mono (terminal.from U)] :
    IsIso (SheafOfModules.overPushforwardOverAdj.{m} (R := R) U).counit := by
  have := over_forget_full U
  have : IsIso (Over.forgetAdjStar U).unit := inferInstance
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  apply (isIso_iff_of_reflects_iso _ (SheafOfModules.forget (R.over U))).mp
  apply (isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)).mp
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (M.val.presheaf.map ((Over.forgetAdjStar U).unit.app X.unop).op)
  exact (ConcreteCategory.bijective_of_isIso _)
set_option backward.isDefEq.respectTransparency false in
private noncomputable def restrictionDerivedIso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (T : DerivedCategory A ⥤ DerivedCategory B)
    (q : DerivedCategory.Q ⋙ T ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :
    F.mapDerivedCategory ≅ T := by
  let : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) T := ⟨q⟩
  exact Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory T (Iso.refl _)

private theorem derived_open_counit_iso
    {C : Type u} [Category.{v} C] [HasTerminal C] [HasBinaryProducts C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r}) (U : C)
    [Mono (terminal.from U)]
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    [HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    [HasDerivedCategory.{w} (SheafOfModules.{max u v r} R)]
    [HasDerivedCategory.{w} (SheafOfModules.{max u v r} (R.over U))]
    (T : DerivedCategory (SheafOfModules.{max u v r} R) ⥤
      DerivedCategory (SheafOfModules.{max u v r} (R.over U)))
    (G : DerivedCategory (SheafOfModules.{max u v r} (R.over U)) ⥤
      DerivedCategory (SheafOfModules.{max u v r} R))
    (adj : T ⊣ G)
    (q : DerivedCategory.Q ⋙ T ≅ moduleOverComplex R U ⋙ DerivedCategory.Q) :
    IsIso adj.counit := by
  have : Abelian.HasKInjectiveResolutions (SheafOfModules.{max u v r} (R.over U)) :=
    module_hasKInjective.{max u v, v, r} (R.over U)
  let F := SheafOfModules.overFunctor.{max u v r} R U
  let G₀ := SheafOfModules.pushforward.{max u v r} (SheafOfModules.pushforwardOver (R := R) U)
  let a : F ⊣ G₀ := SheafOfModules.overPushforwardOverAdj U
  have : PreservesFiniteLimits F := (SheafOfModules.overFunctor_exact_ofUniverses R U).1
  have : PreservesFiniteColimits F := (SheafOfModules.overFunctor_exact_ofUniverses R U).2
  have : G₀.Additive := a.right_adjoint_additive
  have : IsIso a.counit := open_counit_iso R U
  let ff := a.fullyFaithfulROfIsIsoCounit
  have : G₀.Full := ff.full
  have : G₀.Faithful := ff.faithful
  have : G₀.PreservesKInjectiveComplexes := a.preservesKInjectiveComplexes
  let e := restrictionDerivedIso F T q
  let d := a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft e
  let ffD := (Functor.FullyFaithful.ofFullyFaithful G₀.rightDerivedFunctor).ofIso
    (d.rightAdjointUniq adj)
  have : G.Full := ffD.full
  have : G.Faithful := ffD.faithful
  infer_instance

set_option maxHeartbeats 800000 in
-- The five restriction models require simultaneous universe and instance elaboration.
/-- Open direct images are fully faithful and satisfy binary restriction base change.
Source: Stacks Project, Cohomology, Tag 08DG, the right-direct-image calculation.
(blueprint: lem-sp-ringed-topos-direct-image-restriction).

Proof: On a slice, the underived direct image evaluates a module F at C × Z → Z.
The restriction/direct-image adjunction is given by restriction of sections in one
direction and evaluation on C → Z in the other. Since Z is subterminal, the counit
is an isomorphism. On C → U, C × V identifies with C × W; hence the map from the
V direct image to the W direct image is an isomorphism after restriction to U.
The symmetric assertion follows by exchanging U and V. These comparisons identify
the maps with the adjunction mates in the statement. To derive them, resolve on the
slice by a K-injective complex. Restriction preserves K-injectives since its left
adjoint, extension by zero, is exact. Right direct image preserves K-injectives since
its left adjoint, restriction, is exact. Thus the same sectionwise identifications
compute all derived images and derived counits. Finally transport along the unique
adjoint isomorphisms to the displayed choices; the q isomorphisms determine restrictions
on the localization, and the two composition equations determine the comparison maps.
No cover or boundedness hypothesis is used. Empty and equal subterminals are included.
-/
theorem ringedTopos_directImage_restriction
    {C : Type u} [Category.{v} C] [HasTerminal C] [HasPullbacks C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (R : Sheaf J CommRingCat.{r})
    (U V : C) [Mono (terminal.from U)] [Mono (terminal.from V)]
    [HasDerivedCategory.{w} (ringedSiteModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    [HasDerivedCategory.{w} (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V))]
    [HasDerivedCategory.{w} (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over
        (pullback (terminal.from U) (terminal.from V))))]
    (rU : DerivedCategory (ringedSiteModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)))
    (rV : DerivedCategory (ringedSiteModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)))
    (rW : DerivedCategory (ringedSiteModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over
          (pullback (terminal.from U) (terminal.from V)))))
    (rUW : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over
          (pullback (terminal.from U) (terminal.from V)))))
    (rVW : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over
          (pullback (terminal.from U) (terminal.from V)))))
    (RU : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (RV : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (RW : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over
        (pullback (terminal.from U) (terminal.from V)))) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (adjU : rU ⊣ RU) (adjV : rV ⊣ RV) (adjW : rW ⊣ RW)
    (compU : rW ≅ rU ⋙ rUW) (compV : rW ≅ rV ⋙ rVW)
    (qU : DerivedCategory.Q ⋙ rU ≅
      moduleOverComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U ⋙
        DerivedCategory.Q)
    (qV : DerivedCategory.Q ⋙ rV ≅
      moduleOverComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) V ⋙
        DerivedCategory.Q)
    (qW : DerivedCategory.Q ⋙ rW ≅
      moduleOverComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        (pullback (terminal.from U) (terminal.from V)) ⋙ DerivedCategory.Q)
    (qUW : DerivedCategory.Q ⋙ rUW ≅
      moduleOverMapComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        (pullback.fst (terminal.from U) (terminal.from V)) ⋙ DerivedCategory.Q)
    (qVW : DerivedCategory.Q ⋙ rVW ≅
      moduleOverMapComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        (pullback.snd (terminal.from U) (terminal.from V)) ⋙ DerivedCategory.Q)
    (compU_on_complexes : ∀ K,
      compU.hom.app (DerivedCategory.Q.obj K) ≫
        rUW.map (qU.hom.app K) ≫
          qUW.hom.app
            ((moduleOverComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U).obj K) =
      qW.hom.app K ≫ DerivedCategory.Q.map
        ((moduleOverComplexComp ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
          (pullback.fst (terminal.from U) (terminal.from V))).hom.app K))
    (compV_on_complexes : ∀ K,
      compV.hom.app (DerivedCategory.Q.obj K) ≫
        rVW.map (qV.hom.app K) ≫
          qVW.hom.app
            ((moduleOverComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) V).obj K) =
      qW.hom.app K ≫ DerivedCategory.Q.map
        ((moduleOverComplexComp ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
          (pullback.snd (terminal.from U) (terminal.from V))).hom.app K)) :
    (∀ A : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)), IsIso (adjU.counit.app A)) ∧
    (∀ B : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)), IsIso (adjV.counit.app B)) ∧
    (∀ B : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)),
      IsIso (rU.map (restrictionAdjunctionMap (rUW := rVW) adjV adjW compV B))) ∧
    (∀ A : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)),
      IsIso (rV.map (restrictionAdjunctionMap (rUW := rUW) adjU adjW compU A))) := by
  let : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C
  let : HasSheafify J AddCommGrpCat.{max u v r} :=
    binaryDescent_hasSheafify.{u, v, max u v r} J
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u v r} :=
    binaryDescent_wEqualsLocallyBijective.{u, v, max u v r} J
  let : HasSheafify (J.over U) AddCommGrpCat.{max u v r} :=
    binaryDescent_hasSheafify.{max u v, v, max u v r} (J.over U)
  let : HasSheafify (J.over V) AddCommGrpCat.{max u v r} :=
    binaryDescent_hasSheafify.{max u v, v, max u v r} (J.over V)
  let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r} :=
    binaryDescent_wEqualsLocallyBijective.{max u v, v, max u v r} (J.over U)
  let : (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v r} :=
    binaryDescent_wEqualsLocallyBijective.{max u v, v, max u v r} (J.over V)
  have := derived_open_counit_iso
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U rU RU adjU qU
  have := derived_open_counit_iso
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) V rV RV adjV qV
  refine ⟨fun A ↦ inferInstance, fun B ↦ inferInstance, ?_⟩
  exact ringedTopos_crossDirectImage_restriction.{u, v, r, w}
    J R U V rU rV rW rUW rVW RU RV RW adjU adjV adjW compU compV
    qU qV qW qUW qVW compU_on_complexes compV_on_complexes

end CategoryTheory
end
