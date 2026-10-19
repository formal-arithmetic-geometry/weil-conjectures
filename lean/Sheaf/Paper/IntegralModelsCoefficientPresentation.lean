/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Paper.IntegralModelsDefinitions
import Sheaf.Paper.IntegralModelsCoefficientRingDiagram
import Sheaf.Paper.ContinuousCoefficientModuleEncoding
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Sheaf.Paper.ConstantCoefficientScalarEquivalence
import all Sheaf.Paper.FlatRingedIdealCompleteEquivalence

/-! # Embedded coefficients and the canonical constant quotient tower

Source: blueprint main-20261015, sk-lem-integral-models, proof step 2,
and Stacks Tags 099I and 099L.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
namespace CategoryTheory.ConstantCompletion
private theorem kernelIdeal_sections {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{u}}
    (q : R ⟶ S) (U : C) :
    (kernelIdeal q).sections U = RingHom.ker (q.hom.app (op U)).hom :=
  (kernelIdeal_existsUnique q).exists.choose_spec U

private theorem kernelIdeal_map {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R B S T : Sheaf J CommRingCat.{u}}
    (q : R ⟶ S) (r : B ⟶ T) (e : R ≅ B) (f : S ≅ T)
    (h : e.hom ≫ r = q ≫ f.hom) (U : C) :
    Ideal.map (e.hom.hom.app (op U)).hom ((kernelIdeal q).sections U) =
      (kernelIdeal r).sections U := by
  rw [kernelIdeal_sections, kernelIdeal_sections]
  have he : Function.Bijective (e.hom.hom.app (op U)).hom :=
    ConcreteCategory.bijective_of_isIso ((sheafToPresheaf _ _).mapIso e |>.hom.app (op U))
  have hf : Function.Injective (f.hom.hom.app (op U)).hom :=
    (ConcreteCategory.bijective_of_isIso
      ((sheafToPresheaf _ _).mapIso f |>.hom.app (op U))).1
  have hw (x : R.obj.obj (op U)) :
      r.hom.app (op U) (e.hom.hom.app (op U) x) =
        f.hom.hom.app (op U) (q.hom.app (op U) x) :=
    ConcreteCategory.congr_hom (congr_app (congrArg (fun k : R ⟶ T ↦ k.hom) h) (op U)) x
  ext b
  rw [Ideal.mem_map_iff_of_surjective _ he.2]
  constructor
  · rintro ⟨a, ha, rfl⟩
    change r.hom.app (op U) (e.hom.hom.app (op U) a) = 0
    rw [hw, (RingHom.mem_ker.mp ha), map_zero]
  · intro hb
    obtain ⟨a, rfl⟩ := he.2 b
    refine ⟨a, ?_, rfl⟩
    apply RingHom.mem_ker.mpr
    apply hf
    rw [map_zero, ← hw]
    exact hb

private theorem complete_coefficientIso {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R B S T : Sheaf J CommRingCat.{u}}
    (q : R ⟶ S) (r : B ⟶ T) (e : R ≅ B) (f : S ≅ T)
    (h : e.hom ≫ r = q ≫ f.hom) (M : D B) :
    IsComplete q ((dres e.hom).obj M) ↔ IsComplete r M := by
  let : HasDerivedCategory (Mod R) := HasDerivedCategory.standard _
  let : HasDerivedCategory (Mod B) := HasDerivedCategory.standard _
  let := fun U : C ↦ HasDerivedCategory.standard (Mod (R.over U))
  let := fun U : C ↦ HasDerivedCategory.standard (Mod (B.over U))
  let I := kernelIdeal q
  let IB := kernelIdeal r
  have hIB : ∀ (U : C) (b : B.obj.obj (op U)),
      b ∈ IB.sections U ↔ ∃ S : Sieve U, S ∈ J U ∧
        ∀ (V : C) (g : V ⟶ U), S g →
          B.obj.map g.op b ∈ Ideal.map (e.hom.hom.app (op V)).hom (I.sections V) := by
    intro U b
    dsimp only [I, IB]
    simp_rw [kernelIdeal_map q r e f h]
    constructor
    · intro hb
      exact ⟨⊤, J.top_mem U, fun V g _ ↦ IB.restriction g b hb⟩
    · rintro ⟨S, hS, hb⟩
      exact IB.local_mem U b S hS hb
  let F := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map e.hom)
  let := (siteRestrictScalars_exact e.hom).1
  let := (siteRestrictScalars_exact e.hom).2
  have hc := restrictScalars_locallyDerivedComplete_iff J R B e.hom I IB hIB M
  let i : F.mapDerivedCategory.obj M ≅ DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj (DerivedCategory.Q.objPreimage M)) :=
    F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫
      F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage M)
  exact ⟨fun hM ↦ hc.mp
      (locallyDerivedRingedIdealComplete_of_iso R I i.symm hM),
    fun hM ↦ locallyDerivedRingedIdealComplete_of_iso R I i (hc.mpr hM)⟩
end CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.ProEtale
private def smallModuleEquivalence (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ≌
      ConstantCompletion.Mod (IntegralModelsStacks.smallRing X R) := by
  let e := (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).symm
  have : e.functor.IsContinuous (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      (Scheme.ProEt.topology X) := inferInstanceAs
    ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).IsContinuous
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X))
  have : e.inverse.IsContinuous (Scheme.ProEt.topology X)
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) :=
    Scheme.coefficientProEtaleModelUp_isContinuous.{u, u} X
  let O := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) R)
  let ep := SheafOfModules.pushforwardPushforwardEquivalence e
    (J := Scheme.coefficientProEtaleModelTopology.{u, u} X)
    (K := Scheme.ProEt.topology X) (R := O) (𝟙 _) (𝟙 O)
    (by
      ext U x
      change (O.obj.map (𝟙 _)).hom x = x
      rw [O.obj.map_id]
      rfl)
    (by
      ext U x
      change (O.obj.map (𝟙 _)).hom x = x
      change (O.obj.map (𝟙 (op (AsSmall.down.obj U.unop)))).hom
        (show O.obj.obj (op (AsSmall.down.obj U.unop)) from x) = x
      rw [O.obj.map_id]
      rfl)
  exact (InternalAbelianSheafModule.sectionModuleEquivalence
    (Scheme.ProEt.topology X) R).trans ep


private theorem smallModuleEquivalence_functor (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (smallModuleEquivalence X R).functor = IntegralModelsStacks.smallModules X R := by
  rfl

private theorem smallModules_additive (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (IntegralModelsStacks.smallModules X R).Additive := by
  constructor
  intro M N f g
  ext U x
  rfl

private def smallDerivedEquivalence (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) ≌
      ConstantCompletion.D (IntegralModelsStacks.smallRing X R) := by
  let e := smallModuleEquivalence X R
  have : e.functor.Additive := by
    change (smallModuleEquivalence X R).functor.Additive
    rw [smallModuleEquivalence_functor]
    exact smallModules_additive X R
  have : e.inverse.Additive := e.inverse_additive
  let : HasDerivedCategory (ConstantCompletion.Mod (IntegralModelsStacks.smallRing X R)) :=
    HasDerivedCategory.standard _
  exact e.mapDerivedCategory

private theorem smallDerivedObject_iso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)) :
    Nonempty (IntegralModelsStacks.smallDerivedObject X R K ≅
      (smallDerivedEquivalence X R).functor.obj K) := by
  let : HasDerivedCategory (ConstantCompletion.Mod (IntegralModelsStacks.smallRing X R)) :=
    HasDerivedCategory.standard _
  have : (IntegralModelsStacks.smallModules X R).Additive := smallModules_additive X R
  have : PreservesFiniteLimits (IntegralModelsStacks.smallModules X R) := by
    rw [← smallModuleEquivalence_functor]
    infer_instance
  have : PreservesFiniteColimits (IntegralModelsStacks.smallModules X R) := by
    rw [← smallModuleEquivalence_functor]
    infer_instance
  refine ⟨?_⟩
  change IntegralModelsStacks.smallDerivedObject X R K ≅
    (IntegralModelsStacks.smallModules X R).mapDerivedCategory.obj K
  exact ((IntegralModelsStacks.smallModules X R).mapDerivedCategoryFactors.app
    (DerivedCategory.Q.objPreimage K)).symm ≪≫
      (IntegralModelsStacks.smallModules X R).mapDerivedCategory.mapIso
        (DerivedCategory.Q.objObjPreimageIso K)


private def smallModulesComapIso (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] :
    Mod.comap φ ⋙ IntegralModelsStacks.smallModules X R ≅
      IntegralModelsStacks.smallModules X S ⋙ ConstantCompletion.res
        (IntegralModelsStacks.smallMap X φ) := by
  let J := Scheme.ProEt.topology X
  let K := Scheme.coefficientProEtaleModelTopology.{u, u} X
  let A := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R
  let B := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J S
  let f := IntegralModelsStacks.sectionMap X φ
  let PR : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A) ⥤
        ConstantCompletion.Mod (IntegralModelsStacks.smallRing X R) :=
    SheafOfModules.pushforward (F := AsSmall.down) (𝟙 _)
  let PS : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B) ⥤
        ConstantCompletion.Mod (IntegralModelsStacks.smallRing X S) :=
    SheafOfModules.pushforward (F := AsSmall.down) (𝟙 _)
  let FR := (InternalAbelianSheafModule.sectionModuleEquivalence J R).functor
  let FS := (InternalAbelianSheafModule.sectionModuleEquivalence J S).functor
  let G := SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map f)
  let H := ConstantCompletion.res (IntegralModelsStacks.smallMap X φ)
  have i : Mod.comap φ ⋙ FR ≅ FS ⋙ G := CondensedRing.sectionModuleComapIso X φ
  have j : G ⋙ PR ≅ PS ⋙ H :=
    NatIso.ofComponents (fun M ↦ Iso.refl _) (by intros; rfl)
  exact (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight i PR ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft FS j ≪≫
    (Functor.associator _ _ _).symm
private def coefficientDerivedEquivalence {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{u}}
    (e : R ≅ S) : ConstantCompletion.D R ≌ ConstantCompletion.D S := by
  let f := SheafOfModules.coefficientEquivalence
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).mapIso e.symm)
  let : HasDerivedCategory (ConstantCompletion.Mod R) := HasDerivedCategory.standard _
  let : HasDerivedCategory (ConstantCompletion.Mod S) := HasDerivedCategory.standard _
  have : f.functor.Additive := inferInstanceAs
    (ConstantCompletion.res e.inv).Additive
  have : f.inverse.Additive := f.inverse_additive
  exact f.mapDerivedCategory

private def resCompIso {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R S T : Sheaf J CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    ConstantCompletion.res g ⋙ ConstantCompletion.res f ≅
      ConstantCompletion.res (f ≫ g) := Iso.refl _

private def resSquareIso {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R S R' S' : Sheaf J CommRingCat.{u}}
    (f : R ⟶ S) (g : R' ⟶ S') (a : R ≅ R') (b : S ≅ S')
    (h : f ≫ b.hom = a.hom ≫ g) :
    ConstantCompletion.res b.inv ⋙ ConstantCompletion.res g ≅
      ConstantCompletion.res f ⋙ ConstantCompletion.res a.inv := by
  have w : g ≫ b.inv = a.inv ≫ f := by
    apply (cancel_mono b.hom).mp
    simp only [Category.assoc, b.inv_hom_id, Category.comp_id]
    rw [h, Iso.inv_hom_id_assoc]
  exact resCompIso g b.inv ≪≫ eqToIso (congrArg ConstantCompletion.res w) ≪≫
    (resCompIso a.inv f).symm


private theorem complete_of_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u}} (q : R ⟶ S)
    {M N : ConstantCompletion.D R} (e : M ≅ N)
    (h : ConstantCompletion.IsComplete q M) : ConstantCompletion.IsComplete q N := by
  let : HasDerivedCategory (ConstantCompletion.Mod R) := HasDerivedCategory.standard _
  let := fun U : C ↦ HasDerivedCategory.standard (ConstantCompletion.Mod (R.over U))
  intro U f hf
  exact (h U f hf).of_iso ((derivedInternalHom (J.over U) (R.over U)).mapIso
    ((Iso.refl _).prod ((ringedDerivedRestriction R U).mapIso e))).symm

private theorem presentation_of_smallDiagram (X : Scheme.{u})
    {R B SR SB : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj B] [MonObj SR] [MonObj SB]
    [IsCommMonObj R] [IsCommMonObj B] [IsCommMonObj SR] [IsCommMonObj SB]
    (φ : R ⟶ B) [IsMonHom φ] (qR : R ⟶ SR) [IsMonHom qR]
    (qB : B ⟶ SB) [IsMonHom qB]
    {R' B' S' : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X) CommRingCat.{u + 1}}
    (φ' : R' ⟶ B') (qR' : R' ⟶ S') (qB' : B' ⟶ S')
    (eR : IntegralModelsStacks.smallRing X R ≅ R')
    (eB : IntegralModelsStacks.smallRing X B ≅ B')
    (eSR : IntegralModelsStacks.smallRing X SR ≅ S')
    (eSB : IntegralModelsStacks.smallRing X SB ≅ S')
    (hφ : IntegralModelsStacks.smallMap X φ ≫ eB.hom = eR.hom ≫ φ')
    (hR : IntegralModelsStacks.smallMap X qR ≫ eSR.hom = eR.hom ≫ qR')
    (hB : IntegralModelsStacks.smallMap X qB ≫ eSB.hom = eB.hom ≫ qB') :
    ∃ (EB : DerivedCategory.{u + 1}
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B) ≌ ConstantCompletion.D B')
      (ER : DerivedCategory.{u + 1}
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) ≌ ConstantCompletion.D R'),
      (∀ K, IntegralModelsEmbedded.complete X qB K ↔
        ConstantCompletion.IsComplete qB' (EB.functor.obj K)) ∧
      (∀ L, IntegralModelsEmbedded.complete X qR L ↔
        ConstantCompletion.IsComplete qR' (ER.functor.obj L)) ∧
      Nonempty (EB.functor ⋙ ConstantCompletion.dres φ' ≅
        (Mod.comap φ).mapDerivedCategory ⋙ ER.functor) := by
  let : HasDerivedCategory (ConstantCompletion.Mod (IntegralModelsStacks.smallRing X B)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (ConstantCompletion.Mod (IntegralModelsStacks.smallRing X R)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (ConstantCompletion.Mod B') := HasDerivedCategory.standard _
  let : HasDerivedCategory (ConstantCompletion.Mod R') := HasDerivedCategory.standard _
  let FB := IntegralModelsStacks.smallModules X B
  let FR := IntegralModelsStacks.smallModules X R
  let GB := ConstantCompletion.res eB.inv
  let GR := ConstantCompletion.res eR.inv
  let EB := (smallDerivedEquivalence X B).trans (coefficientDerivedEquivalence eB)
  let ER := (smallDerivedEquivalence X R).trans (coefficientDerivedEquivalence eR)
  have : FB.Additive := smallModules_additive X B
  have : FR.Additive := smallModules_additive X R
  have : GB.IsEquivalence := by
    change (SheafOfModules.coefficientEquivalence
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        eB.symm)).functor.IsEquivalence
    infer_instance
  have : GR.IsEquivalence := by
    change (SheafOfModules.coefficientEquivalence
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        eR.symm)).functor.IsEquivalence
    infer_instance
  refine ⟨EB, ER, ?_, ?_, ?_⟩
  · intro K
    obtain ⟨i⟩ := smallDerivedObject_iso X B K
    have w : eB.inv ≫ IntegralModelsStacks.smallMap X qB = qB' ≫ eSB.inv := by
      apply (cancel_mono eSB.hom).mp
      simp only [Category.assoc, eSB.inv_hom_id, Category.comp_id]
      rw [hB, Iso.inv_hom_id_assoc]
    have hc := CategoryTheory.ConstantCompletion.complete_coefficientIso
      qB' (IntegralModelsStacks.smallMap X qB) eB.symm eSB.symm w
      ((smallDerivedEquivalence X B).functor.obj K)
    exact (Iff.intro (complete_of_iso _ i) (complete_of_iso _ i.symm)).trans hc.symm
  · intro L
    obtain ⟨i⟩ := smallDerivedObject_iso X R L
    have w : eR.inv ≫ IntegralModelsStacks.smallMap X qR = qR' ≫ eSR.inv := by
      apply (cancel_mono eSR.hom).mp
      simp only [Category.assoc, eSR.inv_hom_id, Category.comp_id]
      rw [hR, Iso.inv_hom_id_assoc]
    have hc := CategoryTheory.ConstantCompletion.complete_coefficientIso
      qR' (IntegralModelsStacks.smallMap X qR) eR.symm eSR.symm w
      ((smallDerivedEquivalence X R).functor.obj L)
    exact (Iff.intro (complete_of_iso _ i) (complete_of_iso _ i.symm)).trans hc.symm
  · let H : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B ⥤
        Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R := Mod.comap φ
    let F := ConstantCompletion.res φ'
    let G := ConstantCompletion.res (IntegralModelsStacks.smallMap X φ)
    have : FB.IsEquivalence := by
      change (IntegralModelsStacks.smallModules X B).IsEquivalence
      rw [← smallModuleEquivalence_functor]
      infer_instance
    have : FR.IsEquivalence := by
      change (IntegralModelsStacks.smallModules X R).IsEquivalence
      rw [← smallModuleEquivalence_functor]
      infer_instance
    have : PreservesFiniteLimits F := (siteRestrictScalars_exact φ').1
    have : PreservesFiniteColimits F := (siteRestrictScalars_exact φ').2
    let i : H ⋙ FR ≅ FB ⋙ G := smallModulesComapIso X φ
    let j : GB ⋙ F ≅ G ⋙ GR :=
      resSquareIso (IntegralModelsStacks.smallMap X φ) φ' eR eB hφ
    let a : (FB ⋙ GB) ⋙ F ≅ H ⋙ (FR ⋙ GR) :=
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft FB j ≪≫
        (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight i.symm GR ≪≫
        Functor.associator _ _ _
    refine ⟨?_⟩
    change (FB.mapDerivedCategory ⋙ GB.mapDerivedCategory) ⋙ F.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ (FR.mapDerivedCategory ⋙ GR.mapDerivedCategory)
    exact Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso FB GB).symm
        F.mapDerivedCategory ≪≫
      (Functor.mapDerivedCategoryCompIso (FB ⋙ GB) F).symm ≪≫
      Functor.mapDerivedCategoryNatIso a ≪≫
      Functor.mapDerivedCategoryCompIso H (FR ⋙ GR) ≪≫
      Functor.isoWhiskerLeft H.mapDerivedCategory (Functor.mapDerivedCategoryCompIso FR GR)

/-- Changing from internal module objects to the small ringed site identifies the
embedded coefficients with the constant ring and its canonical quotient-tower limit.
The comparison preserves both first-reduction kernel ideals and the actual restriction
functor. This is a comparison of ambient categories, with no completeness restriction.

Source: blueprint main-20261015, sk-lem-integral-models, proof step 2; Stacks 099L.
(blueprint: lem-sfb-embedded-integral-coefficient-presentation).

Proof: use the section-action equivalence and AsSmall.down to obtain exact equivalences
of module categories. Extend them termwise to the derived categories and identify the
chosen representative used by smallDerivedObject with that functor's value. The normalized
ring diagram identifies both scalar rings and their first quotient maps. Restriction
along these ring isomorphisms gives the remaining module and derived equivalences.
For each first-reduction square, the kernel ideals correspond sectionwise: use the
bijective scalar map to lift a section, and the injective residue map to test its image
being zero. Local ideal membership then gives the hypotheses of the existing restriction
completeness theorem. Identify its chosen-representative functor with exact derived
restriction; completeness is invariant under isomorphisms by derived internal Hom.
Finally section-action commutes with scalar restriction, and AsSmall pushforward preserves
that comparison on the same sections and actions. The scalar square identifies the two
composite restriction functors. The exact-functor composition isomorphisms descend this
ordinary comparison to the required unbounded derived comparison. No complete-object
equivalence theorem is used. Empty schemes and zero complexes are included. -/
theorem embeddedIntegral_coefficient_presentation
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (X : Scheme.{u}) [IsNoetherian X] :
    let A := ULift.{u + 1} (PadicAlgCl.integers ℓ E.1)
    let I : Ideal A := Ideal.map ULift.ringEquiv.symm.toRingHom (Ideal.span {π})
    let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
    ∃ (eB : DerivedCategory.{u + 1}
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (integralCoefficientObject X ℓ E)) ≌
        ConstantCompletion.D (ConstantCompletion.completed J A I))
      (eR : DerivedCategory.{u + 1}
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (IntegralModelsEmbedded.discreteObj
            (PadicAlgCl.integers ℓ E.1)) X)) ≌
        ConstantCompletion.D (ConstantCompletion.constant J A)),
      (∀ K, IntegralModelsEmbedded.completedComplete ℓ E π X K ↔
        ConstantCompletion.IsComplete (ConstantCompletion.projection J A I 0)
          (eB.functor.obj K)) ∧
      (∀ L, IntegralModelsEmbedded.constantComplete ℓ E π X L ↔
        ConstantCompletion.IsComplete (ConstantCompletion.quotient J A I 0)
          (eR.functor.obj L)) ∧
      Nonempty (eB.functor ⋙ ConstantCompletion.dres (ConstantCompletion.coefficientMap J A I) ≅
        IntegralModelsEmbedded.restriction ℓ E X ⋙ eR.functor) := by
  let A := ULift.{u + 1} (PadicAlgCl.integers ℓ E.1)
  let I : Ideal A := Ideal.map ULift.ringEquiv.symm.toRingHom (Ideal.span {π})
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
  obtain ⟨eB, eR, eSB, eSR, hφ, hB, hR⟩ :=
    embeddedIntegral_coefficient_ring_diagram ℓ E π hπ X
  exact presentation_of_smallDiagram X (IntegralModelsEmbedded.scalarMap ℓ E X)
    (IntegralModelsEmbedded.residueMap ℓ E π X)
    (completedCoefficientMap X (completedReduction ℓ E π 0)).hom
    (ConstantCompletion.coefficientMap J A I) (ConstantCompletion.quotient J A I 0)
    (ConstantCompletion.projection J A I 0) eR eB eSR eSB hφ hR hB

end AlgebraicGeometry.ProEtale
