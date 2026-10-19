/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.Paper.SbcCompletedOperations
public import Sheaf.Paper.WitnessCompatibility
import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
import Sheaf.AlgebraicGeometry.FiniteCoefficientRealizationDirectImage
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Finite operations under the canonical quotient coefficient realization

Source: Stacks Project, Modules on Sites, Tags 03CY and 03DA; Cohomology on Sites,
Tags 0D6D and 0D6E (blueprint: lem-sbc-finite-witness-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

private theorem functionScalars_normalization (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    pbcFunctionScalars W d n =
      Functor.whiskerRight (toSheafify (ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of (ProEtale.PbcQuotient d n))))
          (forget₂ CommRingCat RingCat) ≫
      ((adicLisseForget W).map (pbcLevelConstantComparison W d n).hom).hom := by
  let c := AdicCoefficients.constants W (ProEtale.PbcQuotient d n)
  let η := toSheafify (ProEt.topology W)
    (AdicCoefficients.functionPresheaf W (ProEtale.PbcQuotient d n))
  let F := forget₂ CommRingCat.{u + 1} RingCat.{u + 1}
  have he : toSheafify (ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of (ProEtale.PbcQuotient d n))) ≫
      (pbcLevelConstantComparison W d n).hom.hom = c ≫ η := by
    ext U b
    exact (pbcLevelConstantComparison_exists W d n).exists.choose_spec U b
  have hη := (AdicCoefficients.finiteRingComparison_exists W
    (ProEtale.PbcQuotient d n)).choose_spec.1.2
  have h : Functor.whiskerRight (c ≫ η) F ≫
      (AdicCoefficients.finiteRingComparison W (ProEtale.PbcQuotient d n)).hom.hom =
        ProEtale.finiteCoefficientScalarMap W (ProEtale.PbcQuotient d n) := by
    rw [Functor.whiskerRight_comp, Category.assoc]
    erw [hη]
    rfl
  rw [← he, Functor.whiskerRight_comp, Category.assoc] at h
  rw [pbcFunctionScalars, ← h]
  have hcancel := congrArg (fun k ↦ k.hom)
    (AdicCoefficients.finiteRingComparison W (ProEtale.PbcQuotient d n)).hom_inv_id
  change (AdicCoefficients.finiteRingComparison W (ProEtale.PbcQuotient d n)).hom.hom ≫
    (AdicCoefficients.finiteRingComparison W (ProEtale.PbcQuotient d n)).inv.hom = 𝟙 _
    at hcancel
  simp only [Category.assoc, hcancel]
  rfl

private theorem finiteDirectImage_scalars (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U V : Scheme.{u}} (q : U ⟶ V) (n : ℕ) :
    pbcFunctionScalars V (pbcIntegralDatum l E) n ≫
        Functor.whiskerRight
          (proEtaleRingDirectImageMap q
            ((pbcAdicRings V (pbcIntegralDatum l E)).obj (op n))
            ((pbcAdicRings U (pbcIntegralDatum l E)).obj (op n))
            (sbcFiniteCoefficientIso l E q n)).hom
          (forget₂ CommRingCat RingCat) =
      Functor.whiskerLeft (proEtaleBaseChange q).op
        (pbcFunctionScalars U (pbcIntegralDatum l E) n) := by
  let d := pbcIntegralDatum l E
  let P := ProEtale.PbcQuotient d n
  let adj := proEtaleSheafAdjunction q CommRingCat.{u + 1}
  let G := proEtaleSheafDirectImage q CommRingCat.{u + 1}
  let L := proEtaleSheafInverseImage q CommRingCat.{u + 1}
  have hc : proEtaleRingDirectImageMap q
        ((pbcAdicRings V d).obj (op n)) ((pbcAdicRings U d).obj (op n))
        (sbcFiniteCoefficientIso l E q n) =
      (pbcLevelConstantComparison V d n).inv ≫
        proEtaleConstantDirectImageMap q CommRingCat.{u + 1} (CommRingCat.of P) ≫
          G.map (pbcLevelConstantComparison U d n).hom := by
    change adj.homEquiv _ _ (L.map (pbcLevelConstantComparison V d n).inv ≫
      proEtaleConstantInverseImageMap q CommRingCat.{u + 1} (CommRingCat.of P) ≫
      (pbcLevelConstantComparison U d n).hom) = _
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    exact congrArg (fun k ↦ (pbcLevelConstantComparison V d n).inv ≫ k ≫
      G.map (pbcLevelConstantComparison U d n).hom)
      ((adj.homEquiv (adicLisseConstantRing V P) (adicLisseConstantRing U P)).apply_symm_apply
        (proEtaleConstantDirectImageMap q CommRingCat.{u + 1} (CommRingCat.of P)))
  have hs : toSheafify (ProEt.topology V)
      ((Functor.const V.ProEtᵒᵖ).obj (CommRingCat.of P)) ≫
        (proEtaleConstantDirectImageMap q CommRingCat.{u + 1} (CommRingCat.of P)).hom =
      Functor.whiskerLeft (proEtaleBaseChange q).op
        (toSheafify (ProEt.topology U)
          ((Functor.const U.ProEtᵒᵖ).obj (CommRingCat.of P))) :=
    ((sheafificationAdjunction (ProEt.topology V) CommRingCat.{u + 1}).homEquiv
      _ _).apply_symm_apply _
  rw [functionScalars_normalization, functionScalars_normalization, hc]
  change Functor.whiskerRight
      (toSheafify (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj (CommRingCat.of P)) ≫
        (pbcLevelConstantComparison V d n).hom.hom ≫
        ((pbcLevelConstantComparison V d n).inv ≫
          proEtaleConstantDirectImageMap q CommRingCat.{u + 1} (CommRingCat.of P) ≫
          G.map (pbcLevelConstantComparison U d n).hom).hom)
        (forget₂ CommRingCat RingCat) = _
  have he : (pbcLevelConstantComparison V d n).hom.hom ≫
      (pbcLevelConstantComparison V d n).inv.hom = 𝟙 _ :=
    congrArg (fun k ↦ k.hom) (pbcLevelConstantComparison V d n).hom_inv_id
  change Functor.whiskerRight
      (toSheafify (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj (CommRingCat.of P)) ≫
        (pbcLevelConstantComparison V d n).hom.hom ≫
        (pbcLevelConstantComparison V d n).inv.hom ≫
        (proEtaleConstantDirectImageMap q CommRingCat.{u + 1} (CommRingCat.of P)).hom ≫
        Functor.whiskerLeft (proEtaleBaseChange q).op
          (pbcLevelConstantComparison U d n).hom.hom)
        (forget₂ CommRingCat RingCat) = _
  rw [← Category.assoc (pbcLevelConstantComparison V d n).hom.hom, he,
    Category.id_comp, ← Category.assoc, hs]
  rfl

private noncomputable def fixedEmbedding (W : Scheme.{u})
    (P : Type (u + 1)) [CommRing P] :=
  sheafToPresheaf (ProEt.topology W) (ModuleCat.{u + 1} P) ⋙
    ProEtale.finiteCoefficientModulePresheaf W.ProEt P

private noncomputable def presentationRestriction (W : Scheme.{u})
    (P : Type (u + 1)) [CommRing P] (R : Sheaf (ProEt.topology W) RingCat.{u + 1})
    (α : (Functor.const W.ProEtᵒᵖ).obj (RingCat.of P) ⟶ R.obj) :=
  SheafOfModules.forget.{u + 1} R ⋙ PresheafOfModules.restrictScalars.{u + 1} α

private noncomputable def presentationUnit (W : Scheme.{u})
    (P : Type (u + 1)) [CommRing P] (R : Sheaf (ProEt.topology W) RingCat.{u + 1})
    (α : (Functor.const W.ProEtᵒᵖ).obj (RingCat.of P) ⟶ R.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology W) α]
    [Presheaf.IsLocallySurjective (ProEt.topology W) α] :
    fixedEmbedding W P ≅ pbcAssociatedModule W P R α ⋙
      presentationRestriction W P R α := by
  let η := Functor.whiskerLeft (fixedEmbedding W P)
    (PresheafOfModules.sheafificationAdjunction.{u + 1} α).unit
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro F
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    change IsIso (toSheafify (ProEt.topology W)
      (F.obj ⋙ forget₂ (ModuleCat.{u + 1} P) AddCommGrpCat.{u + 1}))
    exact isIso_toSheafify (ProEt.topology W)
      ((sheafCompose (ProEt.topology W)
        (forget₂ (ModuleCat.{u + 1} P) AddCommGrpCat.{u + 1})).obj F).property
  exact asIso η

private noncomputable def restrictionDirectImage (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U V : Scheme.{u}} (q : U ⟶ V) (n : ℕ) :
    proEtaleRingModuleDirectImage q
        ((pbcAdicRings V (pbcIntegralDatum l E)).obj (op n))
        ((pbcAdicRings U (pbcIntegralDatum l E)).obj (op n))
        (sbcFiniteCoefficientIso l E q n) ⋙
      presentationRestriction V (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
        ((adicLisseForget V).obj ((pbcAdicRings V (pbcIntegralDatum l E)).obj (op n)))
        (pbcFunctionScalars V (pbcIntegralDatum l E) n) ≅
    presentationRestriction U (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
        ((adicLisseForget U).obj ((pbcAdicRings U (pbcIntegralDatum l E)).obj (op n)))
        (pbcFunctionScalars U (pbcIntegralDatum l E) n) ⋙
      PresheafOfModules.pushforward₀ (proEtaleBaseChange q)
        ((Functor.const U.ProEtᵒᵖ).obj
          (RingCat.of (ProEtale.PbcQuotient (pbcIntegralDatum l E) n))) := by
  let d := pbcIntegralDatum l E
  let P := ProEtale.PbcQuotient d n
  let G := proEtaleRingModuleDirectImage q
    ((pbcAdicRings V d).obj (op n)) ((pbcAdicRings U d).obj (op n))
    (sbcFiniteCoefficientIso l E q n)
  let RV := (adicLisseForget V).obj ((pbcAdicRings V d).obj (op n))
  let RU := (adicLisseForget U).obj ((pbcAdicRings U d).obj (op n))
  let HV := presentationRestriction V P RV (pbcFunctionScalars V d n)
  let HU := presentationRestriction U P RU (pbcFunctionScalars U d n)
  let Q := PresheafOfModules.pushforward₀ (proEtaleBaseChange q)
    ((Functor.const U.ProEtᵒᵖ).obj (RingCat.of P))
  have e : G ⋙ HV ≅ HU ⋙ Q := by
    refine NatIso.ofComponents (fun M ↦ ?_) ?_
    · let L := (G ⋙ HV).obj M
      let R := (HU ⋙ Q).obj M
      change L ≅ R
      refine PresheafOfModules.isoMk (fun W ↦ ?_) ?_
      · let g : L.obj W ≃ₗ[P] R.obj W :=
          { toFun := fun x ↦ x
            invFun := fun x ↦ x
            left_inv := fun _ ↦ rfl
            right_inv := fun _ ↦ rfl
            map_add' := fun _ _ ↦ rfl
            map_smul' := by
              intro r m
              have h := congrArg (fun t ↦ (t.app W).hom r)
                (finiteDirectImage_scalars l E q n)
              exact congrArg (fun a ↦ a •
                (show M.val.obj ((proEtaleBaseChange q).op.obj W) from m)) h }
        exact g.toModuleIso
      · intro W Z g
        ext x
        rfl
    · intro M N g
      ext W x
      rfl
  exact e

private noncomputable def realizationDirectImage (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U V : Scheme.{u}} (q : U ⟶ V) (n : ℕ) :
    pbcFunctionRealization U (pbcIntegralDatum l E) n ⋙
        proEtaleRingModuleDirectImage q
          ((pbcAdicRings V (pbcIntegralDatum l E)).obj (op n))
          ((pbcAdicRings U (pbcIntegralDatum l E)).obj (op n))
          (sbcFiniteCoefficientIso l E q n) ≅
      ProEtale.lowerStar (ModuleCat.{u + 1}
        (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)) q ⋙
          pbcFunctionRealization V (pbcIntegralDatum l E) n := by
  let d := pbcIntegralDatum l E
  let P := ProEtale.PbcQuotient d n
  let RV := (adicLisseForget V).obj ((pbcAdicRings V d).obj (op n))
  let RU := (adicLisseForget U).obj ((pbcAdicRings U d).obj (op n))
  let HV := presentationRestriction V P RV (pbcFunctionScalars V d n)
  let Q := PresheafOfModules.pushforward₀ (proEtaleBaseChange q)
    ((Functor.const U.ProEtᵒᵖ).obj (RingCat.of P))
  have : HV.Full := (PresheafOfModules.sheafificationAdjunction
    (pbcFunctionScalars V d n)).fullyFaithfulROfIsIsoCounit.full
  have : HV.Faithful := (PresheafOfModules.sheafificationAdjunction
    (pbcFunctionScalars V d n)).fullyFaithfulROfIsIsoCounit.faithful
  let e := Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (pbcFunctionRealization U d n)
      (restrictionDirectImage l E q n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (presentationUnit U P RU (pbcFunctionScalars U d n)).symm Q ≪≫
    (Iso.refl _ : fixedEmbedding U P ⋙ Q ≅
      ProEtale.lowerStar (ModuleCat.{u + 1} P) q ⋙ fixedEmbedding V P) ≪≫
    Functor.isoWhiskerLeft (ProEtale.lowerStar (ModuleCat.{u + 1} P) q)
      (presentationUnit V P RV (pbcFunctionScalars V d n)) ≪≫
    (Functor.associator _ _ _).symm
  exact Functor.fullyFaithfulCancelRight HV e

private noncomputable def derivedRealizationDirectImage (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U V : Scheme.{u}} (q : U ⟶ V) (n : ℕ) :
    pbcDerivedFunctionRealization U (pbcIntegralDatum l E) n ⋙ sbcFinitePush l E q n ≅
      (ProEtale.lowerStar (ModuleCat.{u + 1}
        (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)) q).rightDerivedFunctor ⋙
          pbcDerivedFunctionRealization V (pbcIntegralDatum l E) n := by
  let d := pbcIntegralDatum l E
  let RU := pbcFunctionRealization U d n
  let RV := pbcFunctionRealization V d n
  let G := proEtaleRingModuleDirectImage q
    ((pbcAdicRings V d).obj (op n)) ((pbcAdicRings U d).obj (op n))
    (sbcFiniteCoefficientIso l E q n)
  let F := ProEtale.lowerStar (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) q
  exact Functor.isoWhiskerRight RU.rightDerivedFunctorIsoMapDerivedCategory.symm
      G.rightDerivedFunctor ≪≫
    (Functor.rightDerivedFunctorCompIso RU G).symm ≪≫
    Functor.rightDerivedFunctorNatIso (realizationDirectImage l E q n) ≪≫
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso F RV

private noncomputable def witnessDirectImageIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U V : Scheme.{u}} (q : U ⟶ V) (n : ℕ) :
    ProEtale.pbcWitnessDirectImage q (pbcIntegralDatum l E) n ≅
      (ProEtale.lowerStar (ModuleCat.{u + 1}
        (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)) q).rightDerivedFunctor := by
  let P := ProEtale.PbcQuotient (pbcIntegralDatum l E) n
  let FU := ProEtale.finiteCoefficientRealization U P
  let FV := ProEtale.finiteCoefficientRealization V P
  let G := ProEtale.finiteCoefficientModuleDirectImage q P
  let F := ProEtale.lowerStar (ModuleCat.{u + 1} P) q
  let a := (ProEtale.finiteCoefficientRealization_directImage q P).some
  let b : FU.mapDerivedCategory ⋙ G.rightDerivedFunctor ≅
      F.rightDerivedFunctor ⋙ FV.mapDerivedCategory :=
    Functor.isoWhiskerRight FU.rightDerivedFunctorIsoMapDerivedCategory.symm
      G.rightDerivedFunctor ≪≫
    (Functor.rightDerivedFunctorCompIso FU G).symm ≪≫
    Functor.rightDerivedFunctorNatIso a ≪≫
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso F FV
  have : FV.asEquivalence.functor.Additive := inferInstanceAs FV.Additive
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight b (ProEtale.finiteCoefficientUnrealization V P).mapDerivedCategory ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F.rightDerivedFunctor
      FV.asEquivalence.mapDerivedCategory.unitIso.symm ≪≫ Functor.rightUnitor _

private noncomputable def witnessPullbackIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U V : Scheme.{u}} (q : U ⟶ V) (n : ℕ) :
    ProEtale.pbcWitnessPullback q (pbcIntegralDatum l E) n ≅
      (ProEtale.upperStar (ModuleCat.{u + 1}
        (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)) q).mapDerivedCategory := by
  let P := ProEtale.PbcQuotient (pbcIntegralDatum l E) n
  let FU := ProEtale.finiteCoefficientRealization U P
  let FV := ProEtale.finiteCoefficientRealization V P
  let IU := ProEtale.finiteCoefficientUnrealization U P
  let IV := ProEtale.finiteCoefficientUnrealization V P
  let F := ProEtale.upperStar (ModuleCat.{u + 1} P) q
  let e : FV ⋙ (IV ⋙ F ⋙ FU) ⋙ IU ≅ F :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight FV.asEquivalence.unitIso.symm (F ⋙ FU) ≪≫
      Functor.leftUnitor _) IU ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F FU.asEquivalence.unitIso.symm ≪≫ Functor.rightUnitor _
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso FV
      (ProEtale.finiteCoefficientPullback V P q)).symm IU.mapDerivedCategory ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫ Functor.mapDerivedCategoryNatIso e

private noncomputable def realizationPullback (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U V : Scheme.{u}} (q : U ⟶ V) (n : ℕ) :
    ProEtale.upperStar (ModuleCat.{u + 1}
        (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)) q ⋙
        pbcFunctionRealization U (pbcIntegralDatum l E) n ≅
      pbcFunctionRealization V (pbcIntegralDatum l E) n ⋙
        proEtaleRingModulePullback q
          ((pbcAdicRings V (pbcIntegralDatum l E)).obj (op n))
          ((pbcAdicRings U (pbcIntegralDatum l E)).obj (op n))
          (sbcFiniteCoefficientIso l E q n) := by
  let d := pbcIntegralDatum l E
  let P := ProEtale.PbcQuotient d n
  let RU := (pbcFunctionRealization U d n).asEquivalence
  let RV := (pbcFunctionRealization V d n).asEquivalence
  let F := ProEtale.upperStar (ModuleCat.{u + 1} P) q
  let G := ProEtale.lowerStar (ModuleCat.{u + 1} P) q
  let a := proEtaleRingModuleAdjunction q
    ((pbcAdicRings V d).obj (op n)) ((pbcAdicRings U d).obj (op n))
    (sbcFiniteCoefficientIso l E q n)
  let D := proEtaleRingModuleDirectImage q
    ((pbcAdicRings V d).obj (op n)) ((pbcAdicRings U d).obj (op n))
    (sbcFiniteCoefficientIso l E q n)
  let e : D ⋙ RV.inverse ≅ RU.inverse ⋙ G :=
    (Functor.leftUnitor (D ⋙ RV.inverse)).symm ≪≫
    Functor.isoWhiskerRight RU.counitIso.symm (D ⋙ RV.inverse) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft RU.inverse
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (realizationDirectImage l E q n) RV.inverse ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft G RV.unitIso.symm ≪≫ Functor.rightUnitor _)
  exact (conjugateIsoEquiv
    (RV.toAdjunction.comp a)
    ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} P) q).comp RU.toAdjunction)).symm e

/-- Canonical realization intertwines ordinary finite direct image and inverse image.
Source: Stacks Project, Tags 03CY, 03DA, 0D6D and 0D6E.
(blueprint: lem-sbc-finite-witness-realization).

Proof: realize fixed scalars as modules over the sheaf of locally constant coefficient
functions. The comparison with the adic quotient sheaf is fixed on constant sections.
The coefficient direct-image square commutes: both maps pull a constant scalar back
to the same constant scalar. Constant scalars locally generate the coefficient sheaf,
so this proves the square on all sections. Restriction of module actions therefore
commutes with direct image. Its inverse equivalence gives the ordinary realization
comparison. Uniqueness of left adjoints gives the inverse-image comparison. These
inverse images are exact. Derive their comparison termwise; compute the direct-image
comparison on K-injective resolutions, which the exact realization equivalences
preserve. The result is the stated comparison of unbounded derived functors. -/
theorem sbcFiniteWitnessRealization (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U V : Scheme.{u}} (q : U ⟶ V) (n : ℕ) :
    Nonempty (ProEtale.pbcWitnessDirectImage q (pbcIntegralDatum l E) n ⋙
        pbcDerivedFunctionRealization V (pbcIntegralDatum l E) n ≅
      pbcDerivedFunctionRealization U (pbcIntegralDatum l E) n ⋙ sbcFinitePush l E q n) ∧
    Nonempty (ProEtale.pbcWitnessPullback q (pbcIntegralDatum l E) n ⋙
        pbcDerivedFunctionRealization U (pbcIntegralDatum l E) n ≅
      pbcDerivedFunctionRealization V (pbcIntegralDatum l E) n ⋙ sbcFinitePull l E q n) := by
  refine ⟨?_, ?_⟩
  · exact ⟨Functor.isoWhiskerRight (witnessDirectImageIso l E q n) _ ≪≫
      (derivedRealizationDirectImage l E q n).symm⟩
  · exact ⟨Functor.isoWhiskerRight (witnessPullbackIso l E q n) _ ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (realizationPullback l E q n) ≪≫
      Functor.mapDerivedCategoryCompIso _ _⟩

end WeilConjectures
