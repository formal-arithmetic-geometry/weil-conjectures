/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.Paper.RealizationScalarFunctor
public import Sheaf.Paper.CompletedTowerDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ContinuousCoefficientGeneralPullbackIso
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import all Sheaf.Paper.ContinuousChartSchemeNaturality
import all Sheaf.Paper.ContinuousCoefficientPullbackIso
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Direct image under normalized continuous coefficient encodings -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]
variable {T U : Scheme.{u}} [IsNoetherian T] [IsNoetherian U]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
  [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
variable (h : T ⟶ U)
  (sT : RealizationScalarFunctorData l E T) (sU : RealizationScalarFunctorData l E U)

private theorem derive_conjugacy
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (eT : A ≌ C) (eU : B ≌ D) [eT.functor.Additive] [eT.inverse.Additive]
    [eU.functor.Additive] [eU.inverse.Additive]
    (F : A ⥤ B) (P : C ⥤ D) [F.Additive] [P.Additive]
    (z : F ⋙ eU.functor ≅ eT.functor ⋙ P) :
    Nonempty (eT.mapDerivedCategory.inverse ⋙ F.rightDerivedFunctor ⋙
      eU.mapDerivedCategory.functor ≅ P.rightDerivedFunctor) := by
  let d : F.rightDerivedFunctor ⋙ eU.mapDerivedCategory.functor ≅
      eT.mapDerivedCategory.functor ⋙ P.rightDerivedFunctor :=
    (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F eU.functor).symm ≪≫
      Functor.rightDerivedFunctorNatIso z ≪≫
      Functor.rightDerivedFunctorCompIso eT.functor P ≪≫
      Functor.isoWhiskerRight eT.functor.rightDerivedFunctorIsoMapDerivedCategory _
  exact ⟨Functor.isoWhiskerLeft eT.mapDerivedCategory.inverse d ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight eT.mapDerivedCategory.counitIso _ ≪≫ Functor.leftUnitor _⟩

private theorem coefficient_map_value (V : U.ProEtᵒᵖ)
    (r : (InternalModuleOperations.ring (Profinite.continuousCoefficientRingObj E) U).obj.obj V) :
    (InternalModuleOperations.coefficientMap
      (Profinite.continuousCoefficientRingObj E) h).hom.app V r =
      (condensedPushforwardHom (Profinite.continuousCoefficientRingObj E) h).hom.app V r := by
  exact (InternalModuleOperations.coefficientMap_existsUnique
    (Profinite.continuousCoefficientRingObj E) h).exists.choose_spec V r

private theorem comparison_square :
    condensedPushforwardHom (Profinite.continuousCoefficientRingObj E) h ≫
      (lowerStar Ab.{u + 1} h).map sT.coefficientIso.hom.hom =
    sU.coefficientIso.hom.hom ≫ LatticePullbackProof.additiveDirectMap h E := by
  let adjX := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ U))
  let CY := (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousCoefficientRingSheaf T E)
  have hleft := chartMate_homEquiv h (toSpecZ U) (toSpecZ T) (comp_toSpecZ h)
    (pointUpperStar.obj (Profinite.continuousCoefficientRingObj E)) CY
      (sT.coefficientIso.hom.hom)
  rw [← condensedPullbackHom_eq (Profinite.continuousCoefficientRingObj E) h] at hleft
  apply (adjX.homEquiv _ _).injective
  conv_rhs => rw [adjX.homEquiv_naturality_right]
  simp only [adjX, Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply]
  simp only [← unitAlgHom_comp_map_condensedPullbackHom, Category.assoc]
  erw [hleft, pointUpperStarLowerStarAdjunction.homEquiv_naturality_right]
  ext S s
  apply ULift.ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  change ((((lowerStarFactor Ab.{u + 1} (comp_toSpecZ h)).inv.app CY).hom.app
    (op (profiniteToProEt.obj S.unop)))
      ((((pointUpperStarLowerStarAdjunction.comp
        (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ T))).homEquiv _ _
          sT.coefficientIso.hom.hom).hom.app S) s)).down =
    (((LatticePullbackProof.additiveDirectMap h E).hom.app
      (op ((profiniteToProEtOf U).obj S.unop)))
        ((((pointUpperStarLowerStarAdjunction.comp
          (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ U))).homEquiv _ _
            sU.coefficientIso.hom.hom).hom.app S) s)).down
  erw [sT.coefficient_normalization S.unop s.down,
    sU.coefficient_normalization S.unop s.down]
  rw [lowerStarFactor_inv_app_hom_app]
  change (s.down.comp (profiniteTestProjection T S.unop)).comp
      (((MorphismProperty.Over.pullbackComp h (toSpecZ U) (toSpecZ T)
        (comp_toSpecZ h).symm).inv.app (profiniteToProEt.obj S.unop)).left.base.hom) =
    (s.down.comp (profiniteTestProjection U S.unop)).comp
      (pullback.fst (((profiniteToProEtOf U).obj S.unop).hom) h).base.hom
  have hp :
      ((MorphismProperty.Over.pullbackComp h (toSpecZ U) (toSpecZ T)
        (comp_toSpecZ h).symm).inv.app (profiniteToProEt.obj S.unop)).left ≫
          pullback.fst (toSpecZ (profiniteToScheme.obj S.unop)) (toSpecZ T) =
      pullback.fst (((profiniteToProEtOf U).obj S.unop).hom) h ≫
        pullback.fst (toSpecZ (profiniteToScheme.obj S.unop)) (toSpecZ U) := by
    simp only [MorphismProperty.Over.pullbackComp_inv_app_left]
    dsimp only [pullback.map]
    erw [Category.assoc, pullback.lift_fst]
    simp only [Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
    rfl
  have hp' := congrArg (fun g ↦ g.base.hom) hp
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp] at hp'
  simp only [profiniteTestProjection, ContinuousMap.comp_assoc]
  rw [hp']

private theorem comparison_value (V : U.ProEtᵒᵖ)
    (r : (InternalModuleOperations.ring (Profinite.continuousCoefficientRingObj E) U).obj.obj V) :
    (sT.coefficientIso.hom.hom).hom.app ((proEtaleBaseChange h).op.obj V)
      ((condensedPushforwardHom (Profinite.continuousCoefficientRingObj E) h).hom.app V r) =
    (LatticePullbackProof.additiveDirectMap h E).hom.app V
      ((sU.coefficientIso.hom.hom).hom.app V r) := by
  exact congrArg (fun z ↦ (z.hom.app V).hom r) (comparison_square l E h sT sU)

private theorem section_forward_square
    (cE : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l U E) ≅ rationalCoefficientSheaf l T E)
    (hcE : rationalCoefficientRestrictionNormalized l E h cE.hom) :
    InternalModuleOperations.coefficientMap (Profinite.continuousCoefficientRingObj E) h ≫
        (proEtaleSheafDirectImage h RingCat.{u + 1}).map
          (((adicLisseForget T).mapIso sT.sectionIso).hom) =
      ((adicLisseForget U).mapIso sU.sectionIso).hom ≫
        (adicLisseForget U).map (proEtaleRingDirectImageMap h _ _ cE) := by
  apply Sheaf.hom_ext
  ext V r
  have hc := coefficient_map_value E h V r
  have ht := sT.section_normalization ((proEtaleBaseChange h).op.obj V)
    ((InternalModuleOperations.coefficientMap
      (Profinite.continuousCoefficientRingObj E) h).hom.app V r)
  have hu := sU.section_normalization V r
  have he := comparison_value l E h sT sU V r
  have hp := rationalCoefficientDirectImage_value l E h cE.hom hcE V.unop
    (sU.sectionIso.hom.hom.app V r)
  apply rationalCoefficientValue_ext l E T ((proEtaleBaseChange h).op.obj V)
  intro x
  change rationalCoefficientValue l E T ((proEtaleBaseChange h).op.obj V)
      (sT.sectionIso.hom.hom.app _
        ((InternalModuleOperations.coefficientMap
          (Profinite.continuousCoefficientRingObj E) h).hom.app V r)) x =
    rationalCoefficientValue l E T ((proEtaleBaseChange h).op.obj V)
      ((proEtaleRingDirectImageMap h _ _ cE).hom.app V (sU.sectionIso.hom.hom.app V r)) x
  rw [ht]
  change (InternalModuleOperations.coefficientMap
    (Profinite.continuousCoefficientRingObj E) h).hom.app V r = _ at hc
  rw [hc]
  change _ = rationalCoefficientValue l E T ((proEtaleBaseChange h).op.obj V)
    (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _ cE.hom).hom.app V
      (sU.sectionIso.hom.hom.app V r)) x
  erw [hp]
  exact (congrArg (fun z ↦ z.down x) he).trans (hu _).symm

/-- Continuous internal direct image in the prescribed sectionwise coordinates.
Source: Bhatt--Scholze, Lemma 4.2.12 and Remark 6.8.15; Stacks Tag 0D6E.
(blueprint: lem-weil-pbc-realization-continuous-direct-image)

Proof: coefficient_normalization determines the additive realization map by
adjunction on profinite tests. Naturality of the point pullback identifies its
scheme direct-image square with continuous precomposition. The equation
section_normalization makes the reconstructed ring square the same square.
The internal/section module equivalence intertwines ordinary direct image:
both underlying sheaves have sections on the base-changed test object, and the
ring square identifies their scalar actions. This is identity on sections,
natural in every module. Exact coefficient equivalences preserve K-injectives,
so applying the universal derived direct-image comparison and the two inverse
equivalence identities gives the displayed conjugated isomorphism. The
normalization of cE identifies its adjunct with that same precomposition map. -/
theorem realizationContinuousDirectImage
    (cE : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l U E) ≅ rationalCoefficientSheaf l T E)
    (hcE : rationalCoefficientRestrictionNormalized l E h cE.hom) :
    let eT := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (ProEt.topology T) (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)).trans
        (ringModuleEquivalenceOfIso T ((adicLisseForget T).mapIso sT.sectionIso).symm)
    let eU := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (ProEt.topology U) (condensedRingObj (Profinite.continuousCoefficientRingObj E) U)).trans
        (ringModuleEquivalenceOfIso U ((adicLisseForget U).mapIso sU.sectionIso).symm)
    letI := sT.encodingAdditive
    letI := sT.encodingInverseAdditive
    letI := sU.encodingAdditive
    letI := sU.encodingInverseAdditive
    Nonempty (eT.mapDerivedCategory.inverse ⋙
        (lowerStar (Profinite.continuousCoefficientRingObj E) h).rightDerivedFunctor ⋙
          eU.mapDerivedCategory.functor ≅ proEtaleRingDerivedDirectImage h _ _ cE) := by
  classical
  dsimp only
  let eT := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology T) (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)).trans
      (ringModuleEquivalenceOfIso T ((adicLisseForget T).mapIso sT.sectionIso).symm)
  let eU := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology U) (condensedRingObj (Profinite.continuousCoefficientRingObj E) U)).trans
      (ringModuleEquivalenceOfIso U ((adicLisseForget U).mapIso sU.sectionIso).symm)
  letI := sT.encodingAdditive
  letI := sT.encodingInverseAdditive
  letI := sU.encodingAdditive
  letI := sU.encodingInverseAdditive
  let P := proEtaleRingModuleDirectImage h _ _ cE
  let F := lowerStar (Profinite.continuousCoefficientRingObj E) h
  let eTR := (adicLisseForget T).mapIso sT.sectionIso
  let eUR := (adicLisseForget U).mapIso sU.sectionIso
  let φ := InternalModuleOperations.coefficientMap (Profinite.continuousCoefficientRingObj E) h
  let ψ := (adicLisseForget U).map (proEtaleRingDirectImageMap h _ _ cE)
  let R := proEtaleSheafDirectImage h RingCat.{u + 1}
  have hs : eUR.inv ≫ φ = ψ ≫ R.map eTR.inv := by
    apply (cancel_epi eUR.hom).mp
    apply (cancel_mono (R.map eTR.hom)).mp
    simp only [Category.assoc]
    erw [Iso.hom_inv_id_assoc, ← R.map_comp, Iso.inv_hom_id,
      R.map_id, Category.comp_id]
    exact section_forward_square l E h sT sU cE hcE
  let q : InternalModuleOperations.lowerStar
      (Profinite.continuousCoefficientRingObj E) h ⋙
        (ringModuleEquivalenceOfIso U eUR.symm).functor ≅
      (ringModuleEquivalenceOfIso T eTR.symm).functor ⋙ P :=
    NatIso.ofComponents (fun M ↦
      (SheafOfModules.fullyFaithfulForget _).preimageIso
        (PresheafOfModules.isoMk (fun V ↦
          { hom := ModuleCat.ofHom
              (X := ((InternalModuleOperations.lowerStar
                (Profinite.continuousCoefficientRingObj E) h ⋙
                  (ringModuleEquivalenceOfIso U eUR.symm).functor).obj M).val.obj V)
              (Y := (((ringModuleEquivalenceOfIso T eTR.symm).functor ⋙ P).obj M).val.obj V)
              { toFun := id
                map_add' := fun _ _ ↦ rfl
                map_smul' := by
                  intro r x
                  change (φ.hom.app V (eUR.inv.hom.app V r)) •
                      (show M.val.obj ((proEtaleBaseChange h).op.obj V) from x) =
                    (eTR.inv.hom.app ((proEtaleBaseChange h).op.obj V) (ψ.hom.app V r)) •
                      (show M.val.obj ((proEtaleBaseChange h).op.obj V) from x)
                  exact congrArg (fun a : (InternalModuleOperations.ring
                      (Profinite.continuousCoefficientRingObj E) T).obj.obj
                        ((proEtaleBaseChange h).op.obj V) ↦
                    a • (show M.val.obj ((proEtaleBaseChange h).op.obj V) from x))
                      (congrArg (fun z ↦ (z.hom.app V).hom r) hs) }
            inv := ModuleCat.ofHom
              (X := (((ringModuleEquivalenceOfIso T eTR.symm).functor ⋙ P).obj M).val.obj V)
              (Y := ((InternalModuleOperations.lowerStar
                (Profinite.continuousCoefficientRingObj E) h ⋙
                  (ringModuleEquivalenceOfIso U eUR.symm).functor).obj M).val.obj V)
              { toFun := id
                map_add' := fun _ _ ↦ rfl
                map_smul' := by
                  intro r x
                  change (eTR.inv.hom.app ((proEtaleBaseChange h).op.obj V) (ψ.hom.app V r)) •
                      (show M.val.obj ((proEtaleBaseChange h).op.obj V) from x) =
                    (φ.hom.app V (eUR.inv.hom.app V r)) •
                      (show M.val.obj ((proEtaleBaseChange h).op.obj V) from x)
                  exact congrArg (fun a : (InternalModuleOperations.ring
                      (Profinite.continuousCoefficientRingObj E) T).obj.obj
                        ((proEtaleBaseChange h).op.obj V) ↦
                    a • (show M.val.obj ((proEtaleBaseChange h).op.obj V) from x))
                      (congrArg (fun z ↦ (z.hom.app V).hom r) hs).symm }
            hom_inv_id := by ext; rfl
            inv_hom_id := by ext; rfl })
          (by intros; ext; rfl))) (by intros; ext; rfl)
  let z : F ⋙ eU.functor ≅ eT.functor ⋙ P :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (InternalModuleOperations.lowerComparison
        (Profinite.continuousCoefficientRingObj E) h) _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ q ≪≫
      (Functor.associator _ _ _).symm
  exact derive_conjugacy eT eU F P z

end WeilConjectures
