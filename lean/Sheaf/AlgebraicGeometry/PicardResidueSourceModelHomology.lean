/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module
public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.AffineKFlatResiduePullbackModel
import Sheaf.AlgebraicGeometry.AffineResidueScalarTransport
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import all Sheaf.AlgebraicGeometry.AffineFreeTerminalSectionsReconstruction
import Sheaf.AlgebraicGeometry.AffinePerfectModuleModel

/-! # Homology of a strictly perfect affine residue model

Source: Stacks Project, Tags 01IB, 064K, 06YJ and 010V.
(blueprint: new-picard-residue-source-model-homology)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- Restriction along the canonical affine chart, with restriction along its inverse. -/
private noncomputable def picardSpecChartEquivalence (W : Scheme.{v}) (U : W.Opens)
    (hU : IsAffineOpen U) :
    SheafOfModules.{v} (moduleRings (Spec Γ(W, U)).toRingedSpace) ≌ U.toScheme.Modules :=
  CategoryTheory.Equivalence.mk
    (Modules.restrictFunctor hU.isoSpec.hom) (Modules.restrictFunctor hU.isoSpec.inv)
    ((Modules.restrictFunctorId).symm ≪≫
      Modules.restrictFunctorCongr (by simp) ≪≫
      Modules.restrictFunctorComp hU.isoSpec.inv hU.isoSpec.hom)
    ((Modules.restrictFunctorComp hU.isoSpec.hom hU.isoSpec.inv).symm ≪≫
      Modules.restrictFunctorCongr (by simp) ≪≫ Modules.restrictFunctorId)

/-- The affine chart equivalence with the localized site. Named constructions keep
its unit and counit from being repeated in every complex comparison. -/
private noncomputable def picardChartEquivalence (W : Scheme.{v}) (U : W.Opens)
    (hU : IsAffineOpen U) :
    SheafOfModules.{v} (moduleRings (Spec Γ(W, U)).toRingedSpace) ≌
      SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) :=
  (picardSpecChartEquivalence W U hU).trans (Modules.overEquiv U).symm

private theorem picardChartEquivalence_functor (W : Scheme.{v}) (U : W.Opens)
    (hU : IsAffineOpen U) :
    (picardChartEquivalence W U hU).functor =
      Modules.restrictFunctor hU.isoSpec.hom ⋙ (Modules.overEquiv U).inverse := rfl

private theorem picardChartEquivalence_inverse (W : Scheme.{v}) (U : W.Opens)
    (hU : IsAffineOpen U) :
    (picardChartEquivalence W U hU).inverse =
      (Modules.overEquiv U).functor ⋙ Modules.restrictFunctor hU.isoSpec.inv := rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Terminal sections reconstruct a strictly perfect affine complex.
Source: Stacks Project, Tag 01IB. The affine perfect module model puts each term
in the sheafification functor's essential image, so the affine adjunction counit
is invertible there. The chart-sections comparison identifies its right adjoint
with terminal evaluation; naturality gives an isomorphism of complexes. -/
private theorem picardTerminalSectionsReconstruction
    (W : Scheme.{v}) (U : W.Opens) (hU : IsAffineOpen U)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K) :
    let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
        ModuleCat.{v} Γ(W, U) :=
      SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
    letI : F.Additive := inferInstanceAs
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
    Nonempty (((affinePerfectSheafification W U hU).mapHomologicalComplex (.up ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj K) ≅ K)  := by
  dsimp only
  let R := W.presheaf.obj (.op U)
  let S := SheafOfModules.{v} (moduleRings (Spec R).toRingedSpace)
  let D := SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)
  let rF := Modules.restrictFunctor hU.isoSpec.hom
  let rG := Modules.restrictFunctor hU.isoSpec.inv
  let E := picardChartEquivalence W U hU
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : E.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let T : ModuleCat.{v} R ⥤ S := tilde.functor R
  have : T.Additive := ⟨by intros; exact tilde.map_add _ _⟩
  have : T.Faithful := inferInstanceAs (tilde.functor R).Faithful
  have : T.Full := inferInstanceAs (tilde.functor R).Full
  have : E.functor.Faithful := inferInstance
  have : E.functor.Full := inferInstance
  let H := E.inverse ⋙ moduleSpecΓFunctor (R := R)
  let F := T ⋙ E.functor
  have : F.Additive := inferInstanceAs (T ⋙ E.functor).Additive
  have : F.Full := Functor.Full.comp (F := T) (G := E.functor)
  have : F.Faithful := Functor.Faithful.comp (F := T) (G := E.functor)
  let adj : F ⊣ H := tilde.adjunction.comp E.toAdjunction
  have : H.IsRightAdjoint := adj.isRightAdjoint
  have : (moduleSpecΓFunctor (R := R)).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ rfl⟩
  have : H.PreservesZeroMorphisms := inferInstance
  have : H.Additive := Functor.additive_of_preserves_binary_products _
  have hF : F = affinePerfectSheafification W U hU := by
    dsimp only [F, E, T, affinePerfectSheafification]
    rw [picardChartEquivalence_functor]
    rfl
  obtain ⟨P, _, ⟨eP⟩⟩ := affine_perfect_module_model W U hU K hK
  have hcounit (n : ℤ) : IsIso (adj.counit.app (K.X n)) := by
    apply adj.isIso_counit_app_of_iso
    · rw [hF]
      exact ((HomologicalComplex.eval D (.up ℤ) n).mapIso eP).symm
  let e := picardSpecChartEquivalence W U hU
  let β : rG ≅ SheafOfModules.pushforward hU.isoSpec.hom.toRingCatSheafHom :=
    e.toAdjunction.rightAdjointUniq (Modules.restrictAdjunction hU.isoSpec.hom)
  let S := moduleSpecΓFunctor (R := R)
  let Fe : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      ModuleCat.{v} Γ(W, U) :=
    SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
  have : Fe.Additive := inferInstanceAs
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
  obtain ⟨α⟩ := overChartSectionsIso W U hU
  have hH : H = (Modules.overEquiv U).functor ⋙ rG ⋙ S := by
    dsimp only [H, E]
    rw [picardChartEquivalence_inverse]
    rfl
  let γ : H ≅ Fe := eqToIso hH ≪≫
    Functor.isoWhiskerLeft (Modules.overEquiv U).functor
      (Functor.isoWhiskerRight β S) ≪≫ α
  let ε := (NatTrans.mapHomologicalComplex adj.counit (.up ℤ)).app K
  have hε : IsIso ε := by
    have : ∀ n : ℤ, IsIso (ε.f n) := hcounit
    exact HomologicalComplex.Hom.isIso_of_components ε
  let δ := (NatIso.mapHomologicalComplex γ (.up ℤ)).app K
  let a := (NatIso.mapHomologicalComplex (eqToIso hF).symm (.up ℤ)).app
    ((Fe.mapHomologicalComplex (.up ℤ)).obj K)
  let b := (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ F)) (.up ℤ)).app K
  exact ⟨a ≪≫ (F.mapHomologicalComplex (.up ℤ)).mapIso δ.symm ≪≫ b.symm ≪≫
    (@asIso _ _ _ _ ε hε) ≪≫ (Functor.mapHomologicalComplexIdIso D (.up ℤ)).app K⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The geometric comparison reduces the residue fibre to homology of the
scalar extension of the section complex.  This is the derived-model part of
Tags 01IB, 064K, 06YJ and 010V; the explicit quotient comparison is separate.
(blueprint: new-picard-residue-source-model-homology) -/
theorem picard_residue_source_model_homology
    [∀ Y : Scheme.{v}, HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (w : W)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K)) :
    let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      ModuleCat.{v} Γ(W, U) :=
      SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
    letI : F.Additive := inferInstanceAs
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
    let T := ModuleCat.extendScalars.{v, v, v} (W.evaluation U w hwU).hom
    letI : T.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
    let C := ((F ⋙ T).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    Nonempty (derivedFiberCohomology W E 1 w ≃ₗ[W.residueField w] C.homology 1) := by
  dsimp only
  classical
  let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      ModuleCat.{v} Γ(W, U) := SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
  have : F.Additive := inferInstanceAs
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
  let P₀ : CochainComplex (ModuleCat.{v} Γ(W, U)) ℤ :=
    (F.mapHomologicalComplex (.up ℤ)).obj K
  have hP₀ : (HomologicalComplex.quasiIso (ModuleCat.{v} Γ(W, U)) (.up ℤ)).kFlat P₀ := by
    obtain ⟨a, b, hbound⟩ := hK.1
    have : P₀.IsStrictlyLE b := (P₀.isStrictlyLE_iff b).2
      (fun j hj ↦ F.map_isZero (hbound j (Or.inr hj)))
    have hflat (j : ℤ) : ObjectProperty.flat (P₀.X j) := by
      obtain ⟨m, ι, π, hιπ⟩ := hK.2 j
      let V := SheafOfModules.free
        (R := (moduleRings W.toRingedSpace).over U) (ULift.{v} (Fin m))
      let e : F.obj V ≃ₗ[Γ(W, U)] (ULift.{v} (Fin m) → Γ(W, U)) :=
        SheafOfModules.freeSectionsLinearEquiv
          (R := (moduleRings W.toRingedSpace).over U)
          (ULift.{v} (Fin m)) (.op (Over.mk (𝟙 U)))
      have : Module.Free Γ(W, U) (F.obj V) := Module.Free.of_equiv e.symm
      have : Projective (F.obj V) := ModuleCat.projective_of_categoryTheory_projective _
      have : Projective (P₀.X j) :=
        (Retract.map (⟨ι, π, hιπ⟩ : Retract (K.X j) V) F).projective
      have : Module.Projective Γ(W, U) (P₀.X j) := inferInstance
      exact (ModuleCat.flat_iff_flat (P₀.X j)).2 inferInstance
    have (X : ModuleCat.{v} Γ(W, U)) : PreservesColimitsOfShape ℤ
        ((MonoidalCategory.curriedTensor (ModuleCat.{v} Γ(W, U))).flip.obj X) :=
      inferInstanceAs (PreservesColimitsOfShape ℤ (MonoidalCategory.tensorRight X))
    have : HasExactColimitsOfShape ℤ (ModuleCat.{v} Γ(W, U)) :=
      HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{v} Γ(W, U))
        (AsSmall.equiv (C := ℤ)).symm
    exact CochainComplex.kFlat_of_isStrictlyLE_of_flat P₀ b hflat
  let T := ModuleCat.extendScalars.{v, v, v} (W.evaluation U w hwU).hom
  have : T.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
  let C := ((F ⋙ T).mapHomologicalComplex (.up ℤ)).obj K
  let L := tilde.functor (W.residueField w)
  have : L.Additive := ⟨by intros; exact tilde.map_add _ _⟩
  let P := (L.mapHomologicalComplex (.up ℤ)).obj C
  let Y := Spec (W.residueField w)
  let B := SheafOfModules.{v} (moduleRings Y.toRingedSpace)
  let Γ := moduleSpecΓFunctor (R := W.residueField w)
  have : Γ.IsEquivalence := isEquivalence_moduleSpecΓFunctor (Field.toIsField _)
  have : Γ.PreservesHomology := inferInstance
  obtain ⟨a⟩ := picardTerminalSectionsReconstruction W U hU K hK
  obtain ⟨b⟩ := hE
  have hmodel : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification W U hU).mapHomologicalComplex (.up ℤ)).obj P₀)) :=
    ⟨b ≪≫ DerivedCategory.Q.mapIso a.symm⟩
  obtain ⟨c⟩ := affine_kFlat_residuePullback_model W E U hU P₀ hP₀ hmodel ⟨w, hwU⟩
  obtain ⟨δ⟩ := affine_residue_scalar_transport W U hU ⟨w, hwU⟩
  have : (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal.IsPrime := by
    set_option backward.isDefEq.respectTransparency false in infer_instance
  have : IsIso (U.ι.residueFieldMap ⟨w, hwU⟩) := by
    set_option backward.isDefEq.respectTransparency false in infer_instance
  have : IsIso (hU.isoSpec.hom.residueFieldMap ⟨w, hwU⟩) := by
    set_option backward.isDefEq.respectTransparency false in infer_instance
  let S := ModuleCat.extendScalars.{v, v, v}
    (algebraMap Γ(W, U) (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal.ResidueField)
  let : S.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
  let e := asIso (U.ι.residueFieldMap ⟨w, hwU⟩) ≪≫
    (asIso (hU.isoSpec.hom.residueFieldMap ⟨w, hwU⟩)).symm ≪≫
      Spec.residueFieldIso Γ(W, U) (hU.isoSpec.hom ⟨w, hwU⟩)
  let R := ModuleCat.restrictScalars.{v, v, v} e.hom.hom
  set_option backward.isDefEq.respectTransparency false in
  let d : (R.mapHomologicalComplex (.up ℤ)).obj
      ((S.mapHomologicalComplex (.up ℤ)).obj P₀) ≅
      (T.mapHomologicalComplex (.up ℤ)).obj P₀ :=
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (S ⋙ R)) (.up ℤ)).app P₀).symm ≪≫
      (NatIso.mapHomologicalComplex δ (.up ℤ)).app P₀
  let q := (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ T)) (.up ℤ)).app K
  let e := c ≪≫ DerivedCategory.Q.mapIso ((L.mapHomologicalComplex (.up ℤ)).mapIso
    (d ≪≫ q.symm))
  let h : derivedFiberCohomology W E 1 w ≅ Γ.obj (P.homology 1) :=
    Γ.mapIso ((DerivedCategory.homologyFunctor B 1).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors B 1).app P)
  let hΓ : Γ.obj (P.homology 1) ≅
      ((Γ.mapHomologicalComplex (.up ℤ)).obj P).homology 1 :=
    ((P.sc 1).mapHomologyIso Γ).symm
  let t : ((Γ.mapHomologicalComplex (.up ℤ)).obj P) ≅ C :=
    (Functor.mapHomologicalComplexCompIso (tilde.toTildeΓNatIso).symm (.up ℤ)).app C ≪≫
      (Functor.mapHomologicalComplexIdIso (ModuleCat.{v} (W.residueField w)) (.up ℤ)).app C
  exact ⟨(h ≪≫ hΓ ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{v} (W.residueField w))
      (.up ℤ) 1).mapIso t).toLinearEquiv⟩

end AlgebraicGeometry.Scheme
