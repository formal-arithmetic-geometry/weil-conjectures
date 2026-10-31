/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # Comparing derived evaluation in the two coefficient presentations

Source: the evaluation step of the proper closed-injective cohomology calculation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private noncomputable def fixedEmbedding (T : Scheme.{u})
    (A : Type u) [CommRing A] :=
  sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⋙
    ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1, u} A)

private noncomputable def realizationUnitIso (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    fixedEmbedding T A ≅ (sfIntrinsicModuleEquivalence T A).functor ⋙
      SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
        (ProEtale.finiteCoefficientIntrinsicScalarMap T A) := by
  let η := Functor.whiskerLeft (fixedEmbedding T A)
    (PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
      (ProEtale.finiteCoefficientIntrinsicScalarMap T A)).unit
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    change IsIso ((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
      (ProEtale.finiteCoefficientIntrinsicScalarMap T A)).unit.app
        ((fixedEmbedding T A).obj M))
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose (ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1})).obj M).property
  exact asIso η

private noncomputable def realizationEvaluationIso (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] (V : T.ProEt) :
    (sfIntrinsicModuleEquivalence T A).functor ⋙
        SheafOfModules.evaluation
          ((sheafCompose (ProEt.topology T)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (proEtaleConstantRing T A)) (op V) ⋙
        forget₂ (ModuleCat.{u + 1} _) AddCommGrpCat.{u + 1} ≅
      sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⋙
        (CategoryTheory.evaluation T.ProEtᵒᵖ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj (op V) ⋙
        forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1} := by
  exact (Functor.isoWhiskerRight (realizationUnitIso T A)
    (PresheafOfModules.toPresheaf _ ⋙
      (CategoryTheory.evaluation T.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj (op V))).symm

/-- Vanishing of derived sections in fixed-scalar coordinates implies vanishing of the
intrinsic higher direct image evaluated at an affine weakly contractible object.
Source: the evaluation step in the proper closed-injective calculation; Stacks, Tag 07A5.
(blueprint: lem-sp-proetale-derived-evaluation-comparison).

Proof: the scalar-unit sheafification is an isomorphism on the underlying abelian
presheaf, since that presheaf is already a sheaf. This compares the two underived
section functors. The canonical realization equivalence preserves injectives, so
precomposition by it commutes with right derivation. Evaluation at the specified
weakly contractible object is exact, as is forgetting a module action; these functors
therefore commute with homology of an injective resolution. The resulting isomorphism
identifies the two derived evaluations. Forgetting the module action reflects zero. -/
theorem isZero_intrinsic_directImage_evaluation_of_fixed
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasInjectiveResolutions (proEtaleRingModules X (proEtaleConstantRing X A))]
    (W : Y.ProEt) [IsAffine W.left]
    (hW : ∀ (F G : Sheaf (ProEt.topology Y) (Type (u + 1))) (e : F ⟶ G),
      Epi e → Function.Surjective (e.hom.app (op W)))
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) (q : ℕ)
    (hz : IsZero (((sheafToPresheaf (ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⋙
      (CategoryTheory.evaluation X.ProEtᵒᵖ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (op ((proEtaleBaseChange f).obj W))).rightDerived q).obj M)) :
    IsZero ((SheafOfModules.evaluation
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing Y A)) (op W)).obj
      (((proEtaleConstantModuleDirectImage f A).rightDerived q).obj
        ((sfIntrinsicModuleEquivalence X A).functor.obj M))) := by
  let RY : Sheaf (ProEt.topology Y) RingCat.{u + 1} := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing Y A)
  let E := (sfIntrinsicModuleEquivalence X A).functor
  let P := proEtaleConstantModuleDirectImage f A
  let V : SheafOfModules.{u + 1} RY ⥤
      ModuleCat.{u + 1} (RY.obj.obj (op W)) :=
    SheafOfModules.evaluation.{u + 1} RY (op W)
  let U : ModuleCat.{u + 1} (RY.obj.obj (op W)) ⥤ AddCommGrpCat.{u + 1} :=
    forget₂ (ModuleCat.{u + 1} (RY.obj.obj (op W))) AddCommGrpCat.{u + 1}
  let Q := V ⋙ U
  let S := sheafToPresheaf (ProEt.topology X)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⋙
    (CategoryTheory.evaluation X.ProEtᵒᵖ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
      (op ((proEtaleBaseChange f).obj W))
  let U₀ := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1}
  have hV := ProEt.affine_weaklyContractible_evaluation_colimits
    Y (proEtaleConstantRing Y A) W hW
  let : PreservesFiniteLimits V := hV.1
  let : PreservesFiniteColimits V := hV.2.1
  let : V.Additive := Functor.additive_of_preserves_binary_products V
  let : PreservesColimitsOfSize.{0, 0} U :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, 0, 0} (RY.obj.obj (op W))
  let : PreservesFiniteColimits U :=
    PreservesColimitsOfSize0.preservesFiniteColimits U
  let : PreservesColimitsOfSize.{0, 0} U₀ :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, 0, 0} (ULift.{u + 1, u} A)
  let : PreservesFiniteColimits U₀ :=
    PreservesColimitsOfSize0.preservesFiniteColimits U₀
  let : Q.Additive := inferInstance
  let : PreservesFiniteLimits Q := by
    dsimp only [Q]
    infer_instance
  let : PreservesFiniteColimits Q := by
    dsimp only [Q]
    infer_instance
  let : PreservesFiniteLimits P := (proEtaleConstantModuleDirectImage_additive_leftExact f A).2
  let c : E ⋙ (P ⋙ Q) ≅ S ⋙ U₀ :=
    Functor.isoWhiskerRight (sfIntrinsicDirectImageComparison f A) Q ≪≫
      Functor.isoWhiskerLeft
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)
        (realizationEvaluationIso Y A W)
  let e₁ := Functor.compRightDerivedObjIso E (P ⋙ Q)
    (fun I _ ↦ by
      have : Injective (E.obj I) := E.injective_obj_of_injective inferInstance
      exact Functor.rightAcyclic_of_injective (E.obj I)) q M
  let e₂ := Functor.rightDerivedObjIsoOfIso c q M
  let e₃ := Functor.rightDerivedCompObjIso S U₀ q M
  let e₄ := Functor.rightDerivedCompObjIso P Q q (E.obj M)
  have hzero := (U₀.map_isZero hz).of_iso e₃
  have hzero' := hzero.of_iso (e₁.symm ≪≫ e₂)
  have hzero'' := hzero'.of_iso e₄.symm
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact AddCommGrpCat.isZero_iff_subsingleton.mp hzero''

end AlgebraicGeometry.Scheme
