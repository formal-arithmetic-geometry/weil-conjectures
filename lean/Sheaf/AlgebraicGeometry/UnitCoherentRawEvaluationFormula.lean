/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.UnitScalarRawData
import Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization
import Sheaf.AlgebraicGeometry.UnitCoherentRawEvaluationFormulaAux
import Sheaf.AlgebraicGeometry.UnitCoherentRawEvaluationFormulaMapAux

/-! # Evaluation formula for transported unit coefficient classes -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible]
  Etale.sheafHToDerived Etale.sheafHDerivedEquiv
  Etale.rawRestrictedCohomologyComparison coherentEtaleRestrictionIso
  unitStructureCoefficientIso Etale.cohomology Etale.upperStar
  RingedSpace.moduleCohomology CoherentEtale.Coeff
  tensorPullback tensorPullbackObj
  CategoryTheory.derivedExtEvaluation
  unitLocalizedCoefficientIso unitCoherentRawClass
attribute [local instance] Etale.RawRestrictedComparison.etaleComposition
  Etale.RawRestrictedComparison.etaleIdentities Etale.RawRestrictedComparison.etalePullbacks
  Etale.RawRestrictedComparison.etaleBaseChange Etale.RawRestrictedComparison.sheafifyInstance
  Etale.RawRestrictedComparison.weakSheafifyInstance
attribute [local instance 2000] CategoryTheory.hasGlobalSectionsFunctor_of_hasTerminal
  HasSmallSiteSheafify.hasSheafify IsGrothendieckAbelian.hasExt
  HasDerivedCategory.ofIsGrothendieckAbelian
  Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology_addCommGrpCat
  Scheme.enoughInjectives_sheaf_smallEtaleTopology_addCommGrpCat
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true



private theorem map_comp_value {C : Type*} [Category C]
    (H : C ⥤ AddCommGrpCat.{u + 1}) {A B D : C} (a : A ⟶ B) (b : B ⟶ D)
    (x : H.obj A) : H.map b (H.map a x) = H.map (a ≫ b) x :=
  (ConcreteCategory.congr_hom (H.map_comp a b) x).symm

private theorem localized_hom {X Y : Scheme.{u}} (j : Y ⟶ X)
    [AlgebraicGeometry.Etale j] :
    (unitLocalizedCoefficientIso j).hom =
      (Etale.upperStar AddCommGrpCat.{u + 1} j).map (unitStructureCoefficientIso X).inv ≫
        (coherentEtaleRestrictionIso j (SheafOfModules.unit X.ringCatSheaf)).hom := by
  unfold unitLocalizedCoefficientIso
  rfl



private theorem equiv_comp_apply {A B D E : AddCommGrpCat.{u + 1}}
    (r : A ⟶ B) [IsIso r] (e : D ≃+ B) (k : D ≅ E) (z : A) :
    ((asIso r).addCommGroupIsoToAddEquiv.trans
      (e.symm.trans k.addCommGroupIsoToAddEquiv)) z = k.hom (e.symm (r z)) := by
  rfl

private instance unit_pullback_qcoh {X Y : Scheme.{u}} (j : Y ⟶ X) :
    ((tensorPullback j).obj (SheafOfModules.unit X.ringCatSheaf)).IsQuasicoherent :=
  isQuasicoherent_tensorPullback j (SheafOfModules.unit X.ringCatSheaf)

/-- The coherent raw evaluation agrees with derived cohomology of the explicit
localized coefficient isomorphism.
Source: Stacks Project, Tag 03Q8 (lemma-higher-direct-images), and Cohomology on
Sites, Tags 03FD and 01FT, coefficient naturality of evaluation.
(blueprint: new-unit-coherent-raw-evaluation-formula).

Proof: write L for inverse image along the chart projection, K for normalized
coherent restriction and c for the unit coefficient isomorphism. Raw coefficient
naturality identifies evaluation of the transported raw class with cohomology
of L(c.inv) applied to the original raw evaluation. By definition,
affineRealizationRawEvaluation applies the inverse Ext-to-derived equivalence,
then Ext of K.hom. Naturality of sheafHToDerived moves K.hom outside this inverse;
the equivalence cancels its inverse. Functoriality composes L(c.inv) with K.hom,
which is precisely unitLocalizedCoefficientIso.hom. All maps remain defined on
empty charts, and no realization or module action on higher images is assumed. -/
theorem unitCoherentRawClass_evaluation {X S : Scheme.{u}} (f : X ⟶ S)
    (q : ℕ) (U : S.Etale)
    (z : (Etale.abelianHigherDirectImageRawPresheaf f q X.etaleAdditiveSheaf).obj (op U)) :
    Etale.sheafHToDerived
        (liftedCoherentEtaleSheaf (affineRealizationCoefficient f
          (SheafOfModules.unit X.ringCatSheaf) U)) q
        (affineRealizationRawEvaluation f (SheafOfModules.unit X.ringCatSheaf) q U
          (unitCoherentRawClass f q U z)) =
      (Etale.cohomology AddCommGrpCat.{u + 1} (Limits.pullback U.hom f) (q : ℤ)).map
        (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
          (unitLocalizedCoefficientIso (pullback.snd U.hom f)).hom))
            (Etale.rawRestrictedCohomologyComparison f q X.etaleAdditiveSheaf U z) := by
  rw [unit_coherent_raw_evaluation_formula, unit_evaluation_map_symm]
  have hn := ConcreteCategory.congr_hom
    (((Etale.rawRestrictedClassNormalization f q X.etaleAdditiveSheaf).2.2.2.2.2
      _ (unitStructureCoefficientIso X).inv).1 U) z
  simp only [ConcreteCategory.comp_apply] at hn
  unfold Etale.normalizationRestrictedCoefficient at hn
  unfold unitCoherentRawClass
  rw [hn]
  let H := CochainComplex.singleFunctor
    (Sheaf (Limits.pullback U.hom f).smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
      DerivedCategory.Q ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} (Limits.pullback U.hom f) (q : ℤ)
  exact (map_comp_value H _ _ _).trans
    (congrArg (fun k => H.map k
      (Etale.rawRestrictedCohomologyComparison f q X.etaleAdditiveSheaf U z))
      (localized_hom (pullback.snd U.hom f)).symm)

end
end AlgebraicGeometry.Scheme.Modules
