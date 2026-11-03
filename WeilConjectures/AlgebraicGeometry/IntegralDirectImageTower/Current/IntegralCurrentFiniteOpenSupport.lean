/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormulaCore
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerCurrentStatement
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import all WeilConjectures.Algebra.Homology.RingedOpenScalar.RingedOpenScalarAdjunction
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSlicePresentation
import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionModuleOperationsData
import all WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerOpenAdjunctionEvaluation

/-! # Finite evaluated reduction preserves open support -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local instance 2000] localizedModuleExtension_additive
  localizedModuleExtension_limits localizedModuleExtension_colimits
  localizedModuleRestriction_additive localizedModuleRestriction_limits
  localizedModuleRestriction_colimits

private def localizedScalarOpenIso {T : Scheme.{u}} (W : T.ProEt)
    {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)
    (A : SystemScalarModel.{u + 1, u, u + 1} a)
    (B : SystemScalarModel.{u + 1, u, u + 1}
      (J := (Scheme.ProEt.topology T).over W)
      (((Scheme.ProEt.topology T).overPullback CommRingCat.{u + 1} W).map a)) :
    (localizedModuleExtension R W).mapDerivedCategory ⋙ A.model.T ≅
      B.model.T ⋙ (localizedModuleExtension S W).mapDerivedCategory := by
  let d := RingedOpenScalar.restrictionIso.{u + 1, u, u + 1} W a
  let e := RingedOpenScalar.derivedSquare _ _ _ _ d
  exact ((localizedModuleDerivedAdjunction R W).comp A.adjunction).leftAdjointUniq
    ((B.adjunction.comp (localizedModuleDerivedAdjunction S W)).ofNatIsoRight e.symm)

private theorem internalOpenSlicePresentation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] :
    ∃ e : ModuleRingedComparison.modules Λ U ≌
        SheafOfModules.{u + 1} ((InternalModuleOperations.ring Λ T).over
          (Scheme.ProEt.mk j)),
      Nonempty (CondensedRing.openImmersionLowerShriek Λ j ⋙
          (ModuleRingedComparison.equivalence Λ T).functor ≅
        (ModuleRingedComparison.equivalence Λ U).functor ⋙ e.functor ⋙
          localizedModuleExtension (ModuleRingedComparison.ring Λ T) (Scheme.ProEt.mk j)) := by
  let lc := InternalModuleOperations.lowerComparison Λ j ≪≫ pushBridge j Λ
  let p := (InternalModuleOperations.comparison_existsUnique
    (InternalModuleOperations.equivalence Λ T)
    (InternalModuleOperations.equivalence Λ U)
    (CondensedRing.upperStarLowerStarAdjunction Λ j)
    (Scheme.proEtaleRingModuleAdjunction j _ _ (spCoefficientIso j Λ)) lc).exists.choose
  let q := (InternalModuleOperations.comparison_existsUnique
    (InternalModuleOperations.equivalence Λ U)
    (InternalModuleOperations.equivalence Λ T)
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j)
    (Adjunction.ofIsRightAdjoint
      (Scheme.proEtaleRingModulePullback j _ _ (spCoefficientIso j Λ))) p).exists.choose
  obtain ⟨e, ⟨he⟩⟩ := Scheme.proEtaleOpen_slicePresentation j
    (ModuleRingedComparison.ring Λ T) (ModuleRingedComparison.ring Λ U)
    (spCoefficientIso j Λ)
  exact ⟨e, ⟨q ≪≫ Functor.isoWhiskerLeft _ he⟩⟩

private def evaluationSectionIso (s : Coefficients l E) (T : Scheme.{u})
    (n : ℕ) (M : spCoefficientTowers l E T) (U : T.ProEtᵒᵖ) :
    ((SpTowerShriek.ev l E T n).obj
      ((s.base.realization T).functor.obj M)).val.obj U ≅
      ((spCoefficientEvaluation l E T (s.towers T).equivalence n).obj M).val.obj U := by
  have h := eq_of_heq ((s.base.sections T M n U).trans
    ((s.towers T).sections M n U).symm)
  let P := ((s.base.realization T).functor.obj M).val.obj (op (n, U.unop))
  have hc : ((eqToHom (WeilConjectures.SemilinearSections.evaluation_ring
      (Scheme.ProEt.topology T) (SpTowerShriek.B l E T)
      (SpTowerShriek.tau l E T) n).symm).hom.app U).hom =
      RingHom.id _ := by
    rw [ObjectProperty.eqToHom_hom, eqToHom_app]
    rfl
  change (ModuleCat.restrictScalars _).obj P ≅ _
  exact ModuleCat.restrictScalarsId'App _ hc P ≪≫ eqToIso h

private theorem evaluationSectionIso_sections (s : Coefficients l E) (T : Scheme.{u})
    (n : ℕ) (M : spCoefficientTowers l E T) (U : T.ProEtᵒᵖ)
    (x : ((SpTowerShriek.ev l E T n).obj
      ((s.base.realization T).functor.obj M)).val.obj U) :
    HEq ((evaluationSectionIso l E s T n M U).hom x) x := by
  have h := eq_of_heq ((s.base.sections T M n U).trans
    ((s.towers T).sections M n U).symm)
  exact moduleCast_heq h x

private def evaluationObjectIso (s : Coefficients l E) (T : Scheme.{u})
    (n : ℕ) (M : spCoefficientTowers l E T) :
    (SpTowerShriek.ev l E T n).obj ((s.base.realization T).functor.obj M) ≅
      (spCoefficientEvaluation l E T (s.towers T).equivalence n).obj M := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (evaluationSectionIso l E s T n M) ?_
  intro U V f
  have hU := eq_of_heq ((s.base.sections T M n U).trans
    ((s.towers T).sections M n U).symm)
  have hV := eq_of_heq ((s.base.sections T M n V).trans
    ((s.towers T).sections M n V).symm)
  have hr : ((WeilConjectures.SemilinearSections.ring
      (WeilConjectures.coefficientSequenceTopology (Scheme.ProEt.topology T))
      (WeilConjectures.SemilinearSections.systemRing
        (Scheme.ProEt.topology T) (SpTowerShriek.B l E T)
        (SpTowerShriek.tau l E T))).obj.map
          (Prod.mkHom (𝟙 n) f.unop).op).hom =
      ((SpTowerShriek.B l E T n).obj.map f).hom := by
    change ((forget₂ CommRingCat RingCat).map
      ((((WeilConjectures.SemilinearSections.rings
        (Scheme.ProEt.topology T) (SpTowerShriek.B l E T)
        (SpTowerShriek.tau l E T)).map (𝟙 (op n))).hom.app U) ≫
        (SpTowerShriek.B l E T n).obj.map f)).hom = _
    rw [(WeilConjectures.SemilinearSections.rings
      (Scheme.ProEt.topology T) (SpTowerShriek.B l E T)
      (SpTowerShriek.tau l E T)).map_id]
    rfl
  ext x
  exact semilinearCast_sections _ _ hr hU hV
    (((s.base.realization T).functor.obj M).val.map
      (Prod.mkHom (𝟙 n) f.unop).op)
    (((s.towers T).equivalence.functor.obj M).level n |>.val.map f)
    ((s.base.restrictions T M (Prod.mkHom (𝟙 n) f.unop).op).trans
      ((s.towers T).restrictions M n f).symm) x

private def normalizedEvaluation (s : Coefficients l E) : Evaluation l E s where
  ordinary T n := NatIso.ofComponents (evaluationObjectIso l E s T n) (by
    intro M N a
    ext U x
    have h := moduleCast_naturality
      (eq_of_heq ((s.base.sections T M n U).trans
        ((s.towers T).sections M n U).symm))
      (eq_of_heq ((s.base.sections T N n U).trans
        ((s.towers T).sections N n U).symm))
      (((s.base.realization T).functor.map a).val.app (op (n, U.unop)))
      (((s.towers T).equivalence.functor.map a).app n |>.val.app U)
      ((s.base.morphisms T a (op (n, U.unop))).trans
        ((s.towers T).morphisms a n U).symm)
    exact congrArg (fun t ↦ t x) h)
  sections T n M U x := evaluationSectionIso_sections l E s T n M U x

private theorem finiteOpenSlicePresentation (b : SpTowerShriek.Base l E)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ) :
    ∃ e : Scheme.proEtaleRingModules U (SpTowerShriek.B l E U n) ≌
        SheafOfModules.{u + 1} (((sheafCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (SpTowerShriek.B l E T n)).over (Scheme.ProEt.mk j)),
      Nonempty (Scheme.sfIntrinsicExtensionByZero j (SpTowerShriek.R l E n) ≅
        e.functor ⋙ localizedModuleExtension (SpTowerShriek.B l E T n)
          (Scheme.ProEt.mk j)) := by
  let := b.finite n
  let a := SpTowerShriek.finiteOpenAdjunction l E b j n
  let q := a.leftAdjointUniq (Adjunction.ofIsRightAdjoint
    (Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) j))
  obtain ⟨e, ⟨he⟩⟩ := Scheme.proEtaleOpen_slicePresentation j
    (SpTowerShriek.B l E T n) (SpTowerShriek.B l E U n)
    (Scheme.proEtaleConstantRingComparison j (SpTowerShriek.R l E n))
  exact ⟨e, ⟨q ≪≫ he⟩⟩

private theorem finiteReduction_supported (s : Coefficients l E)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (N : Integral l E U) (n : ℕ) :
    (Scheme.sfIntrinsicExtensionByZero j (SpTowerShriek.R l E n)).mapDerivedCategory.essImage
      ((SpTowerShriek.Ev l E T n).obj ((derivedReduction l E s T).obj
        ((CondensedRing.openImmersionLowerShriek
          (spIntegralCondensed l E) j).mapDerivedCategory.obj N))) := by
  classical
  let := s.base.finite n
  let W := Scheme.ProEt.mk j
  let a := spIntegralReductionScalar l E T (s.reduction T).coefficient n
  let A := (s.towers T).scalar a
  let B := (nonempty_systemScalarModel
    (((Scheme.ProEt.topology T).overPullback CommRingCat.{u + 1} W).map a)).some
  obtain ⟨eR, ⟨hR⟩⟩ := internalOpenSlicePresentation (spIntegralCondensed l E) j
  obtain ⟨eS, ⟨hS⟩⟩ := finiteOpenSlicePresentation l E s.base j n
  let := Functor.additive_of_preserves_binary_products eR.functor
  let := Functor.additive_of_preserves_binary_products eS.functor
  let := Functor.additive_of_preserves_binary_products eS.inverse
  let M := (((spIntegralModuleEquivalence l E U).functor ⋙ eR.functor).mapDerivedCategory.obj N)
  let Y := B.model.T.obj M
  let Z := eS.mapDerivedCategory.inverse.obj Y
  let hRD := Functor.mapDerivedCategorySquareIso
    (F₁ := CondensedRing.openImmersionLowerShriek (spIntegralCondensed l E) j)
    (F₂ := (spIntegralModuleEquivalence l E T).functor)
    (G₁ := (spIntegralModuleEquivalence l E U).functor ⋙ eR.functor)
    (G₂ := localizedModuleExtension (spIntegralSectionRing l E T) W) hR
  let hSD := Functor.mapDerivedCategoryNatIso hS ≪≫
    Functor.mapDerivedCategoryCompIso eS.functor
      (localizedModuleExtension (SpTowerShriek.B l E T n) W)
  let K := (CondensedRing.openImmersionLowerShriek
    (spIntegralCondensed l E) j).mapDerivedCategory.obj N
  let er : (SpTowerShriek.Ev l E T n).obj ((derivedReduction l E s T).obj K) ≅
      A.model.T.obj ((sectionEquivalence l E T).functor.obj K) :=
    (Evaluation.derived l E s (normalizedEvaluation l E s) T n).app ((red l E s T).obj K) ≪≫
      ((s.reduction T).evaluation n).app ((sectionEquivalence l E T).functor.obj K)
  let t := er ≪≫ A.model.T.mapIso (hRD.app N) ≪≫
    (localizedScalarOpenIso W a A B).app M ≪≫
    (localizedModuleExtension (SpTowerShriek.B l E T n) W).mapDerivedCategory.mapIso
      (eS.mapDerivedCategory.counitIso.app Y).symm ≪≫ (hSD.app Z).symm
  exact ⟨Z, ⟨t.symm⟩⟩

/-- Each finite evaluation of the tower open counit is invertible on a reduced
integral extension by zero. Source: blueprint integral direct-image proof paragraph
(2), exact slice tensor identity; this is the finite-level support step only.

Proof: identify the two ordinary tower evaluations by the identity on their
recorded sections, restriction maps and morphisms, and localize this comparison.
The evaluation field of the reduction tower then identifies the evaluated reduced
object with the recorded derived scalar extension of the integral section module.
Use the actual internal/section-module comparisons and the open slice presentation
to express integral extension by zero as localized module extension. Restriction
of scalars commutes with restriction to that slice, sectionwise. Localize this
exact square and conjugate under the scalar and open adjunctions. Uniqueness of
left adjoints identifies scalar extension of slice extension with slice extension
of scalar extension, including for nonflat coefficient maps and unbounded complexes.
The finite open slice presentation therefore puts the evaluated reduced object in
the essential image of finite extension by zero. Finite extension is fully
faithful, and the exact localized adjunction remains fully faithful because its
unit is the localization of an invertible unit. Its counit is invertible on the
preceding object. Finally, the recorded derived open-unit evaluation equation
identifies the inverse mate of the evaluation square; the mate counit equation
expresses the evaluated tower counit as the finite counit composed with the two
invertible comparison maps. Empty opens, identity opens, zero complexes and n=0
are covered by the same argument.
(blueprint: lem-sp-current-finite-open-support). -/
theorem finite_open_reduction_support (s : Coefficients l E)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (N : Integral l E U) (n : ℕ) :
    IsIso ((SpTowerShriek.Ev l E T n).map
      ((s.operations.openOp j).derivedAdjunction.counit.app
        ((derivedReduction l E s T).obj
          ((CondensedRing.openImmersionLowerShriek
            (spIntegralCondensed l E) j).mapDerivedCategory.obj N)))) := by
  let := s.base.finite n
  let o := s.operations.openOp j
  let a := SpTowerShriek.finiteOpenAdjunction l E s.base j n
  let R := Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) j
  let b := a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
    R.rightDerivedFunctorIsoMapDerivedCategory
  let L := Scheme.sfIntrinsicExtensionByZero j (SpTowerShriek.R l E n)
  have : L.Full := by
    dsimp only [L, Scheme.sfIntrinsicExtensionByZero]
    infer_instance
  have : L.Faithful := by
    dsimp only [L, Scheme.sfIntrinsicExtensionByZero]
    infer_instance
  have : IsIso (SpTowerShriek.finiteOpenAdjunction l E s.base j n).unit :=
    Adjunction.unit_isIso_of_L_fully_faithful _
  let ff := b.fullyFaithfulLOfCompIsoId
    ((Functor.mapDerivedCategoryCompIso L
      (Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) j)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (asIso (SpTowerShriek.finiteOpenAdjunction l E s.base j n).unit).symm ≪≫
      Functor.mapDerivedCategoryIdIso _)
  have := ff.full
  have := ff.faithful
  let K := (derivedReduction l E s T).obj
    ((CondensedRing.openImmersionLowerShriek (spIntegralCondensed l E) j).mapDerivedCategory.obj N)
  have : IsIso (b.counit.app ((SpTowerShriek.Ev l E T n).obj K)) :=
    b.isIso_counit_app_iff_mem_essImage.mpr (finiteReduction_supported l E s j N n)
  exact evaluated_counit_isIso o.derivedAdjunction b
    (SpTowerShriek.openEvaluation l E s.base o n)
    ((s.operations.geometry j).pullEvaluation n)
    (SpTowerShriek.open_adjunction_unit_evaluation l E s.base o n) K

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current
