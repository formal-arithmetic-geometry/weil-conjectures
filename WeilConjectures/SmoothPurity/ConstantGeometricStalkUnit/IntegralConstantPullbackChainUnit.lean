/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.CoefficientPullbackUnitCoordinates
import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
import all WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.CoefficientPullbackUnitCoordinates
import all WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure
import all WeilConjectures.ZetaWeil.ConstantPullbackUnitQuasiIsomorphism.ConstantPullbackUnitQuasiIsomorphism
import WeilConjectures.SmoothPurity.ConstantScalarStrictUnit.ConstantScalarStrictUnit

/-! # The finite quotient of the normalized integral coefficient unit

Source: Stacks 099N(5) and the normalized strict Roos construction of the constant unit.
(blueprint: lem-pur-integral-constant-pullback-chain-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
attribute [local implicit_reducible] WeilConjectures.scalarReductionDerivedRestriction
  WeilConjectures.integralCoefficientSheaf WeilConjectures.integralCoefficientCommRingSheaf
  WeilConjectures.finiteConstantCoefficientObject
  WeilConjectures.constantWeilIntegralGood WeilConjectures.constantWeilIntegralObject
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.integralOperationsGoodComplex
  WeilConjectures.integralOperationsPullbackOnGood
  WeilConjectures.integralOperationsGoodLocalization
  WeilConjectures.constantWeilIntegralComplex
namespace WeilConjectures.ConstantGeometricStalkUnit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Finite multiplication in the constant-ring pullback presentation.
Source: Stacks 03D6; the unit-preserving finite pullback change of presentation.
(blueprint: lem-pur-integral-constant-pullback-chain-unit). -/
def finiteRingUnit {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f).obj
      (finiteConstantCoefficientObject l E Y n) ≅ finiteConstantCoefficientObject l E X n :=
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  (openSquareDerivedPullbackModel (Padic.coefficientExtensionRing l E (n + 1)) f).app _ ≪≫
    finiteUnit l E f n

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence HasDerivedCategory.standard limit
  finiteRegularIso finiteSingleRegularIso finiteRingUnit

private theorem finite_coordinate_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    (integralFinitePullbackModel l E f n).hom.app
        (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) ≫
      (openSquarePullbackModel (Padic.coefficientExtensionRing l E (n + 1)) f).hom.app
        (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) ≫ finiteUnitHom l E f n =
      (ConstantPullbackUnitQuasiIsomorphism.stalkFinitePullbackRegularIso l E f n).hom := by
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let M := SheafOfModules.unit (integralCoefficientSheaf l E Y n)
  have he : (integralFinitePullbackModel l E f n).hom.app M ≫
        (openSquarePullbackModel A f).hom.app M =
      (inverseImageFiniteIntrinsicPullbackComparison f A).hom.app M := by
    let adj₁ := coefficientProEtaleModuleAdjunction.{u, u} f (CommRingCat.of (ULift.{u + 1} A))
    let adj₂ := sfIntrinsicConstantModuleAdjunction f A
    apply (adj₁.homEquiv _ _).injective
    change (adj₁.homEquiv _ _) _ =
      (adj₁.homEquiv _ _) ((adj₁.leftAdjointUniq adj₂).hom.app M)
    rw [adj₁.homEquiv_leftAdjointUniq_hom_app adj₂, Adjunction.homEquiv_unit]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change ((openSquarePullbackModel A f).hom.app M).val.app
      (op ((proEtaleBaseChange f).obj U.unop))
        (((integralFinitePullbackModel l E f n).hom.app M).val.app
          (op ((proEtaleBaseChange f).obj U.unop)) ((adj₁.unit.app M).val.app U m)) = _
    erw [(integralFinitePullbackModel_existsUnique l E f n).exists.choose_spec]
    exact (openSquarePullbackModel_existsUnique A f).exists.choose_spec M U.unop m
  rw [← Category.assoc, he]
  simpa only [ConstantPullbackUnitQuasiIsomorphism.stalkFinitePullbackRegularIso,
    asIso_hom] using WeilConjectures.ConstantGeometricStalkUnit.finiteUnitHom_tensor l E f n

private def finiteChainUnit {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  ((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).map
      (WeilConjectures.finiteSingleRegularIso l E Y n).hom ≫
    ((integralOperationsLevelPullback l E f n).mapCochainComplexSingleFunctor 0).hom.app
      (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) ≫
    (CochainComplex.singleFunctor _ 0).map
      (ConstantPullbackUnitQuasiIsomorphism.stalkFinitePullbackRegularIso l E f n).hom

attribute [local irreducible] finiteChainUnit

private theorem chain_projection {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    integralChainUnit l E f ≫
      CochainComplex.mappingCocone.fst (constantWeilPullbackRoosEndomorphism l E f) ≫
      Pi.π (fun j ↦ (constantWeilPullbackTower l E f).obj (op j)) n ≫
      ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).map
        (finiteChainUnit l E f n) =
      ConstantScalarStrictUnit.projectionComplex l E X n := by
  have he := WeilConjectures.normalized_chainUnit_unique l E f _
    (integralChainUnit_existsUnique l E f).exists.choose_spec
  change integralChainUnit l E f = _ at he
  erw [he]
  simp only [WeilConjectures.chainUnitCandidate,
    CochainComplex.mappingCocone.lift_fst_assoc, WeilConjectures.pullbackUnitProduct,
    Pi.lift_π_assoc]
  have hp := ConstantPullbackUnitQuasiIsomorphism.stalkPullbackLevelRegularIso_projection
    l E f n
  apply (cancel_mono ((HomologicalComplex.singleMapHomologicalComplex
    (scalarReductionRestriction l E X n) (.up ℤ) 0).hom.app
      (SheafOfModules.unit (integralCoefficientSheaf l E X n)))).1
  simpa only [Category.assoc, ConstantPullbackUnitQuasiIsomorphism.stalkPullbackLevelRegularIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, finiteChainUnit,
    ConstantScalarStrictUnit.projectionComplex, ConstantScalarStrictUnit.projectionModule,
    Iso.inv_hom_id_app, Category.comp_id, Functor.mapCochainComplexSingleFunctor] using! hp

end WeilConjectures.ConstantGeometricStalkUnit
