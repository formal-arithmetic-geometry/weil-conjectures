/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedOpenScalarLimitCoherence
public import WeilConjectures.AlgebraicGeometry.StrictTowerExchangeMateNormalization
public import WeilConjectures.AlgebraicGeometry.ProjectionCompactification
public import WeilConjectures.AlgebraicGeometry.StrictConstantTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.StrictTowerOpenExtension
public import WeilConjectures.AlgebraicGeometry.CompletedPullback
public import WeilConjectures.AlgebraicGeometry.IntrinsicCompletion
public import WeilConjectures.AlgebraicGeometry.CompletedExtensionZeroComparison
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.OpenImmersionSquare
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.CategoryTheory.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatumSupplement
import all WeilConjectures.CategoryTheory.ExactEquivalenceDerivedSquares
import all WeilConjectures.CategoryTheory.StrictRoosShiftLocalization
import all WeilConjectures.AlgebraicGeometry.NormalizedLimitSquareCoherence
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
import all WeilConjectures.CategoryTheory.StrictRoosComparison
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Preadditive.Injective.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import all WeilConjectures.CategoryTheory.StrictRoosDerivation
import all WeilConjectures.CategoryTheory.StrictRoosModel
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import all Mathlib.CategoryTheory.Abelian.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all WeilConjectures.Algebra.Homology.RoosComplex
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import all WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all WeilConjectures.CategoryTheory.StrictRoosNormalization
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import all Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import all Mathlib.Logic.Denumerable
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosDescent
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosResolution
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosCompatibility
import all WeilConjectures.AlgebraicGeometry.StrictTowerExchangeMateNormalization
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.CategoryTheory.ExchangeMateCube
import WeilConjectures.CategoryTheory.DerivedExactCube
import all WeilConjectures.AlgebraicGeometry.RingedOpenScalarLimitCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleRingedOpenExtensionProducts
import WeilConjectures.AlgebraicGeometry.ProEtaleOpenSlicePresentation
import WeilConjectures.CategoryTheory.RingedOpenScalarAdjunction
import all WeilConjectures.AlgebraicGeometry.OpenImmersionTensorPiece
import WeilConjectures.AlgebraicGeometry.RingedOpenStrictReduction
import WeilConjectures.AlgebraicGeometry.CompleteCompactSupportProetale
import all WeilConjectures.AlgebraicGeometry.ConstantTowerDirectImageNormalization
import all WeilConjectures.AlgebraicGeometry.CompletedDirectImageLimits
import all WeilConjectures.SixFunctors.ExactLocalizationInverseMate

/-! # Transport of normalized completed open endpoints

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-cbc,
lem-cbc-completed-extension-zero-comparison.proof.md, finite-exchange and final
inverse-limit paragraphs (blueprint: lem-cbc-completed-open-endpoint-limit-transport).

All towers are derived objects of the category of strict module sequences. The
constant and completed coefficient rings remain distinct. The limit comparison
is the constant-diagram mate: its augmentation normalization uniquely fixes it,
and identifies it with the signed Roos / K-injective comparison of
`exactProductFunctorStrictLimit`. No comparison is chosen from a triangle alone.
-/

@[expose] public noncomputable section
set_option autoImplicit false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t uC vC uD vD
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] cbcAbSheafify cbcAbLocallyBijective
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Finite limits of strict diagrams are computed at each level.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
instance cbcEndpointWhiskerLimits {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D] [HasFiniteLimits C]
    (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F) where
  preservesFiniteLimits _ _ _ := inferInstance

/-- Finite colimits of strict diagrams are computed at each level.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
instance cbcEndpointWhiskerColimits {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D] [HasFiniteColimits C]
    (F : C ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F) where
  preservesFiniteColimits _ _ _ := inferInstance

/-- The existing exact ringed extension by zero, with its universal open adjunction.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
abbrev cbcEndpointOpen {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :=
  proEtaleRingOpenExtension j (d.completedRing T) (d.completedRing U) (d.integralRingIso j)

/-- The ordinary section-normalized open adjunction.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointOpenAdj {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcEndpointOpen d j ⊣ proEtaleRingModulePullback j (d.completedRing T)
      (d.completedRing U) (d.integralRingIso j) := Adjunction.ofIsRightAdjoint _

/-- The exact derived open adjunction, using the published derived pullback.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointDerivedOpenAdj {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    (cbcEndpointOpen d j).mapDerivedCategory ⊣ d.pull j :=
  Adjunction.ofNatIsoRight (cbcEndpointOpenAdj d j).mapDerivedCategoryRightDerivedAdjunction
    (proEtaleRingModulePullback j (d.completedRing T) (d.completedRing U)
      (d.integralRingIso j)).rightDerivedFunctorIsoMapDerivedCategory

/-- The open adjunction on actual derived strict towers.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointTowerOpenAdj {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcTowerDerived (cbcEndpointOpen d j) ⊣ d.towerPull j :=
  Adjunction.ofNatIsoRight
    ((cbcEndpointOpenAdj d j).whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction
    (d.towerModulePull j).rightDerivedFunctorIsoMapDerivedCategory

attribute [local irreducible] cbcEndpointOpenAdj
  ProEtale.StrictTower.moduleJAdj exchangeOrdinaryResPull

/-- The inverse scalar/open comparison is the mate of canonical restriction/pullback.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointScalarOpenInv {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    proEtaleRingRestrictScalars (exchangeScalar d U) ⋙ ProEtale.StrictTower.moduleJ A j ⟶
      cbcEndpointOpen d j ⋙ proEtaleRingRestrictScalars (exchangeScalar d T) :=
  (mateEquiv (cbcEndpointOpenAdj d j) (ProEtale.StrictTower.moduleJAdj A j)).symm
    (exchangeOrdinaryResPull d j).hom

private theorem cbcEndpointInverseMate_app
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {LT : E ⥤ F} {RT : F ⥤ E}
    (a : L ⊣ R) (b : LT ⊣ RT) (P : C ⥤ E) (Q : D ⥤ F)
    (s : R ⋙ P ⟶ Q ⋙ RT) (K : C) :
    ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ s)).natTrans.app K =
      (b.homEquiv _ _).symm (P.map (a.unit.app K) ≫ s.app (L.obj K)) := by
  apply (b.homEquiv _ _).injective
  erw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ s) K).symm

/-- The scalar/open mate is the identity of underlying extension presheaves, hence invertible.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport).
Proof: Apply lem-cbc-ringed-open-scalar-limit-coherence after the localized-site
transport of lem-pur-site-restriction-module-adjunction-exact. Restriction of scalars
leaves every direct-sum extension generator and its restriction map unchanged. The
identity on these presheaves descends through abelian sheafification. Its unit and
counit equations identify its inverse with the displayed mate of
exchangeOrdinaryResPull, whose coefficient maps send constants to their residues.
Thus this is the specified identity comparison, including on the empty open. -/
theorem cbcEndpointScalarOpenInv_isIso {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] : IsIso (cbcEndpointScalarOpenInv d j) := by
  let R := exchangeConstantRing T A
  let S := d.completedRing T
  let adjS := Adjunction.ofIsRightAdjoint
    (proEtaleRingModulePullback j S (d.completedRing U) (d.integralRingIso j))
  let adjR := ProEtale.StrictTower.moduleJAdj A j
  let e := (cbcEndpointOpenAdj d j).leftAdjointUniq adjS
  obtain ⟨eS, ⟨hS⟩⟩ := proEtaleOpen_slicePresentation j
    S (d.completedRing U) (d.integralRingIso j)
  obtain ⟨eR, ⟨hR⟩⟩ := proEtaleOpen_slicePresentation j
    R (exchangeConstantRing U A) (exchangeConstantIso j A)
  let := SheafOfModules.localizedUnit_isIso j S
  let := SheafOfModules.localizedUnit_isIso j R
  let ffS := (SheafOfModules.localizedModuleAdjunctionIndependent
    S (ProEt.mk j)).fullyFaithfulLOfIsIsoUnit
  let ffR := (SheafOfModules.localizedModuleAdjunctionIndependent
    R (ProEt.mk j)).fullyFaithfulLOfIsIsoUnit
  have := ffS.full
  have := ffS.faithful
  have := ffR.full
  have := ffR.faithful
  have : (cbcEndpointOpen d j).Full := Functor.Full.of_iso (e ≪≫ hS).symm
  have : (cbcEndpointOpen d j).Faithful :=
    Functor.Faithful.of_iso (e ≪≫ hS).symm
  have : (ProEtale.StrictTower.moduleJ A j).Full := Functor.Full.of_iso hR.symm
  have : (ProEtale.StrictTower.moduleJ A j).Faithful := Functor.Faithful.of_iso hR.symm
  have : IsIso (cbcEndpointOpenAdj d j).unit := inferInstance
  obtain ⟨_, _, scalarIso, _, _⟩ :=
    SheafOfModules.RingedOpenScalar.comparison.{t + 1, t, 0, t + 2}
      (ProEt.mk j) (exchangeScalar d T)
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  let LR := SheafOfModules.localizedModuleExtension.{t} R (ProEt.mk j)
  have hs : LR.essImage
      ((proEtaleRingRestrictScalars (exchangeScalar d T)).obj ((cbcEndpointOpen d j).obj M)) := by
    refine Functor.essImage.ofIso
      ((scalarIso.app (eS.functor.obj M)).symm ≪≫
        (proEtaleRingRestrictScalars (exchangeScalar d T)).mapIso ((e ≪≫ hS).app M).symm) ?_
    exact LR.obj_mem_essImage _
  have ht : (eR.functor ⋙ LR).essImage
      ((proEtaleRingRestrictScalars (exchangeScalar d T)).obj ((cbcEndpointOpen d j).obj M)) :=
    Functor.essImage_comp_apply_of_essSurj.mpr hs
  have : IsIso (adjR.counit.app
      ((proEtaleRingRestrictScalars (exchangeScalar d T)).obj ((cbcEndpointOpen d j).obj M))) :=
    adjR.isIso_counit_app_iff_mem_essImage.mpr (Functor.essImage.ofNatIso hR.symm ht)
  change IsIso (((mateEquiv (cbcEndpointOpenAdj d j) adjR).symm _).natTrans.app M)
  simp only [mateEquiv_symm_apply, TwoSquare.natTrans, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.comp_map, Functor.comp_obj, Category.id_comp]
  have : IsIso ((proEtaleRingRestrictionPullbackInv j
      (exchangeConstantRing T A) (d.completedRing T)
      (exchangeConstantRing U A) (d.completedRing U)
      (exchangeScalar d T) (exchangeScalar d U)
      (exchangeConstantIso j A) (d.integralRingIso j) (exchangeScalar_comm d j))) :=
    proEtaleRingRestrictionPullbackInv_isIso _ _ _ _ _ _ _ _ _ _
  infer_instance

/-- The specified scalar/open isomorphism, in the direction used by the endpoints.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointScalarOpen {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcEndpointOpen d j ⋙ proEtaleRingRestrictScalars (exchangeScalar d T) ≅
      proEtaleRingRestrictScalars (exchangeScalar d U) ⋙ ProEtale.StrictTower.moduleJ A j :=
  (@asIso _ _ _ _ (cbcEndpointScalarOpenInv d j)
    (cbcEndpointScalarOpenInv_isIso d j)).symm

/-- The same specified scalar/open comparison on derived objects.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointDerivedScalarOpen {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] :=
  cbcDerivedSquare (cbcEndpointOpen d j)
    (proEtaleRingRestrictScalars (exchangeScalar d T))
    (proEtaleRingRestrictScalars (exchangeScalar d U)) (ProEtale.StrictTower.moduleJ A j)
    (cbcEndpointScalarOpen d j)

/-- The same specified scalar/open comparison on derived strict towers.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointTowerScalarOpen {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] :=
  cbcDerivedTowerSquare (cbcEndpointOpen d j)
    (proEtaleRingRestrictScalars (exchangeScalar d T))
    (proEtaleRingRestrictScalars (exchangeScalar d U)) (ProEtale.StrictTower.moduleJ A j)
    (cbcEndpointScalarOpen d j)

/-- The inverse quotient/open comparison is the transpose of the reduced open unit.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointReductionInv {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : d.derived U) :
    (cbcTowerDerived (cbcEndpointOpen d j)).obj ((completedReductionTower U d).obj K) ⟶
      (completedReductionTower T d).obj ((cbcEndpointOpen d j).mapDerivedCategory.obj K) :=
  ((cbcEndpointTowerOpenAdj d j).homEquiv _ _).symm
    ((completedReductionTower U d).map ((cbcEndpointDerivedOpenAdj d j).unit.app K) ≫
      (d.reductionTowerPullbackIso j).inv.app ((cbcEndpointOpen d j).mapDerivedCategory.obj K))

private theorem cbcEndpointReduction_naturality {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (K L : d.derived U) (k : K ⟶ L) :
    (cbcTowerDerived (cbcEndpointOpen d j)).map ((completedReductionTower U d).map k) ≫
        cbcEndpointReductionInv d j L =
      cbcEndpointReductionInv d j K ≫ (completedReductionTower T d).map
        ((cbcEndpointOpen d j).mapDerivedCategory.map k) := by
  let n := ((mateEquiv (cbcEndpointDerivedOpenAdj d j) (cbcEndpointTowerOpenAdj d j)).symm
    (TwoSquare.mk _ _ _ _ (d.reductionTowerPullbackIso j).inv)).natTrans
  have h (M : d.derived U) : n.app M = cbcEndpointReductionInv d j M :=
    cbcEndpointInverseMate_app (cbcEndpointDerivedOpenAdj d j) (cbcEndpointTowerOpenAdj d j)
      (completedReductionTower U d) (completedReductionTower T d)
      (d.reductionTowerPullbackIso j).inv M
  have hn := n.naturality k
  simpa only [Functor.comp_map, h] using hn


private theorem cbcEndpointExactAdjunction_eq
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
    {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R) :
    a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        R.rightDerivedFunctorIsoMapDerivedCategory = exactLocalizationDerivedAdjunction a := by
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  let K' := (HomotopyCategory.quotient A (.up ℤ)).obj K
  have hs : (a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        R.rightDerivedFunctorIsoMapDerivedCategory).unit.app (DerivedCategory.Q.obj K) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K') ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K') =
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app K') := by
    simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Category.assoc]
    rw [← R.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
    have hu := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso A (.up ℤ))
      L.mapDerivedCategoryFactorsh.hom R.rightDerivedFunctorUnit K'
    change a.mapDerivedCategoryRightDerivedAdjunction.unit.app
      (DerivedCategory.Q.obj K) ≫
      R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app K') = _ at hu
    erw [reassoc_of% hu]
    have hf := congr_app R.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
      ((L.mapHomotopyCategory (.up ℤ)).obj K')
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
    erw [reassoc_of% hf, Iso.inv_hom_id_app, Category.comp_id]
  have he : (exactLocalizationDerivedAdjunction a).unit.app (DerivedCategory.Q.obj K) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K') ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K') =
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app K') := by
    rw [CategoryTheory.exact_unit_app]
    have hl := AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.factorsh_hom L K
    have hr := AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.factorsh_hom R
      ((L.mapHomologicalComplex (.up ℤ)).obj K)
    change L.mapDerivedCategoryFactorsh.hom.app K' = _ at hl
    change R.mapDerivedCategoryFactorsh.hom.app
      ((L.mapHomotopyCategory (.up ℤ)).obj K') = _ at hr
    rw [hl, hr]
    simp only [Category.assoc, ← R.mapDerivedCategory.map_comp_assoc,
      Iso.inv_hom_id_app]
    erw [R.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app,
      Category.comp_id]
    change DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) =
      DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient A (.up ℤ)).obj K))
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
    rfl
  exact (cancel_mono (R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K') ≫
    R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K'))).mp
    (by simpa only [Category.assoc] using hs.trans he.symm)



private theorem cbcEndpointExact_unit_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : L ⊣ R) [IsIso a.unit] :
    IsIso (exactLocalizationDerivedAdjunction a).unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  let P := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  have h (P : CochainComplex C ℤ) :
      IsIso ((exactLocalizationDerivedAdjunction a).unit.app (DerivedCategory.Q.obj P)) := by
    rw [CategoryTheory.exact_unit_app]
    have : IsIso ((a.mapHomologicalComplex (.up ℤ)).unit.app P) := by
      have hc (q : ℤ) :
          IsIso (((a.mapHomologicalComplex (.up ℤ)).unit.app P).f q) := by
        simp only [Adjunction.mapHomologicalComplex_unit_app_f]
        infer_instance
      exact HomologicalComplex.Hom.isIso_of_components _
    infer_instance
  have := h P
  have hn := (exactLocalizationDerivedAdjunction a).unit.naturality e.hom
  dsimp only [Functor.id_map] at hn
  have : IsIso (e.hom ≫ (exactLocalizationDerivedAdjunction a).unit.app X) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left e.hom _

private theorem cbcEndpointOpen_fullFaithful {U T : Scheme.{t}}
    (j : U ⟶ T) [IsOpenImmersion j] :
    (cbcEndpointOpen d j).Full ∧ (cbcEndpointOpen d j).Faithful := by
  obtain ⟨e, ⟨i⟩⟩ := proEtaleOpen_slicePresentation j
    (d.completedRing T) (d.completedRing U) (d.integralRingIso j)
  let := SheafOfModules.localizedUnit_isIso j (d.completedRing T)
  let ff := (SheafOfModules.localizedModuleAdjunctionIndependent
    (d.completedRing T) (ProEt.mk j)).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  exact ⟨Functor.Full.of_iso i.symm, Functor.Faithful.of_iso i.symm⟩

private theorem cbcEndpointReduction_isIso {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] (K : d.derived U) : IsIso (cbcEndpointReductionInv d j K) := by
  let a := cbcEndpointOpenAdj d j
  let b := cbcEndpointTowerOpenAdj d j
  obtain ⟨hfull, hfaith⟩ := cbcEndpointOpen_fullFaithful d j
  have : IsIso a.unit := inferInstance
  have hu := cbcEndpointExact_unit_isIso a
  have : IsIso (cbcEndpointDerivedOpenAdj d j).unit := by
    dsimp only [cbcEndpointDerivedOpenAdj]
    rw [cbcEndpointExactAdjunction_eq]
    exact hu
  let H := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (cbcEndpointOpen d j)
  have : H.Full := inferInstance
  have : H.Faithful := inferInstance
  have : IsIso (a.whiskerRight ℕᵒᵖ).unit := inferInstance
  have hub := cbcEndpointExact_unit_isIso (a.whiskerRight ℕᵒᵖ)
  have : IsIso b.unit := by
    dsimp only [b, cbcEndpointTowerOpenAdj]
    rw [cbcEndpointExactAdjunction_eq]
    exact hub
  have hfullb := b.fullyFaithfulLOfIsIsoUnit
  have := hfullb.full
  have := hfullb.faithful
  let ag := Adjunction.ofNatIsoRight (cbcOpenAdjunction d j inferInstance)
    (@asIso _ _ _ _ (cbcPullToRestriction d j) (cbcPullToRestriction_isIso d j)).symm
  let e := a.leftAdjointUniq ag
  have := cbcOpenShriek_additive d j inferInstance
  have := cbcOpenShriek_finiteLimits d j inferInstance
  have := cbcOpenShriek_finiteColimits d j inferInstance
  let ed := Functor.mapDerivedCategoryNatIso e
  let et := Functor.mapDerivedCategoryNatIso
    ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso e)
  let W := cbcOpenObject j inferInstance
  have : IsOpenImmersion W.hom := ‹IsOpenImmersion j›
  let rho := (cbcRingedOpenStrictReduction W d).exists.choose
  let k : (cbcEndpointOpen d j).mapDerivedCategory ⋙ completedReductionTower T d ≅
      completedReductionTower U d ⋙ cbcTowerDerived (cbcEndpointOpen d j) :=
    Functor.isoWhiskerRight ed (completedReductionTower T d) ≪≫ rho ≪≫
      Functor.isoWhiskerLeft (completedReductionTower U d) et.symm
  have hc : IsIso (b.counit.app ((completedReductionTower T d).obj
      ((cbcEndpointOpen d j).mapDerivedCategory.obj K))) :=
    b.isIso_counit_app_iff_mem_essImage.mpr
      (Functor.essImage.ofIso (k.symm.app K) (Functor.obj_mem_essImage _ _))
  have : IsIso (b.counit.app ((completedReductionTower T d).obj
      ((cbcEndpointOpen d j).mapDerivedCategory.obj K))) := hc
  let n := ((mateEquiv (cbcEndpointDerivedOpenAdj d j) b).symm
    (TwoSquare.mk _ _ _ _ (d.reductionTowerPullbackIso j).inv)).natTrans
  have hn : n.app K = cbcEndpointReductionInv d j K :=
    cbcEndpointInverseMate_app _ _ _ _ _ K
  rw [← hn]
  dsimp only [n]
  simp only [mateEquiv_symm_apply, TwoSquare.natTrans, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.comp_map, Functor.comp_obj, Category.id_comp, TwoSquare.mk]
  erw [(cbcTowerDerived (cbcEndpointOpen d j)).map_id,
    (cbcTowerDerived (cbcEndpointOpen d j)).map_id,
    Category.id_comp, Category.id_comp, Category.comp_id]
  have : IsIso ((cbcTowerDerived (cbcEndpointOpen d j)).map
      ((completedReductionTower U d).map ((cbcEndpointDerivedOpenAdj d j).unit.app K))) :=
    inferInstance
  have : IsIso ((cbcTowerDerived (cbcEndpointOpen d j)).map
      ((d.reductionTowerPullbackIso j).inv.app
        ((cbcEndpointOpen d j).mapDerivedCategory.obj K))) := inferInstance
  infer_instance

/-- The canonical quotient/open comparison is invertible and natural before evaluation.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport).
Proof: Use the exact open adjunction and the canonical reduction/pullback
comparison of def-weil-pbc-completed-pullback. On a K-flat representative the
transpose is the tensor balancing map from open extension of its reduction to
reduction of its open extension. The inverse is the usual balanced section map.
Open extension preserves K-flatness: tensoring with an acyclic ambient complex
is extension of tensor with its exact restriction. The maps commute with quotient
transitions, differentials and quotient augmentations. They therefore give inverse
strict tower maps and descend through quasi-isomorphisms. Naturality follows from
the open unit and the normalized reduction/pullback comparison, without faithfulness
of derived evaluation. -/
theorem cbcEndpointReductionInv_properties {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] :
    (∀ K : d.derived U, IsIso (cbcEndpointReductionInv d j K)) ∧
      ∀ (K L : d.derived U) (k : K ⟶ L),
        (cbcTowerDerived (cbcEndpointOpen d j)).map ((completedReductionTower U d).map k) ≫
            cbcEndpointReductionInv d j L =
          cbcEndpointReductionInv d j K ≫ (completedReductionTower T d).map
            ((cbcEndpointOpen d j).mapDerivedCategory.map k) := by
  exact ⟨cbcEndpointReduction_isIso d j, cbcEndpointReduction_naturality d j⟩

/-- The natural inverse comparison, assembled using the preceding naturality statement.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointReductionInvNat {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    completedReductionTower U d ⋙ cbcTowerDerived (cbcEndpointOpen d j) ⟶
      (cbcEndpointOpen d j).mapDerivedCategory ⋙ completedReductionTower T d where
  app := cbcEndpointReductionInv d j
  naturality {_ _} k := (cbcEndpointReductionInv_properties d j).2 _ _ k

/-- The canonical quotient/open comparison on all strict transitions.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointReduction {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    (cbcEndpointOpen d j).mapDerivedCategory ⋙ completedReductionTower T d ≅
      completedReductionTower U d ⋙ cbcTowerDerived (cbcEndpointOpen d j) :=
  (NatIso.ofComponents
    (fun K ↦ @asIso _ _ _ _ ((cbcEndpointReductionInvNat d j).app K)
      ((cbcEndpointReductionInv_properties d j).1 K))
    (fun {_ _} k ↦ (cbcEndpointReductionInvNat d j).naturality k)).symm

/-- The quotient/open comparison followed by the specified scalar/open comparison.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointQuotientOpen {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    (cbcEndpointOpen d j).mapDerivedCategory ⋙ completedReductionTower T d ⋙
        exchangeTowerRes d T ≅
      completedReductionTower U d ⋙ exchangeTowerRes d U ⋙ ProEtale.StrictTower.J A j :=
  Functor.isoWhiskerRight (cbcEndpointReduction d j) (exchangeTowerRes d T) ≪≫
    Functor.isoWhiskerLeft (completedReductionTower U d) (cbcEndpointTowerScalarOpen d j)

section Limit
variable {T S : Scheme.{t}}
  {R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
  {R' : Sheaf (ProEt.topology S) CommRingCat.{t + 1}}

/-- The existing constant-tower / total-derived-limit adjunction for the actual coefficient ring.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointLimitAdj (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    (Functor.const ℕᵒᵖ : reductionModules T R ⥤ _).mapDerivedCategory ⊣ completedRlim T R :=
  (constLimAdj : (Functor.const ℕᵒᵖ : reductionModules T R ⥤ _) ⊣
    completedTowerLimit T R).mapDerivedCategoryRightDerivedAdjunction

/-- The exact constant-diagram comparison induced by the identity on every level.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointConst
    (F : reductionModules T R ⥤ reductionModules S R') [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.mapDerivedCategory ⋙ (Functor.const ℕᵒᵖ).mapDerivedCategory ≅
      (Functor.const ℕᵒᵖ).mapDerivedCategory ⋙ cbcTowerDerived F :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Functor.compConstIso ℕᵒᵖ F) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The normalized inverse-limit comparison as the constant-diagram adjunction mate.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointLimitMap
    (F : reductionModules T R ⥤ reductionModules S R') [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    completedRlim T R ⋙ F.mapDerivedCategory ⟶ cbcTowerDerived F ⋙ completedRlim S R' :=
  mateEquiv (cbcEndpointLimitAdj T R) (cbcEndpointLimitAdj S R')
    (cbcEndpointConst F).hom

/-- Strict-augmentation normalization, expressed through the derived constant-tower adjunction.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def CbcEndpointAugmentationNormalized
    (F : reductionModules T R ⥤ reductionModules S R') [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] : Prop :=
  ∀ (V : reductionDerivedCategory T R)
    (M : DerivedCategory (ℕᵒᵖ ⥤ reductionModules T R))
    (gamma : (Functor.const ℕᵒᵖ).mapDerivedCategory.obj V ⟶ M),
    F.mapDerivedCategory.map
        ((cbcEndpointLimitAdj T R).unit.app V ≫ (completedRlim T R).map gamma) ≫
        (cbcEndpointLimitMap F).app M =
      (cbcEndpointLimitAdj S R').unit.app (F.mapDerivedCategory.obj V) ≫
        (completedRlim S R').map
          ((cbcEndpointConst F).hom.app V ≫ (cbcTowerDerived F).map gamma)

private theorem cbcEndpointLimit_normalized
    (F : reductionModules T R ⥤ reductionModules S R') [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    CbcEndpointAugmentationNormalized F := by
  intro V M gamma
  rw [Functor.map_comp, Category.assoc]
  have hn := (cbcEndpointLimitMap F).naturality gamma
  change F.mapDerivedCategory.map ((completedRlim T R).map gamma) ≫ _ = _ at hn
  rw [hn]
  rw [← Category.assoc]
  erw [unit_mateEquiv (cbcEndpointLimitAdj T R) (cbcEndpointLimitAdj S R')
    (cbcEndpointConst F).hom V]
  simp only [Functor.comp_map, Functor.map_comp, Functor.id_obj, Category.assoc]

end Limit

private theorem cbcEndpointLimit_square {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j]
    (M : DerivedCategory (ℕᵒᵖ ⥤ reductionModules U (d.completedRing U))) :
    (proEtaleRingRestrictScalars (exchangeScalar d T)).mapDerivedCategory.map
        ((cbcEndpointLimitMap (cbcEndpointOpen d j)).app M) ≫
      (cbcEndpointLimitMap (proEtaleRingRestrictScalars (exchangeScalar d T))).app
        ((cbcTowerDerived (cbcEndpointOpen d j)).obj M) ≫
      (completedRlim T (exchangeConstantRing T A)).map
        ((cbcEndpointTowerScalarOpen d j).hom.app M) =
    (cbcEndpointDerivedScalarOpen d j).hom.app ((completedRlim U (d.completedRing U)).obj M) ≫
      (ProEtale.StrictTower.moduleJ A j).mapDerivedCategory.map
        ((cbcEndpointLimitMap (proEtaleRingRestrictScalars (exchangeScalar d U))).app M) ≫
      (cbcEndpointLimitMap (ProEtale.StrictTower.moduleJ A j)).app
        ((exchangeTowerRes d U).obj M) := by
  let F := cbcEndpointOpen d j
  let G := proEtaleRingRestrictScalars (exchangeScalar d T)
  let H := proEtaleRingRestrictScalars (exchangeScalar d U)
  let J := ProEtale.StrictTower.moduleJ A j
  let e := cbcEndpointScalarOpen d j
  have hc := Functor.mapDerivedCategory_exactCube
    H J (Functor.const ℕᵒᵖ) F G (Functor.const ℕᵒᵖ)
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj G) (Functor.const ℕᵒᵖ)
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F) (Functor.const ℕᵒᵖ)
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj J)
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj H)
    e.symm (Functor.compConstIso ℕᵒᵖ G) (Functor.compConstIso ℕᵒᵖ F)
    (Functor.compConstIso ℕᵒᵖ J) (Functor.compConstIso ℕᵒᵖ H)
    ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso e.symm) (by
      intro X
      ext n
      simp)
  have hc' (X : d.derived U) := NatTrans.congr_app hc X
  have hcube (X : d.derived U) :
      (Functor.const ℕᵒᵖ).mapDerivedCategory.map
          ((cbcEndpointDerivedScalarOpen d j).inv.app X) ≫
        (cbcEndpointConst G).hom.app (F.mapDerivedCategory.obj X) ≫
        (cbcTowerDerived G).map ((cbcEndpointConst F).hom.app X) =
      (cbcEndpointConst J).hom.app (H.mapDerivedCategory.obj X) ≫
        (cbcTowerDerived J).map ((cbcEndpointConst H).hom.app X) ≫
        (cbcEndpointTowerScalarOpen d j).inv.app
          ((Functor.const ℕᵒᵖ).mapDerivedCategory.obj X) := by
    simpa only [cbcEndpointDerivedScalarOpen, cbcEndpointTowerScalarOpen,
      cbcDerivedSquare, cbcDerivedTowerSquare, CategoryTheory.NormalizedLimitSquare.towerSquare,
      Functor.mapDerivedCategorySquareIso, cbcEndpointConst,
      Functor.mapDerivedCategoryNatIso_symm, Iso.trans_inv, Iso.symm_inv,
      Iso.symm_hom, Iso.trans_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.mapIso_symm, Functor.comp_obj, Category.assoc] using hc' X
  exact exchangeMate_cube
    (cbcEndpointLimitAdj U (d.completedRing U))
    (cbcEndpointLimitAdj T (d.completedRing T))
    (cbcEndpointLimitAdj U (exchangeConstantRing U A))
    (cbcEndpointLimitAdj T (exchangeConstantRing T A))
    H.mapDerivedCategory (cbcTowerDerived H) G.mapDerivedCategory (cbcTowerDerived G)
    (cbcEndpointConst H).symm (cbcEndpointDerivedScalarOpen d j)
    (cbcEndpointTowerScalarOpen d j) (cbcEndpointConst G).symm
    (cbcEndpointConst F).hom (cbcEndpointConst J).hom hcube M

private def cbcEndpointCochainUnit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  derivedCochainRightUnit (completedTowerLimit T R) (completedRlim T R)
    (completedRlimUnit T R)

private theorem cbcEndpointCochainUnit_eq (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (X : CochainComplex (ℕᵒᵖ ⥤ reductionModules T R) ℤ) :
    (cbcEndpointCochainUnit T R).app X = exchangeDerivedUnit (completedTowerLimit T R) X := by
  unfold cbcEndpointCochainUnit
  rw [cochainRightUnit_app_eq]
  dsimp only [exchangeDerivedUnit]
  simp only [quotient_hom_id, quotient_inv_id, Category.id_comp]
  erw [(completedTowerLimit T R).rightDerivedFunctor.map_id, Category.comp_id]
  rfl

private def cbcEndpointRoosUnit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ completedRlim T R :=
  (Functor.isoWhiskerRight
    (CategoryTheory.StrictRoosShiftProof.limitModelIso (A := reductionModules T R))
    DerivedCategory.Q).inv ≫ cbcEndpointCochainUnit T R

private theorem cbcEndpointRoosUnit_derived (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    (completedRlim T R).IsRightDerivedFunctor (cbcEndpointRoosUnit T R)
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ reductionModules T R) (.up ℤ)) := by
  have : (completedRlim T R).IsRightDerivedFunctor (completedRlimUnit T R)
      (HomotopyCategory.quasiIso _ (.up ℤ)) := by
    dsimp only [completedRlim, completedRlimUnit]
    infer_instance
  have h := cochainRightUnit_universal (completedTowerLimit T R) (completedRlim T R)
    (completedRlimUnit T R)
  apply (Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _ _).mpr
  exact (Functor.isLeftKanExtension_iff_of_iso₂
    (cbcEndpointCochainUnit T R) (cbcEndpointRoosUnit T R)
    (Functor.isoWhiskerRight
      (CategoryTheory.StrictRoosShiftProof.limitModelIso (A := reductionModules T R))
      DerivedCategory.Q) (Iso.refl _) (by
        dsimp only [cbcEndpointRoosUnit, Iso.refl_hom]
        rw [Functor.whiskerLeft_id', Category.comp_id,
          ← Category.assoc, Iso.hom_inv_id, Category.id_comp])).mp h

private theorem cbcEndpointRoos_normalization
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasLimits C] [HasLimits D] [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape ℕᵒᵖ F]
    (LA : DerivedCategory (ℕᵒᵖ ⥤ C) ⥤ DerivedCategory C)
    (LB : DerivedCategory (ℕᵒᵖ ⥤ D) ⥤ DerivedCategory D)
    (uA : (lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LA)
    (uB : (lim : (ℕᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LB)
    (lambda : LA ⋙ F.mapDerivedCategory ≅ cbcTowerDerived F ⋙ LB)
    (hnorm : CbcLimitNormalized F LA LB
      ((Functor.isoWhiskerRight CategoryTheory.StrictRoosShiftProof.limitModelIso
        DerivedCategory.Q).inv ≫ uA)
      ((Functor.isoWhiskerRight CategoryTheory.StrictRoosShiftProof.limitModelIso
        DerivedCategory.Q).inv ≫ uB) lambda) :
    ∀ X : CochainComplex (ℕᵒᵖ ⥤ C) ℤ,
      F.mapDerivedCategory.map (uA.app X) ≫ lambda.hom.app (DerivedCategory.Q.obj X) ≫
        LB.map ((cbcTowerFactors F).hom.app X) =
      F.mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ)).obj X) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (preservesLimitNatIso F (J := ℕᵒᵖ)) (.up ℤ)).hom.app X) ≫
        uB.app ((((Functor.whiskeringRight ℕᵒᵖ C D).obj F).mapHomologicalComplex
          (.up ℤ)).obj X) := by
  let tau := preservesLimitNatIso F (J := ℕᵒᵖ)
  intro X
  let Y :=
    (((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (.up ℤ)).obj X
  let iA := CategoryTheory.StrictRoosShiftProof.limitModelPointIso X
  let iB := CategoryTheory.StrictRoosShiftProof.limitModelPointIso Y
  let beta := limit.lift _ ((F.mapHomologicalComplex (.up ℤ)).mapCone
    (limit.cone X.asFunctor))
  have hi : (F.mapHomologicalComplex (.up ℤ)).map iA.hom ≫ beta =
      (NatIso.mapHomologicalComplex tau (.up ℤ)).hom.app X ≫ iB.hom := by
    apply limit.hom_ext
    intro n
    dsimp only [beta]
    rw [Category.assoc, limit.lift_π]
    dsimp only [Functor.mapCone, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    erw [← Functor.map_comp,
      CategoryTheory.StrictRoosShiftProof.limitModelPointIso_hom_π,
      Category.assoc, CategoryTheory.StrictRoosShiftProof.limitModelPointIso_hom_π]
    apply HomologicalComplex.Hom.ext
    funext q
    change F.map (limit.π (X.X q) n) =
      (preservesLimitIso F (X.X q)).hom ≫ limit.π _ n
    exact (preservesLimitIso_hom_π F (X.X q) n).symm
  have hh := congrArg (fun z ↦ F.mapDerivedCategory.map (DerivedCategory.Q.map iA.hom) ≫ z)
    (hnorm.equation X)
  simp only [NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.assoc, Functor.map_comp] at hh
  change F.mapDerivedCategory.map (DerivedCategory.Q.map iA.hom) ≫
    F.mapDerivedCategory.map (DerivedCategory.Q.map iA.inv) ≫ _ = _ at hh
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp] at hh
  erw [F.mapDerivedCategoryFactors_hom_naturality_assoc] at hh
  simp only [← DerivedCategory.Q.map_comp_assoc] at hh
  erw [reassoc_of% hi] at hh
  change _ = _ ≫ DerivedCategory.Q.map
    ((NatIso.mapHomologicalComplex tau (.up ℤ)).hom.app X ≫ iB.hom ≫ iB.inv) ≫ _ at hh
  simp only [Iso.hom_inv_id, Category.comp_id] at hh
  exact hh

private theorem cbcEndpointLimit_cochain_normalized {T S : Scheme.{t}}
    {R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    {R' : Sheaf (ProEt.topology S) CommRingCat.{t + 1}}
    (F : reductionModules T R ⥤ reductionModules S R') [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape ℕᵒᵖ F]
    (lambda : completedRlim T R ⋙ F.mapDerivedCategory ≅
      cbcTowerDerived F ⋙ completedRlim S R')
    (hnorm : CbcLimitNormalized F (completedRlim T R) (completedRlim S R')
      (cbcEndpointRoosUnit T R) (cbcEndpointRoosUnit S R') lambda) :
    ExchangeDerivedPushNormalized (completedTowerLimit T R)
      (completedTowerLimit S R') F ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F)
      (preservesLimitNatIso F (J := ℕᵒᵖ)) lambda := by
  have h := cbcEndpointRoos_normalization F (completedRlim T R) (completedRlim S R')
    (cbcEndpointCochainUnit T R) (cbcEndpointCochainUnit S R') lambda hnorm
  intro X
  simpa only [cbcEndpointCochainUnit_eq] using h X

private theorem cbcEndpointLimit_mate_eq {T S : Scheme.{t}}
    {R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    {R' : Sheaf (ProEt.topology S) CommRingCat.{t + 1}}
    (F : reductionModules T R ⥤ reductionModules S R') [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hphi : ∀ N : ℕ → reductionModules T R, IsIso (piComparison F N))
    (lambda : completedRlim T R ⋙ F.mapDerivedCategory ≅
      cbcTowerDerived F ⋙ completedRlim S R')
    (hnorm : CbcLimitNormalized F (completedRlim T R) (completedRlim S R')
      (cbcEndpointRoosUnit T R) (cbcEndpointRoosUnit S R') lambda) :
    lambda.hom = cbcEndpointLimitMap F := by
  have : PreservesLimitsOfShape (Discrete ℕ) F := natProducts F hphi
  have : PreservesLimitsOfShape ℕᵒᵖ F := natProducts_preservesTowers F
  let aa := (constLimAdj : (Functor.const ℕᵒᵖ : reductionModules T R ⥤ _) ⊣ lim)
  let bb := (constLimAdj : (Functor.const ℕᵒᵖ : reductionModules S R' ⥤ _) ⊣ lim)
  let tau := preservesLimitNatIso F (J := ℕᵒᵖ)
  have hm : (mateEquiv aa bb (TwoSquare.mk _ _ _ _
      (Functor.compConstIso ℕᵒᵖ F).hom)).natTrans = tau.hom := by
    apply NatTrans.ext
    funext M
    apply limit.hom_ext
    intro n
    have h := congrArg (fun z ↦ z.app n)
      (mateEquiv_counit aa bb (TwoSquare.mk _ _ _ _
        (Functor.compConstIso ℕᵒᵖ F).hom) M)
    change (mateEquiv aa bb (TwoSquare.mk _ _ _ _
      (Functor.compConstIso ℕᵒᵖ F).hom)).natTrans.app M ≫ limit.π _ n = _ at h
    exact h.trans (preservesLimitIso_hom_π F M n).symm
  have he := cbcEndpointLimit_cochain_normalized F lambda hnorm
  have hh := exactDerivedMate_eq aa bb (Functor.compConstIso ℕᵒᵖ F) tau hm lambda he
  change lambda.hom = cbcEndpointLimitMap F
  simpa only [exactDerivedMate, cbcEndpointLimitMap, cbcEndpointLimitAdj,
    cbcEndpointConst, Functor.mapDerivedCategorySquareIso] using hh


private theorem cbcEndpointLimit_isIso_of_products {T S : Scheme.{t}}
    {R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    {R' : Sheaf (ProEt.topology S) CommRingCat.{t + 1}}
    (F : reductionModules T R ⥤ reductionModules S R') [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hphi : ∀ N : ℕ → reductionModules T R, IsIso (piComparison F N)) :
    IsIso (cbcEndpointLimitMap F) := by
  have := ambient_exact T R
  have := ambient_exact S R'
  obtain ⟨a, _⟩ := CategoryTheory.NormalizedLimitSquare.cornerData
    (ProEt.topology T) (reductionModuleRing T R) (completedRlim T R) (cbcEndpointRoosUnit T R)
      (cbcEndpointRoosUnit_derived T R)
  obtain ⟨b, _⟩ := CategoryTheory.NormalizedLimitSquare.cornerData
    (ProEt.topology S) (reductionModuleRing S R') (completedRlim S R') (cbcEndpointRoosUnit S R')
      (cbcEndpointRoosUnit_derived S R')
  obtain ⟨c, _⟩ := CategoryTheory.NormalizedLimitSquare.comparisonData a b F hphi
  have hnorm := CategoryTheory.comparison_normalized F a b c
  rw [← cbcEndpointLimit_mate_eq F hphi c.lambda hnorm]
  infer_instance

/-- The scalar-restriction comparison is invertible with its strict-augmentation normalization.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport).
Proof: Scalar restriction is exact and preserves the canonical countable products.
Apply lem-cbc-exact-product-functor-strict-limit. On K-injective resolutions its
comparison is F lim I = lim FI followed by the target resolution. Its strict-
augmentation clause identifies the transpose under the constant-tower/limit
adjunction with the identity constant-diagram comparison. Thus its comparison is
exactly cbcEndpointLimitMap, proving invertibility and the displayed normalization.
The same argument works on arbitrary unbounded strict towers. -/
theorem cbcEndpointScalarLimit_properties (T : Scheme.{t}) :
    IsIso (cbcEndpointLimitMap (proEtaleRingRestrictScalars (exchangeScalar d T))) ∧
      CbcEndpointAugmentationNormalized (proEtaleRingRestrictScalars (exchangeScalar d T)) := by
  constructor
  · apply cbcEndpointLimit_isIso_of_products
      (proEtaleRingRestrictScalars (exchangeScalar d T))
    intro M
    let R := reductionModuleRing T (exchangeConstantRing T A)
    let S := reductionModuleRing T (d.completedRing T)
    let G := SheafOfModules.toSheaf.{t + 1} R
    have : PreservesLimitsOfShape (Discrete (ULift.{t + 1} ℕ))
        (SheafOfModules.toSheaf.{t + 1} S) :=
      ((moduleSheaves_colimits_forgetful S).2.2.2.2.2 _).1
    have : PreservesLimitsOfShape (Discrete (ULift.{t + 1} ℕ)) G :=
      ((moduleSheaves_colimits_forgetful R).2.2.2.2.2 _).1
    have : PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.toSheaf.{t + 1} S) :=
      preservesLimitsOfShape_of_equiv
        (Discrete.equivalence (Equiv.ulift : ULift.{t + 1} ℕ ≃ ℕ)) _
    have : PreservesLimitsOfShape (Discrete ℕ) G :=
      preservesLimitsOfShape_of_equiv
        (Discrete.equivalence (Equiv.ulift : ULift.{t + 1} ℕ ≃ ℕ)) _
    have : ReflectsLimitsOfShape (Discrete ℕ) G :=
      reflectsLimitsOfShape_of_reflectsIsomorphisms
    have : PreservesLimitsOfShape (Discrete ℕ)
        (proEtaleRingRestrictScalars (exchangeScalar d T) ⋙ G) :=
      inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.toSheaf S))
    have : PreservesLimitsOfShape (Discrete ℕ) (proEtaleRingRestrictScalars (exchangeScalar d T)) :=
      preservesLimitsOfShape_of_reflects_of_preserves _ G
    infer_instance
  · exact cbcEndpointLimit_normalized _

private theorem endpointOpenProducts {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] [QuasiCompact j]
    (RV : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (RU : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
    (c : (proEtaleSheafInverseImage j CommRingCat.{t + 1}).obj RV ≅ RU)
    (N : ℕ → proEtaleRingModules U RU) :
    IsIso (piComparison (proEtaleRingOpenExtension j RV RU c) N) := by
  let : WeaklyEtale j := inferInstance
  have : IsOpenImmersion (ProEt.mk j).hom := ‹IsOpenImmersion j›
  have : QuasiCompact (ProEt.mk j).hom := ‹QuasiCompact j›
  obtain ⟨e, ⟨i⟩⟩ := proEtaleOpen_slicePresentation j RV RU c
  have h (I : Type (t + 1)) (N : I → SheafOfModules.{t + 1}
      ((proEtaleModuleCoefficients RV).over (ProEt.mk j))) :
      IsIso (piComparison (SheafOfModules.localizedModuleExtension RV (ProEt.mk j)) N) :=
    (proEtaleRingedExtensionByZero_products (ProEt.mk j) RV I N).1
  have hN (N : ℕ → SheafOfModules.{t + 1}
      ((proEtaleModuleCoefficients RV).over (ProEt.mk j))) :=
    countableComparison (SheafOfModules.localizedModuleExtension RV (ProEt.mk j)) h N
  have : ∀ N : ℕ → _, PreservesLimit (Discrete.functor N)
      (SheafOfModules.localizedModuleExtension RV (ProEt.mk j)) := fun N ↦ by
    have := hN N
    exact PreservesProduct.of_iso_comparison _ N
  have : PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.localizedModuleExtension RV (ProEt.mk j)) :=
    preservesLimitsOfShape_of_discrete _
  have : PreservesLimitsOfShape (Discrete ℕ) (proEtaleRingOpenExtension j RV RU c) :=
    preservesLimitsOfShape_of_natIso i.symm
  infer_instance

/-- Both coefficient versions of a quasi-compact open have the same normalized limit comparison.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport).
Proof: Apply lem-cbc-ringed-open-scalar-limit-coherence on the open slice, for
the constant-to-completed coefficient map. The exact adjunctions identify its
extensions with the existing geometric extensions used here, with their units.
Quasi-compactness gives their canonical product comparisons, including the empty
product, while countable products on the pro-etale module categories are exact.
Apply lem-cbc-exact-product-functor-strict-limit. Its resolution formula and
strict-augmentation normalization identify its unique comparison with the
constant-diagram mate cbcEndpointLimitMap for each of the two coefficient rings.
This proves both invertibility and normalization without a degree bound. -/
theorem cbcEndpointOpenLimit_properties {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] [QuasiCompact j] :
    (IsIso (cbcEndpointLimitMap (cbcEndpointOpen d j)) ∧
      CbcEndpointAugmentationNormalized (cbcEndpointOpen d j)) ∧
    (IsIso (cbcEndpointLimitMap (ProEtale.StrictTower.moduleJ A j)) ∧
      CbcEndpointAugmentationNormalized (ProEtale.StrictTower.moduleJ A j)) := by
  constructor
  · constructor
    · exact cbcEndpointLimit_isIso_of_products _
        (endpointOpenProducts j (d.completedRing T) (d.completedRing U) (d.integralRingIso j))
    · exact cbcEndpointLimit_normalized (cbcEndpointOpen d j)
  · constructor
    · exact cbcEndpointLimit_isIso_of_products _ ((fun _ ↦ endpointOpenProducts j
          (exchangeConstantRing T A) (exchangeConstantRing U A) (exchangeConstantIso j A) _))
    · exact cbcEndpointLimit_normalized (ProEtale.StrictTower.moduleJ A j)

/-- The specified normalized scalar / derived-limit isomorphism.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointScalarLimit (T : Scheme.{t}) :=
  @asIso _ _ _ _ (cbcEndpointLimitMap (proEtaleRingRestrictScalars (exchangeScalar d T)))
    (cbcEndpointScalarLimit_properties d T).1

/-- The specified normalized completed-ring open / derived-limit isomorphism.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointCompletedOpenLimit {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] [QuasiCompact j] :=
  @asIso _ _ _ _ (cbcEndpointLimitMap (cbcEndpointOpen d j))
    (cbcEndpointOpenLimit_properties d j).1.1

/-- The specified normalized constant-ring open / derived-limit isomorphism.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointConstantOpenLimit {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] [QuasiCompact j] :=
  @asIso _ _ _ _ (cbcEndpointLimitMap (ProEtale.StrictTower.moduleJ A j))
    (cbcEndpointOpenLimit_properties d j).2.1

private theorem cbcEndpointLimit_inverse_square {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] [QuasiCompact j]
    (M : DerivedCategory (ℕᵒᵖ ⥤ reductionModules U (d.completedRing U))) :
    (proEtaleRingRestrictScalars (exchangeScalar d T)).mapDerivedCategory.map
        ((cbcEndpointCompletedOpenLimit d j).inv.app M) ≫
      (cbcEndpointDerivedScalarOpen d j).hom.app ((completedRlim U (d.completedRing U)).obj M) ≫
      (ProEtale.StrictTower.moduleJ A j).mapDerivedCategory.map
        ((cbcEndpointScalarLimit d U).hom.app M) =
    (cbcEndpointScalarLimit d T).hom.app ((cbcTowerDerived (cbcEndpointOpen d j)).obj M) ≫
      (completedRlim T (exchangeConstantRing T A)).map
        ((cbcEndpointTowerScalarOpen d j).hom.app M) ≫
      (cbcEndpointConstantOpenLimit d j).inv.app ((exchangeTowerRes d U).obj M) := by
  apply (cancel_epi ((proEtaleRingRestrictScalars (exchangeScalar d T)).mapDerivedCategory.map
    ((cbcEndpointCompletedOpenLimit d j).hom.app M))).mp
  apply (cancel_mono ((cbcEndpointConstantOpenLimit d j).hom.app
    ((exchangeTowerRes d U).obj M))).mp
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  exact (cbcEndpointLimit_square d j M).symm


private theorem cbcEndpointConstantOpen_unit {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : d.derived U) :
    (d.derivedConstantTower U).map ((cbcEndpointDerivedOpenAdj d j).unit.app K) ≫
      (d.derivedConstantPullbackIso j).inv.app
        ((cbcEndpointOpen d j).mapDerivedCategory.obj K) =
    (cbcEndpointTowerOpenAdj d j).unit.app ((d.derivedConstantTower U).obj K) ≫
      (d.towerPull j).map ((cbcEndpointConst (cbcEndpointOpen d j)).inv.app K) := by
  let a := cbcEndpointOpenAdj d j
  let beta := (Functor.compConstIso ℕᵒᵖ (cbcEndpointOpen d j)).symm
  let delta := (d.constantPullbackIso j).symm
  have hd : delta = Functor.compConstIso ℕᵒᵖ
      (proEtaleRingModulePullback j (d.completedRing T) (d.completedRing U)
        (d.integralRingIso j)) := by
    ext M n
    rfl
  have hb : ∀ M, (a.whiskerRight ℕᵒᵖ).unit.app ((Functor.const ℕᵒᵖ).obj M) ≫
      (d.towerModulePull j).map (beta.hom.app M) =
      (Functor.const ℕᵒᵖ).map (a.unit.app M) ≫ delta.hom.app ((cbcEndpointOpen d j).obj M) := by
    intro M
    ext n
    simp [a, beta, delta, hd]
  have he : Functor.whiskerRight (exactLocalizationDerivedAdjunction a).unit
        (d.derivedConstantTower U) ≫
      Functor.whiskerLeft (cbcEndpointOpen d j).mapDerivedCategory
        (Functor.mapDerivedCategorySquareIso delta).hom =
      Functor.whiskerLeft (d.derivedConstantTower U)
        (exactLocalizationDerivedAdjunction (a.whiskerRight ℕᵒᵖ)).unit ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso beta).hom (d.towerPull j) := by
    apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    intro X
    exact (CategoryTheory.mate_unit_Q a (a.whiskerRight ℕᵒᵖ) delta beta hb X).symm
  have h := congr_app he K
  dsimp only [cbcEndpointDerivedOpenAdj, cbcEndpointTowerOpenAdj]
  rw [cbcEndpointExactAdjunction_eq,
    cbcEndpointExactAdjunction_eq]
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    cbcEndpointConst, Functor.mapDerivedCategorySquareIso, beta, delta,
    Functor.mapDerivedCategoryNatIso_symm, Iso.symm_hom, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_inv, Category.assoc, AdicCoefficientDatum.derivedConstantPullbackIso] using h

/-- The canonical quotient/open comparison retains the entire strict quotient augmentation.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport).
Proof: Represent K by a K-flat complex with flat terms. The inverse comparison
is the transpose of the reduced open unit, so its section formula is the balanced
tensor map. Both paths from the constant tower send a section x to x tensor 1
at every positive quotient level, with the same open generator. This equality
holds in the strict tower complex, since all quotient transitions preserve 1.
Descend by the universal K-flat counits. No equality is tested using derived
evaluation or unrelated morphisms to individual tower levels. -/
theorem cbcEndpointReduction_augmentation {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] (K : d.derived U) :
    (completedReductionAugmentation d T).app ((cbcEndpointOpen d j).mapDerivedCategory.obj K) ≫
        (cbcEndpointReduction d j).hom.app K =
      (cbcEndpointConst (cbcEndpointOpen d j)).hom.app K ≫
        (cbcTowerDerived (cbcEndpointOpen d j)).map
          ((completedReductionAugmentation d U).app K) := by
  let b := cbcEndpointTowerOpenAdj d j
  let a := cbcEndpointDerivedOpenAdj d j
  have hi : (cbcTowerDerived (cbcEndpointOpen d j)).map
        ((completedReductionAugmentation d U).app K) ≫ cbcEndpointReductionInv d j K =
      (cbcEndpointConst (cbcEndpointOpen d j)).inv.app K ≫
        (completedReductionAugmentation d T).app
          ((cbcEndpointOpen d j).mapDerivedCategory.obj K) := by
    apply (b.homEquiv _ _).injective
    rw [b.homEquiv_naturality_left, b.homEquiv_naturality_right]
    change _ ≫ (b.homEquiv _ _) ((b.homEquiv _ _).symm _) = _
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    rw [← Category.assoc, ← (completedReductionAugmentation d U).naturality]
    rw [Category.assoc]
    have hr := reduction_augmentation d j ((cbcEndpointOpen d j).mapDerivedCategory.obj K)
    have hr' : (completedReductionAugmentation d U).app
          ((d.pull j).obj ((cbcEndpointOpen d j).mapDerivedCategory.obj K)) ≫
        (d.reductionTowerPullbackIso j).inv.app _ =
      (d.derivedConstantPullbackIso j).inv.app _ ≫
        (d.towerPull j).map ((completedReductionAugmentation d T).app _) := by
      apply (cancel_epi ((d.derivedConstantPullbackIso j).hom.app _)).mp
      apply (cancel_mono ((d.reductionTowerPullbackIso j).hom.app _)).mp
      simp only [Category.assoc, Iso.inv_hom_id_app, Iso.hom_inv_id_app_assoc]
      erw [Category.comp_id]
      exact hr.symm
    erw [hr']
    rw [← Category.assoc, cbcEndpointConstantOpen_unit d j K]
  apply (cancel_mono ((cbcEndpointReduction d j).inv.app K)).mp
  rw [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  rw [Category.assoc]
  change _ = _ ≫ _ ≫ cbcEndpointReductionInv d j K
  rw [hi, ← Category.assoc, Iso.hom_inv_id_app]
  erw [Category.id_comp]


/-- The pulled-back completed quotient tower Q, as a natural functor in the input.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointQ {U T T' : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] (u : T' ⟶ T) :=
  (cbcEndpointOpen d j).mapDerivedCategory ⋙ completedReductionTower T d ⋙ d.towerPull u

/-- The pulled-back completed quotient tower C.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointC {U U' : Scheme.{t}} (v : U' ⟶ U) :=
  completedReductionTower U d ⋙ d.towerPull v

/-- The constant-coefficient strict reduction tower M.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointM (U : Scheme.{t}) :=
  completedReductionTower U d ⋙ exchangeTowerRes d U

/-- The constant-coefficient inverse image H = G_v M.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointH {U U' : Scheme.{t}} (v : U' ⟶ U) :=
  cbcEndpointM d U ⋙ ProEtale.StrictTower.G A v

/-- The constant-coefficient inverse image N = G_u J_j M.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointN {U T T' : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] (u : T' ⟶ T) :=
  cbcEndpointM d U ⋙ ProEtale.StrictTower.J A j ⋙ ProEtale.StrictTower.G A u

/-- The canonical finite-reduction/scalar source comparison a.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointA {U T T' : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] (u : T' ⟶ T) :
    cbcEndpointQ d j u ⋙ exchangeTowerRes d T' ≅ cbcEndpointN d j u :=
  Functor.isoWhiskerLeft
      ((cbcEndpointOpen d j).mapDerivedCategory ⋙ completedReductionTower T d)
      (exchangeResPull d u) ≪≫
    Functor.isoWhiskerRight (cbcEndpointQuotientOpen d j) (ProEtale.StrictTower.G A u)

/-- The canonical finite-reduction/scalar target comparison d.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointD {U U' : Scheme.{t}} (v : U' ⟶ U) :
    cbcEndpointC d v ⋙ exchangeTowerRes d U' ≅ cbcEndpointH d v :=
  Functor.isoWhiskerLeft (completedReductionTower U d) (exchangeResPull d v)

/-- The target tower endpoint b = J(d) e_C, using the same scalar/open isomorphism.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointB {U U' T' : Scheme.{t}} (v : U' ⟶ U) (j' : U' ⟶ T')
    [IsOpenImmersion j'] :
    cbcEndpointC d v ⋙ cbcTowerDerived (cbcEndpointOpen d j') ⋙ exchangeTowerRes d T' ≅
      cbcEndpointH d v ⋙ ProEtale.StrictTower.J A j' :=
  Functor.isoWhiskerLeft (cbcEndpointC d v) (cbcEndpointTowerScalarOpen d j') ≪≫
    Functor.isoWhiskerRight (cbcEndpointD d v) (ProEtale.StrictTower.J A j')

/-- The canonical source endpoint a-hat = L(a) lambda_r, naturally in the input.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointSource {U T T' : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (u : T' ⟶ T) :
    cbcEndpointQ d j u ⋙ completedRlim T' (d.completedRing T') ⋙
        (proEtaleRingRestrictScalars (exchangeScalar d T')).mapDerivedCategory ≅
      cbcEndpointN d j u ⋙ completedRlim T' (exchangeConstantRing T' A) :=
  Functor.isoWhiskerLeft (cbcEndpointQ d j u) (cbcEndpointScalarLimit d T') ≪≫
    Functor.isoWhiskerRight (cbcEndpointA d j u)
      (completedRlim T' (exchangeConstantRing T' A))

/-- The canonical target endpoint b-hat = J(L(d) lambda_r) e, naturally in the input.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport). -/
def cbcEndpointTarget {U U' T' : Scheme.{t}} (v : U' ⟶ U) (j' : U' ⟶ T')
    [IsOpenImmersion j'] :
    cbcEndpointC d v ⋙ completedRlim U' (d.completedRing U') ⋙
        (cbcEndpointOpen d j').mapDerivedCategory ⋙
          (proEtaleRingRestrictScalars (exchangeScalar d T')).mapDerivedCategory ≅
      cbcEndpointH d v ⋙ completedRlim U' (exchangeConstantRing U' A) ⋙
        (ProEtale.StrictTower.moduleJ A j').mapDerivedCategory :=
  Functor.isoWhiskerLeft (cbcEndpointC d v ⋙ completedRlim U' (d.completedRing U'))
      (cbcEndpointDerivedScalarOpen d j') ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (cbcEndpointC d v) (cbcEndpointScalarLimit d U') ≪≫
        Functor.isoWhiskerRight (cbcEndpointD d v)
          (completedRlim U' (exchangeConstantRing U' A)))
      (ProEtale.StrictTower.moduleJ A j').mapDerivedCategory

private theorem cbcEndpoint_pasting {U U' T' : Scheme.{t}}
    (v : U' ⟶ U) (j' : U' ⟶ T') [IsOpenImmersion j'] [QuasiCompact j']
    (K : d.derived U) :
    (proEtaleRingRestrictScalars (exchangeScalar d T')).mapDerivedCategory.map
        ((cbcEndpointCompletedOpenLimit d j').inv.app ((cbcEndpointC d v).obj K)) ≫
        (cbcEndpointTarget d v j').hom.app K =
      (cbcEndpointScalarLimit d T').hom.app
          ((cbcTowerDerived (cbcEndpointOpen d j')).obj ((cbcEndpointC d v).obj K)) ≫
        (completedRlim T' (exchangeConstantRing T' A)).map
          ((cbcEndpointB d v j').hom.app K) ≫
        (cbcEndpointConstantOpenLimit d j').inv.app ((cbcEndpointH d v).obj K) := by
  have h := cbcEndpointLimit_inverse_square d j' ((cbcEndpointC d v).obj K)
  have hn := (cbcEndpointConstantOpenLimit d j').inv.naturality
    ((cbcEndpointD d v).hom.app K)
  dsimp only [Functor.comp_map] at hn
  simp only [cbcEndpointTarget, cbcEndpointB, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj,
    Functor.map_comp, Category.assoc]
  erw [reassoc_of% h]
  exact congrArg (fun z ↦ (cbcEndpointScalarLimit d T').hom.app _ ≫
    (completedRlim T' (exchangeConstantRing T' A)).map
      ((cbcEndpointTowerScalarOpen d j').hom.app _) ≫ z) hn.symm

/-- Normalized endpoint pasting and transport of every derived strict-tower morphism.
The source and target endpoints are natural isomorphisms with the formulas in their
definitions. Scalar and open completion units use the augmentation normalization
of cbcEndpointScalarLimit_properties, cbcEndpointOpenLimit_properties and
cbcEndpointReduction_augmentation, hence the actual quotient units.
Source: blueprint finite-exchange and final derived-limit paragraphs
(blueprint: lem-cbc-completed-open-endpoint-limit-transport).
Proof: 1. Apply lem-pc-quasi-compact-base-change to sq, obtaining hqc for j-prime.
Apply lem-cbc-ringed-open-scalar-limit-coherence to that open and the constant-to-
completed scalar map. Under the unit-preserving ringed slice identifications its
e is cbcEndpointScalarOpen and all four lambda are the constant-diagram mates
above, by lem-cbc-exact-product-functor-strict-limit and its resolution formula.
2. The completed pullback is Rlim of the pulled strict quotient tower. The
canonical scalar/finite-reduction comparisons are cbcEndpointA and cbcEndpointD,
using exchangeResPull and the quotient/open transpose. Thus the actual source
comparison is L(a) lambda_r and the target is J(L(d) lambda_r) e, exactly
cbcEndpointSource and cbcEndpointTarget. The strict augmentation equations above
identify their quotient completion units with the constant-coefficient units.
3. Invert the two open-limit comparisons in the coherence square. Compose with
J(L(d)); naturality of the constant open comparison at d replaces this by
L(J(d)) followed by the inverse comparison at H. Functoriality gives the first
displayed identity with b = J(d) e.
4. For arbitrary theta use naturality of the scalar-limit comparison to move
r(Rlim theta) across lambda_r. Substitute the first identity and cancel
lambda_r followed by its inverse in a-hat inverse. Functoriality of L combines
the remaining three maps into L(b r(theta) a inverse). Every equality is in
the full derived strict-tower categories; no evaluation faithfulness, mate
condition on theta, etale-origin witness or common degree bound is used. -/
theorem completedOpenEndpointLimitTransport
    {U' U T' T : Scheme.{t}} {v : U' ⟶ U} {j' : U' ⟶ T'} {j : U ⟶ T} {u : T' ⟶ T}
    [IsOpenImmersion j] [IsOpenImmersion j'] [QuasiCompact j]
    (sq : OpenImmersionSquare v j' j u)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : d.derived U) (_hK : cbcCompleteProperty d U r a ha K)
    (_hJK : cbcCompleteProperty d T r a ha ((cbcEndpointOpen d j).mapDerivedCategory.obj K)) :
    ∃ hqc : QuasiCompact j',
      @id Prop
        ((proEtaleRingRestrictScalars (exchangeScalar d T')).mapDerivedCategory.map
            ((@cbcEndpointCompletedOpenLimit _ _ d _ _ j' inferInstance hqc).inv.app
              ((cbcEndpointC d v).obj K)) ≫ (cbcEndpointTarget d v j').hom.app K =
          (cbcEndpointScalarLimit d T').hom.app
              ((cbcTowerDerived (cbcEndpointOpen d j')).obj ((cbcEndpointC d v).obj K)) ≫
            (completedRlim T' (exchangeConstantRing T' A)).map
              ((cbcEndpointB d v j').hom.app K) ≫
            (@cbcEndpointConstantOpenLimit _ _ d _ _ j' inferInstance hqc).inv.app
              ((cbcEndpointH d v).obj K)) ∧
      ∀ theta : (cbcEndpointQ d j u).obj K ⟶
          (cbcTowerDerived (cbcEndpointOpen d j')).obj ((cbcEndpointC d v).obj K),
        (cbcEndpointSource d j u).inv.app K ≫
            (proEtaleRingRestrictScalars (exchangeScalar d T')).mapDerivedCategory.map
              ((completedRlim T' (d.completedRing T')).map theta ≫
                (@cbcEndpointCompletedOpenLimit _ _ d _ _ j' inferInstance hqc).inv.app
                  ((cbcEndpointC d v).obj K)) ≫
            (cbcEndpointTarget d v j').hom.app K =
          (completedRlim T' (exchangeConstantRing T' A)).map
            ((cbcEndpointA d j u).inv.app K ≫ (exchangeTowerRes d T').map theta ≫
              (cbcEndpointB d v j').hom.app K) ≫
            (@cbcEndpointConstantOpenLimit _ _ d _ _ j' inferInstance hqc).inv.app
              ((cbcEndpointH d v).obj K) := by
  have hqc : QuasiCompact j' := by
    rw [← sq.hom_snd]
    infer_instance
  let := hqc
  refine ⟨hqc, ?_, ?_⟩
  · exact cbcEndpoint_pasting d v j' K
  · intro theta
    have hp := cbcEndpoint_pasting d v j' K
    simp only [Functor.map_comp, Category.assoc]
    rw [hp]
    have hn := (cbcEndpointScalarLimit d T').hom.naturality theta
    change (proEtaleRingRestrictScalars (exchangeScalar d T')).mapDerivedCategory.map
        ((completedRlim T' (d.completedRing T')).map theta) ≫ _ =
      _ ≫ (completedRlim T' (exchangeConstantRing T' A)).map
        ((exchangeTowerRes d T').map theta) at hn
    rw [reassoc_of% hn]
    simp only [cbcEndpointSource, Iso.trans_inv, NatTrans.comp_app,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
      Iso.inv_hom_id_app_assoc]

end AlgebraicGeometry.Scheme
