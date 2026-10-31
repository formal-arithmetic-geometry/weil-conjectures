/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedTateIntegralData
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Analysis.Normed.Field.Basic
public import WeilConjectures.AlgebraicGeometry.CondensedERealizationDefinitions
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.AlgebraicGeometry.CompletedRlimFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatumSupplement
import WeilConjectures.AlgebraicGeometry.CondensedERealization
import WeilConjectures.AlgebraicGeometry.PurTwistSheafLocallyFree
import WeilConjectures.AlgebraicGeometry.ProEtaleRootsOfUnitySheafSupplement
import WeilConjectures.AlgebraicGeometry.CompletedCondensedCoefficients
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import WeilConjectures.Algebra.Homology.KFlatSupplement
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic

/-!
# Realization of the reconstructed positive Tate tower

Source: main-20261015, smooth purity, rational-and-qbar-purity proof, Step 2;
Bhatt--Scholze, Sections 3.1 and 6.8; Stacks 03EK, 06YU and 0941
(blueprint: lem-pur-condensed-tate-realization).

## Main statements

* `balancedPower_existsUnique`: the balanced tensor maps fixed on all generators and the unit.

## Main constructions

* `finiteTower`, `reconstructed`, `shiftedReconstructed`: the specified positive strict tower.
* `realized`, `shiftedComparison`: the recorded J-realization and its canonical comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option linter.mathlibStandardSet false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open WeilConjectures WeilConjectures.CondensedERealization
open scoped CategoryTheory.Obj

set_option allowUnsafeReducibility true in
attribute [local reducible] reductionModulesHasDerivedCategory
  reductionRingModulesHasDerivedCategory proEtaleRingModules_hasDerivedCategory
  reductionTowerHasDerivedCategory

attribute [local instance 40000] reductionRingModulesHasDerivedCategory
  proEtaleRingModules_hasDerivedCategory reductionTowerHasDerivedCategory

attribute [local instance 41000] reductionModulesHasDerivedCategory

attribute [local irreducible] _root_.instCategoryDerivedCategory
  HasDerivedCategory.standard Functor.leftAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Mod.monoidalClosed DerivedCategory.monoidalClosed
  Mod.extendScalars Mod.derivedExtendMapDerivedCategoryAdjunction
  AlgebraicGeometry.ProEtale.upperStarFromPoint

attribute [local irreducible] moduleEncoding

namespace AlgebraicGeometry.ProEtale.CondensedTateRealization

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

attribute [local irreducible] integralEncoding

attribute [local instance] At.encodingAdditive

/-- The actual completed derived limit, with its functor interface named once.
Source: completedRlim (blueprint: lem-pur-condensed-tate-realization). -/
def tateRlim (B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    DerivedCategory (reductionTowerCategory X (reductionModuleRing X B)) ⥤
      reductionDerivedCategory X B :=
  completedRlim X B

/-- The original completed-limit projection through the named functor interface.
Source: completedRlimProjection (blueprint: lem-pur-condensed-tate-realization). -/
def tateRlimProjection (B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (n : ℕ) :
    tateRlim X B ⟶ reductionTowerDerivedEvaluation X (reductionModuleRing X B) n :=
  completedRlimProjection X B n

/-- Compose a derived natural transformation with the standard single comparison.
Source: exact-functor comparison and blueprint realization, Step 6
(blueprint: lem-pur-condensed-tate-realization). -/
def singleDerivedProjection {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (L : DerivedCategory C ⥤ DerivedCategory D) (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (π : L ⟶ F.mapDerivedCategory) (N : C) :
    L.obj ((DerivedCategory.singleFunctor C 0).obj N) ⟶
      (DerivedCategory.singleFunctor D 0).obj (F.obj N) :=
  π.app ((DerivedCategory.singleFunctor C 0).obj N) ≫
    (F.mapDerivedCategorySingleFunctor 0).hom.app N

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The unshifted reconstructed object is the actual functorial derived limit.
Source: blueprint realization, Step 6
(blueprint: lem-pur-condensed-tate-realization). -/
def reconstructed (r : At l (LiftedQ.{u} l) X) (d : ℕ) :
    reductionDerivedCategory X (CompletedRing X l) :=
  (tateRlim X (CompletedRing X l)).obj
    ((DerivedCategory.singleFunctor _ 0).obj (encodedTower X l r d))

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The specified reconstructed object M_d, with cohomological shift 2d.
Source: blueprint realization, Step 6
(blueprint: lem-pur-condensed-tate-realization). -/
def shiftedReconstructed (r : At l (LiftedQ.{u} l) X) (d : ℕ) :
    reductionDerivedCategory X (CompletedRing X l) :=
  (shiftFunctor _ (2 * d : ℤ)).obj (reconstructed X l r d)

attribute [local semireducible] integralEncoding

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The encoded projections satisfy naturality for the actual strict-tower steps.
Source: blueprint realization, Steps 4 and 6
(blueprint: lem-pur-condensed-tate-realization).
Proof: Functor.ofOpSequence_map_homOfLE_succ identifies the step of finiteTower
with finiteTransition. The step of encodedTower is its image under integralEncoding.
The constant tower has identity steps. Apply integralEncoding.functor.map to
powerProjection_compatible, use map_comp, and remove the identity composition. -/
theorem augmentation_compatible (r : At l (LiftedQ.{u} l) X) (d n : ℕ) :
    𝟙 ((integralEncoding X l r).functor.obj (integralPower X l d)) ≫
        (integralEncoding X l r).functor.map (powerProjection X l n d) =
      (integralEncoding X l r).functor.map (powerProjection X l (n + 1) d) ≫
        (encodedTower X l r d).map (homOfLE (n.le_add_right 1)).op := by
  simp only [Category.id_comp, encodedTower, Functor.comp_map, finiteTower,
    Functor.ofOpSequence_map_homOfLE_succ]
  convert! congrArg (integralEncoding X l r).functor.map
    (powerProjection_compatible X l n d).symm using 1

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The cone of the original tensor projections, transported without changing maps.
Source: blueprint realization, Steps 4 and 6
(blueprint: lem-pur-condensed-tate-realization). -/
def augmentation (r : At l (LiftedQ.{u} l) X) (d : ℕ) :
    (Functor.const ℕᵒᵖ).obj
      ((integralEncoding X l r).functor.obj (integralPower X l d)) ⟶
        encodedTower X l r d :=
  NatTrans.ofOpSequence
    (fun n ↦ (integralEncoding X l r).functor.map (powerProjection X l n d))
    (fun n ↦ augmentation_compatible X l r d n)

attribute [local irreducible] integralEncoding

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The canonical constant-tower/derived-limit adjunction.
Source: Stacks 079P, blueprint realization Step 6
(blueprint: lem-pur-condensed-tate-realization). -/
def limitAdjunction :
    (Functor.const ℕᵒᵖ :
      pbcModules X (CompletedRing X l) ⥤ _).mapDerivedCategory ⊣
      tateRlim X (CompletedRing X l) :=
  (constLimAdj : (Functor.const ℕᵒᵖ :
    pbcModules X (CompletedRing X l) ⥤ _) ⊣
      completedTowerLimit X (CompletedRing X l)).mapDerivedCategoryRightDerivedAdjunction

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The derived augmentation, obtained by transposing the actual cone.
Source: blueprint realization, Step 6
(blueprint: lem-pur-condensed-tate-realization). -/
def derivedAugmentation (r : At l (LiftedQ.{u} l) X) (d : ℕ) :
    (DerivedCategory.singleFunctor (pbcModules X (CompletedRing X l)) 0).obj
      ((integralEncoding X l r).functor.obj (integralPower X l d)) ⟶
        reconstructed X l r d :=
  let A := pbcModules X (CompletedRing X l)
  let D := reductionTowerCategory X (reductionModuleRing X (CompletedRing X l))
  let F : A ⥤ D := Functor.const ℕᵒᵖ
  let S : A ⥤ DerivedCategory A := DerivedCategory.singleFunctor A 0
  let V : D ⥤ DerivedCategory D := DerivedCategory.singleFunctor D 0
  let M : A := (integralEncoding X l r).functor.obj (integralPower X l d)
  let N : D := encodedTower X l r d
  let f : F.obj M ⟶ N := augmentation X l r d
  (limitAdjunction X l).homEquiv (S.obj M) (V.obj N)
    ((F.mapDerivedCategorySingleFunctor 0).hom.app M ≫ V.map f)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The coefficient map used by the recorded scalar-extension realization.
Source: blueprint realization, Step 7
(blueprint: lem-pur-condensed-tate-realization). -/
def scalarMap (r : At l (LiftedQ.{u} l) X) :
    CompletedRing X l ⟶ rationalCoefficientSheaf l X (LiftedQ.{u} l) :=
  r.integralIso.hom ≫ r.inclusion

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The actual derived extension along the fixed rational-to-closure coefficient map.
Source: blueprint realization Step 7 (blueprint: lem-pur-condensed-tate-realization). -/
def rationalDerivedExtension :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (Coefficient (LiftedQ.{u} l) X)) ⥤
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X)) :=
  let left {A B : Type (u + 2)} [Category.{u + 1} A] [Category.{u + 1} B]
      {F : A ⥤ B} {G : B ⥤ A} (_ : F ⊣ G) : A ⥤ B := F
  left (Mod.derivedExtendMapDerivedCategoryAdjunction
    (C := Sheaf (ProEt.topology X) Ab.{u + 1}) (rationalToQbar X l))

attribute [local irreducible] rationalDerivedExtension

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Scalar extension through Q_l to the specified finite-extension-valued closure.
Source: blueprint realization, Step 7
(blueprint: lem-pur-condensed-tate-realization). -/
abbrev ambientRealization (r : At l (LiftedQ.{u} l) X) :
    reductionDerivedCategory X (CompletedRing X l) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj l) X)) :=
  pbcDerivedExtend (scalarMap X l r) ⋙
    (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.inverse ⋙
      (rationalDerivedExtension X l)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Restriction in the reverse order is the right adjoint of scalar extension.
Source: blueprint realization, Step 7
(blueprint: lem-pur-condensed-tate-realization). -/
abbrev ambientRestriction (r : At l (LiftedQ.{u} l) X) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X)) ⥤
        reductionDerivedCategory X (CompletedRing X l) :=
  (Mod.comap (C := Sheaf (ProEt.topology X) Ab.{u + 1}) (rationalToQbar X l)).mapDerivedCategory ⋙
    (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.functor ⋙
      pbcDerivedRestrict (scalarMap X l r)

attribute [local semireducible] rationalDerivedExtension in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The composite derived scalar adjunction, with its original units and counits.
Source: Stacks 06YU and blueprint realization Step 7
(blueprint: lem-pur-condensed-tate-realization). -/
def scalarAdjunction (r : At l (LiftedQ.{u} l) X) :
    ambientRealization X l r ⊣ ambientRestriction X l r :=
  ((pbcDerivedScalarAdjunction (scalarMap X l r)).comp
    (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.symm.toAdjunction).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        (C := Sheaf (ProEt.topology X) Ab.{u + 1}) (rationalToQbar X l))

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The literal iota U(M) in the node: realize M[1/l], then extend to Qbar.
Source: blueprint realization, Step 7
(blueprint: lem-pur-condensed-tate-realization). -/
def realized (r : At l (LiftedQ.{u} l) X) (M : Integral l (LiftedQ.{u} l) X) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X)) :=
  (rationalDerivedExtension X l).obj
    (r.realization.functor.obj (ScalarLocalization.mk M)).obj

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The recorded J scalar-extension comparison, followed by the actual Qbar extension.
Source: blueprint realization, Step 7
(blueprint: lem-pur-condensed-tate-realization). -/
def realizationComparison (r : At l (LiftedQ.{u} l) X) (M : Integral l (LiftedQ.{u} l) X) :
    (ambientRealization X l r).obj M.obj ≅ realized X l r M :=
  (rationalDerivedExtension X l).mapIso
    (((moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.inverse.mapIso
        (r.scalarExtension.app M).symm) ≪≫
      (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.unitIso.symm.app _)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The actual integral-to-closure map of the archived Tate module.
Source: blueprint realization, Step 8
(blueprint: lem-pur-condensed-tate-realization). -/
def integralToQbar := coefficientMap (Profinite.padicIntRingObjToPadicAlgCl l) X

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The specified coefficient map preserves the ring-object operations.
Source: blueprint realization, coefficient maps
(blueprint: lem-pur-condensed-tate-realization).
Proof: The archived padicIntRingObjToPadicAlgCl is a morphism of condensed ring objects.
The strong monoidal point inverse image retains its unit and multiplication equations. -/
@[instance] theorem integralToQbar_isMonHom : IsMonHom (integralToQbar X l) := by
  unfold integralToQbar
  infer_instance

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Balanced tensor-power maps, fixed at the unit and on every tensor generator.
Source: blueprint realization, Steps 8 and 9
(blueprint: lem-pur-condensed-tate-realization). -/
def IsBalancedPowerFamily
    (c : ∀ d : ℕ, integralPower X l d ⟶
      (Mod.comap (integralToQbar X l)).obj (tateTwistNat X l d)) : Prop :=
  (c 0).hom = integralToQbar X l ∧ ∀ d : ℕ,
    Mod.tensorObjπ (integralPower X l d) (tateModule X l) ≫ (c (d + 1)).hom =
      ((c d).hom ⊗ₘ
        ((Mod.extendRestrictAdjunction
          (C := Sheaf (ProEt.topology X) Ab.{u + 1}) (integralToQbar X l)).unit.app
          (tateModule X l)).hom) ≫
        Mod.tensorObjπ (tateTwistNat X l d) (tateTwistOne X l)

section BalancedTensor

open CategoryTheory.MonObj

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [∀ M : C, PreservesColimitsOfSize.{0, 0} (tensorLeft M)]
  [∀ M : C, PreservesColimitsOfSize.{0, 0} (tensorRight M)]
  {A B : C} [MonObj A] [MonObj B] [commA : IsCommMonObj A] [commB : IsCommMonObj B]
  (φ : A ⟶ B) [IsMonHom φ]

omit [MonObj A] [IsCommMonObj A] [IsMonHom φ] in
open CategoryTheory.BraidedCategory in
private lemma restrictionTensor_balanced (M N : Mod C B) :
    ((β_ M.X A).hom ≫ φ ▷ M.X ≫ γ[B,M.X]) ▷ N.X ≫ Mod.tensorObjπ M N =
      ((α_ M.X A N.X).hom ≫ M.X ◁ (φ ▷ N.X ≫ γ[B,N.X])) ≫
        Mod.tensorObjπ M N := by
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  slice_lhs 1 2 =>
    rw [← comp_whiskerRight, ← braiding_naturality_right, comp_whiskerRight]
  slice_lhs 2 3 => rw [← comp_whiskerRight]
  rw [Mod.tensorObjπ_condition, Category.assoc, associator_naturality_middle_assoc]

private def restrictionTensor (M N : Mod C B) :
    (Mod.comap φ).obj M ⊗ (Mod.comap φ).obj N ⟶ (Mod.comap φ).obj (M ⊗ N) :=
  Mod.Hom.mk' (Mod.tensorObjDesc _ _ (Mod.tensorObjπ M N)
    (restrictionTensor_balanced φ M N)) (by
    erw [← cancel_epi (A ◁ Mod.tensorObjπ ((Mod.comap φ).obj M) ((Mod.comap φ).obj N)),
      Mod.whiskerLeft_tensorπ_smul_assoc, Mod.tensorObjπ_tensorObjDesc]
    erw [← whiskerLeft_comp_assoc, Mod.tensorObjπ_tensorObjDesc]
    change (α_ A M.X N.X).inv ≫ (φ ▷ M.X ≫ γ[B,M.X]) ▷ N.X ≫ Mod.tensorObjπ M N =
      A ◁ Mod.tensorObjπ M N ≫ φ ▷ (M ⊗ N).X ≫ γ[B,(M ⊗ N).X]
    rw [whisker_exchange_assoc, Mod.whiskerLeft_tensorπ_smul,
      associator_inv_naturality_left_assoc, comp_whiskerRight, Category.assoc])

private lemma restrictionTensor_π (M N : Mod C B) :
    Mod.tensorObjπ ((Mod.comap φ).obj M) ((Mod.comap φ).obj N) ≫
      (restrictionTensor φ M N).hom = Mod.tensorObjπ M N :=
  Mod.tensorObjπ_tensorObjDesc _ _ _ _

private def restrictionUnit : Mod.regular A ⟶ (Mod.comap φ).obj (Mod.regular B) :=
  Mod.Hom.mk' φ (by
    change μ[A] ≫ φ = A ◁ φ ≫ φ ▷ B ≫ μ[B]
    rw [IsMonHom.mul_hom, tensorHom_def', Category.assoc])

private lemma tensorπ_tensorHom {M N M' N' : Mod C A} (f : M ⟶ M') (g : N ⟶ N') :
    Mod.tensorObjπ M N ≫ (f ⊗ₘ g).hom =
      (f.hom ⊗ₘ g.hom) ≫ Mod.tensorObjπ M' N' := by
  simp only [MonoidalCategory.tensorHom_def, Mod.comp_hom', Category.assoc]
  rw [Mod.tensorObjπ_whiskerRight_assoc, Mod.tensorObjπ_whiskerLeft]

private lemma tensorRestriction_π {P Q : Mod C A} {M N : Mod C B}
    (f : P ⟶ (Mod.comap φ).obj M) (g : Q ⟶ (Mod.comap φ).obj N) :
    Mod.tensorObjπ P Q ≫ ((f ⊗ₘ g) ≫ restrictionTensor φ M N).hom =
      (f.hom ⊗ₘ g.hom) ≫ Mod.tensorObjπ M N := by
  erw [Mod.comp_hom', ← Category.assoc, tensorπ_tensorHom, Category.assoc,
    restrictionTensor_π]
  rfl

end BalancedTensor

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The balanced comparison is unique, including its zeroth tensor power.
Source: blueprint realization, Steps 8 and 9
(blueprint: lem-pur-condensed-tate-realization).
Proof: in degree zero use the prescribed ring inclusion. At a successor the displayed
map on the two underlying sheaves is R-balanced, so descends through the tensor
coequalizer. The coequalizer projection is epic, proving uniqueness by induction.
This is the ordinary scalar-extension tensor comparison, sending
b tensor (z_1 tensor ... tensor z_d) to (b tensor z_1) tensor ... tensor (1 tensor z_d). -/
theorem balancedPower_existsUnique :
    ∃! c : ∀ d : ℕ, integralPower X l d ⟶
      (Mod.comap (integralToQbar X l)).obj (tateTwistNat X l d),
      IsBalancedPowerFamily X l c := by
  let integralComm : IsCommMonObj (R X l) :=
    AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj
      (Profinite.continuousMapRingObj ℤ_[l]) X
  let qbarComm : IsCommMonObj (condensedRingObj (Profinite.padicAlgClRingObj l) X) :=
    AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj (Profinite.padicAlgClRingObj l) X
  let φ : R X l ⟶ condensedRingObj (Profinite.padicAlgClRingObj l) X := integralToQbar X l
  let η := (Mod.extendRestrictAdjunction
    (C := Sheaf (ProEt.topology X) Ab.{u + 1}) φ).unit.app (tateModule X l)
  let c : ∀ d : ℕ, integralPower X l d ⟶
      (Mod.comap (C := Sheaf (ProEt.topology X) Ab.{u + 1}) φ).obj (tateTwistNat X l d) :=
    Nat.rec (restrictionUnit φ) (fun d cd ↦
      (cd ⊗ₘ η) ≫ restrictionTensor (commA := integralComm) (commB := qbarComm) φ
        (tateTwistNat X l d) (tateTwistOne X l))
  have hc : IsBalancedPowerFamily X l c := by
    refine ⟨rfl, ?_⟩
    intro d
    change Mod.tensorObjπ (integralPower X l d) (tateModule X l) ≫
        ((c d ⊗ₘ η) ≫
          restrictionTensor (commA := integralComm) (commB := qbarComm) φ _ _).hom = _
    exact tensorRestriction_π (commA := integralComm) (commB := qbarComm) φ (c d) η
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  funext d
  induction d with
  | zero => exact Mod.hom_ext _ _ (hc'.1.trans hc.1.symm)
  | succ d ih =>
      apply Mod.hom_ext
      apply (cancel_epi (Mod.tensorObjπ (integralPower X l d) (tateModule X l))).1
      exact (hc'.2 d).trans ((congrArg
        (fun f : integralPower X l d ⟶
            (Mod.comap (C := Sheaf (ProEt.topology X) Ab.{u + 1}) φ).obj (tateTwistNat X l d) ↦
          (f.hom ⊗ₘ η.hom) ≫ Mod.tensorObjπ (tateTwistNat X l d) (tateTwistOne X l))
        ih).trans (hc.2 d).symm)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The uniquely specified balanced tensor map into the actual Tate twist.
Source: blueprint realization, Step 8
(blueprint: lem-pur-condensed-tate-realization). -/
def balancedPower (d : ℕ) := (balancedPower_existsUnique X l).exists.choose d

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Ordinary restriction through the same coefficient maps as the derived realization.
Source: blueprint realization, Step 7
(blueprint: lem-pur-condensed-tate-realization). -/
abbrev ordinaryRestriction (r : At l (LiftedQ.{u} l) X) :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X) ⥤
        pbcModules X (CompletedRing X l) :=
  Mod.comap (C := Sheaf (ProEt.topology X) Ab.{u + 1}) (rationalToQbar X l) ⋙
    (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).functor ⋙
      pbcRestrict (scalarMap X l r)

private theorem integralToQbar_factor :
    integralToRational X l ≫ rationalToQbar X l = integralToQbar X l := by
  let F := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})) ⋙ upperStarFromPoint X
  change F.map _ ≫ F.map _ = F.map _
  rw [← F.map_comp]
  rfl

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem transportSectionHom
    {A B : Sheaf (ProEt.topology X) Ab.{u + 1}}
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    {A' B' : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (ea : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology X) A ≅ A')
    (eb : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology X) B ≅ B')
    (φ : A ⟶ B) [IsMonHom φ] (ψ : A' ⟶ B')
    (h : sectionRingMap X φ ≫ eb.hom = ea.hom ≫ ψ)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) A)
    (N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) B)
    (f : M ⟶ (Mod.comap φ).obj N) :
    ∃! c :
        ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
          (ProEt.topology X) A).trans
          (ringModuleEquivalenceOfIso X ((adicLisseForget X).mapIso ea).symm)).functor.obj M ⟶
        (pbcRestrict ψ).obj
          (((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
            (ProEt.topology X) B).trans
            (ringModuleEquivalenceOfIso X ((adicLisseForget X).mapIso eb).symm)).functor.obj N),
      ∀ (V : X.ProEtᵒᵖ) (x : M.X.obj.obj V), c.val.app V x = f.hom.hom.app V x := by
  let f₀ :=
    (InternalAbelianSheafModule.sectionModuleFunctor.{u + 1, u + 1, u}
      (ProEt.topology X) A).map f ≫
      (sectionModuleComapIso X φ).hom.app N
  have hs (V : X.ProEtᵒᵖ) (a : A'.obj.obj V) :
      (sectionRingMap X φ).hom.app V (ea.inv.hom.app V a) =
        eb.inv.hom.app V (ψ.hom.app V a) := by
    have hh := congrArg (fun q ↦ ea.inv ≫ q ≫ eb.inv) h
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.inv_hom_id_assoc] at hh
    exact ConcreteCategory.congr_hom (congr_app (congrArg (fun q ↦ q.hom) hh) V) a
  refine ⟨⟨PresheafOfModules.homMk f.hom.hom ?_⟩, ?_, ?_⟩
  · intro V a x
    have hf := (f₀.val.app V).hom.map_smul (ea.inv.hom.app V a) x
    let MA := (InternalAbelianSheafModule.sectionModuleFunctor.{u + 1, u + 1, u}
      (ProEt.topology X) A).obj M
    let NB := (InternalAbelianSheafModule.sectionModuleFunctor.{u + 1, u + 1, u}
      (ProEt.topology X) B).obj N
    let SA := (adicLisseForget X).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology X) A)
    let SB := (adicLisseForget X).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology X) B)
    let a' : SA.obj.obj V := ea.inv.hom.app V a
    change f.hom.hom.app V (a' • (show MA.val.obj V from x)) =
      (show SB.obj.obj V from (sectionRingMap X φ).hom.app V a') •
        (show NB.val.obj V from f.hom.hom.app V x) at hf
    have hscalar : (show SB.obj.obj V from (sectionRingMap X φ).hom.app V a') =
        (show SB.obj.obj V from eb.inv.hom.app V (ψ.hom.app V a)) := hs V a
    exact hf.trans (congrArg (fun b : SB.obj.obj V ↦
      b • (show NB.val.obj V from f.hom.hom.app V x)) hscalar)
  · intro V x
    rfl
  · intro c hc
    ext V x
    exact hc V x

attribute [local semireducible] integralEncoding moduleEncoding in
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The coefficient-square-normalized ordinary map is unchanged on sections.
Source: blueprint realization, Steps 1, 3, 7 and 8
(blueprint: lem-pur-condensed-tate-realization).
Proof: the defining square for integralComparison identifies the composite scalar
restriction with restriction along integralToQbar. The section-module equivalence and
ring-isomorphism transport retain the underlying sections and restrictions. Thus the
balancedPower map is linear for precisely the completed-ring actions displayed here.
Its underlying section maps determine it uniquely. -/
theorem encodedBalancedPower_existsUnique (r : At l (LiftedQ.{u} l) X) (d : ℕ) :
    ∃! c : (integralEncoding X l r).functor.obj (integralPower X l d) ⟶
        (ordinaryRestriction X l r).obj (tateTwistNat X l d),
      ∀ (V : X.ProEtᵒᵖ) (x : (integralPower X l d).X.obj.obj V),
        c.val.app V x = (balancedPower X l d).hom.hom.app V x := by
  let N := (Mod.comap (rationalToQbar X l)).obj (tateTwistNat X l d)
  let f : integralPower X l d ⟶ (Mod.comap (integralToRational X l)).obj N :=
    balancedPower X l d ≫
      (Mod.comapCongr (integralToQbar_factor X l).symm).hom.app (tateTwistNat X l d) ≫
      (Mod.comapComp (integralToRational X l) (rationalToQbar X l)).hom.app
        (tateTwistNat X l d)
  have h := (integralComparison_existsUnique X l r).exists.choose_spec
  change (integralComparison X l r).hom ≫ scalarMap X l r =
    sectionRingMap X (integralToRational X l) ≫ r.sectionIso.hom at h
  exact transportSectionHom X (integralComparison X l r) r.sectionIso
    (integralToRational X l) (scalarMap X l r) h.symm (integralPower X l d) N f

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The unique completed-coefficient form of the balanced map.
Source: blueprint realization, Step 8
(blueprint: lem-pur-condensed-tate-realization). -/
def encodedBalancedPower (r : At l (LiftedQ.{u} l) X) (d : ℕ) :=
  (encodedBalancedPower_existsUnique X l r d).exists.choose

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The standard exact-functor composition comparisons for restriction.
Source: blueprint realization, Step 7
(blueprint: lem-pur-condensed-tate-realization). -/
def restrictionComparison (r : At l (LiftedQ.{u} l) X) :
    (ordinaryRestriction X l r).mapDerivedCategory ≅ ambientRestriction X l r :=
  Functor.mapDerivedCategoryCompIso
      (Mod.comap (C := Sheaf (ProEt.topology X) Ab.{u + 1}) (rationalToQbar X l) ⋙
        (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).functor)
      (pbcRestrict (scalarMap X l r)) ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryCompIso
        (Mod.comap (C := Sheaf (ProEt.topology X) Ab.{u + 1}) (rationalToQbar X l))
        (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).functor)
      (pbcDerivedRestrict (scalarMap X l r))
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Derive the specified ordinary balanced map and use the standard single comparison.
Source: blueprint realization, Steps 7 and 8
(blueprint: lem-pur-condensed-tate-realization). -/
def derivedBalancedPower (r : At l (LiftedQ.{u} l) X) (d : ℕ) :
    (DerivedCategory.singleFunctor _ 0).obj
        ((integralEncoding X l r).functor.obj (integralPower X l d)) ⟶
      (ambientRestriction X l r).obj (tateTwistDerived X l (d : ℤ)) :=
  (DerivedCategory.singleFunctor _ 0).map (encodedBalancedPower X l r d) ≫
    ((ordinaryRestriction X l r).mapDerivedCategorySingleFunctor 0).inv.app _ ≫
      (restrictionComparison X l r).hom.app _
attribute [local semireducible] HasDerivedCategory.standard in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The actual positive-index derived-limit projection.
Source: blueprint realization, Step 6
(blueprint: lem-pur-condensed-tate-realization). -/
def reconstructedProjection (r : At l (LiftedQ.{u} l) X) (d n : ℕ) :
    reconstructed X l r d ⟶
      (DerivedCategory.singleFunctor _ 0).obj
        ((encodedTower X l r d).obj (op n)) :=
  singleDerivedProjection (tateRlim X (CompletedRing X l))
    (reductionTowerEvaluation X (reductionModuleRing X (CompletedRing X l)) n)
    (tateRlimProjection X (CompletedRing X l) n) (encodedTower X l r d)

attribute [local semireducible] HasDerivedCategory.standard in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Canonical reductions mean the given derived-limit projections factor through the
scalar-extension unit by isomorphisms, retaining the completed-ring action.
Source: blueprint realization, hypothesis on M_d
(blueprint: lem-pur-condensed-tate-realization). -/
def HasCanonicalReductions (r : At l (LiftedQ.{u} l) X) (d : ℕ) : Prop :=
  ∀ n : ℕ, ∃ e :
      (pbcDerivedRestrict (pbcAdicProjection X (pbcIntegralDatum l (LiftedQ.{u} l)) n)).obj
        ((pbcCompletedReduction X (pbcIntegralDatum l (LiftedQ.{u} l)) n).obj
          (shiftedReconstructed X l r d)) ≅
      (shiftFunctor _ (2 * d : ℤ)).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((encodedTower X l r d).obj (op n))),
    (pbcDerivedScalarAdjunction
        (pbcAdicProjection X (pbcIntegralDatum l (LiftedQ.{u} l)) n)).unit.app
          (shiftedReconstructed X l r d) ≫ e.hom =
      (shiftFunctor _ (2 * d : ℤ)).map (reconstructedProjection X l r d n)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The exact sectionwise module equivalence carries the standard derived shift comparison.
Source: blueprint realization, Step 7
(blueprint: lem-pur-condensed-tate-realization). -/
noncomputable instance encodingMapCommShift (r : At l (LiftedQ.{u} l) X) :
    ((moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.functor).CommShift ℤ := by
  letI : (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).functor.Additive := by
    infer_instance
  letI : (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).inverse.Additive := by
    infer_instance
  change ((moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).functor.mapDerivedCategory).CommShift ℤ
  infer_instance

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The inverse exact module equivalence carries the standard derived shift comparison.
Source: blueprint realization, Step 7
(blueprint: lem-pur-condensed-tate-realization). -/
noncomputable instance encodingInverseCommShift (r : At l (LiftedQ.{u} l) X) :
    ((moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.inverse).CommShift ℤ := by
  letI : (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).functor.Additive := by
    infer_instance
  letI : (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).inverse.Additive := by
    infer_instance
  change ((moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).inverse.mapDerivedCategory).CommShift ℤ
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The scalar-extension realization carries the canonical derived shift comparison.
Source: blueprint realization, Steps 7--9
(blueprint: lem-pur-condensed-tate-realization). -/
noncomputable instance ambientRealizationCommShift (r : At l (LiftedQ.{u} l) X) :
    (ambientRealization X l r).CommShift ℤ := by
  let restrictShift {A B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
      (φ : A ⟶ B) : (pbcDerivedRestrict φ).CommShift ℤ := by
    unfold pbcDerivedRestrict
    infer_instance
  let extendShift {A B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
      (φ : A ⟶ B) : (pbcDerivedExtend φ).CommShift ℤ := by
    letI : (pbcDerivedRestrict φ).CommShift ℤ := restrictShift φ
    exact (pbcDerivedScalarAdjunction φ).leftAdjointCommShift ℤ
  letI : (pbcDerivedExtend (scalarMap X l r)).CommShift ℤ :=
    extendShift (scalarMap X l r)
  let G : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X) ⥤
      Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (Coefficient (LiftedQ.{u} l) X) :=
    Mod.comap (C := Sheaf (ProEt.topology X) Ab.{u + 1}) (rationalToQbar X l)
  letI : G.mapDerivedCategory.CommShift ℤ := inferInstance
  letI : (rationalDerivedExtension X l).CommShift ℤ := by
    unfold rationalDerivedExtension
    exact (Mod.derivedExtendMapDerivedCategoryAdjunction (C := Sheaf (ProEt.topology X) Ab.{u + 1})
      (rationalToQbar X l)).leftAdjointCommShift ℤ
  unfold ambientRealization
  infer_instance

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The shifted scalar comparison, formed from the recorded J comparison and the
canonical shift comparison of actual derived scalar extension.
Source: blueprint realization, Steps 7--9
(blueprint: lem-pur-condensed-tate-realization). -/
def shiftedComparison (r : At l (LiftedQ.{u} l) X) (d : ℕ)
    (hM : PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l (LiftedQ.{u} l))
      (shiftedReconstructed X l r d))
    (e : (ambientRealization X l r).obj (reconstructed X l r d) ≅
      tateTwistDerived X l (d : ℤ)) :
    realized X l r ⟨shiftedReconstructed X l r d, hM⟩ ≅
      (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X l (d : ℤ)) :=
  (realizationComparison X l r ⟨shiftedReconstructed X l r d, hM⟩).symm ≪≫
    ((ambientRealization X l r).commShiftIso (2 * d : ℤ)).app
      (reconstructed X l r d) ≪≫ (shiftFunctor _ (2 * d : ℤ)).mapIso e

end AlgebraicGeometry.ProEtale.CondensedTateRealization
