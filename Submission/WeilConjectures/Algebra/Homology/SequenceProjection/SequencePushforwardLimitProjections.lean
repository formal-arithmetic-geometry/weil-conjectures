/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Algebra.Homology.SequenceProjection.SequenceProjectionDerivedAdjunction
public import Submission.WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Submission.WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Submission.WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Submission.WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import Submission.WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.CochainHomotopyComparison
import all Submission.WeilConjectures.CategoryTheory.SixFunctors.ResolvingDerivedAdjunction
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import all Mathlib.CategoryTheory.Filtered.Basic
import all Mathlib.CategoryTheory.Limits.Cones
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Submission.WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
import Submission.WeilConjectures.Algebra.Homology.System.SystemScalarGenerators
import Submission.WeilConjectures.Algebra.Homology.System.SystemGrothendieck
import Submission.WeilConjectures.Algebra.Homology.RestrictedTowerResolution.RestrictedTowerResolutionAcyclicity
import Submission.WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import Submission.WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import Submission.WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Submission.WeilConjectures.Algebra.Homology.KFlatResolution
import Submission.WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Submission.WeilConjectures.CategoryTheory.RingedToposRingData
import Submission.WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import Submission.WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import Submission.WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import Submission.WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import Submission.WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import Submission.WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import Submission.WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import Submission.WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Submission.WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Total-limit projections and the sequence-projection adjunction

Source: Stacks Project, Cohomology on Sites, Tags 0D6E, 0941 and 07A6;
Derived Categories, Tag 09T5.
(blueprint: lem-coef-sequence-pushforward-limit-projections).

All functors act on the existing strict-system and module derived categories.
The initial existential data are exactly the normalized presentation provided by
`derivedAdjunction`. Index `n` denotes positive level `n+1`.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local instance 10000] CategoryTheory.HasSheafify.isRightAdjoint

universe u v w d
open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules.SequenceProjection

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

private theorem complexProjection
    {D E T : Type*} [Category D] [Category E] [Category T]
    [Abelian D] [Abelian E] [Abelian T]
    (F H : D ⥤ E) (U : D ⥤ T) (V W : T ⥤ E)
    [F.Additive] [H.Additive] [U.Additive] [V.Additive] [W.Additive]
    (e : F ≅ U ⋙ V) (p : V ⟶ W) (a : U ⋙ W ≅ H) (q : F ⟶ H)
    (h : e.hom ≫ Functor.whiskerLeft U p ≫ a.hom = q)
    (I : CochainComplex D ℤ) :
    (NatIso.mapHomologicalComplex e (.up ℤ)).hom.app I ≫
      (NatTrans.mapHomologicalComplex p (.up ℤ)).app
        ((U.mapHomologicalComplex (.up ℤ)).obj I) ≫
      (NatIso.mapHomologicalComplex a (.up ℤ)).hom.app I =
        (NatTrans.mapHomologicalComplex q (.up ℤ)).app I := by
  apply HomologicalComplex.hom_ext
  intro i
  have hh := congrArg (fun t ↦ t.app (I.X i)) h
  change e.hom.app (I.X i) ≫ p.app (U.obj (I.X i)) ≫ a.hom.app (I.X i) =
    q.app (I.X i)
  exact hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryLevel
    (A : Sheaf J CommRingCat.{w}) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)
    (G : Modules A ⥤ StrictRingSystem B)
    (e : ∀ (M : Modules A) (n : ℕ),
      (G.obj M).level n ≅ changeOfRings (α.app (op n)) M)
    (hmap : ∀ {M M' : Modules A} (f : M ⟶ M') (n : ℕ),
      (G.map f).app n ≫ (e M' n).hom =
        (e M n).hom ≫ changeOfRingsHom (α.app (op n)) M f)
    (n : ℕ) :
    ∃ a : G ⋙ systemEvaluation B n ⊣ restriction A B α n,
      ∀ (M : Modules A) (K : systemLevel B n)
        (h : M ⟶ (restriction A B α n).obj K) (V : Cᵒᵖ)
        (b : (B.obj (op n)).obj.obj V) (x : M.val.obj V),
        ((a.homEquiv M K).symm h).val.app V
            ((e M n).inv.val.app V (tensorSection (α.app (op n)) M V b x)) =
          @SMul.smul ((B.obj (op n)).obj.obj V) (K.val.obj V) inferInstance b
            (h.val.app V x) := by
  obtain ⟨s⟩ := nonempty_systemScalarModel (α.app (op n))
  let k : G ⋙ systemEvaluation B n ≅ s.model.E :=
    NatIso.ofComponents (fun M ↦ e M n ≪≫ (eqToIso (s.model.obj_eq M)).symm) (by
      intro M M' f
      change (G.map f).app n ≫ ((e M' n).hom ≫ eqToHom (s.model.obj_eq M').symm) =
        ((e M n).hom ≫ eqToHom (s.model.obj_eq M).symm) ≫ s.model.E.map f
      rw [← Category.assoc, hmap, s.model.map_eq]
      simp)
  refine ⟨s.ordinaryAdj.ofNatIsoLeft k.symm, ?_⟩
  intro M K h V b x
  rw [Adjunction.homEquiv_ofNatIsoLeft_symm_apply]
  change ((s.ordinaryAdj.homEquiv M K).symm h).val.app V
    ((k.hom.app M).val.app V
      ((e M n).inv.val.app V (tensorSection (α.app (op n)) M V b x))) = _
  have ht : (k.hom.app M).val.app V
      ((e M n).inv.val.app V (tensorSection (α.app (op n)) M V b x)) =
      systemModelTmul s.model M V b x := by
    change (eqToHom (s.model.obj_eq M).symm).val.app V
      ((e M n).hom.val.app V
        ((e M n).inv.val.app V (tensorSection (α.app (op n)) M V b x))) = _
    have he := congrArg (fun f ↦ f.val.app V (tensorSection (α.app (op n)) M V b x))
      (e M n).inv_hom_id
    change (e M n).hom.val.app V
      ((e M n).inv.val.app V (tensorSection (α.app (op n)) M V b x)) = _ at he
    rw [he]
    exact ((eqToHom (s.model.obj_eq M).symm).val.app V).hom.map_smul b _
  rw [ht, systemScalarModel_transpose_tmul, Equiv.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensor_hom_ext
    (A S : Sheaf J CommRingCat.{w}) (φ : A ⟶ S)
    (M : Modules A) (K : Modules S) (f g : changeOfRings φ M ⟶ K)
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U),
      f.val.app U (tensorSection φ M U 1 x) =
        g.val.app U (tensorSection φ M U 1 x)) : f = g := by
  obtain ⟨s⟩ := nonempty_systemScalarModel φ
  apply (cancel_epi (eqToHom (s.model.obj_eq M))).1
  apply systemScalarModel_hom_ext s M K
  intro U x
  have ht : (eqToHom (s.model.obj_eq M)).val.app U
      (systemModelTmul s.model M U 1 x) = tensorSection φ M U 1 x := by
    dsimp only [systemModelTmul, tensorSection]
    simp only [one_smul]
    change ((eqToHom (s.model.obj_eq M).symm ≫ eqToHom (s.model.obj_eq M)).val.app U)
      _ = _
    rw [eqToHom_trans]
    exact (@one_smul (S.obj.obj U) ((changeOfRings φ M).val.obj U) _ _ _).symm
  change f.val.app U ((eqToHom (s.model.obj_eq M)).val.app U _) =
    g.val.app U ((eqToHom (s.model.obj_eq M)).val.app U _)
  rw [ht]
  exact h U x

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryProjection
    (A : Sheaf J CommRingCat.{w}) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)
    (G : Modules A ⥤ StrictRingSystem B) (F : StrictRingSystem B ⥤ Modules A)
    (e : ∀ (M : Modules A) (n : ℕ),
      (G.obj M).level n ≅ changeOfRings (α.app (op n)) M)
    (π : ∀ (N : StrictRingSystem B) (n : ℕ),
      F.obj N ⟶ (restriction A B α n).obj (N.level n))
    (adj : G ⊣ F)
    (hsection : ∀ M N (h : M ⟶ F.obj N) n U b x,
      (((adj.homEquiv M N).symm h).app n).val.app U
          ((e M n).inv.val.app U (tensorSection (α.app (op n)) M U b x)) =
        @SMul.smul ((B.obj (op n)).obj.obj U) ((N.level n).val.obj U) inferInstance b
          ((π N n).val.app U (h.val.app U x)))
    (n : ℕ) (a : G ⋙ systemEvaluation B n ⊣ restriction A B α n)
    (ha : ∀ M K (h : M ⟶ (restriction A B α n).obj K) U b x,
      ((a.homEquiv M K).symm h).val.app U
          ((e M n).inv.val.app U (tensorSection (α.app (op n)) M U b x)) =
        @SMul.smul ((B.obj (op n)).obj.obj U) (K.val.obj U) inferInstance b
          (h.val.app U x)) (N : StrictRingSystem B) :
    a.homEquiv (F.obj N) (N.level n) ((adj.counit.app N).app n) = π N n := by
  apply (a.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply]
  apply (cancel_epi (e (F.obj N) n).inv).1
  apply tensor_hom_ext A (B.obj (op n)) (α.app (op n))
  intro U x
  change ((adj.counit.app N).app n).val.app U
      ((e (F.obj N) n).inv.val.app U _) = _
  have hc : adj.counit.app N = (adj.homEquiv (F.obj N) N).symm (𝟙 _) := by
    simp [Adjunction.homEquiv_counit]
  rw [hc]
  change _ = ((a.homEquiv (F.obj N) (N.level n)).symm (π N n)).val.app U
    ((e (F.obj N) n).inv.val.app U (tensorSection (α.app (op n)) (F.obj N) U 1 x))
  erw [hsection, ha]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local irreducible] _root_.instCategoryDerivedCategory
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
attribute [local irreducible] DerivedCategory DerivedCategory.Q DerivedCategory.Qh

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- The statement retains all normalized presentation clauses of the sequence adjunction.
-- Retain all normalization clauses in the full comparison statement.
end SheafOfModules.SequenceProjection
