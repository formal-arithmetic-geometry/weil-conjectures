/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Submission.WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import Submission.WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import Submission.WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Submission.WeilConjectures.Algebra.Homology.KFlatResolution
import Submission.WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
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
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
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
import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
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
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Submission.WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Normalized evaluation of a total derived tower functor

Source: Stacks Project, Sites Cohomology, Tag 0A07, lemma-Rf-commutes-with-Rlim,
diagram-topos proof, expanded using Derived Categories, Tags 070I, 070Y and 09T5
(blueprint: lem-weil-pbc-tower-derived-evaluation-normalization).

Natural number `n` denotes the positive tower level `n + 1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uA vA uB vB wA wB wTA wTB uC vC wC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Package Mathlib's pointwise limit-preservation instances for a termwise exact functor.
Source: Stacks Project, Tag 0A07, diagram-topos proof; Mathlib functor-category limits
(blueprint: lem-weil-pbc-tower-derived-evaluation-normalization). -/
instance towerNormalization_preservesFiniteLimits
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [HasFiniteLimits B] (F : B ⥤ A) [PreservesFiniteLimits F] :
    PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj F) where
  preservesFiniteLimits _ _ _ := inferInstance

/-- Package Mathlib's pointwise colimit-preservation instances for a termwise exact functor.
Source: Stacks Project, Tag 0A07, diagram-topos proof; Mathlib functor-category colimits
(blueprint: lem-weil-pbc-tower-derived-evaluation-normalization). -/
instance towerNormalization_preservesFiniteColimits
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [HasFiniteColimits B] (F : B ⥤ A) [PreservesFiniteColimits F] :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj F) where
  preservesFiniteColimits _ _ _ := inferInstance

/-- The canonical transition between derived evaluations, obtained by localizing the
ordinary transition of exact evaluation functors. This includes every transition,
including the identity. Source: Stacks Project, Tag 0A07, diagram-topos proof;
Derived Categories, Tag 05RU
(blueprint: lem-weil-pbc-tower-derived-evaluation-normalization). -/
def towerDerivedEvaluationTransition
    (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]
    {m n : ℕᵒᵖ} (t : m ⟶ n) :
    ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategory ⟶
      ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) _ _
    ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategory
    ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map t) (.up ℤ))
      DerivedCategory.Q)

private theorem towerTransition_fac
    (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]
    {m n : ℕᵒᵖ} (t : m ⟶ n) (J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (towerDerivedEvaluationTransition A t).app (DerivedCategory.Q.obj J) ≫
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app J =
      ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategoryFactors.hom.app J ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map t) (.up ℤ)).app J) := by
  have hm : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
      (((evaluation ℕᵒᵖ A).obj m).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategory =
        ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategoryFactors := rfl
  have hn : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
      (((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory =
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors := rfl
  simp [towerDerivedEvaluationTransition, Localization.liftNatTrans_app, hm, hn]

private theorem towerTransition_inv_fac
    (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]
    {m n : ℕᵒᵖ} (t : m ⟶ n) (J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategoryFactors.inv.app J ≫
        (towerDerivedEvaluationTransition A t).app (DerivedCategory.Q.obj J) =
      DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map t) (.up ℤ)).app J) ≫
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.inv.app J := by
  apply (cancel_mono
    (((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app J)).mp
  simp only [Category.assoc, towerTransition_fac, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app]
  exact (Category.comp_id _).symm

private theorem exactDerivedAdjunction
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [Abelian.HasKInjectiveResolutions A]
    (F : B ⥤ A) (G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    [RG.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (.up ℤ))] :
    ∃ d : F.mapDerivedCategory ⊣ RG,
      ∀ (M : CochainComplex B ℤ) (I : CochainComplex A ℤ)
        (f : (F.mapHomologicalComplex (.up ℤ)).obj M ⟶ I),
        d.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
            (F.mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map f) =
          DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv M I f) ≫
            η.app I := by
  let W := HomologicalComplex.quasiIso B (.up ℤ)
  let V := HomologicalComplex.quasiIso A (.up ℤ)
  let α := F.mapDerivedCategoryFactors.hom
  have : F.mapDerivedCategory.IsLeftDerivedFunctor α W :=
    Functor.isLeftDerivedFunctor_of_inverts W _ F.mapDerivedCategoryFactors
  have : (F.mapDerivedCategory ⋙ RG).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α RG) W :=
    Functor.isLeftDerivedFunctor_of_inverts W _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight F.mapDerivedCategoryFactors RG)
  have : (RG ⋙ F.mapDerivedCategory).IsRightDerivedFunctor
      (Functor.whiskerRight η F.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom) V := by
    have hd : (CochainComplex.KInjectives.localizerMorphism A).Derives
        (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙ F.mapDerivedCategory) := by
      intro I I' f hf
      have : IsIso (DerivedCategory.Q.map
          ((G.mapHomologicalComplex (.up ℤ)).map f.hom)) := (derives G) f hf
      exact F.mapDerivedCategory.map_isIso
        (DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map f.hom))
    apply hd.isRightDerivedFunctor_of_isIso
    intro I
    have : IsIso (η.app I.obj) := (derives G).isIso_of_isRightDerivedFunctor η I
    change IsIso (F.mapDerivedCategory.map (η.app I.obj) ≫ 𝟙 _)
    infer_instance
  let ac := adj.mapHomologicalComplex (.up ℤ)
  let d := ac.derived W V α η
  refine ⟨d, ?_⟩
  intro M I f
  change d.unit.app _ ≫ RG.map (α.app M ≫ DerivedCategory.Q.map f) = _
  rw [RG.map_comp, ← Category.assoc]
  have hunit := ac.derivedη_fac_app W α η M
  change d.unit.app _ ≫ RG.map (α.app M) = _ at hunit
  have hn := η.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [hunit, Category.assoc, ← hn, ← DerivedCategory.Q.map_comp_assoc]
  rfl

end CategoryTheory
