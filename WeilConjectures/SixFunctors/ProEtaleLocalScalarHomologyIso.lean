/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicLisseModuleSupplement
public import WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleLocalRestriction.ProEtaleLocalDerivedRestrictionComparisonsSupplement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcActualScalarPullbackSupplement
import all WeilConjectures.Algebra.Homology.Ringed.RingedTopoiDerivedPullbackIndependentSupplement
import all WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.ProperBaseChange.RingedSliceExtensionTensorHomData

/-! # Local invariance of cohomology after derived scalar extension

Source: Stacks Project, Cohomology on Sites, derived pullback and
lemma-pullback-tensor-product; restriction-K-flat, Tag 0E8K.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

section LocalScalarComparison

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
attribute [local instance 3000] localWEquals

attribute [local irreducible] completedAdicChangeData HasDerivedCategory.standard
  CochainComplex.IsKFlatIndependentCoefficients
  SheafOfModules.monoidalCategory proEtaleModuleInverseImage
  Functor.sheafPullbackConstruction.sheafPullback

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private def scalarAdjunction (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    completedAdicChange X φ ⊣
      SheafOfModules.restrictScalars ((adicLisseForget X).map φ) :=
  pbcScalarAdjunction φ

end LocalScalarComparison

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private theorem complexCounit_isIso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] (LF : DerivedCategory A ⥤ DerivedCategory B)
    (ε : (DerivedCategory.Qh (C := A)) ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := B))
    (P : CochainComplex A ℤ)
    [IsIso (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P))] :
    IsIso ((complexCounit F LF ε).app P) := by
  simp only [complexCounit, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
  infer_instance

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
private theorem derivedSquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (E : A ⥤ B) [E.Additive]
    (F : A ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : B ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (T : C ⥤ D) [T.Additive]
    (LE : DerivedCategory A ⥤ DerivedCategory B)
    (LT : DerivedCategory C ⥤ DerivedCategory D)
    (εE : DerivedCategory.Qh ⋙ LE ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (εT : DerivedCategory.Qh ⋙ LT ⟶ T.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : ObjectProperty (CochainComplex A ℤ))
    (hres : ∀ K : HomotopyCategory A (.up ℤ),
      ∃ (L : (show ObjectProperty (HomotopyCategory A (.up ℤ)) from
          fun K ↦ P K.as).FullSubcategory) (s : L.obj ⟶ K),
        HomotopyCategory.quasiIso A (.up ℤ) s)
    (he : ∀ K : P.FullSubcategory,
      IsIso (εE.app ((HomotopyCategory.quotient A (.up ℤ)).obj K.obj)))
    (ht : ∀ K : P.FullSubcategory,
      IsIso (εT.app ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj K.obj))))
    (b : E ⋙ G ≅ F ⋙ T) :
    Nonempty (LE ⋙ G.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ LT) := by
  let : (F ⋙ T).Additive := by infer_instance
  let : (E ⋙ G).Additive := by infer_instance
  let ec := complexCounit E LE εE
  let tc := complexCounit T LT εT
  let l : DerivedCategory.Q ⋙ (LE ⋙ G.mapDerivedCategory) ⟶
      (E.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q :=
    whiskerRight ec G.mapDerivedCategory ≫
      whiskerLeft (E.mapHomologicalComplex (.up ℤ)) G.mapDerivedCategoryFactors.hom
  let r : DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ LT) ⟶
      (F.mapHomologicalComplex (.up ℤ) ⋙ T.mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q :=
    whiskerRight F.mapDerivedCategoryFactors.hom LT ≫
      whiskerLeft (F.mapHomologicalComplex (.up ℤ)) tc
  let b₀ := Functor.mapHomologicalComplexCompIso (F := E) (G := G) (Iso.refl _) (.up ℤ) ≪≫
    NatIso.mapHomologicalComplex b (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (F := F) (G := T) (Iso.refl _) (.up ℤ)).symm
  have hl (K : P.FullSubcategory) : IsIso (l.app K.obj) := by
    let := he K
    let : IsIso (ec.app K.obj) := complexCounit_isIso E LE εE K.obj
    dsimp only [l, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
    infer_instance
  have hr (K : P.FullSubcategory) : IsIso (r.app K.obj) := by
    let := ht K
    let : IsIso (tc.app ((F.mapHomologicalComplex (.up ℤ)).obj K.obj)) :=
      complexCounit_isIso T LT εT _
    dsimp only [r, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
    infer_instance
  obtain ⟨e, _, _⟩ := comparison_on_resolutions P hres
    (LE ⋙ G.mapDerivedCategory) (F.mapDerivedCategory ⋙ LT) _ _ l r
      (Functor.isoWhiskerRight b₀ DerivedCategory.Q) hl hr
  exact ⟨e⟩

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
attribute [local irreducible] SheafOfModules.monoidalCategory in
set_option backward.isDefEq.respectTransparency true

section LocalScalarComparison

attribute [local instance 3000] localWEquals
attribute [local irreducible] completedAdicChangeData HasDerivedCategory.standard
  CochainComplex.IsKFlatIndependentCoefficients
  SheafOfModules.monoidalCategory proEtaleModuleInverseImage
  Functor.sheafPullbackConstruction.sheafPullback

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
attribute [local instance 3000] sliceDerived

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
attribute [local instance] localFunctor_additive localFunctor_limits localFunctor_colimits

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
set_option linter.defProp false in

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
attribute [local irreducible] sliceChangeData

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
attribute [local instance] sliceChange_additive

attribute [local irreducible] sliceChange Functor.mapHomotopyCategory DerivedCategory.Qh

attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
  ProjectionRestriction.derivedOver ProjectionRestriction.derivedOverModules in
attribute [local irreducible] sliceDerivedChange completedAdicChange
  completedAdicDerivedChange localFunctor

attribute [local irreducible] Functor.mapDerivedCategory DerivedCategory.Q

end LocalScalarComparison

end AlgebraicGeometry.Scheme
