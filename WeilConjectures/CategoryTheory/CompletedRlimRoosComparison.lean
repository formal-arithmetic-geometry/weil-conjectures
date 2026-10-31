/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedRlimFunctor
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.CategoryTheory.StrictRoosDerivation
import WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.Algebra.Homology.RoosComplex
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.AlgebraicGeometry.CompletedRlimFunctor
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-! # The normalized Roos comparison for the actual total inverse limit

Source: Stacks Project, sites-cohomology.tex, Tag 0941,
lemma-derived-limit-is-ok (blueprint: lem-a1-completed-rlim-roos-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory

private instance fixedAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, 0} W
private instance fixedAbBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} W

variable (W : Scheme.{u}) (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})

set_option backward.isDefEq.respectTransparency false in
private def strictTowerLimitIso
    {A : Type*} [Category* A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A] :
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ) ≅
        (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) :=
  NatIso.ofComponents (fun X ↦
    limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval X.asFunctor,
      HomologicalComplex.isLimitConeOfHasLimitEval X.asFunctor⟩) (by
    intro X Y f
    apply (HomologicalComplex.isLimitConeOfHasLimitEval Y.asFunctor).hom_ext
    intro n
    ext p
    have hπ (Z : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
        (limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval Z.asFunctor,
          HomologicalComplex.isLimitConeOfHasLimitEval Z.asFunctor⟩).hom.f p ≫
            limit.π (Z.X p) n = (limit.π Z.asFunctor n).f p := by
      simpa only [HomologicalComplex.comp_f,
        HomologicalComplex.coneOfHasLimitEval_π_app_f, HomologicalComplex.asFunctor,
        HomologicalComplex.eval, Functor.comp] using
        congrArg (fun f ↦ HomologicalComplex.Hom.f f p)
          (limit.isoLimitCone_hom_π
            ⟨HomologicalComplex.coneOfHasLimitEval Z.asFunctor,
              HomologicalComplex.isLimitConeOfHasLimitEval Z.asFunctor⟩ n)
    have hm := congrArg (fun f ↦ HomologicalComplex.Hom.f f p)
      (limMap_π (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) n)
    dsimp at hπ hm ⊢
    simp only [HomologicalComplex.coneOfHasLimitEval_π_app_f,
      HomologicalComplex.asFunctor, HomologicalComplex.eval, Functor.comp] at hπ hm ⊢
    calc
      _ = (limMap (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f)).f p ≫
          (limit.π Y.asFunctor n).f p := by
        rw [Category.assoc, hπ Y]
        rfl
      _ = (limit.π X.asFunctor n).f p ≫ (f.f p).app n := hm
      _ = _ := by
        rw [Category.assoc]
        change _ = _ ≫ limMap (f.f p) ≫ limit.π (Y.X p) n
        rw [limMap_π, ← Category.assoc, hπ X]
        rfl)


private def limitUnit :
    (completedTowerLimit W R).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ completedRlim W R where
  app := (completedTowerLimit W R).rightDerivedFunctorUnitQ
  naturality _ _ f := (completedTowerLimit W R).rightDerivedFunctorUnitQ_naturality f

private theorem limitUnit_derived :
    (completedRlim W R).IsRightDerivedFunctor (limitUnit W R)
      (HomologicalComplex.quasiIso (reductionTowerCategory W (reductionModuleRing W R))
        (.up ℤ)) := by
  apply (derives (completedTowerLimit W R)).isRightDerivedFunctor_of_isIso (limitUnit W R)
  intro I
  have := I.property
  change IsIso ((completedTowerLimit W R).rightDerivedFunctorUnitQ I.obj)
  rw [Functor.rightDerivedFunctorUnitQ_eq]
  infer_instance

private def totalLimitUnit :
    roosLimitFunctor (A := reductionModules W R) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ completedRlim W R :=
  (Functor.isoWhiskerRight strictTowerLimitIso DerivedCategory.Q).hom ≫ limitUnit W R

private theorem totalLimitUnit_derived :
    (completedRlim W R).IsRightDerivedFunctor (totalLimitUnit W R)
      (HomologicalComplex.quasiIso (reductionTowerCategory W (reductionModuleRing W R))
        (.up ℤ)) := by
  apply (Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _ _).2
  apply (Functor.isLeftKanExtension_iff_of_iso₂ (totalLimitUnit W R) (limitUnit W R)
    (Functor.isoWhiskerRight strictTowerLimitIso DerivedCategory.Q)
    (Iso.refl _) (by simp [totalLimitUnit])).2
  exact (Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _ _).1
    (limitUnit_derived W R)

/-- The actual total right-derived inverse limit is computed by the normalized
strict Roos functor, compatibly with each of its actual derived projections.
Source: Stacks Project, sites-cohomology.tex, Tag 0941, lemma-derived-limit-is-ok.
(blueprint: lem-a1-completed-rlim-roos-comparison).
Proof: exact countable products give the universal Roos derived pair. Compare that
pair with the universal pair of the actual inverse-limit functor, identifying the
termwise limit complex with the limit of complexes. The comparison respects their
units. On a K-injective tower resolution the inclusion is (0,z); composing with any
Roos projection gives the ordinary limit projection. The right-derived projection
unit identity therefore identifies the two evaluations on resolutions. Naturality
and inversion of the resolution extend the equation to every tower complex. -/
theorem completedRlim_roosComparison
    [HasExactLimitsOfShape (Discrete ℕ) (reductionModules W R)] :
    ∃ e : roosF (A := reductionModules W R) ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ completedRlim W R,
      (∀ I : CochainComplex (reductionTowerCategory W (reductionModuleRing W R)) ℤ,
        DerivedCategory.Q.map (roosι I) ≫ e.hom.app I =
          DerivedCategory.Q.map
              ((limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval I.asFunctor,
                HomologicalComplex.isLimitConeOfHasLimitEval I.asFunctor⟩).hom) ≫
            (completedTowerLimit W R).rightDerivedFunctorUnitQ I) ∧
      ∀ (P : CochainComplex (reductionTowerCategory W (reductionModuleRing W R)) ℤ)
        (n : ℕ),
        e.hom.app P ≫ (completedRlimProjection W R n).app (DerivedCategory.Q.obj P) ≫
            ((evaluation ℕᵒᵖ (reductionModules W R)).obj
              (op n)).mapDerivedCategoryFactors.hom.app P =
          DerivedCategory.Q.map (roosEval P n) := by
  let S := reductionModuleRing W R
  have hcomm (U : W.ProEtᵒᵖ) (a b : S.obj.obj U) : a * b = b * a :=
    @mul_comm (R.obj.obj U) _ a b
  obtain ⟨CF, κ, hCF, hι⟩ :=
    strictRoosDerivation.{u + 1, u, 0, u + 2} (ProEt.topology W) S hcomm
  let := hCF
  let := totalLimitUnit_derived W R
  let V := HomologicalComplex.quasiIso (reductionTowerCategory W S) (.up ℤ)
  let ρ := CF.rightDerivedUnique (completedRlim W R) (roosDerivedUnit κ)
    (totalLimitUnit W R) V
  let e := κ ≪≫ Functor.isoWhiskerLeft DerivedCategory.Q ρ
  have heunit (I : CochainComplex (reductionTowerCategory W S) ℤ) :
      DerivedCategory.Q.map (roosι I) ≫ e.hom.app I =
        (totalLimitUnit W R).app I := by
    have h := CF.rightDerivedNatTrans_app (completedRlim W R) (roosDerivedUnit κ)
      (totalLimitUnit W R) V (𝟙 _) I
    simpa [e, ρ, Functor.rightDerivedUnique, Functor.rightDerivedNatIso,
      roosDerivedUnit, roosInclusion, roosLimitFunctor,
      Functor.rightDerivedNatTrans, Category.assoc] using h
  refine ⟨e, ?_, ?_⟩
  · exact heunit
  intro P n
  have hunit (I : CochainComplex
      (reductionTowerCategory W (reductionModuleRing W R)) ℤ) :
      (totalLimitUnit W R).app I ≫
        (completedRlimProjection W R n).app (DerivedCategory.Q.obj I) ≫
          ((evaluation ℕᵒᵖ (reductionModules W R)).obj
            (op n)).mapDerivedCategoryFactors.hom.app I =
        DerivedCategory.Q.map (limit.π I.asFunctor (op n)) := by
    dsimp only [totalLimitUnit, NatTrans.comp_app, Functor.whiskerRight_app,
      limitUnit, NatTrans.app]
    simp only [Functor.rightDerivedFunctorUnitQ, DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso,
      Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
    erw [(completedRlim W R).map_id, Category.id_comp, Category.comp_id]
    simp only [Category.assoc]
    change DerivedCategory.Q.map (strictTowerLimitIso.hom.app I) ≫
        (completedRlimUnit W R).app ((HomotopyCategory.quotient _ _).obj I) ≫
          (completedRlimProjection W R n).app (DerivedCategory.Q.obj I) ≫ _ = _
    erw [reassoc_of% (completedRlimProjection_unit W R I n)]
    simp only [Iso.inv_hom_id_app]
    erw [Category.comp_id, ← DerivedCategory.Q.map_comp]
    congr 1
    apply HomologicalComplex.hom_ext
    intro p
    have h := congrArg (fun f ↦ f.f p)
      (limit.isoLimitCone_hom_π
        ⟨HomologicalComplex.coneOfHasLimitEval I.asFunctor,
          HomologicalComplex.isLimitConeOfHasLimitEval I.asFunctor⟩ (op n))
    exact h
  let T := reductionTowerCategory W S
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u + 1} T).obj P
  let q := (CochainComplex.toKInjectiveResolution.{u + 1} T).app P
  have hq : QuasiIso q :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1} T P).2
  have hI : QuasiIso (roosι I) := hι I (fun _ ↦ inferInstance)
  have heI : e.hom.app I ≫
      (completedRlimProjection W R n).app (DerivedCategory.Q.obj I) ≫
        ((evaluation ℕᵒᵖ (reductionModules W R)).obj
          (op n)).mapDerivedCategoryFactors.hom.app I =
      DerivedCategory.Q.map (roosEval I n) := by
    apply (cancel_epi (DerivedCategory.Q.map (roosι I))).1
    rw [← Category.assoc, heunit]
    rw [hunit, ← DerivedCategory.Q.map_comp, roosι_eval]
  let qn := (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n)
  have : QuasiIso qn := (HomologicalComplex.quasiIso_iff_evaluation q).1 hq (op n)
  apply (cancel_mono (DerivedCategory.Q.map qn)).1
  have hnat := e.hom.naturality q
  have hπ := (completedRlimProjection W R n).naturality (DerivedCategory.Q.map q)
  have heval := ((evaluation ℕᵒᵖ (reductionModules W R)).obj
    (op n)).mapDerivedCategoryFactors.hom.naturality q
  dsimp only [Functor.comp_map] at hnat hπ heval
  calc
    _ = e.hom.app P ≫ (completedRlim W R).map (DerivedCategory.Q.map q) ≫
        (completedRlimProjection W R n).app (DerivedCategory.Q.obj I) ≫
        ((evaluation ℕᵒᵖ (reductionModules W R)).obj
          (op n)).mapDerivedCategoryFactors.hom.app I := by
      have heval' :
          (reductionTowerDerivedEvaluation W S n).map (DerivedCategory.Q.map q) ≫
              ((evaluation ℕᵒᵖ (reductionModules W R)).obj
                (op n)).mapDerivedCategoryFactors.hom.app I =
            ((evaluation ℕᵒᵖ (reductionModules W R)).obj
                (op n)).mapDerivedCategoryFactors.hom.app P ≫
              DerivedCategory.Q.map qn := heval
      simp only [Category.assoc]
      rw [← heval', ← reassoc_of% hπ]
    _ = DerivedCategory.Q.map (roosF.map q) ≫
        DerivedCategory.Q.map (roosEval I n) := by
      simp only [Functor.id_obj] at hnat
      dsimp only [I] at *
      erw [← Category.assoc, ← hnat, Category.assoc, heI]
    _ = _ := by
      simp only [Functor.id_obj] at *
      rw [← DerivedCategory.Q.map_comp, roosEval_natural, DerivedCategory.Q.map_comp]


end CategoryTheory
