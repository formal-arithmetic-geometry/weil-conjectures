/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenTensorQuotientAugmentation
public import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorTensorModel
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
public import WeilConjectures.CategoryTheory.StrictRoosComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.StrictRoosDerivation
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.RoosComplex
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.R.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.StrictRoosNormalization
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.Logic.Denumerable
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosDescent
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosCompatibility
public import WeilConjectures.SixFunctors.Constructible.ConstructibleTensorCompletion
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SixFunctors.LocalizedModuleExactIndependent
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerCanonical
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.SixFunctors.SfOpenRoos.SfOpenRoosExtensionComparison

/-! # The open tensor augmentation limit square

Source: Bhatt--Scholze, Lemmas 6.5.5 and 6.5.8(2),(3), pp.49--50;
Stacks 0940, normalized augmented strict Roos calculation
(blueprint: lem-sf-open-tensor-augmentation-limit-square).

The index n denotes the positive exponent n+1. All maps are localized maps of
unbounded complexes. The supplied lambda is pinned on both signed Roos coordinates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenTensorAugmentation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : IntegralOpenReduction.Operations l E j)
  (SX : CoefficientDerivedSystemCalculus l E X)
  (SU : CoefficientDerivedSystemCalculus l E U)
  (AX : OpenSemilinearTensor.OrdinaryReduction l E X)
  (AU : OpenSemilinearTensor.OrdinaryReduction l E U)
  (st : IntegralOpenReduction.TensorComparison l E j o)
  (m : OpenSemilinearTensor.Comparison l E j o SX SU AX AU st)
  (c : IntegralOpenReduction.Comparison l E j o SX SU st)
  (q : OpenTensorQuotient.Comparison l E j o SX SU AX AU st m c)

attribute [local irreducible] integralOperationsTensorTowerFunctor
  coefficientTotalTensor integralOperationsTensorLevel
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  unrestrictedIntegralComplexFunctor scalarReductionExistence unrestrictedIntegralReductionExistence

set_option maxHeartbeats 800000 in
-- The representative identities elaborate several independent tensor and Roos presentations.
/-- The quotient tensor augmentations are invertible and their actual maps satisfy
 the signed Roos limit square. The first two equalities identify them with the
 recorded chi maps through the defining completed-tensor identifications.

Source: Bhatt--Scholze 6.5.5, 6.5.8(2),(3), pp.49--50; Stacks 0940
(blueprint: lem-sf-open-tensor-augmentation-limit-square).

Proof:
1. Finite type over k makes X and U qcqs, and l is invertible. The quotient-square
 theorem preserves constructibility under open extension and restriction, so both
 input pairs satisfy lem-fix-constructible-tensor-completion.
2. Apply that theorem to both pairs. Its chain augmentation has precisely the
 quotient maps in its first coordinates and zero shifted coordinate. The two
 RoosNormalization hypotheses identify these with the specified strict
 augmentations. Tensor.canonical identifies their localizations with chi under
 the defining completed-tensor comparisons. Both localized maps are invertible.
3. Apply the Roos functor to the strict square z.square. Its action is the product
 of gamma on each signed summand. The first coordinates of the two routes agree
 by z.lowerRouteFormula; the shifted coordinates are zero. Thus the chain maps
 agree, with every quotient transition retained in the boundary 1-s.
4. The first and shifted normalization equations for lambda identify the lower
 route with extension of the lower augmentation followed by lambda. Localize
 this equality to obtain the displayed equality of actual derived morphisms.
 No finite-Tor hypothesis over any A_n is used. -/
theorem openTensorAugmentationLimitSquare
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    [U.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [j.IsOver (Spec (.of D.k))]
    (Q : CochainComplex (scalarReductionSource l E U) ℤ)
    (F : CochainComplex (scalarReductionSource l E X) ℤ)
    (hQ : integralOperationsGoodComplex l E U Q)
    (hF : integralOperationsGoodComplex l E X F)
    (hQX : integralOperationsGoodComplex l E X
      ((OpenSemilinearTensor.extensionComplex l E j o).obj Q))
    (hFU : integralOperationsGoodComplex l E U
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj F))
    (_hK : sfIntegralConstructible l E U (DerivedCategory.Q.obj Q))
    (_hP : sfIntegralConstructible l E X (DerivedCategory.Q.obj F))
    (z : OpenTensorQuotient.StrictSquare l E j o m.totalComparison q.scalar st
      q.strictScalar Q F)
    (_nX : OpenTensorQuotient.RoosNormalization l E X q.tensorX
      ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) F z.upper)
    (_nU : OpenTensorQuotient.RoosNormalization l E U q.tensorU Q
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj F) z.lower)
    (lambda : integralOperationsRoosFunctor ⋙ OpenSemilinearTensor.extensionComplex l E j o ≅
      OpenTensorQuotient.extendTower l E j o ⋙ integralOperationsRoosFunctor)
    (_first : ∀ T : OpenTensorQuotient.Towers l E U,
      lambda.hom.app T ≫ CochainComplex.mappingCocone.fst
          (towerTransitionEndomorphism (K := fun n ↦
            ((OpenTensorQuotient.extendTower l E j o).obj T).obj (op n))
            (integralOperationsTowerStep ((OpenTensorQuotient.extendTower l E j o).obj T))) =
        (OpenSemilinearTensor.extensionComplex l E j o).map
          (CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism (K := fun n ↦ T.obj (op n))
              (integralOperationsTowerStep T))) ≫
          piComparison (OpenSemilinearTensor.extensionComplex l E j o)
            (fun n ↦ T.obj (op n)))
    (_shifted : ∀ (T : OpenTensorQuotient.Towers l E U) (i k : ℤ) (h : i + -1 = k),
      (lambda.hom.app T).f i ≫ (CochainComplex.mappingCocone.snd
        (towerTransitionEndomorphism (K := fun n ↦
          ((OpenTensorQuotient.extendTower l E j o).obj T).obj (op n))
          (integralOperationsTowerStep ((OpenTensorQuotient.extendTower l E j o).obj T)))).v
            i k h =
      (IntegralOpenReduction.extension l E j o).map
        ((CochainComplex.mappingCocone.snd
          (towerTransitionEndomorphism (K := fun n ↦ T.obj (op n))
            (integralOperationsTowerStep T))).v i k h) ≫
        (piComparison (OpenSemilinearTensor.extensionComplex l E j o)
          (fun n ↦ T.obj (op n))).f k) :
    ∃ (bT : (OpenSemilinearTensor.total l E X).obj
        ((OpenSemilinearTensor.extensionComplex l E j o).obj Q, F) ⟶
        integralOperationsRoos ((integralOperationsTensorTowerFunctor l E X).obj
          ((OpenSemilinearTensor.extensionComplex l E j o).obj Q, F)))
      (bS : (OpenSemilinearTensor.total l E U).obj
        (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F) ⟶
        integralOperationsRoos ((integralOperationsTensorTowerFunctor l E U).obj
          (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F))),
    (∀ n : ℕ, bT ≫ CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism
        (K := fun n ↦ ((integralOperationsTensorTowerFunctor l E X).obj
          ((OpenSemilinearTensor.extensionComplex l E j o).obj Q, F)).obj (op n))
        (integralOperationsTowerStep ((integralOperationsTensorTowerFunctor l E X).obj
          ((OpenSemilinearTensor.extensionComplex l E j o).obj Q, F)))) ≫
        Pi.π (fun k ↦ ((integralOperationsTensorTowerFunctor l E X).obj
          ((OpenSemilinearTensor.extensionComplex l E j o).obj Q, F)).obj (op k)) n =
      z.upper.map.app (op n)) ∧
    (∀ (i k : ℤ) (h : i + -1 = k), bT.f i ≫
      (CochainComplex.mappingCocone.snd
      (towerTransitionEndomorphism
        (K := fun n ↦ ((integralOperationsTensorTowerFunctor l E X).obj
          ((OpenSemilinearTensor.extensionComplex l E j o).obj Q, F)).obj (op n))
        (integralOperationsTowerStep ((integralOperationsTensorTowerFunctor l E X).obj
          ((OpenSemilinearTensor.extensionComplex l E j o).obj Q, F))))).v i k h = 0) ∧
    (∀ n : ℕ, bS ≫ CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism
        (K := fun n ↦ ((integralOperationsTensorTowerFunctor l E U).obj
          (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F)).obj (op n))
        (integralOperationsTowerStep ((integralOperationsTensorTowerFunctor l E U).obj
          (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F)))) ≫
        Pi.π (fun k ↦ ((integralOperationsTensorTowerFunctor l E U).obj
          (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F)).obj (op k)) n =
      z.lower.map.app (op n)) ∧
    (∀ (i k : ℤ) (h : i + -1 = k), bS.f i ≫
      (CochainComplex.mappingCocone.snd
      (towerTransitionEndomorphism
        (K := fun n ↦ ((integralOperationsTensorTowerFunctor l E U).obj
          (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F)).obj (op n))
        (integralOperationsTowerStep ((integralOperationsTensorTowerFunctor l E U).obj
          (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F))))).v i k h = 0) ∧
    IsIso (DerivedCategory.Q.map bT) ∧ IsIso (DerivedCategory.Q.map bS) ∧
    (∃ (compareX : (constructibleTensorTotal l E X).obj
          ((OpenSemilinearTensor.extensionComplex l E j o).obj Q, F) ≅
        (OpenSemilinearTensor.total l E X).obj
          ((OpenSemilinearTensor.extensionComplex l E j o).obj Q, F))
       (compareU : (constructibleTensorTotal l E U).obj
          (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F) ≅
        (OpenSemilinearTensor.total l E U).obj
          (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F))
       (flatQX : proEtaleFlatRepresentatives X
          (completedIntegralCommRingSheafUnrestricted l E X)
          ((OpenSemilinearTensor.extensionComplex l E j o).obj Q))
       (flatF : proEtaleFlatRepresentatives X
          (completedIntegralCommRingSheafUnrestricted l E X) F)
       (flatQ : proEtaleFlatRepresentatives U
          (completedIntegralCommRingSheafUnrestricted l E U) Q)
       (flatFU : proEtaleFlatRepresentatives U
          (completedIntegralCommRingSheafUnrestricted l E U)
          ((OpenSemilinearTensor.restrictionComplex l E j o).obj F)),
      (∀ (p r : ℤ) (V : X.ProEtᵒᵖ)
        (x : (((OpenSemilinearTensor.extensionComplex l E j o).obj Q).X p).val.obj V)
        (y : (F.X r).val.obj V),
        (compareX.hom.f (p + r)).val.app V
          (constructibleTensorTotalSection l E X
            ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) F p r V x y) =
          OpenTensorQuotient.totalSection l E X
            ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) F p r V x y) ∧
      (∀ (p r : ℤ) (V : U.ProEtᵒᵖ) (x : (Q.X p).val.obj V)
        (y : (((OpenSemilinearTensor.restrictionComplex l E j o).obj F).X r).val.obj V),
        (compareU.hom.f (p + r)).val.app V
          (constructibleTensorTotalSection l E U Q
            ((OpenSemilinearTensor.restrictionComplex l E j o).obj F) p r V x y) =
          OpenTensorQuotient.totalSection l E U Q
            ((OpenSemilinearTensor.restrictionComplex l E j o).obj F) p r V x y) ∧
      q.tensorX.ordinary.representative.hom.app
          (⟨(OpenSemilinearTensor.extensionComplex l E j o).obj Q, flatQX⟩, ⟨F, flatF⟩) ≫
        (q.tensorX.chi l E).app
          (DerivedCategory.Q.obj ((OpenSemilinearTensor.extensionComplex l E j o).obj Q),
            DerivedCategory.Q.obj F) ≫
        (integralCompletedTensorComparison l E X).hom.app
          (⟨(OpenSemilinearTensor.extensionComplex l E j o).obj Q, hQX⟩, ⟨F, hF⟩) =
        DerivedCategory.Q.map (compareX.hom ≫ bT) ∧
      q.tensorU.ordinary.representative.hom.app
          (⟨Q, flatQ⟩, ⟨(OpenSemilinearTensor.restrictionComplex l E j o).obj F, flatFU⟩) ≫
        (q.tensorU.chi l E).app
          (DerivedCategory.Q.obj Q,
            DerivedCategory.Q.obj ((OpenSemilinearTensor.restrictionComplex l E j o).obj F)) ≫
        (integralCompletedTensorComparison l E U).hom.app
          (⟨Q, hQ⟩, ⟨(OpenSemilinearTensor.restrictionComplex l E j o).obj F, hFU⟩) =
        DerivedCategory.Q.map (compareU.hom ≫ bS)) ∧
    DerivedCategory.Q.map bT ≫
        DerivedCategory.Q.map (integralOperationsRoosMap z.gamma.hom) =
      DerivedCategory.Q.map (m.totalComparison.chain Q F).hom ≫
        DerivedCategory.Q.map ((OpenSemilinearTensor.extensionComplex l E j o).map bS) ≫
        DerivedCategory.Q.map (lambda.hom.app
          ((integralOperationsTensorTowerFunctor l E U).obj
            (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F))) := by
  sorry

end WeilConjectures.OpenTensorAugmentation
