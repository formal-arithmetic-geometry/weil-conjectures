/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.SixFunctors.Open.OpenQuotientKoszulModels
public import Submission.WeilConjectures.SixFunctors.Open.OpenDvrLimitComparison
import Submission.WeilConjectures.SixFunctors.Open.OpenDvrStrictReductionComparison
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
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import all Mathlib.CategoryTheory.Limits.HasLimits

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
/-! # Reduction and augmentation under canonical DVR coefficients

Source: Stacks Tags 0941, 099B and 0A0E; canonical coefficient transport.
(blueprint: lem-sf-open-dvr-augmented-reduction-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The reduction-only part of the augmented comparison, relative to the separately
constructed normalized limit comparison. Source: Stacks 07A6, 0D6E and 0941
(blueprint: lem-sf-open-dvr-augmented-reduction-comparison). -/
structure OpenDvrAugmentedReductionComparison
    {d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)} {T : Scheme.{u}}
    (C : OpenDvrCoefficientModel l E d T) (S : CoefficientDerivedSystemCalculus.{u, u} l E T)
    (M : OpenDvrLimitComparison l E C) where
  /-- The two quotient tower functors are canonically identified. -/
  tower : C.derived.functor ⋙ completedAdicReduction T d ≅
    S.reduction ⋙ coefficientSequenceDerivedRestriction.{u, u} l E T ⋙ C.towers
  /-- The same strict tensor augmentation, before taking total derived inverse limit. -/
  representative : ∀ (Q : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ)
      (_hQ : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (J := ProEt.topology T) (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T) Q),
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology T) (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T)
      (Q.X i)) →
    ∃ (B : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ℤ)
      (a : ((Functor.const ℕᵒᵖ : scalarReductionSource.{u, u} l E T ⥤ _).mapHomologicalComplex
        (.up ℤ)).obj Q ⟶ B)
      (κ : HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj B ≅
        unrestrictedIntegralComplexTower.{u, u} l E T Q)
      (e : (S.reduction ⋙ coefficientSequenceDerivedRestriction.{u, u} l E T).obj
        (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj B)
      (τ : ((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).obj
          (C.complexes.obj Q) ≅ C.towerComplexes.obj B),
      (∀ (i : ℤ) (n : ℕ),
        (reconstructionOrdinaryUnit T d).app (C.modules.functor.obj (Q.X i)) ≫
            limit.π ((completedAdicOrdinaryTower T d).obj
              (C.modules.functor.obj (Q.X i))) (op n) ≫ (τ.hom.f i).app (op n) =
          C.modules.functor.map ((a.f i).app (op n))) ∧
      ((completedAdicReduction T d).map
          (C.modules.functor.mapDerivedCategoryFactors.hom.app Q) ≫
          reconstructionReductionComplexCounit T d (C.complexes.obj Q) ≫
          DerivedCategory.Q.map τ.hom =
        tower.hom.app (DerivedCategory.Q.obj Q) ≫ C.towers.map e.hom ≫
          C.ordinaryTowers.mapDerivedCategoryFactors.hom.app B) ∧
      (∀ n : ℕ, HEq
        ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map a).app (op n) ≫
          κ.hom.app (op n)) (unrestrictedTowerUnit.{u, u} l E T Q n)) ∧
      (C.derived.functor.map (S.adjunction.unit.app (DerivedCategory.Q.obj Q)) ≫
          C.derived.functor.map ((coefficientConstantTowerLimit.{u, u} l E T).map e.hom) =
        C.derived.functor.map (DerivedCategory.Q.map
          (((constLimAdj : (Functor.const ℕᵒᵖ : scalarReductionSource.{u, u} l E T ⥤ _) ⊣
              lim).mapHomologicalComplex (.up ℤ)).unit.app Q ≫
              ((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
                (.up ℤ)).map a) ≫
          derivedLimitComplexComparison
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _)
            (coefficientConstantTowerLimit.{u, u} l E T)
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctorUnit B))
  /-- The quotient completion unit is the actual semilinear reduction/limit unit. -/
  unit : ∀ P : DerivedCategory (scalarReductionSource.{u, u} l E T),
    (reconstructionCompletionUnit T d).app (C.derived.functor.obj P) ≫
        (reconstructionRlim T d).map (tower.hom.app P) ≫
          M.rlim.hom.app ((coefficientSequenceDerivedRestriction.{u, u} l E T).obj
            (S.reduction.obj P)) =
      C.derived.functor.map (S.adjunction.unit.app P)
end WeilConjectures
