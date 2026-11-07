/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.SemilinearGeometryDerived
public import Submission.WeilConjectures.AlgebraicGeometry.SemilinearGeometryCore
public import Submission.WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import Submission.WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import Submission.WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Submission.WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Hom
public import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Submission.WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.HomComplex
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Submission.WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Submission.WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Submission.WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.HomComplexProjections
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Submission.WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Submission.WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import Submission.WeilConjectures.Algebra.Homology.HomComplexComponents
public import Submission.WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import Submission.WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Canonical coefficient mates and tensor projection maps

Source: Zheng Lemma 4.10; Stacks 07A4
(blueprint: def-coef-semilinear-geometry-ops).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r c₂ v₂ k

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [ambientSmall : EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

variable (A : Data.{c, v, r} J B τ)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)

namespace Geometry

variable (G : Geometry.{c, v, r} J B τ A J' uInv uPush adjSet)

/-- The coefficient projection arrow b is exactly the dependency's adjunction mate.
Source: Zheng 4.10; Stacks 07A4
(blueprint: def-coef-semilinear-geometry-ops). -/
def coefficientMate {m n : ℕ} (h : n ≤ m) :
    (G.levelPush m).rightDerivedFunctor ⋙ (A.scalar h).T ⟶
      (G.target.scalar h).T ⋙ (G.levelPush n).rightDerivedFunctor :=
  (mateEquiv (G.derivedLevelAdjunction m) (G.derivedLevelAdjunction n)
    (TwoSquare.mk _ _ _ _ (G.coefficientPullback h).hom)).natTrans

/-- The exact extension-form transition formula for GN.
Source: Zheng 4.10 (blueprint: def-coef-semilinear-geometry-ops). -/
def TransitionFormula : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m)
    (N : DS.{c, v, max c v r} J' G.coefficients G.coefficientTransition),
    reduction.{c, v, max c v r} J B τ h (A.scalar h) (G.push.rightDerivedFunctor.obj N) ≫
        (G.pushEvaluation n).hom.app N =
      (A.scalar h).T.map ((G.pushEvaluation m).hom.app N) ≫
        (G.coefficientMate J B τ A J' uInv uPush adjSet h).app
          ((e.{c, v, max c v r} J' G.coefficients G.coefficientTransition m).obj N) ≫
        (G.levelPush n).rightDerivedFunctor.map
          (reduction.{c, v, max c v r} J' G.coefficients G.coefficientTransition h
            (G.target.scalar h) N)

/-- The general tensor projection arrow is the indicated counit transpose.
Source: Stacks 07A4 (blueprint: def-coef-semilinear-geometry-ops). -/
def tensorProjection (N : DS.{c, v, max c v r} J' G.coefficients G.coefficientTransition)
    (P : DS.{c, v, max c v r} J B τ) :
    A.closed.tensor.obj (G.push.rightDerivedFunctor.obj N, P) ⟶
      G.push.rightDerivedFunctor.obj
        (G.target.closed.tensor.obj (N, G.pull.mapDerivedCategory.obj P)) :=
  (G.adjunction.homEquiv _ _)
    ((G.tensorPullback).hom.app (G.push.rightDerivedFunctor.obj N, P) ≫
      G.target.closed.tensor.map (Prod.mkHom (G.adjunction.counit.app N) (𝟙 _)))

/-- The pullback reduction equation uses the inverse of the same tensor comparison.
Source: Zheng 4.1 (blueprint: def-coef-semilinear-geometry-ops). -/
def PullTransitionFormula : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m) (M : DS.{c, v, max c v r} J B τ),
    reduction.{c, v, max c v r} J' G.coefficients G.coefficientTransition h
        (G.target.scalar h) (G.pull.mapDerivedCategory.obj M) ≫
        (G.pullEvaluation n).hom.app M =
      (G.target.scalar h).T.map ((G.pullEvaluation m).hom.app M) ≫
        (G.coefficientPullback h).inv.app ((e.{c, v, max c v r} J B τ m).obj M) ≫
        (derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (G.coefficients n) (G.inverseImage n).modules).map
            (reduction.{c, v, max c v r} J B τ h (A.scalar h) M)

/-- The levelwise tensor projection is the ordinary counit transpose.
Source: Stacks 07A4 (blueprint: def-coef-semilinear-geometry-ops). -/
def levelTensorProjection (n : ℕ) (N : D.{c, v, max c v r} J' (G.coefficients n))
    (P : D.{c, v, max c v r} J (B n)) :
    (A.levelClosed n).tensor.obj ((G.levelPush n).rightDerivedFunctor.obj N, P) ⟶
      (G.levelPush n).rightDerivedFunctor.obj
        ((G.target.levelClosed n).tensor.obj
          (N, (derivedExact.{c, v, max c v r, c, v} J J' (B n)
            (G.coefficients n) (G.inverseImage n).modules).obj P)) :=
  ((G.derivedLevelAdjunction n).homEquiv _ _)
    ((G.levelTensorPullback n).hom.app ((G.levelPush n).rightDerivedFunctor.obj N, P) ≫
      (G.target.levelClosed n).tensor.map
        (Prod.mkHom ((G.derivedLevelAdjunction n).counit.app N) (𝟙 _)))

/-- Evaluation of the constructed system projection is the level projection word.
Source: Stacks 07A4 (blueprint: def-coef-semilinear-geometry-ops). -/
def ProjectionEvaluation : Prop :=
  ∀ (n : ℕ) (N : DS.{c, v, max c v r} J' G.coefficients G.coefficientTransition)
    (P : DS.{c, v, max c v r} J B τ),
    (e.{c, v, max c v r} J B τ n).map
        (G.tensorProjection J B τ A J' uInv uPush adjSet N P) ≫
        (G.pushEvaluation n).hom.app
          (G.target.closed.tensor.obj (N, G.pull.mapDerivedCategory.obj P)) ≫
        (G.levelPush n).rightDerivedFunctor.map
          ((G.target.tensorEvaluation n).hom.app (N, G.pull.mapDerivedCategory.obj P) ≫
            (G.target.levelClosed n).tensor.map
              (Prod.mkHom (𝟙 _) ((G.pullEvaluation n).hom.app P))) =
      (A.tensorEvaluation n).hom.app (G.push.rightDerivedFunctor.obj N, P) ≫
        (A.levelClosed n).tensor.map
          (Prod.mkHom ((G.pushEvaluation n).hom.app N) (𝟙 _)) ≫
        G.levelTensorProjection J B τ A J' uInv uPush adjSet n
          ((e.{c, v, max c v r} J' G.coefficients G.coefficientTransition n).obj N)
          ((e.{c, v, max c v r} J B τ n).obj P)

end Geometry
end WeilConjectures.SemilinearSections
