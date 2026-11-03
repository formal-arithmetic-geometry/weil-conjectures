/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CohomologyPullbackCanonicalArrows
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.KummerLine.KummerLineGeometry
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.KummerNaturality
public import WeilConjectures.CategoryTheory.LeftModuleDerivedEvaluation.LeftModuleDerivedEvaluationForget
public import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.AlgebraicGeometry.Exchange.ExchangeForgetCoefficients
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.StrictlyHenselianUnit
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.ClosedOpen
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.PointUnit

/-! # Normalized Kummer cohomology arrows

This module records the canonical module-derived realization of the scalar Kummer
class and its image in derived global sections.  The realization is obtained by
applying the inverse of the arbitrary-base ordinary finite-class bijection, so
its data is canonical.  The global arrow is the derived constant-sheaf/sections
adjoint transpose.  Source: blueprint latest, sk-prop-a1-kummer,
prop-pur-gm-relative-kummer.proof.md, Step 2; Stacks Tags 03PL and 01EZ
(blueprint: def-pur-normalized-kummer-cohomology-arrows).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

/-- The derived global realization `A[0] → RΓ(T, F)[q]` of a map `A_T[0] → F[0][q]`:
the exact-constant single comparison, the derived constant-sheaf/sections adjunction
and the derived-sections shift comparison.
Source: blueprint prop-pur-gm-relative-kummer.proof.md, Step 2 (global edge sections);
Stacks Tags 01EZ and 072W
(blueprint: def-pur-normalized-kummer-cohomology-arrows). -/
@[irreducible]
def normalizedKummerClassToGlobal (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ)
    (x : (DerivedCategory.singleFunctor _ 0).obj (kummerExchangeConstant A T) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧) :
    (DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of A A) ⟶
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} A) T).obj
        ((DerivedCategory.singleFunctor _ 0).obj F))⟦(q : ℤ)⟧ := by
  let adj := (constantSheafΓAdj T.smallEtaleTopology
    (ModuleCat.{u + 1} A)).mapDerivedCategoryRightDerivedAdjunction
  let y := adj.homEquiv
      ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of A A))
      (((DerivedCategory.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧)
      (((constantSheaf T.smallEtaleTopology
        (ModuleCat.{u + 1} A)).mapDerivedCategorySingleFunctor 0).hom.app
          (ModuleCat.of A A) ≫ x)
  exact y ≫
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} A) T).commShiftIso (q : ℤ)).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj F)
end AlgebraicGeometry.Etale
