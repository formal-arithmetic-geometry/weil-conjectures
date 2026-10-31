/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeKummerStrictLocalInvariance
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
public import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedTensorPullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteChernPullback
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteCoefficientRecords
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import WeilConjectures.AlgebraicGeometry.FiniteP1ChernMapBaseChange
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj
public import WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerSystemSupplement
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
public import WeilConjectures.CategoryTheory.DerivedSingleUnitExact
public import WeilConjectures.CategoryTheory.DerivedSingleUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
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

/-- The unique module-derived arrow `A_T[0] → L_T[1]` whose ordinary class is the
scalar Kummer class `κ_{T,A}(w)` (ordinary Kummer boundary of the unit `w`, followed by
`z ↦ z ⊗ 1`): the inverse of the arbitrary-base ordinary class bijection applied to it.
Source: blueprint prop-pur-gm-relative-kummer.proof.md, Step 2 (normalized constant and
coordinate classes); Stacks Tag 03PL
(blueprint: def-pur-normalized-kummer-cohomology-arrows). -/
@[irreducible]
def normalizedKummerDerivedClass (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤)))
    (w : Γ(T, ⊤)ˣ) :
    (DerivedCategory.singleFunctor _ 0).obj (kummerExchangeConstant A T) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateLine T m A hA))⟦(1 : ℤ)⟧ :=
  (ordinaryFiniteClassEquiv A T (Scheme.finiteEtaleTateLine T m A hA) 1).symm
    (relativeKummerClass A m hA T hT w)

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
