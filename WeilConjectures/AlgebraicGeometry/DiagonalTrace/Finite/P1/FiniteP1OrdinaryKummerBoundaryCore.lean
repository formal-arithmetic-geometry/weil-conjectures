/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.FiniteKummerBoundaryEquation
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1KummerCoordinates
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Ordinary.FiniteOrdinaryBoundaryOfScalarClass
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1OrdinaryCoordinatePullback
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteChernPullback
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteCoefficientRecords
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SmoothPurity.Ringed.RingedTopoiDerivedTensorPullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.AlgebraicGeometry.FiniteP1ChernMapBaseChange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj
import WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
import WeilConjectures.CategoryTheory.DerivedSingleUnitExact
import WeilConjectures.CategoryTheory.DerivedSingleUnit
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction

/-! # The finite ordinary Kummer boundary from the scalar class

Source: diagonal-tower trace (1), the finite positive Kummer class and its site comparison.
(blueprint: lem-sfb-finite-p1-ordinary-kummer-boundary-core).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/--
The normalized scalar Kummer class of the ordinary projective-line Chern arrow
implies the finite intrinsic boundary equation for the explicitly normalized
coefficient coordinates.  The scalar-class hypothesis is the independent
ordinary etale step; the conclusion is the finite site-comparison step.

Source: diagonal-tower trace (1), comparison with the scalar Kummer class;
Stacks 03PL and 03FD.  The proof transports the class through exact evaluation,
coefficient-coordinate, and scalar-forgetting comparisons.  The normalized
section equations identify the integral and root endpoint maps with
`finiteQuotient` and `finiteRootMap`; naturality of the single and shifted
connecting morphisms then gives the boundary equation.  No tower Chern arrow or
normalization hypothesis occurs in the conclusion.
(blueprint: lem-sfb-finite-p1-ordinary-kummer-boundary-core).
-/
theorem finiteP1_ordinary_kummer_boundary_of_class
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (e : X ≅ ProjectiveLine S) (k : Kummer l X)
    (hS : IsUnit (l : Γ(S, ⊤))) (n : ℕ)
    [Finite (SpTowerShriek.R l E n)]
    {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX)
    (hclass : Etale.ordinaryFiniteP1ChernSpec (FiniteRing l E n) (l ^ (n + 1))
      (ULift.ext _ _ (coefficient_annihilates l E n)) S
      (finiteP1_unitOnPullback (l ^ (n + 1)) (ProjectiveLine S ↘ S)
        (by simpa only [Nat.cast_pow] using hS.pow (n + 1)))
      (geoP1EtaleChern (FiniteRing l E n) (l ^ (n + 1))
        (pow_pos (Fact.out : l.Prime).pos _)
        (ULift.ext _ _ (coefficient_annihilates l E n)) S
        (by simpa only [Nat.cast_pow] using hS.pow (n + 1)))) :
    FiniteKummerBoundary l E X n k
      (Scheme.Pic.mapHom e.hom (hyperplanePic S))
      (finiteP1OrdinaryKummerArrow l E n e hS c) := by
  let A := FiniteRing l E n
  let N := l ^ (n + 1)
  let hA : (N : A) = 0 := ULift.ext _ _ (coefficient_annihilates l E n)
  let hP := finiteP1_unitOnPullback N (ProjectiveLine S ↘ S)
    (by simpa only [N, Nat.cast_pow] using hS.pow (n + 1))
  let a := geoP1EtaleChern A N (pow_pos (Fact.out : l.Prime).pos _) hA S
    (by simpa only [N, Nat.cast_pow] using hS.pow (n + 1))
  let t := Etale.projectiveLineTraceTransport N (pow_pos (Fact.out : l.Prime).pos _) A hA
  have hp := Etale.ordinaryFiniteChern_pullback A N hA t e.hom hP hX
    (Etale.ordinaryFiniteP1PicardClass S) a
    ((Etale.ordinaryFiniteP1ChernSpec_iff A N hA S hP a).mp hclass)
  have hb := finiteOrdinary_boundary_of_scalar_class l E X k n c
    (Scheme.Pic.mapHom e.hom (hyperplanePic S))
    (Etale.ordinaryFiniteLinePullbackMap A N hA t e.hom hP a) hp
  have he := eq_of_heq (finiteP1_ordinary_coordinate_pullback l E n e hS c a)
  rw [← he] at hb
  exact hb

end AlgebraicGeometry.ProEtale.DiagonalTrace
