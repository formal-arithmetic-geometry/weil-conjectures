/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
public import WeilConjectures.ZetaWeil.OrdinaryCompactCohomology
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Clopen.FiniteClopenDerivedDecomposition
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ConstructibleExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.Sf.SfOpenExceptionalBaseChange
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Clopen.FiniteClopenConstructibilityBounds
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Pi.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteClopenTensor.ProEtaleFiniteClopenTensorCalculus
public import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicDerivedOpenAdjunction
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import WeilConjectures.ZetaWeil.FrobeniusPointTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek

public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedExchange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenBaseChangeArbitrary

/-!
# Proper condensed exchange and Frobenius

Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/
sk-thm-dl-a1-upper/lem-a1-finite-boundary-weights.proof.md, opening evaluation sentence;
the proper compact-to-ordinary normalization of
`prop-weil-proper-compact-coincidence` (blueprint: lem-a1-condensed-proper-exchange-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.Functor
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The proper comparison attached to the identity compactification.
Source: the identity compactification paragraph of
`prop-weil-proper-compact-coincidence.proof.md`
(blueprint: lem-a1-condensed-proper-exchange-comparison).
This is the canonical identity-open comparison followed by the
proper direct image, with the displayed left-unitor normalization. -/
noncomputable def properIdentityComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] :
    rightDerivedLowerShriekOfCompactification Λ (Compactification.ofIsProper f) ≅
      (lowerStar Λ f).rightDerivedFunctor :=
  Functor.isoWhiskerRight (derivedOpenImmersionLowerShriekId Λ X)
      (lowerStar Λ f).rightDerivedFunctor ≪≫ Functor.leftUnitor _

/-- Identity compactifications on both sides of the specified scheme square.
Source: proper identity compactification in the node's proof, step 1
(blueprint: lem-a1-condensed-proper-exchange-comparison). -/
def properIdentityCompactificationSquare {X S : Scheme.{u}} {a : X ⟶ S}
    [IsProper a] {g : X ⟶ X} {h : S ⟶ S} (sq : CommSq g a a h) :
    CompactificationReindexing.Square
      (Compactification.ofIsProper a) (Compactification.ofIsProper a) g h where
  middle := g
  openSquare := IsPullback.id_vert g
  properSquare := sq

end AlgebraicGeometry.ProEtale.CondensedRing
