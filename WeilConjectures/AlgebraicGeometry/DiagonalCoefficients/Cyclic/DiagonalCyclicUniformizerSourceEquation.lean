/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalCoefficientRouteSquare
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalSourceEndpointTransposeSquare

/-! # The source equation for an existing normalized restriction comparison
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Use the module-sheaf abelian structure of GeoCartierClass.
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian

-- Keep the coefficient category choices of the existing criterion in the signature.
-- This emits its ordinary endpoint equality, not an additional predicate.
local elab "sourceEquation% " f:term:max s:term:max : term => do
  let ef ← Lean.Elab.Term.elabTerm f none
  let es ← Lean.Elab.Term.elabTerm s none
  let .forallE _ domain _ _ ← Lean.Meta.whnf (← Lean.Meta.inferType ef)
    | throwError "criterion has no source hypothesis"
  let pred := domain.getAppArgs.back!
  let conjunction ← Lean.Meta.whnf (Lean.mkApp pred es)
  unless conjunction.isAppOf ``And do
    throwError "criterion source is not a conjunction"
  return conjunction.getAppArgs.back!

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] derivedScalars quotientLine quotientLineMap cyclicLine cyclicLineMap
  Functor.leftDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction
  HasDerivedCategory.standard DerivedCategory.singleFunctors HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ
  Functor.mapDerivedCategory Functor.mapDerivedCategorySingleFunctor
  CondensedRing.lowerStar Profinite.continuousMapRingSheaf
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.ofIsGrothendieckAbelian

attribute [local instance] UniformizerSquareData.inverse_additive
  comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local semireducible] UniformizerSquareData.sourceEndpointLeft
  UniformizerSquareData.sourceEndpointRight

/-- The mate of a normalized ordinary restriction comparison has the prescribed
supported constant endpoint. This lemma assumes the comparison and does not assert
its existence or uniqueness. -/
theorem diagonalCyclic_uniformizerSource_equation
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (A : Type (u + 1)) [CommRing A]
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (q : UniformizerSquareData l Y E π n A hA)
    (s : q.quotientRight ≅ q.restriction ⋙ q.cyclicRight)
    (hs : q.RestrictionNormalized s) :
    sourceEquation% (UniformizerSquareData.endpointSquare l Y E π n A hA q) s  := by
  change q.sourceEndpointLeft s = q.sourceEndpointRight s
  exact (q.cyclicAdjunction.homEquiv _ _).injective (q.source_endpoint_transpose_square s hs)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
