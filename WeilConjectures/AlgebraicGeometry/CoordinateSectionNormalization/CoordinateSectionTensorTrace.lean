/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.TwistedCoordinateSectionCoprojection
import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import all WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineCounitTensor
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceLinePurity
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteCounitCoefficient
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounit
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
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
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
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
import WeilConjectures.AlgebraicGeometry.EtaleOrderedProjectionComparison
import WeilConjectures.AlgebraicGeometry.EtaleTensorTraceBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.SectionProjectionUnitSupplement
import WeilConjectures.AlgebraicGeometry.EtaleCanonicalTensorComparison
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal

import all WeilConjectures.AlgebraicGeometry.SmoothPurity.ShriekTensorCompositionSupplement
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormulaCoherence

/-! Tensor and adjunction consequences of the coordinate scalar normalization. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxRecDepth 4096
set_option Elab.async false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
-- Match the canonical sheaf structure used by the native derived constructions.
attribute [local instance 1000000] CategoryTheory.sheafIsAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
set_option allowUnsafeReducibility true in
attribute [local reducible] ProEtale.CoordinateLine.right Etale.affineTraceLineLeft
  Etale.ordinaryFiniteTensor Etale.ordinaryFinitePullback Etale.ordinaryFinitePushforward

set_option allowUnsafeReducibility true in
attribute [local reducible] ProEtale.CoordinateLine.right Etale.affineTraceLineLeft
  Etale.ordinaryFiniteTensor Etale.ordinaryFinitePullback Etale.ordinaryFinitePushforward
  Etale.ordinaryFiniteTwistedPullback Etale.derivedTensorRight
  Etale.derivedTensorRightDerivedLowerShriek
  Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
  Etale.derivedTensorRightDerivedLowerStar
  Etale.rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar Etale.rightDerivedLowerShriek
set_option linter.auxLemma false in
attribute [local instance 100000] AlgebraicGeometry.Etale.DerivedCategoryModule._proof_1
  AlgebraicGeometry.Etale.DerivedCategoryModule._proof_2
set_option allowUnsafeReducibility true in
attribute [local reducible] AlgebraicGeometry.Etale.ordinaryFiniteDegreeZero
  AlgebraicGeometry.Etale.ordinaryFiniteConstant AlgebraicGeometry.Etale.ordinaryFiniteUnit
  AlgebraicGeometry.Etale.ordinaryFiniteTwistedPullback AlgebraicGeometry.Etale.derivedTensorRight

attribute [local irreducible] AlgebraicGeometry.Etale.derivedTensor
  AlgebraicGeometry.Etale.derivedTensorSymmetry
  AlgebraicGeometry.Etale.unboundedEtaleLowerShriekCompIso
  AlgebraicGeometry.Etale.projectionMapOfCompactification
  AlgebraicGeometry.Etale.unboundedEtaleLowerShriekId
  AlgebraicGeometry.Etale.leftDerivedUpperStarId
set_option allowUnsafeReducibility true in
attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace
  AlgebraicGeometry.Etale.upperStar AlgebraicGeometry.Etale.lowerStar
  _root_.DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
  AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison
  AlgebraicGeometry.Etale.derivedUpperStarLowerStarAdjunction

set_option allowUnsafeReducibility true in
attribute [local reducible] Functor.comp Functor.id Functor.postcompose₂
  Functor.whiskeringLeft₂ Functor.whiskeringLeft Functor.whiskeringRight

attribute [local irreducible] AlgebraicGeometry.Etale.projectionMap

-- Compare only differing arguments, retaining derived-category constructions folded.
-- This is the ordinary congruence/proof-irrelevance method used by the graph PF proof.

namespace AlgebraicGeometry.Etale
open Lean Elab Tactic Meta
private theorem coordinateTensorProofHEq
    {P Q : Prop} (p : P) (q : Q) (h : P = Q) : HEq p q := by
  cases h
  rfl

private meta partial def coordinateTensorCongrHEq (a b : Expr) : MetaM Expr := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return ← mkHEqRefl a
  if ← isProp (← inferType a) then
    let hp ← coordinateTensorCongrHEq (← inferType a) (← inferType b)
    let e ← mkAppM ``eq_of_heq #[hp]
    return ← mkAppM ``coordinateTensorProofHEq #[a, b, e]
  if a.getAppFn == b.getAppFn && a.getAppArgs.size == b.getAppArgs.size then
    let argsA := a.getAppArgs
    let argsB := b.getAppArgs
    let ct ← mkHCongrWithArity a.getAppFn argsA.size
    let mut ps := #[]
    for i in [:argsA.size] do
      let mut h ← coordinateTensorCongrHEq argsA[i]! argsB[i]!
      if ct.argKinds[i]! == .eq then h ← mkAppM ``eq_of_heq #[h]
      ps := ps ++ #[argsA[i]!, argsB[i]!, h]
    let pf := mkAppN ct.proof ps
    if (← inferType pf).isHEq then return pf
    else return ← mkAppM ``heq_of_eq #[pf]
  unless ← withTransparency .default (isDefEq a b) do
    throwError m!"Different projection expressions: {a} versus {b}; \
      heads {a.getAppFn} versus {b.getAppFn}; \
      right arguments {(b.getAppArgs.map fun x ↦ x.getAppFn)}"
  return ← mkHEqRefl a

private meta def coordinateProjectionHead (e : Expr) : MetaM Expr := do
  let .proj structName idx value := e.getAppFn | return e
  let valueType ← withTransparency .default (whnf (← inferType value))
  let .const actualName _ := valueType.getAppFn |
    throwError "unexpected projection structure type {valueType}"
  unless actualName == structName do
    throwError "projection type did not reduce to {structName}: {valueType}"
  let fields := getStructureFields (← getEnv) structName
  let some fieldName := fields[idx]? | throwError "missing structure projection"
  let fn ← mkAppOptM (structName ++ fieldName)
    ((valueType.getAppArgs.push value).map some)
  instantiateMVars (mkAppN fn e.getAppArgs)

private meta def coordinateProjectionNormalize (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  if let .letE _ _ value body _ := e then return body.instantiate1 value
  if let some n := e.getAppFn.constName? then
    let aliases := [
      "identityShriekFunctor", "identityPullbackFunctor", "identityTensorFunctor",
      "identityShriekUnit", "typed_projection", "typed_compositor", "typed_pullback_compositor",
      "closedNativeF", "closedNativeG", "closedNativeL", "closedNativeTensor",
      "closedNativeTransfer", "closedNativeSymmetry", "closedNativeProjectionP",
      "closedNativeProjectionQ", "cachedClosedTransfer", "canonical_shriek_projection",
      "canonical_star_projection", "sectionNativeS", "sectionNativeP", "sectionNativeL",
      "sectionNativeTensor", "sectionNativeTargetTensor", "sectionNativeSourceTensor",
      "sectionNativeClosedIso", "sectionNativeCompactIso", "sectionNativeComposition",
      "sectionNativeClosedProjection", "sectionNativeCompactProjection", "sectionNativeOrderedS",
      "sectionNativeOrderedP", "chosenClosedComparison", "chosenCompactComparison"]
    if aliases.contains n.getString! then
      if let some e' ← withTransparency .default (unfoldDefinition? e) then
        return ← instantiateMVars e'
  let isField ← match e.getAppFn with
    | .proj .. => pure true
    | .const n _ => do pure (← getProjectionFnInfo? n).isSome
    | _ => pure false
  let e ← if isField then withTransparency .default (whnf e) else pure e
  coordinateProjectionHead e

mutual
private meta partial def coordinateProjectionCached (a b : Expr) :
    StateRefT (Std.HashMap (Expr × Expr) Expr) MetaM Expr := do
  let key := (a.consumeMData, b.consumeMData)
  if let some pf := (← get).get? key then return pf
  let pf ← coordinateProjectionStep a b
  modify (·.insert key pf)
  return pf

private meta partial def coordinateProjectionStep (a b : Expr) :
    StateRefT (Std.HashMap (Expr × Expr) Expr) MetaM Expr := do
  if a.consumeMData == b.consumeMData then return ← mkHEqRefl a
  let an ← coordinateProjectionNormalize a
  if an != a then
    let haType ← mkAppM ``HEq #[a, an]
    let ha ← mkAuxTheorem haType (← mkHEqRefl a)
      (zetaDelta := true) (kind? := `_coordinateReduction)
    let hn ← coordinateProjectionCached an b
    let pf ← mkAppM ``HEq.trans #[ha, hn]
    return ← mkAuxTheorem (← inferType pf) pf
      (zetaDelta := true) (kind? := `_coordinateProjection)
  let bn ← coordinateProjectionNormalize b
  if bn != b then
    let hbType ← mkAppM ``HEq #[b, bn]
    let hb ← mkAuxTheorem hbType (← mkHEqRefl b)
      (zetaDelta := true) (kind? := `_coordinateReduction)
    let hb ← mkAppM ``HEq.symm #[hb]
    let hn ← coordinateProjectionCached a bn
    let pf ← mkAppM ``HEq.trans #[hn, hb]
    return ← mkAuxTheorem (← inferType pf) pf
      (zetaDelta := true) (kind? := `_coordinateProjection)
  if ← isProp (← inferType a) then
    let hp ← coordinateProjectionCached (← inferType a) (← inferType b)
    let e ← mkAppM ``eq_of_heq #[hp]
    let pf ← mkAppM ``coordinateTensorProofHEq #[a, b, e]
    return ← mkAuxTheorem (← inferType pf) pf
      (zetaDelta := true) (kind? := `_coordinateProjection)
  if a.getAppFn == b.getAppFn && a.getAppArgs.size == b.getAppArgs.size then
    let argsA := a.getAppArgs
    let argsB := b.getAppArgs
    let ct ← mkHCongrWithArity a.getAppFn argsA.size
    let mut ps := #[]
    for i in [:argsA.size] do
      let mut h ← coordinateProjectionCached argsA[i]! argsB[i]!
      if ct.argKinds[i]! == .eq then h ← mkAppM ``eq_of_heq #[h]
      ps := ps ++ #[argsA[i]!, argsB[i]!, h]
    let pf := mkAppN ct.proof ps
    let pf ← if (← inferType pf).isHEq then pure pf else mkAppM ``heq_of_eq #[pf]
    return ← mkAuxTheorem (← inferType pf) pf
      (zetaDelta := true) (kind? := `_coordinateProjection)
  unless ← withTransparency .default (isDefEq a b) do
    throwError m!"Different projection expressions: {a} versus {b}; \
      heads {a.getAppFn} versus {b.getAppFn}; \
      right arguments {(b.getAppArgs.map fun x ↦ x.getAppFn)}"
  return ← mkHEqRefl a

end

private meta def coordinateProjectionCongrHEq (a b : Expr) : MetaM Expr :=
  (coordinateProjectionCached a b).run' {}

private meta def coordinateNativeAliasNormalize (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  if let .letE _ _ value body _ := e then return body.instantiate1 value
  if let some n := e.getAppFn.constName? then
    let aliases := [
      "sectionNativeS", "sectionNativeP", "sectionNativeP'", "sectionNativeL",
      "sectionNativeTensor", "sectionNativeTargetTensor", "sectionNativeSourceTensor",
      "sectionNativeClosedIso", "sectionNativeCompactIso", "sectionNativeComposition",
      "sectionNativeClosedProjection", "sectionNativeCompactProjection", "sectionNativeOrderedS",
      "sectionNativeOrderedP", "sectionNativeNormalizedComparison"]
    if aliases.contains n.getString! then
      if let some e' ← withTransparency .default (unfoldDefinition? e) then
        return (← instantiateMVars e').headBeta
  return e

mutual
private meta partial def coordinateFoldedCached (a b : Expr) :
    StateRefT (Std.HashMap (Expr × Expr) Expr) MetaM Expr := do
  let key := (a.consumeMData, b.consumeMData)
  if let some pf := (← get).get? key then return pf
  let pf ← coordinateFoldedStep a b
  modify (·.insert key pf)
  return pf

private meta partial def coordinateFoldedStep (a b : Expr) :
    StateRefT (Std.HashMap (Expr × Expr) Expr) MetaM Expr := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return ← mkHEqRefl a
  if ← isProp (← inferType a) then
    let hp ← coordinateFoldedCached (← inferType a) (← inferType b)
    let e ← mkAppM ``eq_of_heq #[hp]
    let pf ← mkAppM ``coordinateTensorProofHEq #[a, b, e]
    return ← mkAuxTheorem (← inferType pf) pf
      (zetaDelta := true) (kind? := `_coordinateFolded)
  if a.getAppFn == b.getAppFn && a.getAppArgs.size == b.getAppArgs.size then
    let argsA := a.getAppArgs
    let argsB := b.getAppArgs
    let ct ← mkHCongrWithArity a.getAppFn argsA.size
    let mut ps := #[]
    for i in [:argsA.size] do
      let mut h ← coordinateFoldedCached argsA[i]! argsB[i]!
      if ct.argKinds[i]! == .eq then h ← mkAppM ``eq_of_heq #[h]
      ps := ps ++ #[argsA[i]!, argsB[i]!, h]
    let pf := mkAppN ct.proof ps
    let pf ← if (← inferType pf).isHEq then pure pf else mkAppM ``heq_of_eq #[pf]
    return ← mkAuxTheorem (← inferType pf) pf
      (zetaDelta := true) (kind? := `_coordinateFolded)
  let aa ← coordinateNativeAliasNormalize a
  if aa != a then
    let haType ← mkAppM ``HEq #[a, aa]
    let ha ← mkAuxTheorem haType (← mkHEqRefl a)
      (zetaDelta := true) (kind? := `_coordinateAlias)
    let hn ← coordinateFoldedCached aa b
    let pf ← mkAppM ``HEq.trans #[ha, hn]
    return ← mkAuxTheorem (← inferType pf) pf
      (zetaDelta := true) (kind? := `_coordinateFolded)
  let bb ← coordinateNativeAliasNormalize b
  if bb != b then
    let hbType ← mkAppM ``HEq #[b, bb]
    let hb ← mkAuxTheorem hbType (← mkHEqRefl b)
      (zetaDelta := true) (kind? := `_coordinateAlias)
    let hb ← mkAppM ``HEq.symm #[hb]
    let hn ← coordinateFoldedCached a bb
    let pf ← mkAppM ``HEq.trans #[hn, hb]
    return ← mkAuxTheorem (← inferType pf) pf
      (zetaDelta := true) (kind? := `_coordinateFolded)
  let an ← coordinateProjectionHead a
  if an != a then
    let haType ← mkAppM ``HEq #[a, an]
    let ha ← mkAuxTheorem haType (← mkHEqRefl a)
      (zetaDelta := true) (kind? := `_coordinateField)
    let hn ← coordinateFoldedCached an b
    let pf ← mkAppM ``HEq.trans #[ha, hn]
    return ← mkAuxTheorem (← inferType pf) pf
      (zetaDelta := true) (kind? := `_coordinateFolded)
  let bn ← coordinateProjectionHead b
  if bn != b then
    let hbType ← mkAppM ``HEq #[b, bn]
    let hb ← mkAuxTheorem hbType (← mkHEqRefl b)
      (zetaDelta := true) (kind? := `_coordinateField)
    let hb ← mkAppM ``HEq.symm #[hb]
    let hn ← coordinateFoldedCached a bn
    let pf ← mkAppM ``HEq.trans #[hn, hb]
    return ← mkAuxTheorem (← inferType pf) pf
      (zetaDelta := true) (kind? := `_coordinateFolded)
  unless ← withTransparency .default (isDefEq a b) do
    throwError m!"Different folded comparison expressions: {a} versus {b}"
  let type ← mkAppM ``HEq #[a, b]
  return ← mkAuxTheorem type (← mkHEqRefl a)
    (zetaDelta := true) (kind? := `_coordinateFoldedDefEq)
end

private meta def coordinateFoldedCongrHEq (a b : Expr) : MetaM Expr :=
  (coordinateFoldedCached a b).run' {}

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale
private theorem identity_projection_of_composition
    {C : Type*} [Category C]
    (F L : C ⥤ C) (T : C ⥤ C ⥤ C) (e : F ≅ 𝟭 C) (l : L ≅ 𝟭 C)
    (p : ∀ M K, (T.obj (F.obj M)).obj K ⟶ F.obj ((T.obj M).obj (L.obj K)))
    (c : L ⟶ L ⋙ L)
    (np : ∀ {M M'} (f : M ⟶ M') (K),
      (T.map (F.map f)).app K ≫ p M' K =
        p M K ≫ F.map ((T.map f).app (L.obj K)))
    (nk : ∀ M {K K'} (f : K ⟶ K'),
      (T.obj (F.obj M)).map f ≫ p M K' =
        p M K ≫ F.map ((T.obj M).map (L.map f)))
    (hc : ∀ K, c.app K ≫ l.hom.app (L.obj K) = 𝟙 _)
    (hp : ∀ M K,
      p (F.obj M) K ≫ F.map (p M (L.obj K)) ≫
        F.map (e.hom.app ((T.obj M).obj (L.obj (L.obj K)))) =
      (T.map (F.map (e.hom.app M))).app K ≫ p M K ≫
        F.map ((T.obj M).map (c.app K)))
    [∀ M K, IsIso (p M K)] (M K : C) :
    p M K ≫ F.map ((T.obj M).map (l.hom.app K)) ≫
      e.hom.app ((T.obj M).obj K) = (T.map (e.hom.app M)).app K := by
  let : (𝟭 C).IsEquivalence := Functor.isEquivalence_refl
  let : F.IsEquivalence := Functor.isEquivalence_of_iso e.symm
  have h := hp M K
  rw [reassoc_of% (np (e.hom.app M) K)] at h
  have h' := (cancel_epi (p (F.obj M) K)).mp h
  rw [← F.map_comp, ← F.map_comp] at h'
  have h'' := F.map_injective h'
  have h''' := congrArg (fun z ↦ z ≫ (T.obj M).map (l.hom.app (L.obj K))) h''
  simp -implicitDefEqProofs only [Category.assoc] at h'''
  rw [← (T.obj M).map_comp, hc, (T.obj M).map_id,
    Category.comp_id] at h'''
  have he := e.hom.naturality ((T.obj M).map (l.hom.app (L.obj K)))
  dsimp only [Functor.id_map] at he
  rw [← he] at h'''
  have hl : L.map (l.hom.app K) = l.hom.app (L.obj K) := by
    apply (cancel_mono (l.hom.app K)).1
    exact l.hom.naturality (l.hom.app K)
  apply (cancel_epi ((T.obj (F.obj M)).map (l.hom.app K))).1
  rw [reassoc_of% (nk M (l.hom.app K)), hl]
  have he2 := e.hom.naturality ((T.obj M).map (l.hom.app K))
  dsimp only [Functor.id_map, Functor.id_obj] at he2 h'''
  rw [he2, reassoc_of% h''']
  exact ((T.map (e.hom.app M)).naturality (l.hom.app K)).symm

private theorem source_projection_composition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)]
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Z) :
    let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
    let G := rightDerivedLowerShriek (ModuleCat.{u + 1} A) g
    let H := rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)
    let T := derivedTensor (ModuleCat.{u + 1} A) X
    let U := derivedTensor (ModuleCat.{u + 1} A) Z
    let Lf := (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
    let Lg := (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor
    let E := unboundedEtaleLowerShriekCompIso A f g
    ((projectionMap (ModuleCat.{u + 1} A) g).app (F.obj M)).app K ≫
        G.map (((projectionMap (ModuleCat.{u + 1} A) f).app M).app (Lg.obj K)) ≫
        E.hom.app ((T.obj M).obj (Lf.obj (Lg.obj K))) =
      (U.map (E.hom.app M)).app K ≫
        ((projectionMap (ModuleCat.{u + 1} A) (f ≫ g)).app M).app K ≫
        H.map ((T.obj M).map ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app K)) := by
  have h := projectionMap_chosen_comp A f g M K
  dsimp only at h ⊢
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "missing comparison equation"
    let eq ← AlgebraicGeometry.Etale.coordinateTensorCongrHEq target
      (← Lean.instantiateMVars d.type)
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

private theorem chosen_projection_composition_of_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (r : X ⟶ Z) (hr : r = f ≫ g)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [HasCompactification r] [QuasiCompact f] [QuasiCompact (f ≫ g)]
    (V : DerivedCategoryModule A X) (M : DerivedCategoryModule A Z) :
    let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
    let G := rightDerivedLowerShriek (ModuleCat.{u + 1} A) g
    let H := rightDerivedLowerShriek (ModuleCat.{u + 1} A) r
    let T := derivedTensor (ModuleCat.{u + 1} A) X
    let U := derivedTensor (ModuleCat.{u + 1} A) Z
    let Lf := (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
    let Lg := (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor
    let k := unboundedEtaleLowerShriekCongr A hr ≪≫
      (unboundedEtaleLowerShriekCompIso A f g).symm
    (U.map (k.hom.app V)).app M ≫
        ((projectionMap (ModuleCat.{u + 1} A) g).app (F.obj V)).app M ≫
        G.map (((projectionMap (ModuleCat.{u + 1} A) f).app V).app (Lg.obj M)) =
      ((projectionMap (ModuleCat.{u + 1} A) r).app V).app M ≫
        H.map ((T.obj V).map ((leftDerivedUpperStarComp
          (ModuleCat.{u + 1} A) f g r hr).hom.app M)) ≫
        k.hom.app ((T.obj V).obj (Lf.obj (Lg.obj M))) := by
  subst r
  dsimp only
  simp -implicitDefEqProofs only [unboundedEtaleLowerShriekCongr, Iso.refl_trans, Iso.symm_hom]
  let E := unboundedEtaleLowerShriekCompIso A f g
  let U := derivedTensor (ModuleCat.{u + 1} A) Z
  let W := ((derivedTensor (ModuleCat.{u + 1} A) X).obj V).obj
    ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
      ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj M))
  have h := source_projection_composition A f g V M
  dsimp only at h
  simpa -implicitDefEqProofs only [E, U, W, Iso.app_inv, Functor.mapIso_inv, Category.assoc] using
    (_root_.inverse_square ((U.mapIso (E.app V)).app M) (E.app W)
    ((((projectionMap (ModuleCat.{u + 1} A) g).app
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj V)).app M) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        (((projectionMap (ModuleCat.{u + 1} A) f).app V).app
          ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj M)))
    ((((projectionMap (ModuleCat.{u + 1} A) (f ≫ g)).app V).app M) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj V).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app M)))
    (by simpa -implicitDefEqProofs only [E, U, W, Category.assoc, Iso.app_hom, Functor.mapIso_hom]
      using h)).symm

private theorem inverse_compositor_unit
    {C : Type*} [Category C] (F H : C ⥤ C)
    (e : F ≅ 𝟭 C) (E : F ⋙ F ≅ H) (c : F ≅ H) (W : C)
    (h : E.hom.app W = F.map (e.hom.app W) ≫ 𝟙 _ ≫ c.hom.app W) :
    c.hom.app W ≫ E.inv.app W = F.map (e.inv.app W) := by
  apply (cancel_mono (E.hom.app W)).1
  rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, h, Category.id_comp,
    ← F.map_comp_assoc, Iso.inv_hom_id_app, F.map_id, Category.id_comp]

private theorem identity_compositor_unit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [IsNoetherian X] (W : DerivedCategoryModule A X) :
    let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 X)
    let e := unboundedEtaleLowerShriekId A X
    let E := unboundedEtaleLowerShriekCompIso A (𝟙 X) (𝟙 X)
    let k := unboundedEtaleLowerShriekCongr A (Category.id_comp (𝟙 X)).symm ≪≫ E.symm
    k.hom.app W = F.map (e.inv.app W) := by
  let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 X)
  let e := unboundedEtaleLowerShriekId A X
  let E := unboundedEtaleLowerShriekCompIso A (𝟙 X) (𝟙 X)
  let k := unboundedEtaleLowerShriekCongr A (Category.id_comp (𝟙 X)).symm ≪≫ E.symm
  change k.hom.app W = F.map (e.inv.app W)
  have h := congr_app (unboundedEtaleLowerShriekCompIso_units A (𝟙 X)).1 W
  simp -implicitDefEqProofs only [Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.leftUnitor_hom_app, Functor.id_obj] at h
  apply inverse_compositor_unit F _ e E
    (unboundedEtaleLowerShriekCongr A (Category.id_comp (𝟙 X)).symm) W
  exact h

private theorem inverse_square_maps
    {C : Type*} [Category C] {W X Y Z : C}
    (a : W ⟶ X) (a' : X ⟶ W) (b : Y ⟶ Z) (b' : Z ⟶ Y)
    (p : W ⟶ Y) (q : X ⟶ Z)
    (ha : a' ≫ a = 𝟙 X) (hb : b ≫ b' = 𝟙 Y)
    (h : p ≫ b = a ≫ q) : q ≫ b' = a' ≫ p := by
  have h' := congrArg (fun z ↦ a' ≫ z ≫ b') h
  simp only [Category.assoc, hb, Category.comp_id] at h'
  rw [← Category.assoc, ha, Category.id_comp] at h'
  exact h'.symm

private theorem projection_recursion_from_inverse
    {C : Type*} [Category C] (F L : C ⥤ C) (T : C ⥤ C ⥤ C)
    (e : F ≅ 𝟭 C)
    (p : ∀ V N, (T.obj (F.obj V)).obj N ⟶ F.obj ((T.obj V).obj (L.obj N)))
    (c : L ⟶ L ⋙ L) (k : F ≅ F ⋙ F) (V N : C)
    (hk : ∀ W, k.hom.app W = F.map (e.inv.app W))
    (h : (T.map (k.hom.app V)).app N ≫ p (F.obj V) N ≫ F.map (p V (L.obj N)) =
      p V N ≫ F.map ((T.obj V).map (c.app N)) ≫
        k.hom.app ((T.obj V).obj (L.obj (L.obj N)))) :
    p (F.obj V) N ≫ F.map (p V (L.obj N)) ≫
        F.map (e.hom.app ((T.obj V).obj (L.obj (L.obj N)))) =
      (T.map (F.map (e.hom.app V))).app N ≫ p V N ≫
        F.map ((T.obj V).map (c.app N)) := by
  rw [hk, hk] at h
  let W := (T.obj V).obj (L.obj (L.obj N))
  have ha : (T.map (F.map (e.hom.app V))).app N ≫
      (T.map (F.map (e.inv.app V))).app N = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← T.map_comp, ← F.map_comp,
      Iso.hom_inv_id_app, F.map_id, T.map_id, NatTrans.id_app]
  have hb : F.map (e.inv.app W) ≫ F.map (e.hom.app W) = 𝟙 _ := by
    rw [← F.map_comp, Iso.inv_hom_id_app, F.map_id]
  simpa only [Category.assoc, W] using
    inverse_square_maps
      ((T.map (F.map (e.inv.app V))).app N)
      ((T.map (F.map (e.hom.app V))).app N)
      (F.map (e.inv.app W)) (F.map (e.hom.app W))
      (p V N ≫ F.map ((T.obj V).map (c.app N)))
      (p (F.obj V) N ≫ F.map (p V (L.obj N))) ha hb
      (by simpa only [Category.assoc, W] using h.symm)

private def identityShriekFunctor
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    DerivedCategoryModule A X ⥤ DerivedCategoryModule A X :=
  rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 X)

private def identityPullbackFunctor
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    DerivedCategoryModule A X ⥤ DerivedCategoryModule A X :=
  (upperStar (ModuleCat.{u + 1} A) (𝟙 X)).leftDerivedFunctor

private def identityTensorFunctor
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    DerivedCategoryModule A X ⥤ DerivedCategoryModule A X ⥤ DerivedCategoryModule A X :=
  derivedTensor (ModuleCat.{u + 1} A) X

private def identityShriekUnit
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :
    identityShriekFunctor A X ≅ 𝟭 (DerivedCategoryModule A X) :=
  unboundedEtaleLowerShriekId A X

private def typed_projection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [IsNoetherian X] :
    let F := identityShriekFunctor A X
    let L := identityPullbackFunctor A X
    let T := identityTensorFunctor A X
    ∀ M K, (T.obj (F.obj M)).obj K ⟶ F.obj ((T.obj M).obj (L.obj K)) :=
  fun M K ↦ ((projectionMap (ModuleCat.{u + 1} A) (𝟙 X)).app M).app K
private def typed_compositor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [IsNoetherian X] :
    let F := identityShriekFunctor A X
    F ≅ F ⋙ F :=
  unboundedEtaleLowerShriekCongr A (Category.id_comp (𝟙 X)).symm ≪≫
    (unboundedEtaleLowerShriekCompIso A (𝟙 X) (𝟙 X)).symm
private def typed_pullback_compositor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [IsNoetherian X] :
    let L := identityPullbackFunctor A X
    L ⟶ L ⋙ L :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 X) (𝟙 X)
    (𝟙 X) (Category.id_comp (𝟙 X)).symm).hom

private theorem named_identity_compositor_unit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [IsNoetherian X] (W : DerivedCategoryModule A X) :
    (typed_compositor A X).hom.app W =
      (identityShriekFunctor A X).map ((identityShriekUnit A X).inv.app W) := by
  simpa only [typed_compositor, identityShriekFunctor, identityShriekUnit] using
    identity_compositor_unit A X W

private theorem named_identity_projection_composition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [IsNoetherian X] (V N : DerivedCategoryModule A X) :
    ((identityTensorFunctor A X).map ((typed_compositor A X).hom.app V)).app N ≫
        typed_projection A X ((identityShriekFunctor A X).obj V) N ≫
        (identityShriekFunctor A X).map
          (typed_projection A X V ((identityPullbackFunctor A X).obj N)) =
      typed_projection A X V N ≫
        (identityShriekFunctor A X).map
          (((identityTensorFunctor A X).obj V).map
            ((typed_pullback_compositor A X).app N)) ≫
        (typed_compositor A X).hom.app
          (((identityTensorFunctor A X).obj V).obj
            ((identityPullbackFunctor A X).obj ((identityPullbackFunctor A X).obj N))) := by
  have h := chosen_projection_composition_of_eq A (𝟙 X) (𝟙 X)
    (𝟙 X) (Category.id_comp (𝟙 X)).symm V N
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.reverse.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "missing identity composition equation"
    let eq ← coordinateProjectionCongrHEq target (← Lean.instantiateMVars d.type)
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

private theorem identity_projection_recursion
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [IsNoetherian X] (V N : DerivedCategoryModule A X) :
    typed_projection A X ((identityShriekFunctor A X).obj V) N ≫
        (identityShriekFunctor A X).map
          (typed_projection A X V ((identityPullbackFunctor A X).obj N)) ≫
        (identityShriekFunctor A X).map
          ((identityShriekUnit A X).hom.app
            (((identityTensorFunctor A X).obj V).obj
              ((identityPullbackFunctor A X).obj ((identityPullbackFunctor A X).obj N)))) =
      ((identityTensorFunctor A X).map
        ((identityShriekFunctor A X).map ((identityShriekUnit A X).hom.app V))).app N ≫
        typed_projection A X V N ≫
        (identityShriekFunctor A X).map
          (((identityTensorFunctor A X).obj V).map
            ((typed_pullback_compositor A X).app N)) := by
  apply projection_recursion_from_inverse
    (identityShriekFunctor A X) (identityPullbackFunctor A X) (identityTensorFunctor A X)
    (identityShriekUnit A X) (typed_projection A X) (typed_pullback_compositor A X)
    (typed_compositor A X) V N
  · exact named_identity_compositor_unit A X
  · exact named_identity_projection_composition A X V N

private theorem named_identity_projection_naturality_left
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [IsNoetherian X]
    {V W : DerivedCategoryModule A X} (f : V ⟶ W) (N : DerivedCategoryModule A X) :
    ((identityTensorFunctor A X).map ((identityShriekFunctor A X).map f)).app N ≫
        typed_projection A X W N =
      typed_projection A X V N ≫ (identityShriekFunctor A X).map
        (((identityTensorFunctor A X).map f).app ((identityPullbackFunctor A X).obj N)) := by
  have h := congr_app ((projectionMap (ModuleCat.{u + 1} A) (𝟙 X)).naturality f) N
  simp -implicitDefEqProofs only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at h
  dsimp only [typed_projection, identityTensorFunctor,
    identityShriekFunctor, identityPullbackFunctor]
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.reverse.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "missing native projection property"
    let eq ← coordinateProjectionCongrHEq target (← Lean.instantiateMVars d.type)
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

private theorem named_identity_projection_naturality_right
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [IsNoetherian X] (V : DerivedCategoryModule A X)
    {N N' : DerivedCategoryModule A X} (f : N ⟶ N') :
    ((identityTensorFunctor A X).obj ((identityShriekFunctor A X).obj V)).map f ≫
        typed_projection A X V N' =
      typed_projection A X V N ≫ (identityShriekFunctor A X).map
        (((identityTensorFunctor A X).obj V).map ((identityPullbackFunctor A X).map f)) := by
  have h := ((projectionMap (ModuleCat.{u + 1} A) (𝟙 X)).app V).naturality f
  dsimp only [typed_projection, identityTensorFunctor,
    identityShriekFunctor, identityPullbackFunctor]
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.reverse.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "missing coefficient naturality equation"
    let eq ← coordinateProjectionCongrHEq target (← Lean.instantiateMVars d.type)
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

private theorem typed_projection_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [IsNoetherian X] (M K : DerivedCategoryModule A X) :
    IsIso (typed_projection A X M K) := by
  let : IsIso (projectionMap (ModuleCat.{u + 1} A) (𝟙 X)) :=
    isIso_projectionMap_of_finite A (𝟙 X)
  have h := NatIso.isIso_app_of_isIso
    ((projectionMap (ModuleCat.{u + 1} A) (𝟙 X)).app M) K
  dsimp only [typed_projection, identityTensorFunctor,
    identityShriekFunctor, identityPullbackFunctor]
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.reverse.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "missing native projection property"
    let eq ← coordinateProjectionCongrHEq target (← Lean.instantiateMVars d.type)
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

private theorem named_identity_projection_unit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [IsNoetherian X] (M K : DerivedCategoryModule A X) :
    typed_projection A X M K ≫
        (identityShriekFunctor A X).map (((identityTensorFunctor A X).obj M).map
          ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app K)) ≫
        (identityShriekUnit A X).hom.app (((identityTensorFunctor A X).obj M).obj K) =
      ((identityTensorFunctor A X).map ((identityShriekUnit A X).hom.app M)).app K := by
  let := typed_projection_isIso A X
  exact identity_projection_of_composition
    (identityShriekFunctor A X) (identityPullbackFunctor A X) (identityTensorFunctor A X)
    (identityShriekUnit A X) (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X)
    (typed_projection A X) (typed_pullback_compositor A X)
    (fun {V W} f N ↦ named_identity_projection_naturality_left A X f N)
    (fun V {N N'} f ↦ named_identity_projection_naturality_right A X V f)
    (fun N ↦ leftDerivedUpperStarComp_id_left_hom_app (ModuleCat.{u + 1} A) (𝟙 X) N)
    (identity_projection_recursion A X) M K

private theorem chosen_identity_projection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [IsNoetherian X]
    (M K : DerivedCategoryModule A X) :
    ((projectionMap (ModuleCat.{u + 1} A) (𝟙 X)).app M).app K ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 X)).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
            ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app K)) ≫
        (unboundedEtaleLowerShriekId A X).hom.app
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj K) =
      ((derivedTensor (ModuleCat.{u + 1} A) X).map
        ((unboundedEtaleLowerShriekId A X).hom.app M)).app K := by
  have h := named_identity_projection_unit A X M K
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.reverse.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "missing identity projection equation"
    let eq ← coordinateProjectionCongrHEq target (← Lean.instantiateMVars d.type)
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

private theorem chosen_identity_projection_inv
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [IsNoetherian X]
    (M K : DerivedCategoryModule A X) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).map
        ((unboundedEtaleLowerShriekId A X).inv.app M)).app K ≫
      ((projectionMap (ModuleCat.{u + 1} A) (𝟙 X)).app M).app K ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 X)).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
          ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app K)) =
    (unboundedEtaleLowerShriekId A X).inv.app
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj K) := by
  apply (cancel_mono ((unboundedEtaleLowerShriekId A X).hom.app
    (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj K))).1
  rw [Category.assoc, Category.assoc, chosen_identity_projection,
    ← NatTrans.comp_app, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Iso.inv_hom_id_app]

private theorem shriekCongr_symm
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [HasCompactification f] [HasCompactification g] (h : f = g) :
    (unboundedEtaleLowerShriekCongr A h).inv =
      (unboundedEtaleLowerShriekCongr A h.symm).hom := by
  subst g
  rfl

private theorem chosen_section_projection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X]
    (s : X ⟶ Y) (p : Y ⟶ X) (hs : s ≫ p = 𝟙 X)
    [HasCompactification s] [HasCompactification p] [HasCompactification (s ≫ p)]
    [QuasiCompact s] [QuasiCompact (s ≫ p)]
    (V M : DerivedCategoryModule A X) :
    let S := rightDerivedLowerShriek (ModuleCat.{u + 1} A) s
    let P := rightDerivedLowerShriek (ModuleCat.{u + 1} A) p
    let T := derivedTensor (ModuleCat.{u + 1} A) X
    let Lp := (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor
    let e := unboundedEtaleLowerShriekCompIso A s p ≪≫
      unboundedEtaleLowerShriekCongr A hs ≪≫ unboundedEtaleLowerShriekId A X
    (T.map (e.inv.app V)).app M ≫
      ((projectionMap (ModuleCat.{u + 1} A) p).app (S.obj V)).app M ≫
      P.map (((projectionMap (ModuleCat.{u + 1} A) s).app V).app (Lp.obj M)) ≫
      P.map (S.map ((T.obj V).map
        ((leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p hs).hom.app M))) =
    e.inv.app ((T.obj V).obj M) := by
  let k := unboundedEtaleLowerShriekCongr A hs.symm ≪≫
    (unboundedEtaleLowerShriekCompIso A s p).symm
  have hc := chosen_projection_composition_of_eq A s p (𝟙 X) hs.symm V M
  have hn := k.hom.naturality
    (((derivedTensor (ModuleCat.{u + 1} A) X).obj V).map
      ((leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p hs).hom.app M))
  dsimp only [k, Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn
  have he : (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s p (𝟙 X) hs.symm).hom.app M ≫
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p hs).hom.app M =
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app M := by
    simp -implicitDefEqProofs only [leftDerivedUpperStarCompSectionIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Iso.hom_inv_id_app_assoc]
  have hg : (unboundedEtaleLowerShriekCongr A hs).inv =
      (unboundedEtaleLowerShriekCongr A hs.symm).hom := by
    exact shriekCongr_symm A hs
  dsimp only
  simp -implicitDefEqProofs only [Iso.trans_inv, NatTrans.comp_app, Functor.map_comp, hg,
    NatTrans.comp_app, Category.assoc]
  simp -implicitDefEqProofs only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp,
    Category.assoc] at hc hn
  dsimp only [rightDerivedLowerShriek, rightDerivedLowerShriekOfCompactification,
    Functor.comp_obj, Functor.comp_map] at hc hn ⊢
  rw [reassoc_of% hc, ← hn]
  rw [← Functor.map_comp_assoc]
  simp -implicitDefEqProofs only [← Functor.map_comp, he]
  rw [reassoc_of% (chosen_identity_projection_inv A X V M)]

end AlgebraicGeometry.Etale

private theorem ordered_section_projection
    {C D : Type*} [Category C] [Category D]
    (S : C ⥤ D) (P : D ⥤ C) (Lp : C ⥤ D) (Ls : D ⥤ C)
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D)
    (t : T ≅ T.flip) (v : U ≅ U.flip)
    (ht : ∀ M V, (t.hom.app M).app V ≫ (t.hom.app V).app M = 𝟙 _)
    (hv : ∀ M V, (v.hom.app M).app V ≫ (v.hom.app V).app M = 𝟙 _)
    (l : Lp ⋙ Ls ≅ 𝟭 C) (e : S ⋙ P ≅ 𝟭 C)
    (ps : ∀ V K, (U.obj (S.obj V)).obj K ⟶ S.obj ((T.obj V).obj (Ls.obj K)))
    (pg : ∀ W M, (T.obj (P.obj W)).obj M ⟶ P.obj ((U.obj W).obj (Lp.obj M)))
    (V M : C)
    (h : (T.map (e.inv.app V)).app M ≫ pg (S.obj V) M ≫
      P.map (ps V (Lp.obj M)) ≫ P.map (S.map ((T.obj V).map (l.hom.app M))) =
      e.inv.app ((T.obj V).obj M)) :
    (T.obj M).map (e.inv.app V) ≫ (t.hom.app M).app (P.obj (S.obj V)) ≫
      pg (S.obj V) M ≫ P.map ((v.hom.app (S.obj V)).app (Lp.obj M)) ≫
      P.map ((v.hom.app (Lp.obj M)).app (S.obj V) ≫ ps V (Lp.obj M) ≫
        S.map ((t.hom.app V).app (Ls.obj (Lp.obj M))) ≫
        S.map ((T.map (l.hom.app M)).app V)) =
    e.inv.app ((T.obj M).obj V) := by
  have hn := (t.hom.app V).naturality (l.hom.app M)
  dsimp only [Functor.flip_obj_map] at hn
  have hnt := (t.hom.app M).naturality (e.inv.app V)
  dsimp only [Functor.flip_obj_map] at hnt
  have he := e.inv.naturality ((t.hom.app V).app M)
  dsimp only [Functor.id_map, Functor.comp_map] at he
  simp -implicitDefEqProofs only [P.map_comp]
  rw [reassoc_of% hnt]
  rw [← P.map_comp_assoc, hv, P.map_id, Category.id_comp]
  rw [← P.map_comp, ← S.map_comp, ← hn, S.map_comp, P.map_comp]
  rw [reassoc_of% h]
  rw [← he]
  rw [← Category.assoc, ht, Category.id_comp]
  rfl

private theorem ordered_projection_transfer
    {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (a : F ⟶ G)
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (L : D ⥤ C)
    (t : T ≅ T.flip) (v : U ≅ U.flip)
    (p : ∀ W K, (U.obj (F.obj W)).obj K ⟶ F.obj ((T.obj W).obj (L.obj K)))
    (q : ∀ W K, (U.obj (G.obj W)).obj K ⟶ G.obj ((T.obj W).obj (L.obj K)))
    (h : ∀ W K, (U.map (a.app W)).app K ≫ q W K =
      p W K ≫ a.app ((T.obj W).obj (L.obj K))) (W : C) (K : D) :
    (U.obj K).map (a.app W) ≫ (v.hom.app K).app (G.obj W) ≫
      q W K ≫ G.map ((t.hom.app W).app (L.obj K)) =
    (v.hom.app K).app (F.obj W) ≫ p W K ≫
      F.map ((t.hom.app W).app (L.obj K)) ≫ a.app ((T.obj (L.obj K)).obj W) := by
  have hn := (v.hom.app K).naturality (a.app W)
  have ha := a.naturality ((t.hom.app W).app (L.obj K))
  dsimp only [Functor.flip_obj_map] at hn
  rw [reassoc_of% hn, reassoc_of% h, ← ha]
  rfl

private theorem ordered_projection_transfer_post
    {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (a : F ⟶ G)
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (L : D ⥤ C)
    (t : T ≅ T.flip) (v : U ≅ U.flip)
    (p : ∀ W K, (U.obj (F.obj W)).obj K ⟶ F.obj ((T.obj W).obj (L.obj K)))
    (q : ∀ W K, (U.obj (G.obj W)).obj K ⟶ G.obj ((T.obj W).obj (L.obj K)))
    (h : ∀ W K, (U.map (a.app W)).app K ≫ q W K =
      p W K ≫ a.app ((T.obj W).obj (L.obj K)))
    (W : C) (K : D) (Z : C) (c : (T.obj (L.obj K)).obj W ⟶ Z) :
    (U.obj K).map (a.app W) ≫ (v.hom.app K).app (G.obj W) ≫
      q W K ≫ G.map ((t.hom.app W).app (L.obj K)) ≫ G.map c =
    (v.hom.app K).app (F.obj W) ≫ p W K ≫
      F.map ((t.hom.app W).app (L.obj K) ≫ c) ≫ a.app Z := by
  rw [F.map_comp]
  rw [reassoc_of% (ordered_projection_transfer a T U L t v p q h W K)]
  simp only [Category.assoc]
  rw [a.naturality c]

private theorem inverse_projection_transfer
    {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (a : F ≅ G) (T : D ⥤ D ⥤ D)
    (M N : C) (K : D)
    (p : (T.obj (F.obj M)).obj K ⟶ F.obj N)
    (q : (T.obj (G.obj M)).obj K ⟶ G.obj N)
    (h : (T.map (a.hom.app M)).app K ≫ q = p ≫ a.hom.app N) :
    (T.map (a.inv.app M)).app K ≫ p = q ≫ a.inv.app N := by
  apply (cancel_epi ((T.map (a.hom.app M)).app K)).1
  rw [← Category.assoc, ← NatTrans.comp_app, ← T.map_comp, Iso.hom_inv_id_app,
    T.map_id, NatTrans.id_app, Category.id_comp]
  rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

private theorem section_projection_unit
    {C D : Type*} [Category C] [Category D]
    (S : C ⥤ D) (P : D ⥤ C)
    (T : C ⥤ C) (U : D ⥤ D) (e : S ⋙ P ≅ 𝟭 C)
    (I M : C) (r : T.obj I ≅ M)
    (ps : S ⋙ U ≅ T ⋙ S) (pg : P ⋙ T ⟶ U ⋙ P)
    (h : T.map (e.inv.app I) ≫ pg.app (S.obj I) ≫
        P.map (ps.hom.app I) = e.inv.app (T.obj I)) :
    e.inv.app M ≫ P.map (S.map r.inv ≫ ps.inv.app I) =
      r.inv ≫ T.map (e.inv.app I) ≫ pg.app (S.obj I) := by
  apply (cancel_mono (P.map (ps.hom.app I))).1
  simp -implicitDefEqProofs only [Category.assoc, ← P.map_comp, ps.inv_hom_id_app,
    Functor.comp_obj, Category.comp_id]
  rw [h]
  simpa -implicitDefEqProofs only [Functor.comp_map, Functor.id_map] using (e.inv.naturality
    r.inv).symm

private theorem supported_tensor_trace
    {C D : Type*} [Category C] [Category D]
    (S : C ⥤ D) (P : D ⥤ C)
    (T : C ⥤ C) (U : D ⥤ D) (e : S ⋙ P ≅ 𝟭 C)
    (I M : C) (r : T.obj I ≅ M)
    (ps : S ⋙ U ≅ T ⋙ S) (pg : P ⋙ T ⟶ U ⋙ P)
    (V : D) (c : S.obj I ⟶ V) (tr : P.obj V ⟶ I)
    (ε : P.obj (U.obj V) ⟶ M)
    (hs : e.inv.app M ≫ P.map (S.map r.inv ≫ ps.inv.app I) =
      r.inv ≫ T.map (e.inv.app I) ≫ pg.app (S.obj I))
    (hc : pg.app V ≫ ε = T.map tr ≫ r.hom) :
    e.inv.app M ≫ P.map (S.map r.inv ≫ ps.inv.app I ≫ U.map c) ≫ ε =
      r.inv ≫ T.map (e.inv.app I ≫ P.map c ≫ tr) ≫ r.hom := by
  have hn := pg.naturality c
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc _ _ (U.map c), P.map_comp]
  simp -implicitDefEqProofs only [Category.assoc]
  rw [reassoc_of% hs]
  simp -implicitDefEqProofs only [Category.assoc, Functor.map_comp]
  rw [← reassoc_of% hn, hc]

private theorem section_projection_transport_maps
    {C D : Type*} [Category C] [Category D]
    {S S' : C ⥤ D} {P P' : D ⥤ C}
    (T : C ⥤ C) (U : D ⥤ D)
    (a : S ≅ S') (b : P ≅ P') (e' : S' ⋙ P' ≅ 𝟭 C)
    (ps : ∀ V, U.obj (S.obj V) ⟶ S.obj (T.obj V))
    (pg : ∀ W, T.obj (P.obj W) ⟶ P.obj (U.obj W))
    (rs : ∀ V, U.obj (S'.obj V) ⟶ S'.obj (T.obj V))
    (rg : ∀ W, T.obj (P'.obj W) ⟶ P'.obj (U.obj W))
    (hnat : ∀ {W W'} (f : W ⟶ W'),
      T.map (P.map f) ≫ pg W' = pg W ≫ P.map (U.map f))
    (hs : ∀ V, U.map (a.hom.app V) ≫ rs V = ps V ≫ a.hom.app (T.obj V))
    (hp : ∀ W, T.map (b.hom.app W) ≫ rg W = pg W ≫ b.hom.app (U.obj W))
    (I : C)
    (h : T.map (e'.inv.app I) ≫ rg (S'.obj I) ≫ P'.map (rs I) =
      e'.inv.app (T.obj I)) :
    let e := Functor.isoWhiskerRight a P ≪≫ Functor.isoWhiskerLeft S' b ≪≫ e'
    T.map (e.inv.app I) ≫ pg (S.obj I) ≫ P.map (ps I) = e.inv.app (T.obj I) := by
  have hs' : rs I ≫ a.inv.app (T.obj I) = U.map (a.inv.app I) ≫ ps I := by
    apply (cancel_epi (U.map (a.hom.app I))).1
    rw [← U.map_comp_assoc, Iso.hom_inv_id_app, U.map_id, Category.id_comp,
      reassoc_of% (hs I), Iso.hom_inv_id_app, Category.comp_id]
  have hp' : T.map (b.inv.app (S'.obj I)) ≫ pg (S'.obj I) =
      rg (S'.obj I) ≫ b.inv.app (U.obj (S'.obj I)) := by
    apply (cancel_epi (T.map (b.hom.app (S'.obj I)))).1
    rw [← T.map_comp_assoc, Iso.hom_inv_id_app, T.map_id, Category.id_comp,
      reassoc_of% (hp (S'.obj I)), Iso.hom_inv_id_app, Category.comp_id]
  have hn := hnat (a.inv.app I)
  dsimp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp -implicitDefEqProofs only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hp']
  have hb := b.inv.naturality (U.map (a.inv.app I) ≫ ps I)
  simp -implicitDefEqProofs only [P.map_comp] at hb
  rw [← hb, ← hs', P'.map_comp]
  simp -implicitDefEqProofs only [Category.assoc]
  rw [reassoc_of% h, b.inv.naturality]

namespace AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
open AffineLinePurity VectorIntegrationSite
set_option allowUnsafeReducibility true in
attribute [local reducible] affineTraceLineCompactification Etale.affineTraceOpenLeft
set_option allowUnsafeReducibility true in
attribute [local reducible] CoordinateLine.right Etale.affineTraceLineLeft
  Etale.ordinaryFiniteTensor Etale.ordinaryFinitePullback Etale.ordinaryFinitePushforward

private theorem id_homEquiv_apply
    {C : Type*} [Category C] (X Y : C) (f : X ⟶ Y) :
    Adjunction.id.homEquiv X Y f = f := by
  rw [Adjunction.homEquiv_unit]
  exact Category.id_comp f

private theorem comp_homEquiv_apply
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {J : E ⥤ D}
    (a : F ⊣ G) (b : H ⊣ J) (X : C) (Y : E) (f : H.obj (F.obj X) ⟶ Y) :
    (a.comp b).homEquiv X Y f = a.homEquiv X _ (b.homEquiv _ Y f) := by
  simp -implicitDefEqProofs only [Adjunction.homEquiv_unit, Adjunction.comp_unit_app,
    Functor.map_comp, Category.assoc]

private theorem conjugate_transpose
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    (X : C) (Y : D) (f : L₁.obj X ⟶ Y) :
    a.homEquiv X Y f ≫ (conjugateEquiv a b α).app Y =
      b.homEquiv X Y (α.app X ≫ f) := by
  rw [a.homEquiv_unit, Category.assoc, (conjugateEquiv a b α).naturality f]
  rw [← Category.assoc, unit_conjugateEquiv]
  simp -implicitDefEqProofs only [Category.assoc, ← R₂.map_comp, b.homEquiv_unit]

private theorem section_transpose
    {C D : Type*} [Category C] [Category D]
    {S : C ⥤ D} {R : D ⥤ C} {P : D ⥤ C} {Q G : C ⥤ D}
    (a : S ⊣ R) (b : P ⊣ Q) (d : P ⊣ G) (e : S ⋙ P ≅ 𝟭 C)
    (M : C) (f : S.obj M ⟶ G.obj M) :
    a.homEquiv M _ f ≫
        R.map ((conjugateIsoEquiv d b (Iso.refl P)).hom.app M) ≫
        (conjugateIsoEquiv (a.comp b) Adjunction.id e.symm).hom.app M =
      e.inv.app M ≫ P.map f ≫ d.counit.app M := by
  have hc : b.homEquiv _ M (d.counit.app M) =
      (conjugateIsoEquiv d b (Iso.refl P)).hom.app M := by
    simpa -implicitDefEqProofs only [Adjunction.homEquiv_unit, d.right_triangle_components,
      NatTrans.id_app, Category.id_comp, conjugateIsoEquiv_apply_hom, Iso.refl_hom] using
      (conjugate_transpose d b (𝟙 P) _ M (d.counit.app M)).symm
  rw [← hc, ← Category.assoc, ← a.homEquiv_naturality_right,
    ← b.homEquiv_naturality_left]
  rw [← comp_homEquiv_apply]
  simp -implicitDefEqProofs only [conjugateIsoEquiv_apply_hom, Iso.symm_hom]
  exact (conjugate_transpose (a.comp b) Adjunction.id e.inv M M
    (P.map f ≫ d.counit.app M)).trans (id_homEquiv_apply M M _)

private theorem closedProjection_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    [IsNoetherian T] (M : Etale.DerivedCategoryModule A T) :
    IsIso (closedProjection A T M) := by
  let : IsLocallyNoetherian (AffineSpace PUnit.{u + 1} T) :=
    LocallyOfFiniteType.isLocallyNoetherian (AffineSpace PUnit.{u + 1} T ↘ T)
  let : CompactSpace (AffineSpace PUnit.{u + 1} T) :=
    QuasiCompact.compactSpace_of_compactSpace (AffineSpace PUnit.{u + 1} T ↘ T)
  have hp : IsIso (Etale.ordinaryFiniteProjection A (sectionMap T)
      (Etale.ordinaryFiniteUnit A T)
      ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M)) := by
    unfold Etale.ordinaryFiniteProjection
    exact Etale.isIso_proper_projection_formula_reordered A (sectionMap T) _ _
  unfold closedProjection
  rw [(closedImage A T).map_comp]
  infer_instance

private theorem closedTensorProjection_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    [IsNoetherian T] (W M : Etale.DerivedCategoryModule A T) :
    IsIso (closedTensorProjection A T W M) := by
  let : IsLocallyNoetherian (AffineSpace PUnit.{u + 1} T) :=
    LocallyOfFiniteType.isLocallyNoetherian (AffineSpace PUnit.{u + 1} T ↘ T)
  let : CompactSpace (AffineSpace PUnit.{u + 1} T) :=
    QuasiCompact.compactSpace_of_compactSpace (AffineSpace PUnit.{u + 1} T ↘ T)
  have hp : IsIso (Etale.ordinaryFiniteProjection A (sectionMap T) W
      ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M)) := by
    unfold Etale.ordinaryFiniteProjection
    exact Etale.isIso_proper_projection_formula_reordered A (sectionMap T) _ _
  unfold closedTensorProjection
  infer_instance

private theorem tensor_adjunct
    {C D : Type*} [Category C] [Category D]
    {S : C ⥤ D} {R : D ⥤ C} (a : S ⊣ R)
    (T : C ⥤ C) (U : D ⥤ D) (p : S ⋙ U ≅ T ⋙ S)
    (I M : C) (e : T.obj I ≅ M) (V : D) (c : S.obj I ⟶ V) :
    a.homEquiv M _
        (S.map e.inv ≫ p.inv.app I ≫ U.map c) =
      e.inv ≫ T.map (a.homEquiv I V c) ≫
        a.homEquiv _ _ (p.inv.app (R.obj V) ≫ U.map (a.counit.app V)) := by
  rw [a.homEquiv_naturality_left]
  have hc : S.map (a.homEquiv I V c) ≫ a.counit.app V = c :=
    (a.homEquiv I V).symm_apply_apply c
  rw [← hc, U.map_comp, ← Category.assoc _ (U.map _) (U.map _)]
  have hn := p.inv.naturality (a.homEquiv I V c)
  dsimp only [Functor.comp_map] at hn
  rw [← hn, Category.assoc, a.homEquiv_naturality_left, hc]

private theorem tensor_adjunct_post
    {C D : Type*} [Category C] [Category D]
    {S : C ⥤ D} {R : D ⥤ C} (a : S ⊣ R)
    (T : C ⥤ C) (U : D ⥤ D) (p : S ⋙ U ≅ T ⋙ S)
    (I M : C) (e : T.obj I ≅ M) (V V' : D)
    (c : S.obj I ⟶ V) (k : U.obj V ⟶ V') :
    a.homEquiv M _ (S.map e.inv ≫ p.inv.app I ≫ U.map c ≫ k) =
      e.inv ≫ T.map (a.homEquiv I V c) ≫
        a.homEquiv _ _ (p.inv.app (R.obj V) ≫ U.map (a.counit.app V) ≫ k) := by
  have h := congrArg (fun f ↦ f ≫ R.map k) (tensor_adjunct a T U p I M e V c)
  simpa -implicitDefEqProofs only [a.homEquiv_naturality_right, Functor.map_comp, Category.assoc]
    using h

private def closedTensorProjectionIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    [IsNoetherian T] (M : Etale.DerivedCategoryModule A T) :
    closedImage A T ⋙
        (Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).obj
          ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M) ≅
      (Etale.ordinaryFiniteTensor A T).obj M ⋙ closedImage A T := by
  have := closedTensorProjection_isIso A T
  refine NatIso.ofComponents (fun W ↦ asIso (closedTensorProjection A T W M)) ?_
  intro W W' f
  dsimp only [Functor.comp_map, asIso_hom]
  unfold closedTensorProjection
  rw [← Category.assoc, ← Etale.ordinaryFiniteProjection_coefficient]
  simp -implicitDefEqProofs only [Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 2
  exact ((Etale.ordinaryFiniteTensor A T).map
    ((Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
      (sectionMap T) (AffineSpace PUnit.{u + 1} T ↘ T)
      (AffineSpace.zeroSection_comp_over PUnit.{u + 1} T)).hom.app M)).naturality f

private theorem closedProjection_eq
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (M : Etale.DerivedCategoryModule A T) :
    closedProjection A T M =
      closedTensorProjection A T (Etale.ordinaryFiniteUnit A T) M ≫
        (closedImage A T).map (Etale.derivedTensorSingleUnitIso M).hom := by
  unfold closedProjection closedTensorProjection
  rw [(closedImage A T).map_comp, Category.assoc]

private theorem coordinates_identity
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (N : ℕ) (hA : (N : A) = 0) (M : Etale.DerivedCategoryModule A T) :
    eqToHom (by unfold ordinarySourceObject; rfl) ≫
      (CoordinateLine.rightCoordinates A N hA T M).hom =
    𝟙 ((((Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).obj
      ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M)).obj
        (CoordinateLine.line A N hA T))) := by
  unfold CoordinateLine.rightCoordinates ordinarySourceObject CoordinateLine.right
    Etale.ordinaryFiniteTwistedPullback Etale.derivedTensorRight
  simp only [id_eq, Functor.comp_obj, Functor.flip_obj_obj, eqToHom_refl,
    Iso.refl_hom, Category.comp_id]

private theorem ordinaryOrientation_tensor
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible)
    (M : Etale.DerivedCategoryModule A T)
    (hpf : IsIso (closedProjection A T M))
    (hmate : IsIso (closedTensorProjection A T
      ((closedImage A T).rightAdjoint.obj (CoordinateLine.line A N hA T)) M)) :
    ordinaryOrientation A T N hN hA hT hI M hpf =
      (Etale.derivedTensorSingleUnitIso M).inv ≫
        ((Etale.ordinaryFiniteTensor A T).obj M).map
          (unitOrientation A T N hN hA hT hI) ≫
        coprojectionMate A T N hA M hmate := by
  let := hpf
  have := closedTensorProjection_isIso A T
  let k :
      (((Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).obj
        ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M)).obj
          (CoordinateLine.line A N hA T)) ⟶ (CoordinateLine.right A N hA T).obj M :=
    eqToHom (by unfold ordinarySourceObject; rfl) ≫
      (CoordinateLine.rightCoordinates A N hA T M).hom
  let Z := (((Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).obj
    ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M)).obj
      (CoordinateLine.line A N hA T))
  have hk : k = 𝟙 Z := by
    exact coordinates_identity A T N hA M
  have hp : tensorSupported A T N hN hA hT hI M hpf =
      (closedImage A T).map (Etale.derivedTensorSingleUnitIso M).inv ≫
        (closedTensorProjectionIso A T M).inv.app (Etale.ordinaryFiniteUnit A T) ≫
        ((Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).obj
          ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M)).map
            (restrictedSupported A T N hN hA hT hI) ≫ k := by
    unfold tensorSupported
    simp -implicitDefEqProofs only [closedProjection_eq, IsIso.inv_comp, ← Functor.map_inv,
      IsIso.Iso.inv_hom]
    simp -implicitDefEqProofs only [closedTensorProjectionIso, NatIso.ofComponents_inv_app,
      asIso_inv,
      id_eq, hk, Z, Category.comp_id, Category.assoc]
  unfold ordinaryOrientation
  rw [hp]
  have h := tensor_adjunct_post (closedAdjunction A T)
    ((Etale.ordinaryFiniteTensor A T).obj M)
    ((Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).obj
      ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M))
    (closedTensorProjectionIso A T M) (Etale.ordinaryFiniteUnit A T) M
    (Etale.derivedTensorSingleUnitIso M) (CoordinateLine.line A N hA T) _
    (restrictedSupported A T N hN hA hT hI) k
  simpa -implicitDefEqProofs only [unitOrientation, coprojectionMate, k,
    Iso.refl_hom, eqToHom_refl, Category.comp_id, closedTensorProjectionIso,
    NatIso.ofComponents_inv_app, asIso_inv, CoordinateLine.line] using h

private def compactTensorProjection
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (W : Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} T))
    (M : Etale.DerivedCategoryModule A T) :
    ((Etale.ordinaryFiniteTensor A T).obj M).obj ((compact A T).obj W) ⟶
      (compact A T).obj
        (((Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).obj
          ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M)).obj W) :=
  ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app M).app _ ≫
    ((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification T)).app W).app M ≫
      (compact A T).map
        (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A)
          (AffineSpace PUnit.{u + 1} T)).hom.app W).app _)

private theorem compactTensorProjection_line
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (N : ℕ) (hA : (N : A) = 0) (M : Etale.DerivedCategoryModule A T) :
    compactTensorProjection A T (CoordinateLine.line A N hA T) M =
      CoordinateLine.projection A N hA T M := by
  unfold compactTensorProjection CoordinateLine.projection
  unfold Etale.projectionMapOfCompactification
  rw [Etale.leftDerivedUpperStarCompactificationIso_eq]
  simp -implicitDefEqProofs only [Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Functor.postcompose₂, Functor.whiskeringRight, Functor.whiskeringLeft,
    Functor.whiskeringLeft₂, Functor.comp_obj,
    affineTraceLineCompactification, Etale.ordinaryFinitePushforward,
    Etale.ordinaryFinitePullback, Etale.affineTraceLineLeft, Etale.affineTraceOpenLeft,
    compact, Etale.rightDerivedLowerShriekOfCompactification,
    Iso.symm_hom, Category.assoc]

private def compactTensorProjectionNat
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (M : Etale.DerivedCategoryModule A T) :
    compact A T ⋙ (Etale.ordinaryFiniteTensor A T).obj M ⟶
      (Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).obj
        ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M) ⋙
          compact A T where
  app W := compactTensorProjection A T W M
  naturality {W W'} f := by
    let P := compact A T
    let L := Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)
    let TX := Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)
    let TT := Etale.ordinaryFiniteTensor A T
    let b := Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) T
    let c := Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A)
      (AffineSpace PUnit.{u + 1} T)
    let q := Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification T)
    have h1 : (TT.obj M).map (P.map f) ≫ (b.hom.app M).app (P.obj W') =
        (b.hom.app M).app (P.obj W) ≫ (TT.map (P.map f)).app M :=
      (b.hom.app M).naturality (P.map f)
    have h2 : (TT.map (P.map f)).app M ≫ (q.app W').app M =
        (q.app W).app M ≫ P.map ((TX.map f).app (L.obj M)) :=
      congr_app (q.naturality f) M
    let K := (Etale.upperStar (ModuleCat.{u + 1} A)
      (AffineSpace PUnit.{u + 1} T ↘ T)).leftDerivedFunctor.obj M
    have h3 : (TX.map f).app K ≫ (c.hom.app W').app K =
        (c.hom.app W).app K ≫ (TX.obj K).map f :=
      congr_app (c.hom.naturality f) K
    change (TT.obj M).map (P.map f) ≫ compactTensorProjection A T W' M =
      compactTensorProjection A T W M ≫ P.map ((TX.obj (L.obj M)).map f)
    unfold compactTensorProjection
    simp -implicitDefEqProofs only [Category.assoc]
    rw [reassoc_of% h1, reassoc_of% h2, ← P.map_comp]
    have h3' := congrArg P.map h3
    dsimp only [c, K, L, Etale.ordinaryFinitePullback] at h3' ⊢
    rw [h3', P.map_comp]

end AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
namespace AlgebraicGeometry.Etale
private def orderedShriekProjection
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (W : DerivedCategoryModule A X) (M : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj M).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W) ⟶
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((ordinaryFinitePullback A f).obj M)).obj W) :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app M).app _ ≫
    ((projectionMap (ModuleCat.{u + 1} A) f).app W).app M ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app W).app _)

private theorem canonical_symmetry_involutive
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [HasDerivedCategory.{u + 1} C] [MonoidalCategory C] [MonoidalClosed C]
    [MonoidalPreadditive C] [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C]
    (M W : DerivedCategory C) :
    ((DerivedCategory.canonicalTensorSymmetry C).hom.app M).app W ≫
      ((DerivedCategory.canonicalTensorSymmetry C).hom.app W).app M = 𝟙 _ := by
  let := DerivedCategory.symmetricCategory' C
  exact SymmetricCategory.symmetry M W
private theorem symmetry_involutive
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (M W : DerivedCategoryModule A X) :
    ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app M).app W ≫
      ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app W).app M = 𝟙 _ := by
  unfold derivedTensorSymmetry derivedTensor
  have h := canonical_symmetry_involutive
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) M W
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "missing tensor symmetry equation"
    let eq ← coordinateTensorCongrHEq target (← Lean.instantiateMVars d.type)
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
open AffineLinePurity VectorIntegrationSite
set_option allowUnsafeReducibility true in
attribute [local reducible] affineTraceLineCompactification Etale.affineTraceOpenLeft
set_option allowUnsafeReducibility true in
attribute [local semireducible] Etale.rightDerivedLowerShriek
attribute [local implicit_reducible] Etale.rightDerivedLowerShriek

section

set_option allowUnsafeReducibility true in
attribute [local irreducible] Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
  Etale.rightDerivedLowerShriekIso Etale.leftDerivedUpperStarCompSectionIso

private def canonical_shriek_projection
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    ∀ (V : Etale.DerivedCategoryModule A X) (M : Etale.DerivedCategoryModule A Y),
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).obj
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj V)).obj M ⟶
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
        (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj V).obj
          ((Etale.ordinaryFinitePullback A f).obj M)) :=
  fun V M ↦ ((Etale.projectionMap (ModuleCat.{u + 1} A) f).app V).app M

private def canonical_star_projection
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∀ (V : Etale.DerivedCategoryModule A X) (M : Etale.DerivedCategoryModule A Y),
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).obj
        ((Etale.ordinaryFinitePushforward A f).obj V)).obj M ⟶
      (Etale.ordinaryFinitePushforward A f).obj
        (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj V).obj
          ((Etale.ordinaryFinitePullback A f).obj M)) :=
  fun V M ↦ ((Etale.rightDerivedLowerStarProjectionMap
    (ModuleCat.{u + 1} A) f).app V).app M

private theorem closed_raw_projection_transfer
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (W : Etale.DerivedCategoryModule A T)
    (K : Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} T)) :
    let a := Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) (sectionMap T)
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) (AffineSpace PUnit.{u + 1} T)).map
      (a.inv.app W)).app K ≫
        ((Etale.projectionMap (ModuleCat.{u + 1} A) (sectionMap T)).app W).app K =
    ((Etale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} A) (sectionMap T)).app W).app K ≫
        a.inv.app (((Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj W).obj
          ((Etale.ordinaryFinitePullback A (sectionMap T)).obj K)) := by
  let a := Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
    (ModuleCat.{u + 1} A) (sectionMap T)
  apply inverse_projection_transfer a
    (Etale.derivedTensor (ModuleCat.{u + 1} A) (AffineSpace PUnit.{u + 1} T)) W
    (((Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj W).obj
      ((Etale.ordinaryFinitePullback A (sectionMap T)).obj K)) K
    (((Etale.projectionMap (ModuleCat.{u + 1} A) (sectionMap T)).app W).app K)
    (((Etale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} A) (sectionMap T)).app W).app K)
  have h := (Etale.projectionMap_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar
    (ModuleCat.{u + 1} A) (sectionMap T) W K).symm
  dsimp only [a] at h ⊢
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.reverse.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "missing proper projection comparison"
    let eq ← AlgebraicGeometry.Etale.coordinateProjectionCongrHEq target
      (← Lean.instantiateMVars d.type)
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

private def canonical_section_coefficient
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (V M : Etale.DerivedCategoryModule A T) :
    ((Etale.ordinaryFiniteTensor A T).obj
      ((Etale.ordinaryFinitePullback A (sectionMap T)).obj
        ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M))).obj V ⟶
      ((Etale.ordinaryFiniteTensor A T).obj M).obj V := by
  simpa -implicitDefEqProofs only [Functor.comp_obj, Functor.id_obj] using
    ((Etale.ordinaryFiniteTensor A T).map
    ((Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
      (sectionMap T) (AffineSpace PUnit.{u + 1} T ↘ T)
      (AffineSpace.zeroSection_comp_over PUnit.{u + 1} T)).hom.app M)).app V

private theorem closedTensorProjection_native_eq
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (V M : Etale.DerivedCategoryModule A T) :
    closedTensorProjection A T V M =
      ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A)
        (AffineSpace PUnit.{u + 1} T)).hom.app
          ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M)).app
            ((Etale.ordinaryFinitePushforward A (sectionMap T)).obj V) ≫
      canonical_star_projection A (sectionMap T) V
        ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M) ≫
      (Etale.ordinaryFinitePushforward A (sectionMap T)).map
        (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app V).app
          ((Etale.ordinaryFinitePullback A (sectionMap T)).obj
            ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M)) ≫
            canonical_section_coefficient A T V M) := by
  unfold closedTensorProjection Etale.ordinaryFiniteProjection
    canonical_star_projection canonical_section_coefficient
  simp -implicitDefEqProofs only [Functor.map_comp, Functor.comp_obj, Functor.id_obj,
    Category.assoc]

private def cachedClosedTransfer
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :
    Etale.ordinaryFinitePushforward A (sectionMap T) ⟶
      Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (sectionMap T) :=
  (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
    (ModuleCat.{u + 1} A) (sectionMap T)).inv

private theorem closed_canonical_projection_transfer
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (W : Etale.DerivedCategoryModule A T)
    (K : Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} T)) :
    ((Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).map
      ((cachedClosedTransfer A T).app W)).app K ≫
      canonical_shriek_projection A (sectionMap T) W K =
    canonical_star_projection A (sectionMap T) W K ≫
      (cachedClosedTransfer A T).app
          (((Etale.ordinaryFiniteTensor A T).obj W).obj
            ((Etale.ordinaryFinitePullback A (sectionMap T)).obj K)) := by
  have h := closed_raw_projection_transfer A T W K
  dsimp only [canonical_shriek_projection, canonical_star_projection]
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.reverse.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "missing native equation"
    let eq ← AlgebraicGeometry.Etale.coordinateProjectionCongrHEq target
      (← Lean.instantiateMVars d.type)
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

private def closedNativeF
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Etale.DerivedCategoryModule A T ⥤
      Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} T) :=
  Etale.ordinaryFinitePushforward A (sectionMap T)
private def closedNativeG
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Etale.DerivedCategoryModule A T ⥤
      Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} T) :=
  Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (sectionMap T)
private def closedNativeL
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} T) ⥤
      Etale.DerivedCategoryModule A T :=
  Etale.ordinaryFinitePullback A (sectionMap T)
private def closedNativeTensor
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    Etale.DerivedCategoryModule A X ⥤
      Etale.DerivedCategoryModule A X ⥤ Etale.DerivedCategoryModule A X :=
  Etale.derivedTensor (ModuleCat.{u + 1} A) X
private def closedNativeSymmetry
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    closedNativeTensor A X ≅ (closedNativeTensor A X).flip :=
  Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) X
private def closedNativeTransfer
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :
    closedNativeF A T ⟶ closedNativeG A T :=
  (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
    (ModuleCat.{u + 1} A) (sectionMap T)).inv
private def closedNativeProjectionP
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    ∀ W K,
      ((closedNativeTensor A (AffineSpace PUnit.{u + 1} T)).obj
        ((closedNativeF A T).obj W)).obj K ⟶
      (closedNativeF A T).obj
        (((closedNativeTensor A T).obj W).obj ((closedNativeL A T).obj K)) :=
  canonical_star_projection A (sectionMap T)
private def closedNativeProjectionQ
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    ∀ W K,
      ((closedNativeTensor A (AffineSpace PUnit.{u + 1} T)).obj
        ((closedNativeG A T).obj W)).obj K ⟶
      (closedNativeG A T).obj
        (((closedNativeTensor A T).obj W).obj ((closedNativeL A T).obj K)) :=
  canonical_shriek_projection A (sectionMap T)

private theorem closedNativeProjectionTransfer
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (W : Etale.DerivedCategoryModule A T)
    (K : Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} T)) :
    ((closedNativeTensor A (AffineSpace PUnit.{u + 1} T)).map
      ((closedNativeTransfer A T).app W)).app K ≫
      closedNativeProjectionQ A T W K =
    closedNativeProjectionP A T W K ≫
      (closedNativeTransfer A T).app
        (((closedNativeTensor A T).obj W).obj ((closedNativeL A T).obj K)) := by
  have h := closed_canonical_projection_transfer A T W K
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.reverse.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "missing native equation"
    let eq ← AlgebraicGeometry.Etale.coordinateProjectionCongrHEq target
      (← Lean.instantiateMVars d.type)
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

private theorem closedOrdered_transfer_native
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (V M : Etale.DerivedCategoryModule A T) :
    ((Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).obj
      ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M)).map
        ((Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) (sectionMap T)).inv.app V) ≫
      Etale.orderedShriekProjection A (sectionMap T) V
        ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M) ≫
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (sectionMap T)).map
        (canonical_section_coefficient A T V M) =
    (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A)
        (AffineSpace PUnit.{u + 1} T)).hom.app
          ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M)).app
            ((Etale.ordinaryFinitePushforward A (sectionMap T)).obj V) ≫
      canonical_star_projection A (sectionMap T) V
        ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M) ≫
      (Etale.ordinaryFinitePushforward A (sectionMap T)).map
        (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app V).app
          ((Etale.ordinaryFinitePullback A (sectionMap T)).obj
            ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M)) ≫
            canonical_section_coefficient A T V M)) ≫
      (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} A) (sectionMap T)).inv.app
          (((Etale.ordinaryFiniteTensor A T).obj M).obj V) := by
  have h := ordered_projection_transfer_post (closedNativeTransfer A T)
    (closedNativeTensor A T) (closedNativeTensor A (AffineSpace PUnit.{u + 1} T))
    (closedNativeL A T) (closedNativeSymmetry A T)
    (closedNativeSymmetry A (AffineSpace PUnit.{u + 1} T))
    (closedNativeProjectionP A T) (closedNativeProjectionQ A T)
    (closedNativeProjectionTransfer A T) V
    ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M)
    (((Etale.ordinaryFiniteTensor A T).obj M).obj V)
    (canonical_section_coefficient A T V M)
  dsimp only [Etale.orderedShriekProjection]
  simp -implicitDefEqProofs only [Category.assoc] at h ⊢
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.reverse.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "missing native equation"
    let eq ← AlgebraicGeometry.Etale.coordinateProjectionCongrHEq target
      (← Lean.instantiateMVars d.type)
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

private theorem closedOrdered_transport
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (V M : Etale.DerivedCategoryModule A T) :
    ((Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).obj
      ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M)).map
        ((Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) (sectionMap T)).inv.app V) ≫
      Etale.orderedShriekProjection A (sectionMap T) V
        ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M) ≫
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (sectionMap T)).map
        (canonical_section_coefficient A T V M) =
    closedTensorProjection A T V M ≫
      (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} A) (sectionMap T)).inv.app
          (((Etale.ordinaryFiniteTensor A T).obj M).obj V) := by
  rw [closedTensorProjection_native_eq]
  exact closedOrdered_transfer_native A T V M

private theorem section_compactification (T : Scheme.{u}) :
    HasCompactification (sectionMap T ≫ (AffineSpace PUnit.{u + 1} T ↘ T)) :=
  HasCompactification.of_eq (AffineSpace.zeroSection_comp_over PUnit.{u + 1} T).symm

attribute [local instance] section_compactification

private def chosenCoordinateComposition
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :
    Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (sectionMap T) ⋙
      Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (AffineSpace PUnit.{u + 1} T ↘ T) ≅ 𝟭 (Etale.DerivedCategoryModule A T) :=
  Etale.unboundedEtaleLowerShriekCompIso A (sectionMap T)
      (AffineSpace PUnit.{u + 1} T ↘ T) ≪≫
    Etale.unboundedEtaleLowerShriekCongr A
      (AffineSpace.zeroSection_comp_over PUnit.{u + 1} T) ≪≫
    Etale.unboundedEtaleLowerShriekId A T

private def chosenSectionOrderedProjection
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (V M : Etale.DerivedCategoryModule A T) :
    ((Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).obj
      ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M)).obj
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (sectionMap T)).obj V) ⟶
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (sectionMap T)).obj
        (((Etale.ordinaryFiniteTensor A T).obj M).obj V) :=
  Etale.orderedShriekProjection A (sectionMap T) V
      ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M) ≫
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (sectionMap T)).map
      (canonical_section_coefficient A T V M)

private theorem chosen_canonical_section_projection
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) [IsNoetherian T]
    (W M : Etale.DerivedCategoryModule A T) :
    ((Etale.ordinaryFiniteTensor A T).map
      ((chosenCoordinateComposition A T).inv.app W)).app M ≫
      canonical_shriek_projection A (AffineSpace PUnit.{u + 1} T ↘ T)
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (sectionMap T)).obj W) M ≫
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (AffineSpace PUnit.{u + 1} T ↘ T)).map
          (canonical_shriek_projection A (sectionMap T) W
            ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M)) ≫
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (AffineSpace PUnit.{u + 1} T ↘ T)).map
          ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (sectionMap T)).map
            (((Etale.ordinaryFiniteTensor A T).obj W).map
              ((Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
                (sectionMap T) (AffineSpace PUnit.{u + 1} T ↘ T)
                (AffineSpace.zeroSection_comp_over PUnit.{u + 1} T)).hom.app M))) =
    (chosenCoordinateComposition A T).inv.app
      (((Etale.ordinaryFiniteTensor A T).obj W).obj M) := by
  have h := Etale.chosen_section_projection A (sectionMap T)
    (AffineSpace PUnit.{u + 1} T ↘ T)
    (AffineSpace.zeroSection_comp_over PUnit.{u + 1} T) W M
  dsimp only [chosenCoordinateComposition, canonical_shriek_projection]
  dsimp only at h
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.reverse.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "missing native equation"
    let eq ← AlgebraicGeometry.Etale.coordinateProjectionCongrHEq target
      (← Lean.instantiateMVars d.type)
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

private theorem chosen_ordered_section_square
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) [IsNoetherian T]
    (W M : Etale.DerivedCategoryModule A T) :
    ((Etale.ordinaryFiniteTensor A T).obj M).map
        ((chosenCoordinateComposition A T).inv.app W) ≫
      Etale.orderedShriekProjection A (AffineSpace PUnit.{u + 1} T ↘ T)
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (sectionMap T)).obj W) M ≫
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (AffineSpace PUnit.{u + 1} T ↘ T)).map (chosenSectionOrderedProjection A T W M) =
    (chosenCoordinateComposition A T).inv.app
      (((Etale.ordinaryFiniteTensor A T).obj M).obj W) := by
  have h := ordered_section_projection
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (sectionMap T))
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace PUnit.{u + 1} T ↘ T))
    (Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T))
    (Etale.ordinaryFinitePullback A (sectionMap T))
    (Etale.ordinaryFiniteTensor A T)
    (Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T))
    (Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) T)
    (Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) (AffineSpace PUnit.{u + 1} T))
    (Etale.symmetry_involutive A T)
    (Etale.symmetry_involutive A (AffineSpace PUnit.{u + 1} T))
    (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) (sectionMap T)
      (AffineSpace PUnit.{u + 1} T ↘ T) (AffineSpace.zeroSection_comp_over PUnit.{u + 1} T))
    (chosenCoordinateComposition A T)
    (canonical_shriek_projection A (sectionMap T))
    (canonical_shriek_projection A (AffineSpace PUnit.{u + 1} T ↘ T)) W M
    (chosen_canonical_section_projection A T W M)
  dsimp only [chosenSectionOrderedProjection, Etale.orderedShriekProjection,
    canonical_shriek_projection, canonical_section_coefficient]
  dsimp only [canonical_shriek_projection] at h
  simp -implicitDefEqProofs only [Functor.map_comp, Category.assoc] at h ⊢
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.reverse.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "missing section projection equation"
    let eq ← AlgebraicGeometry.Etale.coordinateProjectionCongrHEq target
      (← Lean.instantiateMVars d.type)
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

-- This proof instance must inline to avoid expanding the compactification during conversion.
set_option linter.style.haveILetI false in
private theorem compactOrdered_transport
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (W : Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} T))
    (M : Etale.DerivedCategoryModule A T) :
    letI : HasCompactification (AffineSpace PUnit.{u + 1} T ↘ T) :=
      (affineTraceLineCompactification T).hasCompactification
    let b := Etale.rightDerivedLowerShriekIso A (affineTraceLineCompactification T)
    ((Etale.ordinaryFiniteTensor A T).obj M).map (b.hom.app W) ≫
      Etale.orderedShriekProjection A (AffineSpace PUnit.{u + 1} T ↘ T) W M =
    compactTensorProjection A T W M ≫
      b.hom.app (((Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).obj
        ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M)).obj W) := by
  letI : HasCompactification (AffineSpace PUnit.{u + 1} T ↘ T) :=
    (affineTraceLineCompactification T).hasCompactification
  simpa -implicitDefEqProofs only [Etale.orderedShriekProjection,
    compactTensorProjection, Category.assoc] using ordered_projection_transfer
    (Etale.rightDerivedLowerShriekIso A (affineTraceLineCompactification T)).hom
    (Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T))
    (Etale.ordinaryFiniteTensor A T)
    (Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T))
    (Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) (AffineSpace PUnit.{u + 1} T))
    (Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) T)
    (fun V K ↦ ((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification T)).app V).app K)
    (fun V K ↦ ((Etale.projectionMap (ModuleCat.{u + 1} A)
      (AffineSpace PUnit.{u + 1} T ↘ T)).app V).app K)
    (fun V K ↦ (Etale.projectionMapOfCompactification_rightDerivedLowerShriekIso
      A (affineTraceLineCompactification T) V K).symm) W M
section

set_option allowUnsafeReducibility true in
attribute [local irreducible] Etale.rightDerivedLowerShriekIso

private def chosenClosedComparison
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :
    closedImage A T ≅ Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (sectionMap T) :=
  (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
    (ModuleCat.{u + 1} A) (sectionMap T)).symm

private def chosenCompactComparison
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :
    compact A T ≅ Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace PUnit.{u + 1} T ↘ T) :=
  Etale.rightDerivedLowerShriekIso A (affineTraceLineCompactification T)

private theorem compactTensorProjection_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    {W W' : Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} T)} (f : W ⟶ W')
    (M : Etale.DerivedCategoryModule A T) :
    ((Etale.ordinaryFiniteTensor A T).obj M).map ((compact A T).map f) ≫
        compactTensorProjection A T W' M =
      compactTensorProjection A T W M ≫
        (compact A T).map
          (((Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).obj
            ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M)).map f) := by
  have h := (compactTensorProjectionNat A T M).naturality f
  simpa -implicitDefEqProofs only [compactTensorProjectionNat, Functor.comp_map] using h

private def sectionNativeS
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Etale.DerivedCategoryModule A T ⥤
      Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} T) :=
  Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (sectionMap T)
private def sectionNativeP
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :
    Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} T) ⥤
      Etale.DerivedCategoryModule A T := compact A T
private def sectionNativeP'
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} T) ⥤
      Etale.DerivedCategoryModule A T :=
  Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
    (AffineSpace PUnit.{u + 1} T ↘ T)
private def sectionNativeL
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Etale.DerivedCategoryModule A T ⥤
      Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} T) :=
  Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)
private def sectionNativeTensor
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    Etale.DerivedCategoryModule A X ⥤
      Etale.DerivedCategoryModule A X ⥤ Etale.DerivedCategoryModule A X :=
  Etale.ordinaryFiniteTensor A X
private def sectionNativeTargetTensor
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (M : Etale.DerivedCategoryModule A T) :
    Etale.DerivedCategoryModule A T ⥤ Etale.DerivedCategoryModule A T :=
  (sectionNativeTensor A T).obj M
private def sectionNativeSourceTensor
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (M : Etale.DerivedCategoryModule A T) :
    Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} T) ⥤
      Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} T) :=
  (sectionNativeTensor A (AffineSpace PUnit.{u + 1} T)).obj ((sectionNativeL A T).obj M)
private def sectionNativeClosedIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :
    closedImage A T ≅ sectionNativeS A T := chosenClosedComparison A T
private def sectionNativeCompactIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :
    sectionNativeP A T ≅ sectionNativeP' A T := chosenCompactComparison A T
private def sectionNativeComposition
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :
    sectionNativeS A T ⋙ sectionNativeP' A T ≅ 𝟭 (Etale.DerivedCategoryModule A T) :=
  chosenCoordinateComposition A T
private def sectionNativeClosedProjection
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :
    ∀ M V, (sectionNativeSourceTensor A T M).obj ((closedImage A T).obj V) ⟶
      (closedImage A T).obj ((sectionNativeTargetTensor A T M).obj V) :=
  fun M V ↦ closedTensorProjection A T V M
private def sectionNativeCompactProjection
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :
    ∀ M W, (sectionNativeTargetTensor A T M).obj ((sectionNativeP A T).obj W) ⟶
      (sectionNativeP A T).obj ((sectionNativeSourceTensor A T M).obj W) :=
  fun M W ↦ compactTensorProjection A T W M
private def sectionNativeOrderedS
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :
    ∀ M V, (sectionNativeSourceTensor A T M).obj ((sectionNativeS A T).obj V) ⟶
      (sectionNativeS A T).obj ((sectionNativeTargetTensor A T M).obj V) :=
  fun M V ↦ chosenSectionOrderedProjection A T V M
private def sectionNativeOrderedP
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :
    ∀ M W, (sectionNativeTargetTensor A T M).obj ((sectionNativeP' A T).obj W) ⟶
      (sectionNativeP' A T).obj ((sectionNativeSourceTensor A T M).obj W) :=
  fun M W ↦ Etale.orderedShriekProjection A
    (AffineSpace PUnit.{u + 1} T ↘ T) W M

private theorem sectionNativeCompactNaturality
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (M : Etale.DerivedCategoryModule A T)
    {W W' : Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} T)} (f : W ⟶ W') :
    (sectionNativeTargetTensor A T M).map ((sectionNativeP A T).map f) ≫
        sectionNativeCompactProjection A T M W' =
      sectionNativeCompactProjection A T M W ≫
        (sectionNativeP A T).map ((sectionNativeSourceTensor A T M).map f) := by
  have h := compactTensorProjection_naturality A T f M
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.reverse.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "missing native section equation"
    let eq ← AlgebraicGeometry.Etale.coordinateProjectionCongrHEq target
      (← Lean.instantiateMVars d.type)
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

private theorem sectionNativeClosedCompatibility
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (M V : Etale.DerivedCategoryModule A T) :
    (sectionNativeSourceTensor A T M).map ((sectionNativeClosedIso A T).hom.app V) ≫
        sectionNativeOrderedS A T M V =
      sectionNativeClosedProjection A T M V ≫
        (sectionNativeClosedIso A T).hom.app ((sectionNativeTargetTensor A T M).obj V) := by
  have h := closedOrdered_transport A T V M
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.reverse.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "missing native section equation"
    let eq ← AlgebraicGeometry.Etale.coordinateProjectionCongrHEq target
      (← Lean.instantiateMVars d.type)
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

private theorem sectionNativeCompactCompatibility
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (M : Etale.DerivedCategoryModule A T)
    (V : Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} T)) :
    (sectionNativeTargetTensor A T M).map ((sectionNativeCompactIso A T).hom.app V) ≫
        sectionNativeOrderedP A T M V =
      sectionNativeCompactProjection A T M V ≫
        (sectionNativeCompactIso A T).hom.app ((sectionNativeSourceTensor A T M).obj V) := by
  have h := compactOrdered_transport A T V M
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.reverse.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "missing native section equation"
    let eq ← AlgebraicGeometry.Etale.coordinateProjectionCongrHEq target
      (← Lean.instantiateMVars d.type)
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

private theorem sectionNativeChosenProjection
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) [IsNoetherian T]
    (M W : Etale.DerivedCategoryModule A T) :
    (sectionNativeTargetTensor A T M).map ((sectionNativeComposition A T).inv.app W) ≫
        sectionNativeOrderedP A T M ((sectionNativeS A T).obj W) ≫
        (sectionNativeP' A T).map (sectionNativeOrderedS A T M W) =
      (sectionNativeComposition A T).inv.app ((sectionNativeTargetTensor A T M).obj W) := by
  have h := chosen_ordered_section_square A T W M
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.reverse.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "missing native section equation"
    let eq ← AlgebraicGeometry.Etale.coordinateProjectionCongrHEq target
      (← Lean.instantiateMVars d.type)
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

private theorem sectionNativeTransportedProjection
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) [IsNoetherian T]
    (M W : Etale.DerivedCategoryModule A T) :
    let e := Functor.isoWhiskerRight (sectionNativeClosedIso A T) (sectionNativeP A T) ≪≫
      Functor.isoWhiskerLeft (sectionNativeS A T) (sectionNativeCompactIso A T) ≪≫
      sectionNativeComposition A T
    (sectionNativeTargetTensor A T M).map (e.inv.app W) ≫
        sectionNativeCompactProjection A T M ((closedImage A T).obj W) ≫
        (sectionNativeP A T).map (sectionNativeClosedProjection A T M W) =
      e.inv.app ((sectionNativeTargetTensor A T M).obj W) := by
  exact section_projection_transport_maps
    (sectionNativeTargetTensor A T M) (sectionNativeSourceTensor A T M)
    (sectionNativeClosedIso A T) (sectionNativeCompactIso A T)
    (sectionNativeComposition A T) (sectionNativeClosedProjection A T M)
    (sectionNativeCompactProjection A T M) (sectionNativeOrderedS A T M)
    (sectionNativeOrderedP A T M) (fun {V V'} f ↦ sectionNativeCompactNaturality A T M f)
    (sectionNativeClosedCompatibility A T M) (sectionNativeCompactCompatibility A T M)
    W (sectionNativeChosenProjection A T M W)

private def sectionNativeNormalizedComparison
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :
    closedImage A T ⋙ sectionNativeP A T ≅ 𝟭 (Etale.DerivedCategoryModule A T) :=
  Functor.isoWhiskerRight (sectionNativeClosedIso A T) (sectionNativeP A T) ≪≫
    Functor.isoWhiskerLeft (sectionNativeS A T) (sectionNativeCompactIso A T) ≪≫
    sectionNativeComposition A T

private theorem sectionNativeComparison_eq
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :
    sectionComposition A T = sectionNativeNormalizedComparison A T := by
  dsimp only [sectionComposition, sectionNativeNormalizedComparison,
    sectionNativeClosedIso, sectionNativeCompactIso, chosenClosedComparison,
    chosenCompactComparison, sectionNativeComposition, chosenCoordinateComposition,
    sectionNativeP, sectionNativeP', sectionNativeS]

set_option maxHeartbeats 800000 in
-- Comparing the fixed derived-category instance dictionaries needs a larger tactic budget.
private theorem section_projection_square
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) [IsNoetherian T]
    (W M : Etale.DerivedCategoryModule A T) :
    ((Etale.ordinaryFiniteTensor A T).obj M).map ((sectionComposition A T).inv.app W) ≫
      compactTensorProjection A T ((closedImage A T).obj W) M ≫
      (compact A T).map (closedTensorProjection A T W M) =
    (sectionComposition A T).inv.app (((Etale.ordinaryFiniteTensor A T).obj M).obj W) := by
  rw [sectionNativeComparison_eq]
  have h := sectionNativeTransportedProjection A T M W
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.reverse.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "missing native section equation"
    let eq ← AlgebraicGeometry.Etale.coordinateFoldedCongrHEq target
      (← Lean.instantiateMVars d.type)
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

end

end

private theorem tensorSupported_eq
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible)
    (M : Etale.DerivedCategoryModule A T) (hpf : IsIso (closedProjection A T M)) :
    tensorSupported A T N hN hA hT hI M hpf =
    (closedImage A T).map (Etale.derivedTensorSingleUnitIso M).inv ≫
      (closedTensorProjectionIso A T M).inv.app (Etale.ordinaryFiniteUnit A T) ≫
      ((Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).obj
        ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M)).map
          (restrictedSupported A T N hN hA hT hI)  := by
  let := hpf
  have := closedTensorProjection_isIso A T (Etale.ordinaryFiniteUnit A T) M
  unfold tensorSupported
  simp -implicitDefEqProofs only [closedProjection_eq, IsIso.inv_comp, ← Functor.map_inv,
    IsIso.Iso.inv_hom, closedTensorProjectionIso, NatIso.ofComponents_inv_app,
    asIso_inv, id_eq, Category.assoc]

private theorem trace_section_unit
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) [IsNoetherian T]
    (M : Etale.DerivedCategoryModule A T) :
    (sectionComposition A T).inv.app M ≫
        (compact A T).map ((closedImage A T).map (Etale.derivedTensorSingleUnitIso M).inv ≫
          (closedTensorProjectionIso A T M).inv.app (Etale.ordinaryFiniteUnit A T)) =
      (Etale.derivedTensorSingleUnitIso M).inv ≫
        ((Etale.ordinaryFiniteTensor A T).obj M).map
          ((sectionComposition A T).inv.app (Etale.ordinaryFiniteUnit A T)) ≫
        compactTensorProjection A T ((closedImage A T).obj
          (Etale.ordinaryFiniteUnit A T)) M := by
  exact section_projection_unit (closedImage A T) (compact A T)
    ((Etale.ordinaryFiniteTensor A T).obj M)
    ((Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).obj
      ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M))
    (sectionComposition A T) (Etale.ordinaryFiniteUnit A T) M
    (Etale.derivedTensorSingleUnitIso M) (closedTensorProjectionIso A T M)
    (compactTensorProjectionNat A T M)
    (section_projection_square A T (Etale.ordinaryFiniteUnit A T) M)

private theorem trace_projection_counit
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) (M : Etale.DerivedCategoryModule A T) :
    compactTensorProjection A T (CoordinateLine.line A N hA T) M ≫
      (CoordinateLine.adjunction A N hA T hN hT).counit.app M =
    ((Etale.ordinaryFiniteTensor A T).obj M).map
      (CoordinateLine.integration A N hA T hN hT) ≫
        (Etale.derivedTensorSingleUnitIso M).hom := by
  rw [compactTensorProjection_line]
  exact CoordinateLine.projection_counit A N hA T hN hT M

private theorem tensor_trace
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible)
    (M : Etale.DerivedCategoryModule A T) (hpf : IsIso (closedProjection A T M)) :
    (sectionComposition A T).inv.app M ≫
      (compact A T).map (tensorSupported A T N hN hA hT hI M hpf) ≫
      (CoordinateLine.adjunction A N hA T hN hT).counit.app M =
    (Etale.derivedTensorSingleUnitIso M).inv ≫
      ((Etale.ordinaryFiniteTensor A T).obj M).map
        ((sectionComposition A T).inv.app (Etale.ordinaryFiniteUnit A T) ≫
          (compact A T).map (restrictedSupported A T N hN hA hT hI) ≫
          CoordinateLine.integration A N hA T hN hT) ≫
      (Etale.derivedTensorSingleUnitIso M).hom := by
  let := hpf
  have := closedTensorProjection_isIso A T (Etale.ordinaryFiniteUnit A T) M
  have hp := tensorSupported_eq A T N hN hA hT hI M hpf
  rw [hp]
  let TF := (Etale.ordinaryFiniteTensor A T).obj M
  let UF := (Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).obj
    ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M)
  have hs := trace_section_unit A T M
  apply supported_tensor_trace (closedImage A T) (compact A T) TF UF
    (sectionComposition A T) (Etale.ordinaryFiniteUnit A T) M
    (Etale.derivedTensorSingleUnitIso M) (closedTensorProjectionIso A T M)
    (compactTensorProjectionNat A T M) (CoordinateLine.line A N hA T)
    (restrictedSupported A T N hN hA hT hI)
    (CoordinateLine.integration A N hA T hN hT)
    ((CoordinateLine.adjunction A N hA T hN hT).counit.app M) hs
  exact trace_projection_counit A T N hN hA hT M

end AlgebraicGeometry.ProEtale.CoordinateSectionNormalization

namespace AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
open AffineLinePurity VectorIntegrationSite
set_option allowUnsafeReducibility true in
attribute [local reducible] affineTraceLineCompactification Etale.affineTraceOpenLeft
attribute [local irreducible] conjugateIsoEquiv
private def compactCoordinateAdjunction
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) :
    compact A T ⊣ CoordinateLine.right A N hA T :=
  CoordinateLine.adjunction A N hA T hN hT

private theorem comparison_hom_eq
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) (M : Etale.DerivedCategoryModule A T) :
    (CoordinateLine.comparison A N hA T hN hT).hom.app M =
      (conjugateIsoEquiv (compactCoordinateAdjunction A T N hN hA hT)
        (compactAdjunction A T) (Iso.refl (compact A T))).hom.app M := by
  unfold CoordinateLine.comparison CoordinateLine.exceptionalAdjunction
    compactAdjunction compactCoordinateAdjunction
  rfl

private theorem ordinaryOrientation_transpose
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible)
    (M : Etale.DerivedCategoryModule A T) (hpf : IsIso (closedProjection A T M)) :
    ordinaryOrientation A T N hN hA hT hI M hpf ≫
      (closedImage A T).rightAdjoint.map
        ((CoordinateLine.comparison A N hA T hN hT).hom.app M) ≫
      (exceptionalComposition A T).hom.app M =
    (sectionComposition A T).inv.app M ≫
      (compact A T).map (tensorSupported A T N hN hA hT hI M hpf) ≫
      (CoordinateLine.adjunction A N hA T hN hT).counit.app M := by
  unfold ordinaryOrientation exceptionalComposition
  rw [comparison_hom_eq]
  have h := section_transpose (closedAdjunction A T) (compactAdjunction A T)
    (compactCoordinateAdjunction A T N hN hA hT) (sectionComposition A T) M
    (tensorSupported A T N hN hA hT hI M hpf)
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "missing comparison equation"
    let eq ← AlgebraicGeometry.Etale.coordinateTensorCongrHEq target
      (← Lean.instantiateMVars d.type)
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

private theorem lineCounit_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) (M : Etale.DerivedCategoryModule A T) :
    IsIso ((CoordinateLine.adjunction A N hA T hN hT).counit.app M) := by
  unfold CoordinateLine.adjunction
  rw [Adjunction.ofNatIsoRight_counit]
  simp -implicitDefEqProofs only [NatTrans.comp_app, Functor.whiskerRight_app]
  have := Etale.affineTraceLineCounit_isIso A N hN hA
    (Etale.projectiveLineTraceTransport N hN A hA) T hT
    (Etale.projectiveLineTraceDatum N hN A hA T hT) M
  infer_instance

private theorem integration_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) :
    IsIso (CoordinateLine.integration A N hA T hN hT) := by
  let I := Etale.ordinaryFiniteUnit A T
  let F := (Etale.ordinaryFiniteTensor A T).obj I
  let e : F ≅ 𝟭 (Etale.DerivedCategoryModule A T) :=
    (Etale.ordinaryFiniteTensor A T).mapIso
      (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T) ≪≫
        Etale.derivedTensorUnitLeftUnitor (ModuleCat.{u + 1} A) T
  let : (𝟭 (Etale.DerivedCategoryModule A T)).IsEquivalence := Functor.isEquivalence_refl
  let : F.IsEquivalence := Functor.isEquivalence_of_iso e.symm
  have := lineCounit_isIso A T N hN hA hT I
  have := Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite A (ProjectiveLine T ↘ T)
  have hp : IsIso (CoordinateLine.projection A N hA T I) := by
    unfold CoordinateLine.projection
    dsimp only
    infer_instance
  have h := CoordinateLine.projection_counit A N hA T hN hT I
  have hi : IsIso (F.map (CoordinateLine.integration A N hA T hN hT) ≫
      (Etale.derivedTensorSingleUnitIso I).hom) := by
    rw [← h]
    infer_instance
  have : IsIso (F.map (CoordinateLine.integration A N hA T hN hT)) :=
    (isIso_comp_right_iff _ _).mp hi
  exact isIso_of_reflects_iso _ F

private def lineUnitIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (N : ℕ) (hA : (N : A) = 0) :
    (CoordinateLine.right A N hA T).obj (Etale.ordinaryFiniteUnit A T) ≅
      CoordinateLine.line A N hA T := by
  unfold CoordinateLine.right Etale.ordinaryFiniteTwistedPullback Etale.derivedTensorRight
  exact ((Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).mapIso
      (Etale.ordinaryFiniteUnitPullback A (AffineSpace PUnit.{u + 1} T ↘ T))).app _ ≪≫
    ((Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).mapIso
      (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A)
        (AffineSpace PUnit.{u + 1} T))).app _ ≪≫
    (Etale.derivedTensorUnitLeftUnitor (ModuleCat.{u + 1} A)
      (AffineSpace PUnit.{u + 1} T)).app _

private theorem section_adjunct_isIso
    {C D : Type*} [Category C] [Category D]
    {S : C ⥤ D} {R : D ⥤ C} {P : D ⥤ C} {G : C ⥤ D}
    (a : S ⊣ R) (d : P ⊣ G) (e : S ⋙ P ≅ 𝟭 C)
    (X : C) (Y : D) (j : Y ≅ G.obj X) (f : S.obj X ⟶ Y)
    [IsIso (P.map f)] [IsIso (d.counit.app X)] :
    IsIso (a.homEquiv X Y f) := by
  let : (𝟭 C).IsEquivalence := Functor.isEquivalence_refl
  let : (S ⋙ P).IsEquivalence := Functor.isEquivalence_of_iso e.symm
  have hi : IsIso ((a.comp d).homEquiv X X
      (P.map (f ≫ j.hom) ≫ d.counit.app X)) := by
    rw [Adjunction.homEquiv_unit, P.map_comp]
    infer_instance
  have hh : (a.comp d).homEquiv X X
      (P.map (f ≫ j.hom) ≫ d.counit.app X) =
      a.homEquiv X Y f ≫ R.map j.hom := by
    rw [comp_homEquiv_apply]
    rw [d.homEquiv_naturality_left]
    simp -implicitDefEqProofs only [Adjunction.homEquiv_unit, d.right_triangle_components,
      Category.comp_id, a.homEquiv_naturality_right]
  rw [hh] at hi
  exact (isIso_comp_right_iff _ _).mp hi

private theorem unitOrientation_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible)
    (hnorm : (sectionComposition A T).inv.app (Etale.ordinaryFiniteUnit A T) ≫
      (compact A T).map (restrictedSupported A T N hN hA hT hI) ≫
      CoordinateLine.integration A N hA T hN hT = 𝟙 _) :
    IsIso (unitOrientation A T N hN hA hT hI) := by
  have := integration_isIso A T N hN hA hT
  have hi : IsIso ((sectionComposition A T).inv.app (Etale.ordinaryFiniteUnit A T) ≫
      (compact A T).map (restrictedSupported A T N hN hA hT hI) ≫
      CoordinateLine.integration A N hA T hN hT) := by
    rw [hnorm]
    infer_instance
  rw [← Category.assoc] at hi
  have hi' := (isIso_comp_right_iff _ _).mp hi
  have hmap : IsIso ((compact A T).map (restrictedSupported A T N hN hA hT hI)) :=
    (isIso_comp_left_iff _ _).mp hi'
  have := lineCounit_isIso A T N hN hA hT (Etale.ordinaryFiniteUnit A T)
  have : IsIso ((Etale.affineTraceLineLeft A T).map
      (restrictedSupported A T N hN hA hT hI)) := by
    change IsIso ((compact A T).map (restrictedSupported A T N hN hA hT hI))
    exact hmap
  exact section_adjunct_isIso (closedAdjunction A T)
    (CoordinateLine.adjunction A N hA T hN hT) (sectionComposition A T)
    _ _ (lineUnitIso A T N hA).symm _

private theorem scalar_identity
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (I : C) (M : D)
    (r : F.obj I ≅ M) : r.inv ≫ F.map (𝟙 I) ≫ r.hom = 𝟙 M := by
  rw [F.map_id, Category.id_comp, Iso.inv_hom_id]

private theorem normalized_tensor_trace
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible)
    (hnorm : ((sectionComposition A T).inv.app (Etale.ordinaryFiniteUnit A T) ≫
    (compact A T).map (restrictedSupported A T N hN hA hT hI) ≫
      CoordinateLine.integration A N hA T hN hT = 𝟙 _))
    (M : Etale.DerivedCategoryModule A T)
      (hpf : IsIso (closedProjection A T M)) :
      (sectionComposition A T).inv.app M ≫
        (compact A T).map (tensorSupported A T N hN hA hT hI M hpf) ≫
        (CoordinateLine.adjunction A N hA T hN hT).counit.app M = 𝟙 _ := by
  have htrace := tensor_trace A T N hN hA hT hI
  rw [htrace M hpf, hnorm]
  exact scalar_identity ((Etale.ordinaryFiniteTensor A T).obj M)
    (Etale.ordinaryFiniteUnit A T) M (Etale.derivedTensorSingleUnitIso M)

private theorem normalized_exceptional_trace
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible)
    (hnorm : ((sectionComposition A T).inv.app (Etale.ordinaryFiniteUnit A T) ≫
    (compact A T).map (restrictedSupported A T N hN hA hT hI) ≫
      CoordinateLine.integration A N hA T hN hT = 𝟙 _))
    (M : Etale.DerivedCategoryModule A T)
      (hpf : IsIso (closedProjection A T M)) :
      ordinaryOrientation A T N hN hA hT hI M hpf ≫
        (closedImage A T).rightAdjoint.map
          ((CoordinateLine.comparison A N hA T hN hT).hom.app M) ≫
        (exceptionalComposition A T).hom.app M = 𝟙 _ := by
  exact (ordinaryOrientation_transpose A T N hN hA hT hI M hpf).trans
    (normalized_tensor_trace A T N hN hA hT hI hnorm M hpf)

private theorem normalized_orientation_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible)
    (hnorm : ((sectionComposition A T).inv.app (Etale.ordinaryFiniteUnit A T) ≫
    (compact A T).map (restrictedSupported A T N hN hA hT hI) ≫
      CoordinateLine.integration A N hA T hN hT = 𝟙 _))
    (M : Etale.DerivedCategoryModule A T)
      (hpf : IsIso (closedProjection A T M)) :
      IsIso (ordinaryOrientation A T N hN hA hT hI M hpf) := by
  have hi : IsIso (ordinaryOrientation A T N hN hA hT hI M hpf ≫
      (closedImage A T).rightAdjoint.map
        ((CoordinateLine.comparison A N hA T hN hT).hom.app M) ≫
      (exceptionalComposition A T).hom.app M) := by
    rw [normalized_exceptional_trace A T N hN hA hT hI hnorm]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hi

private theorem iso_last_of_eq
    {C : Type*} [Category C] {V W X Y : C}
    (a : V ⟶ W) (b : W ⟶ X) (c : X ⟶ Y) (d : V ⟶ Y)
    [IsIso a] [IsIso b] [IsIso d] (h : d = a ≫ b ≫ c) : IsIso c := by
  have hi : IsIso ((a ≫ b) ≫ c) := by
    rw [Category.assoc, ← h]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp hi

private theorem normalized_coprojection_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible)
    (hnorm : ((sectionComposition A T).inv.app (Etale.ordinaryFiniteUnit A T) ≫
    (compact A T).map (restrictedSupported A T N hN hA hT hI) ≫
      CoordinateLine.integration A N hA T hN hT = 𝟙 _))
    (M : Etale.DerivedCategoryModule A T)
    (hpf : IsIso (closedProjection A T M))
    (hmate : IsIso (closedTensorProjection A T
      ((closedImage A T).rightAdjoint.obj (CoordinateLine.line A N hA T)) M)) :
    IsIso (coprojectionMate A T N hA M hmate) := by
  let := unitOrientation_isIso A T N hN hA hT hI hnorm
  let := normalized_orientation_isIso A T N hN hA hT hI hnorm M hpf
  exact iso_last_of_eq (Etale.derivedTensorSingleUnitIso M).inv
    (((Etale.ordinaryFiniteTensor A T).obj M).map
      (unitOrientation A T N hN hA hT hI))
    (coprojectionMate A T N hA M hmate)
    (ordinaryOrientation A T N hN hA hT hI M hpf)
    (ordinaryOrientation_tensor A T N hN hA hT hI M hpf hmate)

private theorem normalized_coprojection
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible)
    (hnorm : ((sectionComposition A T).inv.app (Etale.ordinaryFiniteUnit A T) ≫
    (compact A T).map (restrictedSupported A T N hN hA hT hI) ≫
      CoordinateLine.integration A N hA T hN hT = 𝟙 _)) :
    CoprojectionNormalization A T N hN hA hT hI := by
  refine ⟨unitOrientation_isIso A T N hN hA hT hI hnorm, ?_⟩
  intro M hM
  let hpf := closedProjection_isIso A T M
  let hmate := closedTensorProjection_isIso A T
    ((closedImage A T).rightAdjoint.obj (CoordinateLine.line A N hA T)) M
  exact ⟨hpf, hmate, normalized_coprojection_isIso A T N hN hA hT hI hnorm M hpf hmate,
    ordinaryOrientation_tensor A T N hN hA hT hI M hpf hmate⟩

/-- Tensoring the normalized coordinate scalar gives the canonical closed
coprojection formula and both twisted transpose equations.

Source: current blueprint, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md, even-shift paragraph;
lem-pur-twisted-coordinate-section-normalization, Steps 6, 8--9.
(blueprint: lem-pur-coordinate-section-tensor-trace).

Proof:
1. Finite-coefficient proper projection is invertible on every coefficient object.
   Coefficient naturality packages the closed projection as a natural isomorphism.
   Naturality of the closed adjunction then expresses ordinaryOrientation as tensoring
   unitOrientation followed by the specified coprojectionMate.
2. Apply compact projection composition to two identity maps. Its compositor unit law,
   inverse-image unit coherence, naturality and cancellation normalize identity projection.
   Apply composition again to the section and its projection. Conjugate by the signed
   tensor symmetries and transport through the proper-support and compactification
   comparisons. The resulting projection square uses exactly sectionComposition.
3. Apply that square and compact projection naturality to restrictedSupported. The actual
   coordinate counit tensor formula gives the compact trace equation for every coefficient
   object, with its stated unitors. The conjugate-adjunction identity identifies the
   exceptional composite with this trace. Scalar normalization makes the composite the
   identity, and cancellation of its comparison isomorphisms proves ordinaryOrientation
   invertible.
4. The coordinate counit is invertible. At the literal unit, finite proper projection and
   the counit tensor formula show that integration is invertible. Scalar normalization
   therefore makes the compact image of restrictedSupported invertible. The composite
   closed and coordinate adjunction has left functor isomorphic to the identity, so its
   unit is invertible; transposition proves unitOrientation invertible. Cancel its tensor
   from the orientation formula to obtain invertibility of coprojectionMate. Specialize
   the all-coefficient identities to the unit and the Tate objects. The signed symmetries
   already account for all shifts, and the argument includes the empty base. -/
theorem coordinateSectionTensorTrace
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible)
    (hnorm : ((sectionComposition A T).inv.app (Etale.ordinaryFiniteUnit A T) ≫
    (compact A T).map (restrictedSupported A T N hN hA hT hI) ≫
      CoordinateLine.integration A N hA T hN hT = 𝟙 _)) :
    CoprojectionNormalization A T N hN hA hT hI ∧
    ∀ r : ℕ, ∃ hpf : IsIso (closedProjection A T
      (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r)),
    IsIso (ordinaryOrientation A T N hN hA hT hI
      (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) hpf) ∧
    ((sectionComposition A T).inv.app
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) ≫
      (compact A T).map (tensorSupported A T N hN hA hT hI
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) hpf) ≫
      (CoordinateLine.adjunction A N hA T hN hT).counit.app
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) =
      (Etale.derivedTensorSingleUnitIso
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r)).inv ≫
      ((Etale.ordinaryFiniteTensor A T).obj
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r)).map
          ((sectionComposition A T).inv.app (Etale.ordinaryFiniteUnit A T) ≫
            (compact A T).map (restrictedSupported A T N hN hA hT hI) ≫
            CoordinateLine.integration A N hA T hN hT) ≫
      (Etale.derivedTensorSingleUnitIso
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r)).hom) ∧
    (ordinaryOrientation A T N hN hA hT hI
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) hpf ≫
      (closedImage A T).rightAdjoint.map
        ((CoordinateLine.comparison A N hA T hN hT).hom.app
          (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r)) ≫
      (exceptionalComposition A T).hom.app
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) = 𝟙 _) := by
  refine ⟨normalized_coprojection A T N hN hA hT hI hnorm, ?_⟩
  intro r
  let hpf := closedProjection_isIso A T
    (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r)
  exact ⟨hpf, normalized_orientation_isIso A T N hN hA hT hI hnorm
      (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) hpf,
    tensor_trace A T N hN hA hT hI
      (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) hpf,
    normalized_exceptional_trace A T N hN hA hT hI hnorm
      (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) hpf⟩

end AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
