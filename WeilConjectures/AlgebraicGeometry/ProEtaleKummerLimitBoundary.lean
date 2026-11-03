/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Kummer.TowerKummerComplex
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwistConstructionsSupplement
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralPullbackData
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarLines
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCanonicalClass
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportExchangeTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.SheafTensor
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SectionActionInternal
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingPresheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtaleObjectPullbackRestriction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalDerivedScalarComparisons
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateTransitivity
public import WeilConjectures.SmoothPurity.Supporting.Coefficient.StrictCoefficientProperReduction
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Native.IntegralNativeDirectComparison
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.CommonFieldLatticeGenerators
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedEquivalence
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCohomologyHom
public import WeilConjectures.SmoothPurity.PurityConventions.PurityConventions
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFrameClass
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorCohomology
public import WeilConjectures.CategoryTheory.Sites.WithSection.TorsorWithSection
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologySequence
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctoriality
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.RingTheory.SmoothFibreRegularLocal
public import WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters
public import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
public import WeilConjectures.RingTheory.ProperBaseChange.SmoothOverFieldRegularLocal
public import Mathlib.RingTheory.Smooth.Flat
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Regular
public import WeilConjectures.AlgebraicGeometry.EffectiveCartierSum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassSystems
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.AlgebraicGeometry.CompatibleKummerCoefficients.CompatibleKummerCoefficientData
public import WeilConjectures.AlgebraicGeometry.CondensedCartier.CondensedCartierCompactExchange

/-! # The compatible-root pro-etale Kummer boundary

Source: Stacks Project, Tag 03PL, and the Kummer-boundary refinement of
`thm-pur-projective-bundle-formula` (blueprint:
`lem-pur-proetale-kummer-limit-boundary`).

The inverse limits below use the actual units and roots sheaves.  The connecting
map is the boundary of the recorded short exact complex, so its sign is fixed by
`ShortComplex.ShortExact.singleδ`.  The final theorem records the native
coefficient and pullback normalizations required by the blueprint.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.ProEtale.CondensedRing
open CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open AlgebraicGeometry.ProEtale.SpTowerClasses
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable {T : Scheme.{u}} (ell : ℕ) [Fact ell.Prime]

/-- The inverse system of actual units with successive power maps.
Source: Stacks 03PL and the blueprint compatible-root construction
(blueprint: lem-pur-proetale-kummer-limit-boundary). -/
abbrev compatibleUnitsTower (T : Scheme.{u}) : ℕᵒᵖ ⥤
    Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  SpTowerClasses.powerUnits ell T

/-- The inverse system of root-of-unity sheaves.
Source: Stacks 03PL and the blueprint compatible-root construction
(blueprint: lem-pur-proetale-kummer-limit-boundary). -/
abbrev compatibleRootsTower (T : Scheme.{u}) : ℕᵒᵖ ⥤
    Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  SpTowerClasses.roots ell T

/-- The categorical inverse limit of the actual unit tower.
Source: Stacks 03PL and the blueprint compatible-root construction
(blueprint: lem-pur-proetale-kummer-limit-boundary). -/
abbrev compatibleUnits (T : Scheme.{u}) :
    Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  limit (compatibleUnitsTower ell T)

/-- The categorical inverse limit of the root tower.
Source: Stacks 03PL and the blueprint compatible-root construction
(blueprint: lem-pur-proetale-kummer-limit-boundary). -/
abbrev compatibleRoots (T : Scheme.{u}) :
    Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  limit (compatibleRootsTower ell T)

/-- Projection of the root limit to its `(n+1)`-st root sheaf.
Source: Stacks 03PL and the blueprint compatible-root construction
(blueprint: lem-pur-proetale-kummer-limit-boundary). -/
noncomputable def compatibleRootsCoordinate (T : Scheme.{u}) (n : ℕ) :
    compatibleRoots ell T ⟶
      Scheme.proEtaleRootsOfUnitySheaf T (ell ^ (n + 1)) :=
  limit.π (compatibleRootsTower ell T) (op n)

/-- Projection of the unit limit to the zeroth unit sheaf.
Source: Stacks 03PL and the blueprint compatible-root construction
(blueprint: lem-pur-proetale-kummer-limit-boundary). -/
noncomputable def compatibleUnitsProjection (T : Scheme.{u}) :
    compatibleUnits ell T ⟶ Scheme.proEtaleUnitsSheaf T :=
  limit.π (compatibleUnitsTower ell T) (op 0)

/-- The finite pro-etale Kummer short complex at a positive exponent.
Source: Stacks 03PL and the blueprint compatible-root construction
(blueprint: lem-pur-proetale-kummer-limit-boundary). -/
abbrev finiteKummerComplex (T : Scheme.{u}) (r : ℕ) :=
  AlgebraicGeometry.ProEtale.cartierProKummerComplex T (ell ^ r)

/-- The positive connecting map of a finite Kummer short exact complex.
Source: Stacks 03PL and the blueprint compatible-root construction
(blueprint: lem-pur-proetale-kummer-limit-boundary). -/
noncomputable def finiteKummerBoundary (T : Scheme.{u}) (r : ℕ)
    (h : (finiteKummerComplex ell T r).ShortExact) :
    (DerivedCategory.singleFunctor (Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}) 0).obj
        (Scheme.proEtaleUnitsSheaf T) ⟶
      ((DerivedCategory.singleFunctor
          (Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}) 0).obj
          (Scheme.proEtaleRootsOfUnitySheaf T (ell ^ r))) ⟦(1 : ℤ)⟧ :=
  h.singleδ

/-- The canonical inclusion of compatible roots into compatible units.
Source: Stacks 03PL and the blueprint compatible-root construction
(blueprint: lem-pur-proetale-kummer-limit-boundary). -/
structure CompatibleRootInclusion (T : Scheme.{u}) where
  hom : compatibleRoots ell T ⟶ compatibleUnits ell T
  zeroth : hom ≫ compatibleUnitsProjection ell T = 0
  positive : ∀ (n : ℕ),
    hom ≫ limit.π (compatibleUnitsTower ell T) (op (n + 1)) =
      limit.π (compatibleRootsTower ell T) (op n) ≫
        Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (n + 1))

/-- The coordinates `(1,z₁,z₂,…)`, in additive notation.
Source: Stacks 03PL and the blueprint compatible-root construction
(blueprint: lem-pur-proetale-kummer-limit-boundary). -/
def compatibleRootComponent (T : Scheme.{u}) :
    ℕ → (compatibleRoots ell T ⟶ Scheme.proEtaleUnitsSheaf T)
  | 0 => 0
  | n + 1 => compatibleRootsCoordinate ell T n ≫
      Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (n + 1))

/-- Adjacent coordinates of the root inclusion are compatible.
Source: Stacks 03PL (blueprint: lem-pur-proetale-kummer-limit-boundary).
Proof: at zero use the root kernel equation; at a successor use the limit
cone equation and the defining prime-power root transition. -/
theorem compatibleRootComponent_transition (T : Scheme.{u}) (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj (compatibleRoots ell T)).map
      (homOfLE (Nat.le_succ n)).op ≫ compatibleRootComponent ell T n =
        compatibleRootComponent ell T (n + 1) ≫
          (compatibleUnitsTower ell T).map (homOfLE (Nat.le_succ n)).op := by
  simp only [Functor.const_obj_map]
  cases n with
  | zero =>
      have hi : Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (0 + 1)) ≫
          (compatibleUnitsTower ell T).map (homOfLE (Nat.le_succ 0)).op = 0 := by
        simp only [compatibleUnitsTower, SpTowerClasses.powerUnits,
          Functor.ofOpSequence_map_homOfLE_succ]
        rw [show ell ^ (0 + 1) = ell from pow_one ell]
        exact kernel.condition (Scheme.proEtaleUnitsPower T ell)
      change 0 = (compatibleRootsCoordinate ell T 0 ≫
        Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (0 + 1))) ≫
          (compatibleUnitsTower ell T).map (homOfLE (Nat.le_succ 0)).op
      calc
        0 = compatibleRootsCoordinate ell T 0 ≫ 0 := (comp_zero).symm
        _ = compatibleRootsCoordinate ell T 0 ≫
            (Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (0 + 1)) ≫
              (compatibleUnitsTower ell T).map (homOfLE (Nat.le_succ 0)).op) :=
          congrArg (fun f ↦ compatibleRootsCoordinate ell T 0 ≫ f) hi.symm
        _ = (compatibleRootsCoordinate ell T 0 ≫
            Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (0 + 1))) ≫
              (compatibleUnitsTower ell T).map (homOfLE (Nat.le_succ 0)).op :=
          (Category.assoc _ _ _).symm
  | succ n =>
      have ht : (compatibleRootsTower ell T).map (homOfLE (Nat.le_succ n)).op ≫
          Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (n + 1)) =
        Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (n + 1 + 1)) ≫
          (compatibleUnitsTower ell T).map (homOfLE (Nat.le_succ (n + 1))).op := by
        dsimp only [compatibleRootsTower, SpTowerClasses.roots,
          Scheme.proEtaleRootsOfUnityTower, compatibleUnitsTower, SpTowerClasses.powerUnits]
        rw [Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_map_homOfLE_succ]
        ext U x
        exact Scheme.proEtaleRootsOfUnityTransition_prime T ell (Fact.out : ell.Prime)
          n U x
      have h := limit.w (compatibleRootsTower ell T) (homOfLE (Nat.le_succ n)).op
      change compatibleRootsCoordinate ell T (n + 1) ≫
        (compatibleRootsTower ell T).map (homOfLE (Nat.le_succ n)).op =
          compatibleRootsCoordinate ell T n at h
      change compatibleRootsCoordinate ell T n ≫
          Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (n + 1)) =
        (compatibleRootsCoordinate ell T (n + 1) ≫
          Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (n + 1 + 1))) ≫
            (compatibleUnitsTower ell T).map (homOfLE (Nat.le_succ (n + 1))).op
      exact (congrArg (fun f ↦ f ≫
        Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (n + 1))) h.symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun f ↦ compatibleRootsCoordinate ell T (n + 1) ≫ f) ht).trans
            (Category.assoc _ _ _).symm))

/-- The componentwise cone, without choosing any limit map.
Source: Stacks 03PL and the blueprint compatible-root construction
(blueprint: lem-pur-proetale-kummer-limit-boundary). -/
def compatibleRootCone (T : Scheme.{u}) : Cone (compatibleUnitsTower ell T) :=
  Cone.mk (compatibleRoots ell T)
    (NatTrans.ofOpSequence (compatibleRootComponent ell T)
      (compatibleRootComponent_transition ell T))

/-- The inclusion is the universal `limit.lift` of the componentwise cone.
Source: Stacks 03PL and the blueprint compatible-root construction
(blueprint: lem-pur-proetale-kummer-limit-boundary). -/
noncomputable def compatibleRootInclusion (T : Scheme.{u}) :
    CompatibleRootInclusion ell T where
  hom := limit.lift (compatibleUnitsTower ell T) (compatibleRootCone ell T)
  zeroth := limit.lift_π (compatibleRootCone ell T) (op 0)
  positive n := limit.lift_π (compatibleRootCone ell T) (op (n + 1))

/-- The coordinate-zero root inclusion composes to zero.
Source: Stacks 03PK (blueprint: lem-pur-proetale-kummer-limit-boundary).
Proof: this is the zeroth-coordinate normalization of `compatibleRootInclusion`. -/
theorem compatibleRootZero (T : Scheme.{u}) :
    (compatibleRootInclusion ell T).hom ≫ compatibleUnitsProjection ell T = 0 := by
  exact (compatibleRootInclusion ell T).zeroth

/-- The compatible-root Kummer short complex.
Source: Stacks 03PL and the blueprint compatible-root construction
(blueprint: lem-pur-proetale-kummer-limit-boundary). -/
noncomputable def compatibleKummerComplex (T : Scheme.{u}) :
    ShortComplex (Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk (compatibleRootInclusion ell T).hom
    (compatibleUnitsProjection ell T) (compatibleRootZero ell T)

/-- The canonical positive boundary of the compatible-root complex.
Source: Stacks 03PL and the blueprint compatible-root construction
(blueprint: lem-pur-proetale-kummer-limit-boundary). -/
noncomputable def compatibleKummerBoundary (T : Scheme.{u})
    (h : (compatibleKummerComplex ell T).ShortExact) :
    (DerivedCategory.singleFunctor (Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}) 0).obj
        (Scheme.proEtaleUnitsSheaf T) ⟶
      ((DerivedCategory.singleFunctor
          (Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}) 0).obj
          (compatibleRoots ell T)) ⟦(1 : ℤ)⟧ :=
  h.singleδ

/-- Canonical maps on the units and root sheaves under geometric inverse image.
Source: Stacks 03PL and the blueprint compatible-root construction
(blueprint: lem-pur-proetale-kummer-limit-boundary). -/
structure CompatiblePullback (T' T : Scheme.{u}) (f : T' ⟶ T) where
  unitMap :
    (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        (Scheme.proEtaleUnitsSheaf T) ⟶ Scheme.proEtaleUnitsSheaf T'
  unitMap_canonical : unitMap = (SpTowerClasses.unitsPull f).app (op 0)
  rootMap (n : ℕ) :
    (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        (Scheme.proEtaleRootsOfUnitySheaf T (ell ^ (n + 1))) ⟶
      Scheme.proEtaleRootsOfUnitySheaf T' (ell ^ (n + 1))
  rootMap_canonical (n : ℕ) :
    rootMap n = Scheme.proEtaleRootsOfUnityInverseImageMap f (ell ^ (n + 1))

/-- Projection of the delivered positive boundary to a finite root target.
Source: Stacks 03PL and the blueprint compatible-root construction
(blueprint: lem-pur-proetale-kummer-limit-boundary). -/
noncomputable def compatibleBoundaryAt (T : Scheme.{u}) (n : ℕ)
    (h : (compatibleKummerComplex ell T).ShortExact) :
    (DerivedCategory.singleFunctor (Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}) 0).obj
        (Scheme.proEtaleUnitsSheaf T) ⟶
      ((DerivedCategory.singleFunctor
          (Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}) 0).obj
          (Scheme.proEtaleRootsOfUnitySheaf T (ell ^ (n + 1)))) ⟦(1 : ℤ)⟧ :=
  compatibleKummerBoundary ell T h ≫
    (shiftFunctor (DerivedCategory (Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1})) 1).map
      ((DerivedCategory.singleFunctor
        (Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}) 0).map
        (compatibleRootsCoordinate ell T n))

/-- The componentwise root inclusion is uniquely determined by its zeroth and positive coordinates.
Source: Stacks Project, Tag 03PK (blueprint: `lem-pur-proetale-kummer-limit-boundary`).
Proof: the zero coordinate is forced to be one, and the successor coordinates are the
actual root inclusions; `proEtaleRootsOfUnityTransition_prime` gives compatibility. -/
theorem compatibleRootInclusion_existsUnique (T : Scheme.{u}) :
    ∃! q : CompatibleRootInclusion ell T,
      q.hom ≫ compatibleUnitsProjection ell T = 0 ∧
        ∀ (n : ℕ),
          q.hom ≫ limit.π (compatibleUnitsTower ell T) (op (n + 1)) =
            limit.π (compatibleRootsTower ell T) (op n) ≫
              Scheme.proEtaleRootsOfUnityInclusion T (ell ^ (n + 1)) := by
  let q := compatibleRootInclusion ell T
  refine ⟨q, ⟨q.zeroth, q.positive⟩, ?_⟩
  intro q' hq'
  have hh : q'.hom = q.hom := by
    apply limit.hom_ext
    rintro ⟨n⟩
    cases n with
    | zero =>
        exact hq'.1.trans q.zeroth.symm
    | succ n =>
        exact (hq'.2 n).trans (q.positive n).symm
  have hext : ∀ a b : CompatibleRootInclusion ell T, a.hom = b.hom → a = b := by
    rintro ⟨a, ha, hpa⟩ ⟨b, hb, hpb⟩ h
    change a = b at h
    cases h
    rfl
  exact hext q' q hh

/-- The upstream coefficient map with its native coefficient endpoints explicit.
Source: blueprint coefficient-change Step 8
(blueprint: lem-pur-proetale-kummer-limit-boundary). -/
abbrev nativeCoefficientMap {c c' : PurityTransport.Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell) (T : Scheme.{u}) :
    condensedRingObj (c.obj ell) T ⟶ condensedRingObj (c'.obj ell) T :=
  coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom T

/-- Use the published commutativity proof at the explicit native coefficient object.
Source: pulled-back condensed coefficients, blueprint Step 8
(blueprint: lem-pur-proetale-kummer-limit-boundary). -/
abbrev nativeCoefficientComm (c : PurityTransport.Coefficient ell) (X : Scheme.{u}) :
    IsCommMonObj (condensedRingObj (c.obj ell) X) :=
  ProEtale.isCommMonObj_condensedRingObj (c.obj ell) X

attribute [local instance] nativeCoefficientComm

/-- The native coefficient map carries the published monoidal image ring-map proof.
Source: coefficient pullback, blueprint Step 8
(blueprint: lem-pur-proetale-kummer-limit-boundary). -/
abbrev nativeCoefficientMap_isMonHom {c c' : PurityTransport.Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell) (X : Scheme.{u}) :
    IsMonHom (nativeCoefficientMap ell a X) := by
  let : IsMonHom (show c.obj ell ⟶ c'.obj ell from a.hom.hom) := a.hom.isMonHom_hom
  change IsMonHom ((upperStarFromPoint X).map a.hom.hom)
  exact Functor.map.instIsMonHom (F := upperStarFromPoint X)
    (c.obj ell) (c'.obj ell) a.hom.hom

attribute [local instance] nativeCoefficientMap_isMonHom

set_option maxHeartbeats 800000 in
-- Elaborating the normalized derived tensor comparisons needs additional heartbeats.
set_option maxHeartbeats 800000 in
-- Elaborating the normalized derived tensor comparisons needs additional heartbeats.
end AlgebraicGeometry.ProEtale
