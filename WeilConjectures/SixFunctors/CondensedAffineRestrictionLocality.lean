/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatum
public import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.CondensedScalarShriekMates
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionNormalization
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionSuccessive
public import WeilConjectures.Compactification.CategoryBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
public import WeilConjectures.SixFunctors.ScalarSixTensorHom
public import WeilConjectures.AlgebraicGeometry.CompactificationCoherenceCocycle
public import WeilConjectures.AlgebraicGeometry.CondensedProperOpenInterchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing

import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.Algebra.Homology.LocalizationHomComparisonData
import WeilConjectures.AlgebraicGeometry.FiniteConstantLocalModel
import WeilConjectures.SixFunctors.ScalarSixCompactSupport
import WeilConjectures.SixFunctors.ScalarSixDirectImage
import WeilConjectures.SixFunctors.ScalarSixExceptional
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.CategoryTheory.LocalizedModuleExactIndependent
import WeilConjectures.Algebra.Homology.KFlatSupplement
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.SixFunctors.OpenTensorNormalization
import WeilConjectures.AlgebraicGeometry.ProEtaleOpenPullbackKInjective
import WeilConjectures.AlgebraicGeometry.ProEtaleRingedOpenCoverReflectsIso
import WeilConjectures.AlgebraicGeometry.ModuleDirectImageOpenPasting
import WeilConjectures.CategoryTheory.PastedMatesCounitNormalization
import WeilConjectures.AlgebraicGeometry.ProEtaleOpenRestrictionCounit
import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.SixFunctors.ScalarDirectImageMateCoherence
import WeilConjectures.AlgebraicGeometry.IntegralFinitePullbackComposition
import WeilConjectures.AlgebraicGeometry.ProEtaleRingedOpenComparison
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
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
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.ProperBasic
import WeilConjectures.AlgebraicGeometry.CompactificationCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.AlgebraicGeometry.CartesianCoefficients
import all WeilConjectures.AlgebraicGeometry.UnboundedLocalizingPullback
import all WeilConjectures.AlgebraicGeometry.OpenExtensionConstantModelConstructible
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Open localization of condensed six-functor constructions

Source: latest blueprint, sec-six-functors/sk-thm-sf-package/
fix-lem-tensor-adjunction.proof.md, Step 2 and the coefficient paragraph.
(blueprint: lem-sf-condensed-affine-restriction-locality).

All functors below act on the existing ordinary derived categories of modules over
`condensedRingObj`. The comparisons are specified by mates, evaluation and the proper/open
compactification word. In particular no assertion of faithfulness of derived open
restriction is made.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.AffineRestrictionLocality

/-- Only an abbreviation for the dependency's module category. Source: Step 2
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
abbrev Modules (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :=
  ModuleRingedComparison.internalModules Λ.X X

/-- The ordinary ambient derived category, not a completion. Source: Step 2
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
abbrev Ambient (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) := DerivedCategory (Modules Λ X)

/-- The exact inverse image, canonically the total derived pullback. Source: Step 2
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
abbrev pull (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  scalarSixPull Λ f

/-- The recorded total derived module pushforward. Source: Step 2
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
abbrev push (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  moduleObjectDerivedPushforward Λ.X f

/-- Exact extension by zero, localized termwise. Source: Step 2
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
abbrev extension (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] := (openImmersionLowerShriek Λ.X j).mapDerivedCategory

/-- The actual proper/open candidate for compact support. Source: Step 2
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
abbrev support (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) := rightDerivedLowerShriekOfCompactification Λ.X c

/-- The dependency's bounded constructible finite-Tor predicate. Source: Step 2
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
abbrev ctf (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) : ObjectProperty (Ambient Λ X) :=
  constantModelBoundedConstructible Λ.X X ⊓ _root_.DerivedCategory.finiteTorAmplitude _

/-- The dependency's ordinary internal Hom. Source: Step 2
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
abbrev hom (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) (K L : Ambient Λ X) :=
  ((derivedHom Λ.X X).obj (op K)).obj L

/-- Left evaluation, with the actual closed adjunction. Source: Step 2
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
abbrev evaluation (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) (K L : Ambient Λ X) :
    K ⊗ hom Λ X K L ⟶ L := (derivedTensorHomAdjunction Λ.X K).counit.app L

/-- The canonical K-flat tensor restriction, transported along exact inverse image.
Source: Step 2, tensor restriction (blueprint: lem-sf-condensed-affine-restriction-locality). -/
def tensorRestriction (Λ : ScalarSixRing.{u}) {T Z : Scheme.{u}} (w : T ⟶ Z)
    (K L : Ambient Λ Z) :
    (pull Λ w).obj (K ⊗ L) ≅ (pull Λ w).obj K ⊗ (pull Λ w).obj L :=
  let e := leftDerivedUpperStarIsoMapDerivedCategory Λ.X w
  (e.app (K ⊗ L)).symm ≪≫
    ((leftDerivedUpperStarTensorIso Λ.X w).app K).app L ≪≫
      asIso ((e.app K).hom ⊗ₘ (e.app L).hom)

/-- The canonical Hom restriction is the evaluation transpose. There is no choice of an
unnormalized isomorphism. Source: Step 2, displayed Hom chain
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
def homRestriction (Λ : ScalarSixRing.{u}) {T Z : Scheme.{u}} (w : T ⟶ Z)
    (K L : Ambient Λ Z) :
    (pull Λ w).obj (hom Λ Z K L) ⟶
      hom Λ T ((pull Λ w).obj K) ((pull Λ w).obj L) :=
  (derivedTensorHomAdjunction Λ.X ((pull Λ w).obj K)).homEquiv _ _
    ((tensorRestriction Λ w K (hom Λ Z K L)).inv ≫
      (pull Λ w).map (evaluation Λ Z K L))

/-- The canonical open-extension exchange, before inversion. It is the mate of the
canonical pullback square under the two exact open adjunctions. Source: Step 2
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
def extensionExchange (Λ : ScalarSixRing.{u})
    {X Z X' Z' : Scheme.{u}} {j : X ⟶ Z} {j' : X' ⟶ Z'}
    {u : X' ⟶ X} {h : Z' ⟶ Z} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : CommSq u j' j h) :
    pull Λ u ⋙ extension Λ j' ⟶ extension Λ j ⋙ pull Λ h :=
  Adjunction.exchangeLeft (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j')
    (derivedOpenCoherencePullbackSquare Λ.X sq).symm

/-- The first displayed restriction isomorphism, with the canonical pullback compositor.
Source: Step 2 (blueprint: lem-sf-condensed-affine-restriction-locality). -/
abbrev pullbackRestriction (Λ : ScalarSixRing.{u})
    {X Y U V : Scheme.{u}} {f : X ⟶ Y} {f' : U ⟶ V}
    {u : U ⟶ X} {v : V ⟶ Y} (sq : CommSq u f' f v) :
    pull Λ f ⋙ pull Λ u ≅ pull Λ v ⋙ pull Λ f' :=
  (derivedOpenCoherencePullbackSquare Λ.X sq).symm

/-- The open-extension exchange is invertible for a Cartesian square.
Source: Step 2, exact extension by zero
(blueprint: lem-sf-condensed-affine-restriction-locality).

Proof: identify open inverse image with slice restriction. Both extensions are zero off
the inverse-image open and agree there through the open unit. The open/closed conservative
pair therefore makes the unit/counit exchange invertible, on all unbounded objects. -/
theorem extensionExchange_isIso (Λ : ScalarSixRing.{u})
    {X Z X' Z' : Scheme.{u}} {j : X ⟶ Z} {j' : X' ⟶ Z'}
    {u : X' ⟶ X} {h : Z' ⟶ Z} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback u j' j h) : IsIso (extensionExchange Λ sq.toCommSq) := by
  have hK (K : Ambient Λ X) : IsIso ((extensionExchange Λ sq.toCommSq).app K) := by
    have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j).unit :=
      inferInstance
    have hd := isIso_derivedCounit_app_upperStar_obj_openImmersionLowerShriek Λ.X sq K
    let e := (Functor.mapDerivedCategoryCompIso
      (openImmersionLowerShriek Λ.X j) (upperStar Λ.X h)).symm.app K
    have : IsIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j').counit.app
        ((pull Λ h).obj ((extension Λ j).obj K))) :=
      (NatTrans.isIso_app_iff_of_iso _ e).mpr hd
    unfold extensionExchange
    rw [Adjunction.exchangeLeft_app]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- Inverse of the specified open-extension mate. Source: Step 2
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
def extensionRestriction (Λ : ScalarSixRing.{u})
    {X Z X' Z' : Scheme.{u}} {j : X ⟶ Z} {j' : X' ⟶ Z'}
    {u : X' ⟶ X} {h : Z' ⟶ Z} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback u j' j h) :
    extension Λ j ⋙ pull Λ h ≅ pull Λ u ⋙ extension Λ j' :=
  letI := extensionExchange_isIso Λ sq
  (asIso (extensionExchange Λ sq.toCommSq)).symm

set_option maxHeartbeats 1600000 in
-- Keep the canonical functor and module instances during elaboration.
/-- The actual compact-support restriction word: first restrict the proper direct image,
then use the inverse open-extension exchange. Source: Step 2, compactification formula
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
def supportRestriction (Λ : ScalarSixRing.{u})
    {X Y X' V : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ V}
    {u : X' ⟶ X} {v : V ⟶ Y} (sq : IsPullback u f' f v) (c : Compactification f) :
    support Λ c ⋙ pull Λ v ⟶ pull Λ u ⋙ support Λ (c.ofIsPullback sq) :=
  letI := c.isOpenImmersion
  letI := (c.ofIsPullback sq).isOpenImmersion
  let os := c.isPullback_i_ofIsPullback sq
  letI := extensionExchange_isIso Λ os
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (extension Λ c.i)
      (derivedDirectImageOpenRestriction Λ.X
        (IsPullback.of_hasPullback c.g v).toCommSq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (asIso (extensionExchange Λ os.toCommSq)).inv
      (push Λ (c.ofIsPullback sq).g) ≫
    (Functor.associator _ _ _).hom

/-- The open projection arrow, fixed by the unit and tensor restriction.
Source: Step 2, projection word (blueprint: lem-sf-condensed-affine-restriction-locality). -/
def openProjection (Λ : ScalarSixRing.{u}) {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (K : Ambient Λ X) (N : Ambient Λ Z) :
    (extension Λ j).obj (K ⊗ (pull Λ j).obj N) ⟶ (extension Λ j).obj K ⊗ N :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j).homEquiv _ _ |>.symm <|
    (((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j).unit.app K ⊗ₘ
      𝟙 ((pull Λ j).obj N)) ≫ (tensorRestriction Λ j ((extension Λ j).obj K) N).inv)

/-- The specified open projection arrow is invertible on the ambient category.
Source: Step 2, open tensor normalization
(blueprint: lem-sf-condensed-affine-restriction-locality).

Proof: use K-flat total tensor on the slice site. Restriction of the open projection
is the identity after the open unit. Off the open, source and target vanish. The
open/closed conservative pair proves invertibility, with no boundedness hypothesis. -/
theorem openProjection_isIso (Λ : ScalarSixRing.{u}) {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (K : Ambient Λ X) (N : Ambient Λ Z) :
    IsIso (openProjection Λ j K N) := by
  let adj := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j
  have : IsIso adj.unit := inferInstance
  have : (extension Λ j).Full := adj.fullyFaithfulLOfIsIsoUnit.full
  have : (extension Λ j).Faithful := adj.fullyFaithfulLOfIsIsoUnit.faithful
  have hs : (extension Λ j).essImage ((extension Λ j).obj K ⊗ N) :=
    tensorObj_mem_essImage_mapDerivedCategory_openImmersionLowerShriek Λ.X j K N
  have : IsIso (adj.counit.app ((extension Λ j).obj K ⊗ N)) :=
    adj.isIso_counit_app_iff_mem_essImage.mpr hs
  unfold openProjection
  rw [Adjunction.homEquiv_counit]
  infer_instance

section OpenPreservation

section Constructibility

set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] upperStar upperStarFromPoint upperStarComp
  openImmersionLowerShriek _root_.DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

attribute [local irreducible] extendedStratification

set_option maxHeartbeats 1600000 in
-- Bound elaboration of the exact open and stratification comparisons.
private theorem extension_stratum {T Z W : Scheme.{u}} (w : T ⟶ Z)
    [IsOpenImmersion w] (g : W ⟶ T)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (h : HasFiniteConstantLocalModel Λ W ((upperStar Λ g).obj M)) :
    HasFiniteConstantLocalModel Λ W
      ((upperStar Λ (g ≫ w)).obj ((openImmersionLowerShriek Λ w).obj M)) := by
  have hu := CondensedRing.open_unit_isIso Λ w
  let eT := (asIso ((openImmersionLowerShriekUpperStarAdjunction Λ w).unit.app M)).symm
  exact constant_model_of_iso Λ
    ((upperStarComp Λ g w).app ((openImmersionLowerShriek Λ w).obj M) ≪≫
      (upperStar Λ g).mapIso eT) h

/-- A generic finite stratification with constant models witnesses constructibility. -/
private theorem constructible_from_finite_models {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (S : Scheme.FiniteLocallyClosedStratification X)
    (hS : ∀ a : Fin S.n, Topology.IsConstructible (S.stratum a))
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hN : ∀ a : Fin S.n, HasFiniteConstantLocalModel Λ (S.domain a)
      ((upperStar Λ (S.immersion a)).obj N)) :
    IsConstantModelConstructible Λ X N := by
  let P : (Y : Scheme.{u}) → (Y ⟶ X) → Prop := fun Y f ↦
    HasFiniteConstantLocalModel Λ Y ((upperStar Λ f).obj N)
  exact constant_constructible_of_models Λ N (stratified_of_property P S hS hN)

private theorem extension_complement {T Z : Scheme.{u}} (w : T ⟶ Z)
    [IsOpenImmersion w]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :
    HasFiniteConstantLocalModel Λ _ ((upperStar Λ w.closedComplement).obj
      ((openImmersionLowerShriek Λ w).obj M)) := by
  exact constant_model_of_isZero Λ _ (module_pullback_lowerShriek_isZero Λ w
    w.closedComplement (by rw [w.range_closedComplement]; exact Set.inter_compl_self _) M)

set_option maxHeartbeats 1600000 in
-- Bound the generic stratification conversion.
private theorem extension_stratified {T Z : Scheme.{u}} (w : T ⟶ Z)
    [IsOpenImmersion w] [IsNoetherian Z]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (S : Scheme.FiniteLocallyClosedStratification T)
    (hS : ∀ a : Fin S.n, HasFiniteConstantLocalModel Λ (S.domain a)
      ((upperStar Λ (S.immersion a)).obj M)) :
    IsConstantModelConstructible Λ Z ((openImmersionLowerShriek Λ w).obj M) := by
  let N := (openImmersionLowerShriek Λ w).obj M
  let P : (Y : Scheme.{u}) → (Y ⟶ Z) → Prop := fun Y f ↦
    HasFiniteConstantLocalModel Λ Y ((upperStar Λ f).obj N)
  exact constructible_from_finite_models Λ (extendedStratification w S)
    (fun b ↦ IsLocallyClosed.isConstructible_of_noetherianSpace
      ((extendedStratification w S).isLocallyClosed_stratum b)) N
    (extendedStratification_property w S P (extension_complement Λ w M)
      (fun a ↦ extension_stratum Λ w (S.immersion a) M (hS a)))

/-- Forget constructibility of the strata while retaining any specified local property. -/
private theorem finite_locally_closed_of_stratification {X : Scheme.{u}}
    (P : (Y : Scheme.{u}) → (Y ⟶ X) → Prop) (S : Scheme.Stratification X)
    (hS : ∀ a : Fin S.n, P (S.domain a) (S.immersion a)) :
    ∃ R : Scheme.FiniteLocallyClosedStratification X,
      ∀ a : Fin R.n, P (R.domain a) (R.immersion a) := by
  let R : Scheme.FiniteLocallyClosedStratification X :=
    { n := S.n
      stratum := S.stratum
      isLocallyClosed_stratum := S.isLocallyClosed_stratum
      iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
      domain := S.domain
      immersion := S.immersion
      isImmersion := S.isImmersion
      range_immersion := S.range_immersion }
  exact ⟨R, hS⟩

private theorem extension_given_stratification {T Z : Scheme.{u}}
    (w : T ⟶ Z) [IsOpenImmersion w] [IsNoetherian Z]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (S : Scheme.Stratification T)
    (hS : ∀ a : Fin S.n, HasFiniteConstantLocalModel Λ (S.domain a)
      ((upperStar Λ (S.immersion a)).obj M)) :
    IsConstantModelConstructible Λ Z ((openImmersionLowerShriek Λ w).obj M) := by
  let P : (Y : Scheme.{u}) → (Y ⟶ T) → Prop := fun Y f ↦
    HasFiniteConstantLocalModel Λ Y ((upperStar Λ f).obj M)
  obtain ⟨R, hR⟩ := finite_locally_closed_of_stratification P S hS
  exact extension_stratified Λ w M R hR

private theorem finite_stratified_of_constructible {T : Scheme.{u}}
    [CompactSpace T] [QuasiSeparatedSpace T]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (hM : IsConstantModelConstructible Λ T M) : IsFiniteConstantStratified Λ T M := by
  classical
  simpa only [IsConstantModelConstructible, if_pos
    (show CompactSpace T ∧ QuasiSeparatedSpace T from ⟨inferInstance, inferInstance⟩)] using hM

set_option maxHeartbeats 1600000 in
-- Bound elaboration of the exact open and stratification comparisons.
private theorem extension_constructible {T Z : Scheme.{u}}
    (w : T ⟶ Z) [IsOpenImmersion w] [IsNoetherian Z] [CompactSpace T]
    [QuasiSeparatedSpace T]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (hM : IsConstantModelConstructible Λ T M) :
    IsConstantModelConstructible Λ Z ((openImmersionLowerShriek Λ w).obj M) := by
  classical
  obtain ⟨S, hS⟩ := finite_stratified_of_constructible Λ M hM
  exact extension_given_stratification Λ w M S hS

end Constructibility

attribute [local irreducible] upperStar upperStarFromPoint
  _root_.DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed

set_option maxHeartbeats 1600000 in
-- The exact-derived comparisons transport both constructibility and tensor-test intervals.
/-- Restriction preserves the exact bounded-constructible and Tor conditions used below.
Source: Step 2, finite-stratification and tensor tests
(blueprint: lem-sf-condensed-affine-restriction-locality).

Proof: intersect the finite strata with the open and restrict their finite constant
presentations and trivializing covers. Exactness restricts cohomology. For any local
module, extend by zero and use the K-flat tensor comparison to test the same Tor interval.
For extension by zero, append the closed complement as a zero stratum and apply the open
projection formula to the same Tor test. The empty open has only the zero object. -/
theorem open_preserves_ctf (Λ : ScalarSixRing.{u}) {T Z : Scheme.{u}}
    (w : T ⟶ Z) [IsOpenImmersion w] [IsNoetherian Z] :
    (∀ K : Ambient Λ Z, ctf Λ Z K → ctf Λ T ((pull Λ w).obj K)) ∧
    (∀ K : Ambient Λ T, ctf Λ T K → ctf Λ Z ((extension Λ w).obj K)) := by
  have : TopologicalSpace.NoetherianSpace T := w.isOpenEmbedding.isInducing.noetherianSpace
  have : CompactSpace T := inferInstance
  have : QuasiSeparatedSpace T := inferInstance
  constructor
  · intro K hK
    have hc := pullback_bounded_constructible Λ.X w
      (fun M hM ↦ pullback_constructible Λ.X w M hM) K hK.1
    have ht := pullback_tor Λ.X w K hK.2
    let e := (leftDerivedUpperStarIsoMapDerivedCategory Λ.X w).app K
    have : (constantModelBoundedConstructible Λ.X T).IsClosedUnderIsomorphisms :=
      (constantModelConstructibleFiniteTor_wellDefined Λ.X T).2.1
    have : ObjectProperty.IsClosedUnderIsomorphisms
        (_root_.DerivedCategory.finiteTorAmplitude (Modules Λ T)) :=
      (constantModelConstructibleFiniteTor_wellDefined Λ.X T).2.2.2.1
    exact ⟨ObjectProperty.prop_of_iso _ e hc, ObjectProperty.prop_of_iso _ e ht⟩
  · intro K hK
    let F := openImmersionLowerShriek Λ.X w
    have hi := (constantModelConstructibleFiniteTor_wellDefined Λ.X Z).1
    have hc : constantModelBoundedConstructible Λ.X Z (F.mapDerivedCategory.obj K) := by
      refine ⟨F.bounded_mapDerivedCategory_obj hK.1.1, fun q ↦ ?_⟩
      exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ.X Z)
        ((F.mapDerivedCategoryHomologyFunctorIso q).app K)
        (extension_constructible Λ.X w _ (hK.1.2 q))
    obtain ⟨a, b, htor⟩ := hK.2
    refine ⟨hc, a, b, fun M ↦ ?_⟩
    let M₀ := (_root_.DerivedCategory.singleFunctor (Modules Λ Z) 0).obj M
    let e := ((upperStar Λ.X w).mapDerivedCategorySingleFunctor 0).app M
    have h := F.homologyConcentratedIn_mapDerivedCategory_obj
      (htor ((upperStar Λ.X w).obj M))
    have : IsIso (openProjection Λ w K M₀) := openProjection_isIso Λ w K M₀
    exact (_root_.DerivedCategory.homologyConcentratedIn a b).prop_of_iso
      (F.mapDerivedCategory.mapIso (((curriedTensor _).obj K).mapIso e).symm ≪≫
        asIso (openProjection Λ w K M₀)) h

end OpenPreservation

set_option maxHeartbeats 1600000 in
-- Keep the canonical functor and module instances during elaboration.
/-- The compactification-defined projection arrow, using the dependency's actual proper
projection mate and the normalized open projection. Source: Step 2, projection formula
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
def supportProjection (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : Ambient Λ X) (N : Ambient Λ Y) :
    (support Λ c).obj K ⊗ N ⟶ (support Λ c).obj (K ⊗ (pull Λ f).obj N) :=
  let e := leftDerivedUpperStarIsoMapDerivedCategory Λ.X c.g
  let b := eqToIso (congrArg (pull Λ) c.comm) ≪≫ scalarSixPullComp Λ c.i c.g
  letI := openProjection_isIso Λ c.i K ((pull Λ c.g).obj N)
  ((AlgebraicGeometry.ProEtale.CondensedRing.projectionMap Λ.X c.g).app
      ((extension Λ c.i).obj K)).app N ≫
    (push Λ c.g).map (𝟙 ((extension Λ c.i).obj K) ⊗ₘ (e.app N).hom) ≫
    (push Λ c.g).map (inv (openProjection Λ c.i K ((pull Λ c.g).obj N))) ≫
    (push Λ c.g).map ((extension Λ c.i).map (𝟙 K ⊗ₘ (b.app N).inv))

/-- The supplied constructible adjunction, with its actual compactification-defined left
functor. This is only a parameter bundle for the node's adjunction; no localizing adjoint
or ambient right adjoint is required. Source: Step 2, exceptional Hom chain
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
structure ConstructibleAdjoint (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) where
  lower_preserves : ∀ K : (ctf Λ X).FullSubcategory,
    ctf Λ Y ((support Λ c).obj K.obj)
  upper : (ctf Λ Y).FullSubcategory ⥤ (ctf Λ X).FullSubcategory
  restrictedAdjunction :
    (ctf Λ Y).lift ((ctf Λ X).ι ⋙ support Λ c) lower_preserves ⊣ upper

/-- The actual left functor of the supplied constructible adjunction. Source: Step 2
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
abbrev ConstructibleAdjoint.lower {Λ : ScalarSixRing.{u}} {X Y : Scheme.{u}}
    {f : X ⟶ Y} {c : Compactification f} (R : ConstructibleAdjoint Λ c) :=
  (ctf Λ Y).lift ((ctf Λ X).ι ⋙ support Λ c) R.lower_preserves

/-- The actual counit, viewed through the full ambient inclusion. Source: Step 2
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
abbrev ConstructibleAdjoint.counit {Λ : ScalarSixRing.{u}} {X Y : Scheme.{u}}
    {f : X ⟶ Y} {c : Compactification f} (R : ConstructibleAdjoint Λ c)
    (K : (ctf Λ Y).FullSubcategory) := (R.restrictedAdjunction.counit.app K).hom

set_option maxHeartbeats 1600000 in
-- Elaborate the supplied adjunction and its full subcategory instances together.
/-- The type of exceptional restriction isomorphisms on the supplied constructible
finite-Tor adjunctions. The two inclusions retain every ambient morphism.
Source: Step 2, exceptional Hom chain
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
abbrev ExceptionalIso (Λ : ScalarSixRing.{u})
    {X Y U V : Scheme.{u}} {f : X ⟶ Y} {f' : U ⟶ V}
    {u : U ⟶ X} {v : V ⟶ Y} (sq : IsPullback u f' f v) (c : Compactification f)
    (R : ConstructibleAdjoint Λ c)
    (T : ConstructibleAdjoint Λ (c.ofIsPullback sq))
    (h : ∀ K : (ctf Λ Y).FullSubcategory, ctf Λ V ((pull Λ v).obj K.obj)) :=
  R.upper ⋙ (ctf Λ X).ι ⋙ pull Λ u ≅
    scalarExceptionalPull v h ⋙ T.upper ⋙ (ctf Λ U).ι

/-- Counit normalization of exceptional restriction. It fixes the actual isomorphism;
its inverse and the same adjunction Hom bijections fix the unit normalization.
Source: Step 2, displayed exceptional Hom chain
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
def ExceptionalNormalized (Λ : ScalarSixRing.{u})
    {X Y U V : Scheme.{u}} {f : X ⟶ Y} {f' : U ⟶ V}
    {u : U ⟶ X} {v : V ⟶ Y} [IsOpenImmersion u] [IsOpenImmersion v]
    (sq : IsPullback u f' f v) (c : Compactification f)
    (R : ConstructibleAdjoint Λ c)
    (T : ConstructibleAdjoint Λ (c.ofIsPullback sq))
    (h : ∀ K : (ctf Λ Y).FullSubcategory, ctf Λ V ((pull Λ v).obj K.obj))
    (e : ExceptionalIso Λ sq c R T h) : Prop :=
  ∀ K : (ctf Λ Y).FullSubcategory,
    mateOpenTargetLowerShriek Λ.X sq c ((pull Λ u).obj (R.upper.obj K).obj) ≫
        (support Λ (c.ofIsPullback sq)).map (e.hom.app K) ≫
        T.counit ((scalarExceptionalPull v h).obj K) =
      (pull Λ v).map ((support Λ c).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X u).counit.app
          (R.upper.obj K).obj) ≫ R.counit K)

set_option maxHeartbeats 1600000 in
-- The full coherent diagram is elaborated in the ordinary derived module categories.
/-- Proof fields for tensor/Hom, direct-image, and successive-open normalization.
Every arrow is an already specified canonical arrow. Source: Step 2
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
structure AmbientAssertions (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : ScalarSixRing.{u}) : Prop where
  hom_isIso : ∀ {T Z : Scheme.{u}} (w : T ⟶ Z) [IsOpenImmersion w]

    [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    [w.IsOver (Spec (.of D.k))]
    (K L : Ambient Λ Z), IsIso (homRestriction Λ w K L)
  hom_naturality : ∀ {T Z : Scheme.{u}} (w : T ⟶ Z) [IsOpenImmersion w]
    [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    [w.IsOver (Spec (.of D.k))]
    {K K' L L' : Ambient Λ Z} (a : K' ⟶ K) (b : L ⟶ L'),
    (pull Λ w).map (((derivedHom Λ.X Z).map a.op).app L ≫
        ((derivedHom Λ.X Z).obj (op K')).map b) ≫ homRestriction Λ w K' L' =
      homRestriction Λ w K L ≫
        ((derivedHom Λ.X T).map ((pull Λ w).map a).op).app ((pull Λ w).obj L) ≫
        ((derivedHom Λ.X T).obj (op ((pull Λ w).obj K'))).map ((pull Λ w).map b)
  hom_successive : ∀ {W T Z : Scheme.{u}} (a : W ⟶ T) (b : T ⟶ Z)
    [IsOpenImmersion a] [IsOpenImmersion b]
    [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))]
    [QuasiCompact (W ↘ Spec (.of D.k))]
    [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    [a.IsOver (Spec (.of D.k))]
    [b.IsOver (Spec (.of D.k))]
    (K L : Ambient Λ Z),
    (scalarSixPullComp Λ a b).hom.app (hom Λ Z K L) ≫
        (pull Λ a).map (homRestriction Λ b K L) ≫
        homRestriction Λ a ((pull Λ b).obj K) ((pull Λ b).obj L) =
      homRestriction Λ (a ≫ b) K L ≫
        ((derivedHom Λ.X W).map ((scalarSixPullComp Λ a b).inv.app K).op).app
          ((pull Λ (a ≫ b)).obj L) ≫
        ((derivedHom Λ.X W).obj (op ((pull Λ a).obj ((pull Λ b).obj K)))).map
          ((scalarSixPullComp Λ a b).hom.app L)
  tensor_successive : ∀ {W T Z : Scheme.{u}} (a : W ⟶ T) (b : T ⟶ Z)
    [IsOpenImmersion a] [IsOpenImmersion b]
    [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))]
    [QuasiCompact (W ↘ Spec (.of D.k))]
    [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    [a.IsOver (Spec (.of D.k))]
    [b.IsOver (Spec (.of D.k))]
    (K L : Ambient Λ Z),
    (scalarSixPullComp Λ a b).hom.app (K ⊗ L) ≫
        (pull Λ a).map (tensorRestriction Λ b K L).hom ≫
        (tensorRestriction Λ a ((pull Λ b).obj K) ((pull Λ b).obj L)).hom =
      (tensorRestriction Λ (a ≫ b) K L).hom ≫
        ((scalarSixPullComp Λ a b).hom.app K ⊗ₘ
          (scalarSixPullComp Λ a b).hom.app L)
  direct : ∀ {X Y X' V : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ V}
    {u : X' ⟶ X} {v : V ⟶ Y} [IsOpenImmersion u] [IsOpenImmersion v]
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [X'.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of D.k))]
    [QuasiCompact (X' ↘ Spec (.of D.k))]
    [V.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of D.k))]
    [QuasiCompact (V ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))]
    [f'.IsOver (Spec (.of D.k))]
    [u.IsOver (Spec (.of D.k))]
    [v.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback u f' f v), DirectImageRestrictionNormalized Λ.X sq.toCommSq
  direct_unit : ∀ {X Y X' V : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ V}
    {u : X' ⟶ X} {v : V ⟶ Y} [IsOpenImmersion u] [IsOpenImmersion v]
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [X'.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of D.k))]
    [QuasiCompact (X' ↘ Spec (.of D.k))]
    [V.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of D.k))]
    [QuasiCompact (V ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))]
    [f'.IsOver (Spec (.of D.k))]
    [u.IsOver (Spec (.of D.k))]
    [v.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback u f' f v) (N : Ambient Λ Y),
    (pull Λ v).map ((RootCoordinateFace.adjunction Λ.X f).unit.app N) ≫
        (derivedDirectImageOpenRestriction Λ.X sq.toCommSq).app ((pull Λ f).obj N) =
      (RootCoordinateFace.adjunction Λ.X f').unit.app ((pull Λ v).obj N) ≫
        (push Λ f').map ((derivedOpenCoherencePullbackSquare Λ.X sq.toCommSq).hom.app N)
  direct_counit : ∀ {X Y X' V : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ V}
    {u : X' ⟶ X} {v : V ⟶ Y} [IsOpenImmersion u] [IsOpenImmersion v]
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [X'.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of D.k))]
    [QuasiCompact (X' ↘ Spec (.of D.k))]
    [V.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of D.k))]
    [QuasiCompact (V ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))]
    [f'.IsOver (Spec (.of D.k))]
    [u.IsOver (Spec (.of D.k))]
    [v.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback u f' f v) (K : Ambient Λ X),
    (pull Λ f').map ((derivedDirectImageOpenRestriction Λ.X sq.toCommSq).app K) ≫
        (RootCoordinateFace.adjunction Λ.X f').counit.app ((pull Λ u).obj K) =
      (derivedOpenCoherencePullbackSquare Λ.X sq.toCommSq).hom.app ((push Λ f).obj K) ≫
        (pull Λ u).map ((RootCoordinateFace.adjunction Λ.X f).counit.app K)
  direct_successive : ∀ {X Y X' V X'' W : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ V} {f'' : X'' ⟶ W}
    {u : X' ⟶ X} {v : V ⟶ Y} {u' : X'' ⟶ X'} {v' : W ⟶ V}
    [IsOpenImmersion u] [IsOpenImmersion v]
    [IsOpenImmersion u'] [IsOpenImmersion v']
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [X'.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of D.k))]
    [QuasiCompact (X' ↘ Spec (.of D.k))]
    [V.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of D.k))]
    [QuasiCompact (V ↘ Spec (.of D.k))]
    [X''.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X'' ↘ Spec (.of D.k))]
    [QuasiCompact (X'' ↘ Spec (.of D.k))]
    [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))]
    [QuasiCompact (W ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))]
    [f'.IsOver (Spec (.of D.k))]
    [f''.IsOver (Spec (.of D.k))]
    [u.IsOver (Spec (.of D.k))]
    [v.IsOver (Spec (.of D.k))]
    [u'.IsOver (Spec (.of D.k))]
    [v'.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback u f' f v) (sq' : IsPullback u' f'' f' v'),
    DirectImageSuccessiveRestriction Λ.X sq.toCommSq sq'.toCommSq

set_option maxHeartbeats 1600000 in
-- The full coherent diagram is elaborated in the ordinary derived module categories.
/-- Compactification-independent restriction data on finite-type schemes. The comparison
is prescribed by the recorded refinement map, so these are not arbitrary isomorphisms.
Source: Step 2, compactification independence and successive opens
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
structure SupportAssertions (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : ScalarSixRing.{u}) where
  compare : ∀ {X Y : WeilConjectures.SixFunctorSpace D} (f : X ⟶ Y)
    (c d : Compactification f.hom.left) (K : Ambient Λ X.obj.left) (_hK : ctf Λ X.obj.left K),
    (support Λ c).obj K ≅ (support Λ d).obj K
  compare_natural : ∀ {X Y : WeilConjectures.SixFunctorSpace D} (f : X ⟶ Y)
    (c d : Compactification f.hom.left) {K L : Ambient Λ X.obj.left}
    (hK : ctf Λ X.obj.left K) (hL : ctf Λ X.obj.left L) (a : K ⟶ L),
    (support Λ c).map a ≫ (compare f c d L hL).hom =
      (compare f c d K hK).hom ≫ (support Λ d).map a
  compare_refinement : ∀ {X Y : WeilConjectures.SixFunctorSpace D} (f : X ⟶ Y)
    (c d : Compactification.BoundaryCompactification f.hom.left) (r : d ⟶ c)
    (K : Ambient Λ X.obj.left) (hK : ctf Λ X.obj.left K),
    (compare f c.obj.obj d.obj.obj K hK).hom = compactificationRefinementComponent Λ.X r K
  compare_refl : ∀ {X Y : WeilConjectures.SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (K : Ambient Λ X.obj.left) (hK : ctf Λ X.obj.left K),
    compare f c c K hK = Iso.refl _
  compare_trans : ∀ {X Y : WeilConjectures.SixFunctorSpace D} (f : X ⟶ Y)
    (c d e : Compactification f.hom.left) (K : Ambient Λ X.obj.left)
    (hK : ctf Λ X.obj.left K),
    compare f c d K hK ≪≫ compare f d e K hK = compare f c e K hK
  restriction_isIso : ∀ {X Y U V : WeilConjectures.SixFunctorSpace D}
    {f : X ⟶ Y} {f' : U ⟶ V} {u : U ⟶ X} {v : V ⟶ Y}
    [IsOpenImmersion u.hom.left] [IsOpenImmersion v.hom.left]
    (sq : IsPullback u.hom.left f'.hom.left f.hom.left v.hom.left)
    (c : Compactification f.hom.left), IsIso (supportRestriction Λ sq c)
  restriction_compare : ∀ {X Y U V : WeilConjectures.SixFunctorSpace D}
    {f : X ⟶ Y} {f' : U ⟶ V} {u : U ⟶ X} {v : V ⟶ Y}
    [IsOpenImmersion u.hom.left] [IsOpenImmersion v.hom.left]
    (sq : IsPullback u.hom.left f'.hom.left f.hom.left v.hom.left)
    (c d : Compactification f.hom.left) (K : Ambient Λ X.obj.left)
    (hK : ctf Λ X.obj.left K) (huK : ctf Λ U.obj.left ((pull Λ u.hom.left).obj K)),
    (pull Λ v.hom.left).map (compare f c d K hK).hom ≫
        (supportRestriction Λ sq d).app K =
      (supportRestriction Λ sq c).app K ≫
        (compare f' (c.ofIsPullback sq) (d.ofIsPullback sq)
          ((pull Λ u.hom.left).obj K) huK).hom
  restriction_successive : ∀ {X Y U V U' V' : WeilConjectures.SixFunctorSpace D}
    {f : X ⟶ Y} {f' : U ⟶ V} {f'' : U' ⟶ V'}
    {u : U ⟶ X} {v : V ⟶ Y} {u' : U' ⟶ U} {v' : V' ⟶ V}
    [IsOpenImmersion u.hom.left] [IsOpenImmersion v.hom.left]
    [IsOpenImmersion u'.hom.left] [IsOpenImmersion v'.hom.left]
    (sq : IsPullback u.hom.left f'.hom.left f.hom.left v.hom.left)
    (sq' : IsPullback u'.hom.left f''.hom.left f'.hom.left v'.hom.left)
    (c : Compactification f.hom.left) (K : Ambient Λ X.obj.left)
    (hK : ctf Λ U'.obj.left ((pull Λ u'.hom.left).obj ((pull Λ u.hom.left).obj K))),
    (scalarSixPullComp Λ v'.hom.left v.hom.left).hom.app ((support Λ c).obj K) ≫
        (pull Λ v'.hom.left).map ((supportRestriction Λ sq c).app K) ≫
        (supportRestriction Λ sq' (c.ofIsPullback sq)).app ((pull Λ u.hom.left).obj K) ≫
        (compare f'' ((c.ofIsPullback sq).ofIsPullback sq')
          (c.ofIsPullback (sq'.paste_horiz sq))
          ((pull Λ u'.hom.left).obj ((pull Λ u.hom.left).obj K)) hK).hom ≫
        (support Λ (c.ofIsPullback (sq'.paste_horiz sq))).map
          ((scalarSixPullComp Λ u'.hom.left u.hom.left).inv.app K) =
      (supportRestriction Λ (sq'.paste_horiz sq) c).app K
  projection : ∀ {X Y U V : WeilConjectures.SixFunctorSpace D}
    {f : X ⟶ Y} {f' : U ⟶ V} {u : U ⟶ X} {v : V ⟶ Y}
    [IsOpenImmersion u.hom.left] [IsOpenImmersion v.hom.left]
    (sq : IsPullback u.hom.left f'.hom.left f.hom.left v.hom.left)
    (c : Compactification f.hom.left) (K : Ambient Λ X.obj.left)
    (N : Ambient Λ Y.obj.left),
    (pull Λ v.hom.left).map (supportProjection Λ c K N) ≫
        (supportRestriction Λ sq c).app (K ⊗ (pull Λ f.hom.left).obj N) ≫
        (support Λ (c.ofIsPullback sq)).map
          ((tensorRestriction Λ u.hom.left K ((pull Λ f.hom.left).obj N)).hom ≫
            (𝟙 ((pull Λ u.hom.left).obj K) ⊗ₘ
              (derivedOpenCoherencePullbackSquare Λ.X sq.toCommSq).inv.app N)) =
      (tensorRestriction Λ v.hom.left ((support Λ c).obj K) N).hom ≫
        ((supportRestriction Λ sq c).app K ⊗ₘ 𝟙 ((pull Λ v.hom.left).obj N)) ≫
        supportProjection Λ (c.ofIsPullback sq) ((pull Λ u.hom.left).obj K)
          ((pull Λ v.hom.left).obj N)
  exceptional : ∀ {X Y U V : WeilConjectures.SixFunctorSpace D}
    {f : X ⟶ Y} {f' : U ⟶ V} {u : U ⟶ X} {v : V ⟶ Y}
    [IsOpenImmersion u.hom.left] [IsOpenImmersion v.hom.left]
    (sq : IsPullback u.hom.left f'.hom.left f.hom.left v.hom.left)
    (c : Compactification f.hom.left) (R : ConstructibleAdjoint Λ c)
    (T : ConstructibleAdjoint Λ (c.ofIsPullback sq)),
    ∃ h : ∀ K : (ctf Λ Y.obj.left).FullSubcategory,
        ctf Λ V.obj.left ((pull Λ v.hom.left).obj K.obj),
      ∃! e : ExceptionalIso Λ sq c R T h, ExceptionalNormalized Λ sq c R T h e


  exceptional_successive : ∀ {X Y U V U' V' : WeilConjectures.SixFunctorSpace D}
    {f : X ⟶ Y} {f' : U ⟶ V} {f'' : U' ⟶ V'}
    {u : U ⟶ X} {v : V ⟶ Y} {u' : U' ⟶ U} {v' : V' ⟶ V}
    [IsOpenImmersion u.hom.left] [IsOpenImmersion v.hom.left]
    [IsOpenImmersion u'.hom.left] [IsOpenImmersion v'.hom.left]
    (sq : IsPullback u.hom.left f'.hom.left f.hom.left v.hom.left)
    (sq' : IsPullback u'.hom.left f''.hom.left f'.hom.left v'.hom.left)
    (c : Compactification f.hom.left)
    (R : ConstructibleAdjoint Λ c)
    (T : ConstructibleAdjoint Λ (c.ofIsPullback sq))
    (W : ConstructibleAdjoint Λ ((c.ofIsPullback sq).ofIsPullback sq'))
    (A : ConstructibleAdjoint Λ (c.ofIsPullback (sq'.paste_horiz sq)))
    (h : ∀ N : (ctf Λ Y.obj.left).FullSubcategory,
      ctf Λ V.obj.left ((pull Λ v.hom.left).obj N.obj))
    (h' : ∀ N : (ctf Λ V.obj.left).FullSubcategory,
      ctf Λ V'.obj.left ((pull Λ v'.hom.left).obj N.obj))
    (hcomp : ∀ N : (ctf Λ Y.obj.left).FullSubcategory,
      ctf Λ V'.obj.left ((pull Λ (v'.hom.left ≫ v.hom.left)).obj N.obj))
    (e : ExceptionalIso Λ sq c R T h)
    (e' : ExceptionalIso Λ sq' (c.ofIsPullback sq) T W h')
    (ecomp : ExceptionalIso Λ (sq'.paste_horiz sq) c R A hcomp)
    (_he : ExceptionalNormalized Λ sq c R T h e)
    (_he' : ExceptionalNormalized Λ sq' (c.ofIsPullback sq) T W h' e')
    (_hecomp : ExceptionalNormalized Λ (sq'.paste_horiz sq) c R A hcomp ecomp)
    (b : W.upper ⋙ (ctf Λ U'.obj.left).ι ≅ A.upper ⋙ (ctf Λ U'.obj.left).ι)
    (_hb : ∀ N : (ctf Λ V'.obj.left).FullSubcategory,
      (compare f'' ((c.ofIsPullback sq).ofIsPullback sq')
          (c.ofIsPullback (sq'.paste_horiz sq)) (W.upper.obj N).obj
          (W.upper.obj N).property).hom ≫
        (support Λ (c.ofIsPullback (sq'.paste_horiz sq))).map (b.hom.app N) ≫
          A.counit N = W.counit N)
    (N : (ctf Λ Y.obj.left).FullSubcategory),
    ∃ t : (scalarExceptionalPull v'.hom.left h').obj
          ((scalarExceptionalPull v.hom.left h).obj N) ⟶
        (scalarExceptionalPull (v'.hom.left ≫ v.hom.left) hcomp).obj N,
      t.hom = (scalarSixPullComp Λ v'.hom.left v.hom.left).inv.app N.obj ∧
      (scalarSixPullComp Λ u'.hom.left u.hom.left).hom.app (R.upper.obj N).obj ≫
          (pull Λ u'.hom.left).map (e.hom.app N) ≫
          e'.hom.app ((scalarExceptionalPull v.hom.left h).obj N) ≫
          b.hom.app ((scalarExceptionalPull v'.hom.left h').obj
            ((scalarExceptionalPull v.hom.left h).obj N)) ≫
          (A.upper.map t).hom = ecomp.hom.app N

/-- Ordinary scalar extension restricted to its actual full finite-Tor constructible
subcategory. Source: coefficient paragraph
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
abbrev scalarCtf {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (X : Scheme.{u})
    (h : ∀ K : (ctf Λ X).FullSubcategory, ctf Λ' X ((scalarSixChange a X).obj K.obj)) :=
  (ctf Λ' X).lift ((ctf Λ X).ι ⋙ scalarSixChange a X) h

set_option maxHeartbeats 1600000 in
-- Keep the canonical functor and module instances during elaboration.
/-- Specialize the recorded scalar-mates domains to precisely Dctf, using membership
certificates rather than replacing any operation. Source: coefficient paragraph
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
def scalarDomains (g : CondensedScalarShriekMates.Geometry.{u})
    (R : ConstructibleAdjoint g.Λ g.compactification.obj.obj)
    (S : ConstructibleAdjoint g.Λ' g.compactification.obj.obj)
    (hX : ∀ K : (ctf g.Λ g.X.left).FullSubcategory,
      ctf g.Λ' g.X.left ((scalarSixChange g.a g.X.left).obj K.obj))
    (hY : ∀ K : (ctf g.Λ g.Y.left).FullSubcategory,
      ctf g.Λ' g.Y.left ((scalarSixChange g.a g.Y.left).obj K.obj)) :
    CondensedScalarShriekMates.Domains g where
  source := ctf g.Λ g.X.left
  target := ctf g.Λ g.Y.left
  source' := ctf g.Λ' g.X.left
  target' := ctf g.Λ' g.Y.left
  lower_mem := R.lower_preserves
  lower_mem' := S.lower_preserves
  scalar_source_mem := hX
  scalar_target_mem := hY

set_option maxHeartbeats 1600000 in
-- Elaborate the supplied adjunction and its full subcategory instances together.
/-- Exactly the dependency's exceptional scalar transpose; only gamma is inverted.
Source: coefficient paragraph, displayed exceptional transpose
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
abbrev scalarBeta (g : CondensedScalarShriekMates.Geometry.{u})
    (R : ConstructibleAdjoint g.Λ g.compactification.obj.obj)
    (S : ConstructibleAdjoint g.Λ' g.compactification.obj.obj)
    (hX : ∀ K : (ctf g.Λ g.X.left).FullSubcategory,
      ctf g.Λ' g.X.left ((scalarSixChange g.a g.X.left).obj K.obj))
    (hY : ∀ K : (ctf g.Λ g.Y.left).FullSubcategory,
      ctf g.Λ' g.Y.left ((scalarSixChange g.a g.Y.left).obj K.obj))
    (N : (ctf g.Λ g.Y.left).FullSubcategory)
    [hgamma : IsIso ((CondensedScalarShriekMates.compactificationScalarMap g).app
      (R.upper.obj N).obj)] :=
  CondensedScalarShriekMates.exceptionalScalarTranspose (scalarDomains g R S hX hY)
    R.upper R.restrictedAdjunction S.upper S.restrictedAdjunction N

set_option maxHeartbeats 1600000 in
-- Keep the canonical functor and module instances during elaboration.
/-- Base change of the dependency's scalar geometry, keeping the actual compactification
and coefficient arrow. The redundant finite-type certificates are inferred for a base
change of the original separated finite-type map. Source: coefficient paragraph
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
def restrictedGeometry (g : CondensedScalarShriekMates.Geometry.{u})
    {U V : Over (Spec (.of g.field.k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    (f' : U ⟶ V)
    (u : U ⟶ g.X) (v : V ⟶ g.Y)
    (sq : IsPullback u.left f'.left g.f.left v.left) :
    CondensedScalarShriekMates.Geometry.{u} where
  field := g.field
  ell := g.ell
  prime := g.prime
  different := g.different
  Λ := g.Λ
  Λ' := g.Λ'
  a := g.a
  listed := g.listed
  X := U
  Y := V
  f := f'
  separated := MorphismProperty.IsStableUnderBaseChange.of_isPullback sq g.separated
  finiteType := MorphismProperty.IsStableUnderBaseChange.of_isPullback sq g.finiteType
  quasiCompact := MorphismProperty.IsStableUnderBaseChange.of_isPullback sq g.quasiCompact
  compactification := ⟨⟨g.compactification.obj.obj.ofIsPullback sq,
    (g.compactification.obj.obj.ofIsPullback sq).quasiCompact_openImmersion_iff.mpr
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback sq g.quasiCompact)⟩⟩

set_option maxHeartbeats 1600000 in
-- The full coherent diagram is elaborated in the ordinary derived module categories.
/-- Equations for the actual listed-coefficient arrows, before asserting their
invertibility. Source: coefficient paragraph
(blueprint: lem-sf-condensed-affine-restriction-locality). -/
structure ScalarAssertions (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (Λ : ScalarSixRing.{u}) : Prop where
  pull_square : ∀ {Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (_ha : ListedCoefficientMap ell a)
    {X Y U V : Scheme.{u}} {f : X ⟶ Y} {f' : U ⟶ V} {u : U ⟶ X} {v : V ⟶ Y}
    [IsOpenImmersion u] [IsOpenImmersion v]
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [U.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))]
    [QuasiCompact (U ↘ Spec (.of D.k))]
    [V.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of D.k))]
    [QuasiCompact (V ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))]
    [f'.IsOver (Spec (.of D.k))]
    [u.IsOver (Spec (.of D.k))]
    [v.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback u f' f v) (N : Ambient Λ Y),
    (pull Λ' u).map ((scalarDirectImagePullbackData.theta a f).inv.app N) ≫
        (scalarDirectImagePullbackData.theta a u).inv.app ((pull Λ f).obj N) ≫
        (scalarSixChange a U).map
          ((derivedOpenCoherencePullbackSquare Λ.X sq.toCommSq).inv.app N) =
      (derivedOpenCoherencePullbackSquare Λ'.X sq.toCommSq).inv.app
          ((scalarSixChange a Y).obj N) ≫
        (pull Λ' f').map ((scalarDirectImagePullbackData.theta a v).inv.app N) ≫
        (scalarDirectImagePullbackData.theta a f').inv.app ((pull Λ v).obj N)
  tensor_square : ∀ {Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (_ha : ListedCoefficientMap ell a)
    {T Z : Scheme.{u}} (w : T ⟶ Z) [IsOpenImmersion w]
    [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    [w.IsOver (Spec (.of D.k))]
    (K L : Ambient Λ Z),
    (pull Λ' w).map (scalarSixTensorIso a Z K L).hom ≫
        (tensorRestriction Λ' w ((scalarSixChange a Z).obj K)
          ((scalarSixChange a Z).obj L)).hom ≫
        ((scalarDirectImagePullbackData.theta a w).inv.app K ⊗ₘ
          (scalarDirectImagePullbackData.theta a w).inv.app L) =
      (scalarDirectImagePullbackData.theta a w).inv.app (K ⊗ L) ≫
        (scalarSixChange a T).map (tensorRestriction Λ w K L).hom ≫
        (scalarSixTensorIso a T ((pull Λ w).obj K) ((pull Λ w).obj L)).hom
  hom_square : ∀ {Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (_ha : ListedCoefficientMap ell a)
    {T Z : Scheme.{u}} (w : T ⟶ Z) [IsOpenImmersion w]
    [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    [w.IsOver (Spec (.of D.k))]
    (K L : Ambient Λ Z),
    (pull Λ' w).map (scalarSixHomComparison a Z K L) ≫
        homRestriction Λ' w ((scalarSixChange a Z).obj K) ((scalarSixChange a Z).obj L) ≫
        ((derivedHom Λ'.X T).map
          ((scalarDirectImagePullbackData.theta a w).hom.app K).op).app
            ((pull Λ' w).obj ((scalarSixChange a Z).obj L)) ≫
        ((derivedHom Λ'.X T).obj (op ((scalarSixChange a T).obj ((pull Λ w).obj K)))).map
          ((scalarDirectImagePullbackData.theta a w).inv.app L) =
      (scalarDirectImagePullbackData.theta a w).inv.app (hom Λ Z K L) ≫
        (scalarSixChange a T).map (homRestriction Λ w K L) ≫
        scalarSixHomComparison a T ((pull Λ w).obj K) ((pull Λ w).obj L)
  direct_square : ∀ {Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (_ha : ListedCoefficientMap ell a)
    {X Y U V : Scheme.{u}} {f : X ⟶ Y} {f' : U ⟶ V} {u : U ⟶ X} {v : V ⟶ Y}
    [IsOpenImmersion u] [IsOpenImmersion v]
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [U.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))]
    [QuasiCompact (U ↘ Spec (.of D.k))]
    [V.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of D.k))]
    [QuasiCompact (V ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))]
    [f'.IsOver (Spec (.of D.k))]
    [u.IsOver (Spec (.of D.k))]
    [v.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback u f' f v) (K : Ambient Λ X),
    (pull Λ' v).map ((scalarDirectImageMate a f).app K) ≫
        (derivedDirectImageOpenRestriction Λ'.X sq.toCommSq).app
          ((scalarSixChange a X).obj K) ≫
        (push Λ' f').map ((scalarDirectImagePullbackData.theta a u).inv.app K) =
      (scalarDirectImagePullbackData.theta a v).inv.app ((push Λ f).obj K) ≫
        (scalarSixChange a V).map ((derivedDirectImageOpenRestriction Λ.X sq.toCommSq).app K) ≫
        (scalarDirectImageMate a f').app ((pull Λ u).obj K)
  support_square : ∀ {Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (_ha : ListedCoefficientMap ell a)
    {X Y U V : Scheme.{u}} {f : X ⟶ Y} {f' : U ⟶ V} {u : U ⟶ X} {v : V ⟶ Y}
    [IsOpenImmersion u] [IsOpenImmersion v]
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [U.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))]
    [QuasiCompact (U ↘ Spec (.of D.k))]
    [V.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of D.k))]
    [QuasiCompact (V ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))]
    [f'.IsOver (Spec (.of D.k))]
    [u.IsOver (Spec (.of D.k))]
    [v.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback u f' f v) (c : Compactification f) (K : Ambient Λ X),
    (pull Λ' v).map ((scalarCompactSupportMap a c.i c.g).app K) ≫
        (supportRestriction Λ' sq c).app ((scalarSixChange a X).obj K) ≫
        (support Λ' (c.ofIsPullback sq)).map
          ((scalarDirectImagePullbackData.theta a u).inv.app K) =
      (scalarDirectImagePullbackData.theta a v).inv.app ((support Λ c).obj K) ≫
        (scalarSixChange a V).map ((supportRestriction Λ sq c).app K) ≫
        (scalarCompactSupportMap a (c.ofIsPullback sq).i (c.ofIsPullback sq).g).app
          ((pull Λ u).obj K)
  open_square : ∀ {Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (_ha : ListedCoefficientMap ell a)
    {X Z U W : Scheme.{u}} {j : X ⟶ Z} {j' : U ⟶ W} {u : U ⟶ X} {h : W ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion u] [IsOpenImmersion h]
    [X.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [U.Over (Spec (.of D.k))] [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [j.IsOver (Spec (.of D.k))] [j'.IsOver (Spec (.of D.k))]
    [u.IsOver (Spec (.of D.k))] [h.IsOver (Spec (.of D.k))]
    (sq : IsPullback u j' j h) (K : Ambient Λ X),
    (pull Λ' h).map
        ((derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j).hom.app K) ≫
        (extensionRestriction Λ' sq).hom.app ((scalarSixChange a X).obj K) ≫
        (extension Λ' j').map ((scalarDirectImagePullbackData.theta a u).inv.app K) =
      (scalarDirectImagePullbackData.theta a h).inv.app ((extension Λ j).obj K) ≫
        (scalarSixChange a W).map ((extensionRestriction Λ sq).hom.app K) ≫
        (derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j').hom.app
          ((pull Λ u).obj K)
  scalar_refinement : ∀ (g : CondensedScalarShriekMates.Geometry.{u})
    (_hf : g.field = D) (_hell : g.ell = ell) (_hΛ : g.Λ = Λ)
    (d : Compactification.BoundaryCompactification g.f.left) (r : d ⟶ g.compactification)
    (K : Ambient g.Λ g.X.left) (_hK : ctf g.Λ g.X.left K),
    (scalarSixChange g.a g.Y.left).map
        (compactificationRefinementComponent g.Λ.X r K) ≫
        (scalarCompactSupportMap g.a d.obj.obj.i d.obj.obj.g).app K =
      (CondensedScalarShriekMates.compactificationScalarMap g).app K ≫
        compactificationRefinementComponent g.Λ'.X r ((scalarSixChange g.a g.X.left).obj K)
  gamma_isIso : ∀ (g : CondensedScalarShriekMates.Geometry.{u})
    (_hf : g.field = D) (_hell : g.ell = ell) (_hΛ : g.Λ = Λ)
    (K : (ctf g.Λ g.X.left).FullSubcategory),
    IsIso ((CondensedScalarShriekMates.compactificationScalarMap g).app K.obj)
  scalar_preserves : ∀ (g : CondensedScalarShriekMates.Geometry.{u})
    (_hf : g.field = D) (_hell : g.ell = ell) (_hΛ : g.Λ = Λ),
    (∀ K : (ctf g.Λ g.X.left).FullSubcategory,
      ctf g.Λ' g.X.left ((scalarSixChange g.a g.X.left).obj K.obj)) ∧
    (∀ K : (ctf g.Λ g.Y.left).FullSubcategory,
      ctf g.Λ' g.Y.left ((scalarSixChange g.a g.Y.left).obj K.obj))
  exceptional_square : ∀ (g : CondensedScalarShriekMates.Geometry.{u})
    (_hf : g.field = D) (_hell : g.ell = ell) (_hΛ : g.Λ = Λ)
    {U V : Over (Spec (.of g.field.k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    (f' : U ⟶ V)
    (u : U ⟶ g.X) (v : V ⟶ g.Y) [IsOpenImmersion u.left] [IsOpenImmersion v.left]
    (sq : IsPullback u.left f'.left g.f.left v.left)
    (R : ConstructibleAdjoint g.Λ g.compactification.obj.obj)
    (S : ConstructibleAdjoint g.Λ' g.compactification.obj.obj)
    (T : ConstructibleAdjoint g.Λ (g.compactification.obj.obj.ofIsPullback sq))
    (T' : ConstructibleAdjoint g.Λ' (g.compactification.obj.obj.ofIsPullback sq))
    (hX : ∀ K : (ctf g.Λ g.X.left).FullSubcategory,
      ctf g.Λ' g.X.left ((scalarSixChange g.a g.X.left).obj K.obj))
    (hY : ∀ K : (ctf g.Λ g.Y.left).FullSubcategory,
      ctf g.Λ' g.Y.left ((scalarSixChange g.a g.Y.left).obj K.obj))
    (hU : ∀ K : (ctf g.Λ U.left).FullSubcategory,
      ctf g.Λ' U.left ((scalarSixChange g.a U.left).obj K.obj))
    (hV : ∀ K : (ctf g.Λ V.left).FullSubcategory,
      ctf g.Λ' V.left ((scalarSixChange g.a V.left).obj K.obj))
    (hv : ∀ K : (ctf g.Λ g.Y.left).FullSubcategory,
      ctf g.Λ V.left ((pull g.Λ v.left).obj K.obj))
    (hv' : ∀ K : (ctf g.Λ' g.Y.left).FullSubcategory,
      ctf g.Λ' V.left ((pull g.Λ' v.left).obj K.obj))
    (e : ExceptionalIso g.Λ sq g.compactification.obj.obj R T hv)
    (e' : ExceptionalIso g.Λ' sq g.compactification.obj.obj S T' hv')
    (_he : ExceptionalNormalized g.Λ sq g.compactification.obj.obj R T hv e)
    (_he' : ExceptionalNormalized g.Λ' sq g.compactification.obj.obj S T' hv' e')
    (N : (ctf g.Λ g.Y.left).FullSubcategory),
    ∃ t : (scalarCtf g.a V.left hV).obj ((scalarExceptionalPull v.left hv).obj N) ⟶
        (scalarExceptionalPull v.left hv').obj ((scalarCtf g.a g.Y.left hY).obj N),
      t.hom = (scalarDirectImagePullbackData.theta g.a v.left).hom.app N.obj ∧
      (scalarSixChange g.a U.left).map (e.hom.app N) ≫
          (scalarBeta (restrictedGeometry g f' u v sq) T T' hU hV
            ((scalarExceptionalPull v.left hv).obj N)
            (hgamma := gamma_isIso (restrictedGeometry g f' u v sq) _hf _hell _hΛ
              (T.upper.obj ((scalarExceptionalPull v.left hv).obj N)))).hom ≫
          (T'.upper.map t).hom =
        (scalarDirectImagePullbackData.theta g.a u.left).hom.app (R.upper.obj N).obj ≫
          (pull g.Λ' u.left).map (scalarBeta g R S hX hY N
            (hgamma := gamma_isIso g _hf _hell _hΛ (R.upper.obj N))).hom ≫
          e'.hom.app ((scalarCtf g.a g.Y.left hY).obj N)

/-- Finite-cover locality, phrased for existing ambient arrows. Source: Step 2,
finite open tests (blueprint: lem-sf-condensed-affine-restriction-locality). -/
def CoverAssertions (D : WeilConjectures.FiniteFieldDatum.{u}) (Λ : ScalarSixRing.{u}) : Prop :=
  ∀ (Z : WeilConjectures.SixFunctorSpace D) (I : Type u) [Finite I]
    (V : I → Scheme.{u}) (w : ∀ i : I, V i ⟶ Z.obj.left)
    [∀ i : I, IsOpenImmersion (w i)]
    (_cover : ∀ z : Z.obj.left, ∃ (i : I) (x : V i), (w i).base x = z),
    (∀ K : Ambient Λ Z.obj.left,
      ctf Λ Z.obj.left K ↔ ∀ i : I, ctf Λ (V i) ((pull Λ (w i)).obj K)) ∧
    (∀ {K L : Ambient Λ Z.obj.left} (a : K ⟶ L),
      (∀ i : I, IsIso ((pull Λ (w i)).map a)) → IsIso a)

/-- Open restriction for all six ordinary condensed constructions and their actual
comparison arrows, on the full finite-type (possibly non-separated) setting.
Source: latest blueprint fix-lem-tensor-adjunction.proof.md, Step 2 and coefficient paragraph
(blueprint: lem-sf-condensed-affine-restriction-locality).

Proof (the thirteen steps of the node):
1. Cartesian coefficients identify module inverse image with exact inverse image.
The open slice comparison, its exact extension and localized adjunction include units
and counits. Composition gives the pullback restriction isomorphism.
2. Restrict signed total tensor on K-flat resolutions. The open adjunction and open
projection formula give the displayed closed Hom bijections; Yoneda gives the
isomorphism whose transpose is restricted evaluation.
3. Restrict a K-injective representative of the direct image. The sectionwise map
is identity under the Cartesian fibre-product identification. Its actual counit,
and hence its unit, descend by the localized adjunction.
4. Finite-type schemes are Noetherian. Choose a common finite cohomology interval
and refine finitely many local strata by the ordered finite cover. Restrict their
finite scalar presentations. This proves local bounded constructibility.
5. Choose a common finite Tor interval. Restrict tensor tests and detect vanishing
by the cover. In the converse direction extend a local test module by zero. The
same open projection formula preserves Tor intervals and bounded constructibility
under extension by zero. Empty covers use the interval [0,0].
6. Restrict Rp_*j_! by the displayed proper/open word. For a proper refinement use
the non-separated proper/open interchange, its open-unit normalization and its
uniqueness. Restriction preserves that normalization; common refinements give
compactification independence and the cocycle.
7. Proper/open interchange and open composition identify Rf_!u_! with v_!RfV_!.
The supplied constructible adjunctions and exact open adjunctions give the displayed
exceptional Hom chain. Yoneda gives precisely the counit-normalized restriction.
8. Restrict the counit transpose defining the proper projection, then its normalized
open factor. Adjunction injectivity gives the equality of actual projection arrows;
the same argument identifies evaluation.
9. On restricted K-flat scalar resolutions, balancing identifies the scalar/tensor
word with its restricted word. Transpose evaluation to obtain the scalar/Hom square,
without assuming this comparison invertible.
10. Restrict the actual direct-image scalar unit/counit word. Mate pasting gives its
square. The open scalar factor is unit normalized. Their composite is exactly the
recorded compact-support scalar map, including its refinement equation.
11. Cover the target by affine opens. Each proper compactification over an affine
target is separated; the separated scalar theorem inverts gamma on each chart.
Cover conservativity gives its inverse globally, without inverting exceptional beta.
12. Restrict the defining gamma-inverse/counit transpose of exceptional beta.
The preceding actual-arrow equations identify it with the transpose on the open;
adjunction injectivity proves the exceptional scalar square.
13. Pasting the normalized words proves successive-open coherence. Finally apply
exact cohomology and cover conservativity to the cone of an existing arrow. This
detects isomorphisms, and makes no assertion detecting equality of arbitrary arrows. -/
theorem condensedAffineRestrictionLocality
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (_hell : ell ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (_hn : 1 ≤ n) (Λ : ScalarSixRing.{u})
    (_hΛ : Nonempty (Mon.mk Λ.X ≅ Mon.mk (properOpenFiniteCoefficient ell E n)) ∨
      Nonempty (Mon.mk Λ.X ≅ Mon.mk (properOpenIntegralCoefficient ell E)) ∨
      Nonempty (Mon.mk Λ.X ≅ Mon.mk (properOpenFieldCoefficient ell E)) ∨
      Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicAlgClRingObj ell))) :
    AmbientAssertions D Λ ∧ Nonempty (SupportAssertions D Λ) ∧
      ScalarAssertions D ell Λ ∧ CoverAssertions D Λ := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.AffineRestrictionLocality
