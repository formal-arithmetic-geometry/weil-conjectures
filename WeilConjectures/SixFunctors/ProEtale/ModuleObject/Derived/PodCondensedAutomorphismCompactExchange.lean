/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
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
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedHomData
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.WeilSheaf.StrictWeilComplexNotFaithful
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralRestriction.IntegralRestrictionBoundedDescent
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantStratifiedZariskiLocality
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
public import WeilConjectures.CategoryTheory.CompactlyGenerated
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenBoundaryZero
public import WeilConjectures.AlgebraicGeometry.SixFunctors.QcqsProperConstructibleClosedBaseChange
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
public import WeilConjectures.CategoryTheory.BrownRepresentabilityRightAdjoint
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.BaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.EquivalenceAdjunctionComparisonSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ModuleOpenPasting.ModuleDirectImageOpenPasting
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compact.CompactSupportOpenRefinementPasting
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compact.CompactSupportProperTriangle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageOpenCoherenceData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
import WeilConjectures.Compactification.BoundaryRefinement
import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageOpenCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackCoherence
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.CategoryTheory.Adjunction.CondensedSixOperationPreservation

/-! # Concrete geometric-Frobenius compact-support exchange

Source: latest blueprint, sec-poincare-duality/sk-thm-frobenius/
prop-weil-operations.proof.md, sentence 2, and sec-six-functors/sk-rem-sf-pf-done/
lem-fix-weil-operations.proof.md, paragraphs 1--3.
(blueprint: lem-pod-condensed-automorphism-compact-exchange).

All categories below are ordinary condensed module derived categories, or their full
bounded constructible subcategories. In particular the exceptional adjunction is only
on constructibles. No ambient exceptional adjoint or Weil datum is a hypothesis.

## Main definitions and statement

* `podGeometricBaseChange` and `podGeometricCompactification` give the actual scalar extension.
* `podAutomorphismPullbackInverse` is the canonical inverse-pullback comparison.
* `PodFixedPairAdjunctionNormalization` states the mate, Hom, unit and counit formulas.
* `PodCompactAutomorphismData` packages the concrete recipe and all its coherences.
* `pod_condensed_automorphism_compact_exchange` asserts these properties for geometric Frobenius.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u uC uD vC vD
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
attribute [local irreducible] HasDerivedCategory.standard
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory DerivedCategory.monoidalClosed
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Scalar extension to the fixed algebraic closure, on models and their maps.
Source: geometric-fibre paragraph of the node
(blueprint: lem-pod-condensed-automorphism-compact-exchange). -/
abbrev podGeometricBaseChange (D : WeilConjectures.FiniteFieldDatum.{u}) :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- Base change of the chosen model compactification, with its actual two factors.
Source: compactification recipe, proof step 2
(blueprint: lem-pod-condensed-automorphism-compact-exchange). -/
def podGeometricCompactification (D : WeilConjectures.FiniteFieldDatum.{u})
    {X Y : Over (Spec (.of D.k₀))} {f : X ⟶ Y} (c : Compactification f.left) :
    Compactification (((podGeometricBaseChange D).map f).left) where
  Z := ((podGeometricBaseChange D).obj c.overObj).left
  i := ((podGeometricBaseChange D).map c.overI).left
  g := ((podGeometricBaseChange D).map c.overG).left
  comm := by
    change ((podGeometricBaseChange D).map f).left =
      (((podGeometricBaseChange D).map c.overI) ≫
        ((podGeometricBaseChange D).map c.overG)).left
    rw [← Functor.map_comp]
    rw [c.overI_overG]
  isOpenImmersion := MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
    _ c.overI c.isOpenImmersion
  isProper := MorphismProperty.overPullbackMap (P := @IsProper)
    _ c.overG c.isProper

/-- Concrete exchange data for the pulled-back condensed coefficient categories.
Source: latest blueprint prop-weil-operations.proof.md, sentence 2, and
lem-fix-weil-operations.proof.md, paragraphs 1--3
(blueprint: lem-pod-condensed-automorphism-compact-exchange). -/
abbrev podBCX (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (X : Over (Spec (.of D.k₀))) :=
  BoundedConstructible (condensedRingObj Λ ((podGeometricBaseChange D).obj X).left)

/-- The target bounded constructible category.
Source: the node’s constructible operations clause
(blueprint: lem-pod-condensed-automorphism-compact-exchange). -/
abbrev podBCY (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (Y : Over (Spec (.of D.k₀))) :=
  BoundedConstructible (condensedRingObj Λ ((podGeometricBaseChange D).obj Y).left)

/-- The actual compactification functor restricted to constructibles.
Source: the node’s constructible operations clause
(blueprint: lem-pod-condensed-automorphism-compact-exchange). -/
abbrev podF (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (D : WeilConjectures.FiniteFieldDatum.{u}) {X Y : Over (Spec (.of D.k₀))}
    (f : X ⟶ Y) (c : Compactification f.left)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType f.left]
    (h : ∀ K : podBCX Λ D X,
      boundedConstructible (condensedRingObj Λ ((podGeometricBaseChange D).obj Y).left)
        ((F Λ (podGeometricCompactification D c)).obj K.obj)) :
    podBCX Λ D X ⥤ podBCY Λ D Y :=
  (boundedConstructible (condensedRingObj Λ ((podGeometricBaseChange D).obj Y).left)).lift
    ((boundedConstructible (condensedRingObj Λ ((podGeometricBaseChange D).obj X).left)).ι ⋙
    F Λ (podGeometricCompactification D c)) h

/-- Geometric-Frobenius pullback restricted on the source.
Source: the node’s constructible operations clause
(blueprint: lem-pod-condensed-automorphism-compact-exchange). -/
abbrev podPX (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (X : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (h : ∀ K : podBCX Λ D X,
      boundedConstructible (condensedRingObj Λ ((podGeometricBaseChange D).obj X).left)
        ((P Λ (D.geometricFrobenius X).hom).obj K.obj)) :
    podBCX Λ D X ⥤ podBCX Λ D X :=
  (boundedConstructible (condensedRingObj Λ ((podGeometricBaseChange D).obj X).left)).lift
    ((boundedConstructible (condensedRingObj Λ ((podGeometricBaseChange D).obj X).left)).ι ⋙
      P Λ (D.geometricFrobenius X).hom) h

/-- Geometric-Frobenius pullback restricted on the target.
Source: the node’s constructible operations clause
(blueprint: lem-pod-condensed-automorphism-compact-exchange). -/
abbrev podPY (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (Y : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (h : ∀ K : podBCY Λ D Y,
      boundedConstructible (condensedRingObj Λ ((podGeometricBaseChange D).obj Y).left)
        ((P Λ (D.geometricFrobenius Y).hom).obj K.obj)) :
    podBCY Λ D Y ⥤ podBCY Λ D Y :=
  (boundedConstructible (condensedRingObj Λ ((podGeometricBaseChange D).obj Y).left)).lift
    ((boundedConstructible (condensedRingObj Λ ((podGeometricBaseChange D).obj Y).left)).ι ⋙
      P Λ (D.geometricFrobenius Y).hom) h

/-- The localizing exceptional adjunction and its normalized constructible restriction.
Source: the preservation clause used in proof steps 1 and 10
(blueprint: lem-pod-condensed-automorphism-compact-exchange). -/
def PodPreservationAdjunction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : Prop :=
  ∃ (h : ∀ K, localizingClosureProEtale Λ X K →
      localizingClosureProEtale Λ Y ((F Λ c).obj K))
    (_hCX : boundedConstructible (condensedRingObj Λ X) ≤ localizingClosureProEtale Λ X)
    (_hCY : boundedConstructible (condensedRingObj Λ Y) ≤ localizingClosureProEtale Λ Y),
    ∃ (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
        (localizingClosureProEtale Λ X).FullSubcategory)
      (adj : localizingLowerShriek Λ c h ⊣ G),
      adj.RestrictsWithOriginalHomEquiv
        (fun K ↦ boundedConstructible (condensedRingObj Λ X) K.obj)
        (fun L ↦ boundedConstructible (condensedRingObj Λ Y) L.obj)

private theorem pod_compactification_exists
    (D : WeilConjectures.FiniteFieldDatum.{u})
    {X Y : Over (Spec (.of D.k₀))} (f : X ⟶ Y)
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [LocallyOfFiniteType f.left] [QuasiCompact f.left] [IsSeparated f.left] :
    Nonempty (Compactification f.left) := by
  let _ : CompactSpace (Spec (CommRingCat.of D.k₀)) := inferInstance
  let _ : QuasiSeparatedSpace (Spec (CommRingCat.of D.k₀)) := inferInstance
  let _ : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  let _ : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  exact ⟨AlgebraicGeometry.NagataCompactification f.left⟩

open CompactificationReindexing

set_option maxHeartbeats 1600000 in
-- The proposition compares several large native derived-functor endpoints.
end AlgebraicGeometry.ProEtale.CondensedRing
