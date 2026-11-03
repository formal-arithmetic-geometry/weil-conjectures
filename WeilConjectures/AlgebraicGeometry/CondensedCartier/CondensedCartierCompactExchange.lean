/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCanonicalClass
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportFiniteLines
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportExchangeTransport
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarLines
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
public import WeilConjectures.ProEtaleCoefficients.BoundedConstructibleCounterexample.NonFiniteMultiplicationKernel
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.SheafTensor
public import Mathlib.Algebra.TrivSqZeroExt.Basic
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
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityDivisorClass
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassSystems
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal

/-! # Condensed Cartier classes and normalized compact-support exchange

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
thm-pur-rank-one-thom.proof.md, Steps 1 and 3
(blueprint: lem-pur-condensed-cartier-compact-exchange).

The integral normalization below uses the inverse limit of the actual Kummer
sequences and the entire relative pole extension, before extension of scalars.
It does not characterize an integral derived arrow merely by finite evaluations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale.CondensedCartier

variable (ell : ℕ) [Fact ell.Prime]

/-- The supported unit, before deriving. Source: the source of c_D in Step 1
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
abbrev sourceModule (c : Coefficient ell) {D T : Scheme.{u}} (i : D ⟶ T) :=
  (CondensedRing.lowerStar (c.obj ell) i).obj (c.line ell D 0)

/-- Degree-two module Ext is the canonical single-to-shifted-single derived Hom.
Source: the displayed supported Cartier arrow in Step 1
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
abbrev Class (c : Coefficient ell) {D T : Scheme.{u}} (i : D ⟶ T) :=
  Ext (sourceModule ell c i) (c.line ell T 1) 2

/-- The supported class as an actual morphism in the ordinary derived category.
Source: Step 1 (blueprint: lem-pur-condensed-cartier-compact-exchange). -/
abbrev classArrow {c : Coefficient ell} {D T : Scheme.{u}} {i : D ⟶ T}
    (a : Class ell c i) := a.hom

/-- Compact image on the actual proper/open compactification model.
Source: Step 3 (blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def compactArrow {c : Coefficient ell} {D T S : Scheme.{u}}
    {i : D ⟶ T} {f : T ⟶ S} (cf : Compactification f) (a : Class ell c i) :=
  (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cf).map (classArrow ell a)

/-- The ordinary supported scalar unit, including the direct-image/scalar square.
Source: Step 3 (blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def sourceScalarUnit {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell) {D T : Scheme.{u}} (i : D ⟶ T) :
    sourceModule ell c i ⟶
      (Mod.comap (coefficientMap a.hom.hom T)).obj (sourceModule ell c' i) :=
  (CondensedRing.lowerStar (c.obj ell) i).map
      (Mod.comapUnitHom (coefficientMap a.hom.hom D)) ≫
    (CondensedRing.comapLowerStarIso a.hom.hom i).inv.app (c'.line ell D 0)

/-- The derived scalar source map is the adjunct of the full supported unit.
Source: Step 3 (blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def sourceScalarMap {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell) {D T : Scheme.{u}} (i : D ⟶ T) :
    (scalarSixChange a T).obj
        ((DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c i)) ⟶
      (DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c' i) :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap a.hom.hom T)).homEquiv _ _ |>.symm <|
      (DerivedCategory.singleFunctor _ 0).map (sourceScalarUnit ell a i) ≫
        ((Mod.comap (C := Sheaf (ProEt.topology T) Ab.{u + 1})
          (coefficientMap a.hom.hom T)).mapDerivedCategorySingleFunctor 0).inv.app
            (sourceModule ell c' i)

/-- Precisely the coefficient presentations R/pi^m, R, F and Qbar. The redundant
Zell and Qell constructors are their degree-one finite-extension cases.
Source: coefficient paragraph, Steps 1 and 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def Allowed : Coefficient ell → Prop
  | .finite A _ _ _ => ∃ (E : PadicAlgCl.FiniteIntermediateField ell)
      (π : PadicAlgCl.integers ell E.1),
      Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E.1) ∧
      ∃ m : ℕ, Nonempty (A ≃+* completedResidue ell E π m)
  | .integers | .rationals | .integral _ | .rational _ | .closure => True

/-- Retained etale antecedents for a whole arrow, using the recorded witness
rather than only asserting that its endpoints descend.
Source: finite etale-origin clause, Step 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
structure ArrowOrigin (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    {K L : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))}
    (a : K ⟶ L) where
  source : DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))
  target : DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))
  sourceIso : source.obj ≅ K
  targetIso : target.obj ≅ L
  sourceWitness : Scheme.FixedEtaleOriginWitness X A source
  targetWitness : Scheme.FixedEtaleOriginWitness X A target
  arrow : sourceWitness.complex ⟶ targetWitness.complex
  equation : sourceWitness.iso.hom ≫ sourceIso.hom ≫ a =
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map arrow.hom ≫
      targetWitness.iso.hom ≫ targetIso.hom

/-- The same whole-arrow witness in the internal finite-module coordinates.
Source: finite coefficient interpretation, Step 3
(blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def HasOrigin (c : Coefficient ell) (X : Scheme.{u})
    {K L : c.derived ell X} (a : K ⟶ L) : Prop :=
  match c, K, L, a with
  | .finite A fin _ _, _, _, a =>
    letI : Finite A := fin
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := discreteTopology_bot A
    Nonempty (ArrowOrigin (ULift.{u + 1} A) X ((finiteEncodingDerived A X).inverse.map a))
  | _, _, _, _ => True

/-- The same supported arrow and compact image commute with the actual ordinary
(noncompleted) derived scalar functor and proper/open scalar mate. This covers
all reductions and successive coefficient-field extensions.
Source: Step 3 (blueprint: lem-pur-condensed-cartier-compact-exchange). -/
def ScalarProperties (C : Family.{u} ell) {D T S : Scheme.{u}}
    (i : D ⟶ T) {f : T ⟶ S} (cf : Compactification f) : Prop :=
  ∀ (c c' : Coefficient ell) (a : c.bundled.{u} ell ⟶ c'.bundled ell),
    Allowed ell c → Allowed ell c' → IsListedScalarCoefficientMap ell a →
    ∃ ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell,
    ∃ p : ScalarLineCoordinates ell a ha T,
    let X := (DerivedCategory.singleFunctor _ 0).obj (sourceModule ell c i)
    let Y := c.derivedLine ell T 1
    let F' := CondensedRing.rightDerivedLowerShriekOfCompactification (c'.obj ell) cf
    let sx := sourceScalarMap ell a i
    let sy := scalarLineMap ell a T 1 (p.power 1)
    IsIso sx ∧ IsIso sy ∧
    (scalarSixChange a T).map (classArrow ell (C c i)) ≫ sy =
      sx ≫ classArrow ell (C c' i) ∧
    IsIso ((scalarSupportMap a cf).app X) ∧
    IsIso ((scalarSupportMap a cf).app Y) ∧
    (scalarSixChange a S).map (compactArrow ell cf (C c i)) ≫
        (scalarSupportMap a cf).app Y ≫ F'.map sy =
      (scalarSupportMap a cf).app X ≫ F'.map sx ≫ compactArrow ell cf (C c' i) ∧
    HasOrigin ell c' T sx ∧ HasOrigin ell c' T sy ∧
    HasOrigin ell c' S ((scalarSupportMap a cf).app X) ∧
    HasOrigin ell c' S ((scalarSupportMap a cf).app Y)

attribute [instance] Datum.smooth Datum.separated Datum.finiteType Datum.quasiCompact
  Datum.closed Datum.divisorSmooth Datum.divisorProper

end AlgebraicGeometry.ProEtale.CondensedCartier
