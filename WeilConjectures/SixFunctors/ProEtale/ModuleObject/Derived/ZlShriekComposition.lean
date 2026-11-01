/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedHomData
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.SepFinType
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.Compactification.Triangle
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDirectImageComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.Compactification.CommonDenseRefinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperImageLocalizingProper
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralProperBaseChange
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchangeTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedCoefficientIsoExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeAdmissibleGenerators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientProperFormulaTools
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.Algebra.Homology.ScalarPullback.KFlatScalarComparisonNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientExchangeComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AmbientQcqsExchangeCanonicalShifts
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.LocalizingIsoLocus
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compact.CompactSupportRefinementBaseChange
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
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
public import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
public import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc

/-! # Composition of exceptional images with Frobenius

Source: latest blueprint, sec-deligne-laumon-general/sk-prop-wgen-relative-line,
lem-zl-shriek-composition and its proof (blueprint: lem-zl-shriek-composition).

All restrictions below use the ordinary bounded constructible category. The normalized
comparison data are those of the existing condensed composition theorem. In particular,
the exchange is the proper/open base-change map, not an arbitrary intertwiner.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- Geometric base change, in the existing category of separated finite-type schemes.
Source: latest blueprint, geometric-fibre convention in lem-zl-shriek-composition
(blueprint: lem-zl-shriek-composition). -/
def zlGeometricScheme (X₀ : SepFinType D.k₀) : SepFinType D.k :=
  ⟨Over.mk (pullback.snd X₀.obj.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))),
    ⟨inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.obj.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))),
      inferInstanceAs (QuasiCompact (pullback.snd X₀.obj.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))),
      inferInstanceAs (IsSeparated (pullback.snd X₀.obj.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))⟩⟩

/-- The geometric map is exactly the map of the base-change functor.
Source: latest blueprint, geometric-fibre convention in lem-zl-shriek-composition
(blueprint: lem-zl-shriek-composition). -/
def zlGeometricHom {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀) :
    zlGeometricScheme D X₀ ⟶ zlGeometricScheme D Y₀ :=
  ObjectProperty.homMk (Over.homMk
    (pullback.lift
      (pullback.fst X₀.obj.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ f₀.hom.left)
      (pullback.snd X₀.obj.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t ↦ pullback.fst X₀.obj.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ t)
          (Over.w f₀.hom)).trans pullback.condition)))
    (pullback.lift_snd ..))

/-- The existing chosen compactification, with Nagata supplying its existence.
Source: latest blueprint, composition constraint of lem-zl-shriek-composition
(blueprint: lem-zl-shriek-composition). -/
def zlChosenCompactification {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀) :
    Compactification (zlGeometricHom D f₀).hom.left :=
  letI := HasCompactification.of_over (zlGeometricHom D f₀).hom
  HasCompactification.compactification (zlGeometricHom D f₀).hom.left

/-- The recorded chosen lower shriek, with its compactifiability instance supplied by Nagata.
Source: latest blueprint, exceptional images in lem-zl-shriek-composition
(blueprint: lem-zl-shriek-composition). -/
def zlAmbientShriek {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀) :=
  letI := HasCompactification.of_over (zlGeometricHom D f₀).hom
  rightDerivedLowerShriek (Profinite.padicAlgClRingObj ℓ) (zlGeometricHom D f₀).hom.left

/-- Every ordinary bounded constructible object lies in the recorded localizing category.
Source: latest blueprint, first paragraph of lem-zl-shriek-composition.proof
(blueprint: lem-zl-shriek-composition).
Proof: adicConstructibilityPredicateComparison identifies ordinary constructibility with
finite constant local models on the Noetherian finite-type scheme. The condensed
Qbar case of det-def-localizing-closure-ctf-equals-bc gives finite Tor amplitude.
By definition every localizing subcategory containing Dctf contains this object,
proving membership in their intersection. -/
theorem zlDbc_mem (X : SepFinType D.k)
    (K : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.obj.left)) :
    localizingClosureProEtale (Profinite.padicAlgClRingObj ℓ) X.obj.left K.obj := by
  have : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  have : IsLocallyNoetherian X.obj.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.obj.hom
  have : QuasiSeparatedSpace X.obj.left := IsLocallyNoetherian.quasiSeparatedSpace
  have heq := (localizingClosure_ctf_equals_bc ℓ X.obj.left
    (Profinite.padicAlgClRingObj ℓ)
    (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩)))).1.2.2.1
  have hpred := (adicConstructibilityPredicateComparison ℓ X.obj.left
    (Profinite.padicAlgClRingObj ℓ) .algebraicClosure).2
  intro P hP hgen
  apply hgen K.obj
  have hbc : constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
      X.obj.left K.obj := by
    rw [← hpred]
    exact K.property
  simpa only [heq] using hbc

/-- The actual full inclusion from Dbc into Loc, preserving ambient objects and morphisms.
Source: latest blueprint, restriction of composition to Dbc
(blueprint: lem-zl-shriek-composition). -/
def zlDbcToLoc (X : SepFinType D.k) :=
  (localizingClosureProEtale (Profinite.padicAlgClRingObj ℓ) X.obj.left).lift
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.obj.left)).ι
    (zlDbc_mem D ℓ X)

/-- The chosen ambient exceptional image preserves ordinary bounded constructibility.
Source: latest blueprint, the functors on Dbc in lem-zl-shriek-composition
(blueprint: lem-zl-shriek-composition).
Proof: use the constructibility comparison and det-def-localizing-closure-ctf-equals-bc to
regard the input as Dctf. Apply the preserves field of sk-thm-sf-comp-composition to the
chosen compactification; compare its constructibility predicate back to the ordinary one. -/
theorem zlShriek_mem (hℓ : ℓ ≠ D.p) {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀)
    (K : BoundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (zlGeometricScheme D X₀).obj.left)) :
    boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (zlGeometricScheme D Y₀).obj.left)
      ((zlAmbientShriek D ℓ f₀).obj K.obj) := by
  let X := zlGeometricScheme D X₀
  let Y := zlGeometricScheme D Y₀
  let Λ := Profinite.padicAlgClRingObj ℓ
  have : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  have : CompactSpace Y.obj.left := QuasiCompact.compactSpace_of_compactSpace Y.obj.hom
  have : IsLocallyNoetherian X.obj.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.obj.hom
  have : IsLocallyNoetherian Y.obj.left :=
    LocallyOfFiniteType.isLocallyNoetherian Y.obj.hom
  have : QuasiSeparatedSpace X.obj.left := IsLocallyNoetherian.quasiSeparatedSpace
  have hX := (adicConstructibilityPredicateComparison ℓ X.obj.left Λ .algebraicClosure).2
  have hY := (adicConstructibilityPredicateComparison ℓ Y.obj.left Λ .algebraicClosure).2
  have heq := (localizingClosure_ctf_equals_bc ℓ X.obj.left Λ
    (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩)))).1.2.2.1
  have hctf : (constantModelBoundedConstructible Λ X.obj.left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) K.obj := by
    rw [heq, ← hX]
    exact K.property
  have hout := ((zlComparisonData D ℓ hℓ).preserves
    (zlGeometricHom D f₀) (zlChosenCompactification D f₀)).2 K.obj hctf
  exact (congrArg (fun P : ObjectProperty _ ↦ P
    ((zlAmbientShriek D ℓ f₀).obj K.obj)) hY).mpr hout.1

/-- Restriction of the existing chosen exceptional direct image to the ordinary Dbc.
Source: latest blueprint, Rf_! in lem-zl-shriek-composition
(blueprint: lem-zl-shriek-composition). -/
def zlShriek (hℓ : ℓ ≠ D.p) {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀) :=
  (boundedConstructible
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (zlGeometricScheme D Y₀).obj.left)).lift
    ((boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (zlGeometricScheme D X₀).obj.left)).ι ⋙
      zlAmbientShriek D ℓ f₀) (zlShriek_mem D ℓ hℓ f₀)

/-- Canonical Frobenius exchange, restricted from the normalized proper/open exchange.
Its direction is P_Y Rf_! to Rf_! P_X, as in the node's displayed Weil structures.
Source: latest blueprint, Frobenius compatibility in lem-zl-shriek-composition.proof
(blueprint: lem-zl-shriek-composition). -/
def zlFrobeniusExchange (hℓ : ℓ ≠ D.p) {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀) :
    zlShriek D ℓ hℓ f₀ ⋙ zlFrobenius D ℓ Y₀ ≅
      zlFrobenius D ℓ X₀ ⋙ zlShriek D ℓ hℓ f₀ :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
    (((zlComparisonData D ℓ hℓ).exchange
      (f := zlGeometricHom D f₀) (f' := zlGeometricHom D f₀)
      (zlFrobeniusSquare D f₀)
      (zlChosenCompactification D f₀) (zlChosenCompactification D f₀)).app
        ((zlDbcToLoc D ℓ (zlGeometricScheme D X₀)).obj K)))
    (fun f ↦ ObjectProperty.hom_ext _
      (((zlComparisonData D ℓ hℓ).exchange
        (f := zlGeometricHom D f₀) (f' := zlGeometricHom D f₀)
        (zlFrobeniusSquare D f₀)
        (zlChosenCompactification D f₀) (zlChosenCompactification D f₀)).hom.naturality
          ((zlDbcToLoc D ℓ (zlGeometricScheme D X₀)).map f)))

set_option maxHeartbeats 2000000 in
-- Elaborating the restricted comparison unfolds several derived functors and subtype lifts.
end AlgebraicGeometry.ProEtale.CondensedRing
