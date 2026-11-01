/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenBaseChangeArbitrary
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
import Mathlib.CategoryTheory.Monoidal.CommMon_
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.SheafTensor
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SectionActionInternal
import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingPresheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtaleObjectPullbackRestriction
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalDerivedScalarComparisons
import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.SixFunctors.QcqsIntegralFiniteModelCompleteness
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalPullNormalizationExistence
import WeilConjectures.AlgebraicGeometry.Integral.IntegralDirectImageReductionCone
import WeilConjectures.AlgebraicGeometry.Integral.IntegralDirectImageLimits
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelSheafQuotientConstructible
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingConstructibility
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperConstructibleCohomology
import WeilConjectures.AlgebraicGeometry.NormedCoefficientRealization.NormedCoefficientRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTorsionProperFiniteness
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import WeilConjectures.AlgebraicGeometry.Integral.Models.IntegralModelsStacksBlueprint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.Compatibility
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartTriangulated
import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AmbientQcqsExchangeCanonicalShifts
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackConstantModelConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperIntegralRationalScalarComparison
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedQcqsPushforwardContinuitySupplement
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedSliceLocalization
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients

/-!
# Compact-support base change

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
`sk-prop-sp-purity-bc/det-prop-sf-cbc.md`
(blueprint: det-prop-sf-cbc).

The declarations below state the finite étale, finite pro-étale-origin, and condensed
compact-support exchanges. The condensed exchange is the existing proper/open composite,
with its canonical open comparison built from the arbitrary-base open comparison.

## Main definitions

* `compactSupportCondensedFormalism` organizes the existing ordinary derived functors.
* `compactSupportOpenBaseChangeIso` constructs the canonical open comparison.

## Main statements

* `finite_compactSupportBaseChange` and its pro-étale-origin version state clause (a).
* `condensed_compactSupportBaseChange` states clause (b).
* The three following coherence theorems state identity and both pasting laws.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CondensedOpenProper

attribute [local instance 30000]
  CategoryTheory.GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
attribute [local instance 30000]
  CategoryTheory.GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
attribute [local instance 40000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]


/-- Canonical change from an arbitrary Cartesian open square to its literal pullback.
The isomorphism `sq.isoPullback` supplies an equivalence of the exact derived pullback functors.
Insert the inverse counit for its open adjunction, then use the published open and pullback
compositors. This constructs the transport without a choice of an unspecified comparison.
Source: `det-prop-sf-cbc`, canonical open comparison in proof step 8
(blueprint: det-prop-sf-cbc). -/
noncomputable def compactSupportOpenPullbackTransport
    {U' U Z' Z : Scheme.{u}} {t : U' ⟶ U} {j' : U' ⟶ Z'}
    {j : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback t j' j b) :
    P Λ t ⋙ J Λ j' ≅ P Λ (pullback.fst j b) ⋙ J Λ (pullback.snd j b) := by
  let e := sq.isoPullback
  letI : (P Λ e.hom).IsEquivalence :=
    (CategoryTheory.Equivalence.mk (P Λ e.hom) (P Λ e.inv)
      ((pId Λ _).symm ≪≫ eqToIso (by rw [e.inv_hom_id]) ≪≫ pComp Λ e.inv e.hom)
      ((pComp Λ e.hom e.inv).symm ≪≫ eqToIso (by rw [e.hom_inv_id]) ≪≫ pId Λ _)
      ).isEquivalence_functor
  let adj := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ e.hom
  letI : IsIso adj.counit := adj.counit_isIso_of_R_fully_faithful
  let et : P Λ t ≅ P Λ (pullback.fst j b) ⋙ P Λ e.hom :=
    eqToIso (by rw [sq.isoPullback_hom_fst]) ≪≫ pComp Λ e.hom (pullback.fst j b)
  let ej : J Λ j' ≅ J Λ e.hom ⋙ J Λ (pullback.snd j b) :=
    jCongr Λ sq.isoPullback_hom_snd.symm ≪≫
      (jComp Λ e.hom (pullback.snd j b)).symm
  exact Functor.isoWhiskerRight et (J Λ j') ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (P Λ (pullback.fst j b))
      (Functor.isoWhiskerLeft (P Λ e.hom) ej ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (asIso adj.counit) (J Λ (pullback.snd j b)) ≪≫
        Functor.leftUnitor _)

/-- The canonical beta of the supplied compactification square, constructed from
`condensedOpenBaseChangeDerivedIso`. Its middle factor is precisely that existing comparison;
the other factors change its literal pullback to the compactification pullback and identify
exact derived pullback with total left derivation. All data are explicitly constructed.
Source: `det-prop-sf-cbc`, displayed beta and proof step 8 (blueprint: det-prop-sf-cbc). -/
noncomputable def compactSupportOpenBaseChangeIso
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (c : Compactification f) :
    D((c.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst c.g g) ≅
      detSfDerivedPullback Λ (pullback.fst f g) ⋙ D(((c.baseChange g).i)_!open⟦Λ⟧) :=
  Functor.isoWhiskerLeft D((c.i)_!open⟦Λ⟧)
      (leftDerivedUpperStarIsoMapDerivedCategory Λ (pullback.fst c.g g)) ≪≫
    condensedOpenBaseChangeDerivedIso (Mon.mk Λ) c.i (pullback.fst c.g g) ≪≫
    (compactSupportOpenPullbackTransport Λ
      (c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f g))).symm ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory Λ (pullback.fst f g)).symm
      D(((c.baseChange g).i)_!open⟦Λ⟧)

open CategoryTheory.TwoSquare

end AlgebraicGeometry.ProEtale.CondensedRing
