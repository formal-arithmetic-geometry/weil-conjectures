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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NoetherianProperFiniteness
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible
public import WeilConjectures.SixFunctors.RationalIntegralGenerators

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

/-- The existing ordinary condensed-module functors, organized in the existing exchange formalism.
Pullback is total left derivation, direct image is total right derivation, and open extension is
exact termwise descent. The adjunctions and every pullback compositor are the published ones;
only the existing exact/total comparison transports the right side of the open adjunction.
Source: `det-prop-sf-cbc`, exchange definition and proof steps 9--10
(blueprint: det-prop-sf-cbc). -/
noncomputable def compactSupportCondensedFormalism : CompactSupportFormalism := by
  letI (X : Scheme.{u}) :
      ((Scheme.ProEt.topology X).W (A := Ab.{u + 1})).IsMonoidal :=
    CategoryTheory.GrothendieckTopology.W.monoidal
  exact
  { obj := fun X ↦ D Λ X
    pb := fun f ↦ detSfDerivedPullback Λ f
    pbId := fun T ↦ leftDerivedUpperStarId Λ T
    pbComp := fun f g ↦ leftDerivedUpperStarComp Λ f g
    pbComp_assoc := fun f g h K ↦ leftDerivedUpperStarComp_assoc_app Λ f g h K
    pbId_comp := fun f K ↦ leftDerivedUpperStarComp_id_left_app Λ f K
    pbComp_id := fun f K ↦ leftDerivedUpperStarComp_id_right_app Λ f K
    pf := fun f ↦ (lowerStar Λ f).rightDerivedFunctor
    adj := fun f ↦ derivedUpperStarLowerStarAdjunction Λ f
    sh := fun j _ ↦ by
      haveI : IsOpenImmersion j := Fact.out
      exact J Λ j
    shAdj := fun j _ ↦ by
      haveI : IsOpenImmersion j := Fact.out
      exact (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory Λ j).symm }

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

/-- Counit naturality detects isomorphisms between objects on which the counit is invertible. -/
private theorem isIso_of_open_counits
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {A B : D} (m : A ⟶ B)
    [IsIso (adj.counit.app A)] [IsIso (adj.counit.app B)] [IsIso (R.map m)] :
    IsIso m := by
  have hc : IsIso (adj.counit.app A ≫ m) := by
    have h := adj.counit.naturality m
    simp only [Functor.id_map, Functor.comp_map] at h
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_left (adj.counit.app A) m

/-- The canonical open mate is invertible if its endpoints are related by an open comparison.
This is the essential-image and counit-naturality argument of det-prop-sf-cbc, step 8. -/
private theorem isIso_open_baseChange_of_comparison
    (F : CompactSupportFormalism)
    {U' U Z' Z : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'} {r : U ⟶ Z}
    {b : Z' ⟶ Z} [IsOpenImmersion l] [IsOpenImmersion r]
    (sq : IsPullback t l r b)
    [IsIso (F.shAdj l).unit] [IsIso (F.shAdj r).unit]
    (beta : F.sh r ⋙ F.pb b ≅ F.pb t ⋙ F.sh l) :
    IsIso (F.baseChange t l r b sq.w).natTrans := by
  let adj := F.shAdj l
  let ff := adj.fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have hcomp : ∀ M, IsIso ((F.baseChange t l r b sq.w).natTrans.app M) := by
    intro M
    let m := (F.baseChange t l r b sq.w).natTrans.app M
    have hs : IsIso (adj.counit.app ((F.sh r ⋙ F.pb b).obj M)) :=
      adj.isIso_counit_app_of_iso (beta.app M)
    have ht : IsIso (adj.counit.app ((F.pb t ⋙ F.sh l).obj M)) :=
      adj.isIso_counit_app_of_iso (Iso.refl _)
    have hm : IsIso ((F.pb l).map m) := F.isIso_map_baseChange_app t l r b sq.w M
    exact isIso_of_open_counits adj m
  exact NatIso.isIso_of_isIso_app _

/-- The compact-support formalism has extension-by-zero base change on every chosen Cartesian
open square. The proof transports the literal pullback comparison along `sq.isoPullback`.
Exact descent preserves the invertible open-adjunction units, hence open extension is fully
faithful. Both endpoints of the canonical mate lie in its essential image by the transported
comparison. Its restriction is invertible by `isIso_map_baseChange_app`. Counit naturality
expresses the mate as a composite of invertible maps, proving invertibility of the actual mate.
Source: `det-prop-sf-cbc`, proof steps 8--9 (blueprint: det-prop-sf-cbc). -/
@[instance] theorem compactSupportCondensedFormalism_hasBaseChange :
    (compactSupportCondensedFormalism Λ).HasBaseChange := by
  let F := compactSupportCondensedFormalism Λ
  have hunit {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :
      IsIso (F.shAdj j).unit := by
    have : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ j).unit :=
      (openImmersionLowerShriekUpperStarAdjunction Λ j).unit_isIso_of_L_fully_faithful
    have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit :=
      inferInstance
    change IsIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit ≫
      Functor.whiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory Λ j).inv)
    infer_instance
  refine ⟨?_⟩
  intro U' U Z' Z t l r b _ _ sq
  have := hunit l
  have := hunit r
  let beta : J Λ r ⋙ detSfDerivedPullback Λ b ≅
      detSfDerivedPullback Λ t ⋙ J Λ l :=
    Functor.isoWhiskerLeft (J Λ r) (leftDerivedUpperStarIsoMapDerivedCategory Λ b) ≪≫
      condensedOpenBaseChangeDerivedIso (Mon.mk Λ) r b ≪≫
      (compactSupportOpenPullbackTransport Λ sq).symm ≪≫
      Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ t).symm (J Λ l)
  exact isIso_open_baseChange_of_comparison F sq beta

/-- The proper exchange on the extension-by-zero of a bounded-constructible object.
The proof reduces the proper mate to finite scalar models, lifts through derived Nakayama, and
then passes to rational generators.
Source: `det-prop-sf-cbc`, proper exchange step (blueprint: det-prop-sf-cbc). -/
theorem condensed_compactSupport_proper_exchange_isIso
    (ell : ℕ) [Fact ell.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ E : PadicAlgCl.FiniteIntermediateField ell,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ell,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsNoetherian X] [IsNoetherian Y]
    (c : Compactification f) [IsNoetherian c.Z]
    [QuasiCompact (pullback.snd f g)]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hK : boundedConstructible (condensedRingObj Λ X) K) :
    IsIso ((detSfProperBaseChangeMap Λ c.g g).app
      (D((c.i)_!open⟦Λ⟧).obj K)) := by
  sorry

/-- Extension by zero preserves bounded constructibility on the Noetherian compactification.
The proof extends each finite locally-presented stratum by zero across the open complement.
Source: `det-prop-sf-cbc`, constructibility step (blueprint: det-prop-sf-cbc). -/
theorem condensed_compactSupport_extension_boundedConstructible
    (ell : ℕ) [Fact ell.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ E : PadicAlgCl.FiniteIntermediateField ell,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ell,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsNoetherian X] [IsNoetherian Y]
    (c : Compactification f) [IsNoetherian c.Z]
    [QuasiCompact (pullback.snd f g)]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hK : boundedConstructible (condensedRingObj Λ X) K) :
    boundedConstructible (condensedRingObj Λ c.Z)
      (D((c.i)_!open⟦Λ⟧).obj K) := by
  have _ := hΛ
  let e (n : ℤ) :=
    ((openImmersionLowerShriek Λ c.i).mapDerivedCategoryHomologyFunctorIso n).app K
  obtain ⟨⟨a, b, hab⟩, hc⟩ := (mem_boundedConstructible_iff _ K).1 hK
  refine (mem_boundedConstructible_iff _ _).2
    ⟨⟨a, b, fun i hi ↦ ?_⟩, fun n ↦ ?_⟩
  · exact ((openImmersionLowerShriek Λ c.i).map_isZero (hab i hi)).of_iso (e i).symm
  · exact IsConstructibleModuleObject.of_iso (e n)
      (isConstructibleModuleObject_openImmersionLowerShriek_obj Λ c.i _ (hc n))

/-- Proper finiteness sends a bounded-constructible extension-by-zero object to the base.
This is the Noetherian proper-finiteness part, before arbitrary pullback.
Source: `det-prop-sf-cbc`, constructibility step (blueprint: det-prop-sf-cbc). -/
theorem condensed_compactSupport_proper_finiteness
    (ell : ℕ) [Fact ell.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ E : PadicAlgCl.FiniteIntermediateField ell,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ell,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsNoetherian X] [IsNoetherian Y]
    (c : Compactification f) [IsNoetherian c.Z]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hExt : boundedConstructible (condensedRingObj Λ c.Z)
      (D((c.i)_!open⟦Λ⟧).obj K)) :
    boundedConstructible (condensedRingObj Λ Y) ((detSfCompactSupport Λ c).obj K) := by
  have _ := g
  rcases hΛ with h | h | h
  · obtain ⟨E, ⟨e⟩⟩ := h
    exact nppf_transport e c.g
      (proper_pushforward_mem_boundedConstructible ell E _ (Or.inl rfl) c.g)
      _ hExt
  · obtain ⟨E, ⟨e⟩⟩ := h
    exact nppf_transport e c.g
      (proper_pushforward_mem_boundedConstructible ell E _ (Or.inr (Or.inl rfl)) c.g)
      _ hExt
  · obtain ⟨e⟩ := h
    exact nppf_transport e c.g
      (proper_pushforward_mem_boundedConstructible ell
        (⟨⊥, inferInstance⟩ : PadicAlgCl.FiniteIntermediateField ell) _ (Or.inr (Or.inr rfl)) c.g)
      _ hExt

/-- Pullback along the arbitrary base map preserves the bounded-constructible proper endpoint.
This is the coefficient pullback argument, separated from proper finiteness.
Source: `det-prop-sf-cbc`, constructibility step (blueprint: det-prop-sf-cbc). -/
theorem condensed_compactSupport_pullback_constructible
    (ell : ℕ) [Fact ell.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ E : PadicAlgCl.FiniteIntermediateField ell,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ell,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsNoetherian X] [IsNoetherian Y]
    (c : Compactification f) [IsNoetherian c.Z]
    [QuasiCompact (pullback.snd f g)]
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)))
    (hM : boundedConstructible (condensedRingObj Λ Y) M) :
    boundedConstructible (condensedRingObj Λ Y')
      ((detSfDerivedPullback Λ g).obj M) := by
  have _ := hΛ
  exact boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ g M hM

/-- The left compact-support endpoint combines extension-by-zero, proper finiteness and pullback.
Source: `det-prop-sf-cbc`, constructibility step (blueprint: det-prop-sf-cbc). -/
theorem condensed_compactSupport_left_boundedConstructible
    (ell : ℕ) [Fact ell.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ E : PadicAlgCl.FiniteIntermediateField ell,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ell,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsNoetherian X] [IsNoetherian Y]
    (c : Compactification f) [IsNoetherian c.Z]
    [QuasiCompact (pullback.snd f g)]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hK : boundedConstructible (condensedRingObj Λ X) K) :
    boundedConstructible (condensedRingObj Λ Y')
      ((detSfCompactSupport Λ c ⋙ detSfDerivedPullback Λ g).obj K) := by
  have hExt := condensed_compactSupport_extension_boundedConstructible ell Λ hΛ f g c K hK
  have hProper := condensed_compactSupport_proper_finiteness ell Λ hΛ f g c K hExt
  exact condensed_compactSupport_pullback_constructible ell Λ hΛ f g c
    ((detSfCompactSupport Λ c).obj K) hProper

open CategoryTheory.TwoSquare

end AlgebraicGeometry.ProEtale.CondensedRing
