/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import Sheaf.Paper.CurveMiddleExtension
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.SixFunctors.Finite.BaseChange
public import Sheaf.Paper.PbcScalarExtension
import Sheaf.Paper.FieldDerivedScalarTower
public import Sheaf.Paper.AdicGlobalDerivedHom
public import Sheaf.Paper.PbcActualRingedExchange
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.CompletedCoefficientPresentationTransport
public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

import Sheaf.Paper.PbcQbarCategory
import Sheaf.Paper.PbcRationalCategory
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.ProEtaleReplete
import Sheaf.Paper.CompletedCoefficientPushforwardComparison
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Paper.SbcCompletedOperations
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.CompletedConstantSheafReduction
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Paper.CompletedPullbackReduction
import WeilConjectures.SixFunctors.Finite.Stalk
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.AlgebraicGeometry.ProEtaleContinuousCohomologyLimit
import Sheaf.Paper.DerivedNakayama
import Sheaf.Paper.IntrinsicQbarCategory
import Sheaf.Paper.LisseCompletedSystemComparison

/-! # Finite etale direct image and ordinary adic cohomology

Source: main-20261015, sec-fourier-transform/sk-lem-as-properties,
lem-fd-cohomology-affine-line-character.proof.md, first display; Stacks Tags 03QP, 0959.
(blueprint: lem-fd-finite-etale-adic-cohomology).

## Main definitions

* `IsFiniteFreeSystem`: normalized finite locally constant finite-free systems.
* `realization`: their actual completed integral complexes.
* `derivedComparison` and `globalComparison`: canonical direct-image and section maps.
* `CommonStageComparisons`: normalized operations at the common coefficient stage.

## Main statements

* `finiteEtaleAdicCohomology`: finite-etale comparison at all coefficient stages,
  with canonical quotient maps, base change, and actions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.Scheme
namespace FiniteEtaleAdic

variable (l : ℕ) [Fact l.Prime] (Qbar : Type (u + 1)) [Field Qbar]
  [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar]

/-- Normalized finite locally constant systems with finite free geometric fibres.
Source: the finite-free-system hypothesis in the first display, and BS 6.8.4.
(blueprint: lem-fd-finite-etale-adic-cohomology). -/
def IsFiniteFreeSystem (E : Padic.FiniteCoefficientFields l Qbar) (X : Scheme.{u})
    (F : AdicIntegralDiagram l E.val X) : Prop :=
  IsLisseIntegralDiagram l E.val X F ∧
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X) (n : ℕ),
      ∃ r : ℕ, Nonempty
        (((pointSmallEtale x).ulift.{u + 1}.sheafFiber
          (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val))).obj
            (F.obj (op n)) ≅ ModuleCat.of (Padic.coefficientExtensionIntegers l E.val)
              (Fin r → Padic.coefficientExtensionRing l E.val (n + 1)))

/-- Direct image of the entire strict diagram, with its actual quotient transitions.
Source: Stacks 03QP (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def systemPush (E : Padic.FiniteCoefficientFields l Qbar) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    AdicIntegralDiagram l E.val Y ⥤ AdicIntegralDiagram l E.val X :=
  (Functor.whiskeringRight _ _ _).obj
    (Etale.lowerStar (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val)) f)

/-- Change only the coefficient presentation, by associated modules and actual
completed scalar extension. Source: BS 6.8.4
(blueprint: lem-fd-finite-etale-adic-cohomology). -/
def coefficientFunctor (E : Padic.FiniteCoefficientFields l Qbar) (X : Scheme.{u}) :=
  Sheaf.restrictScalars (ProEt.topology X) (middleExtensionIntegerMap l Qbar E) ⋙
    pbcAssociatedModule X (PbcIntegralRing l (pbcFiniteField.{u} l Qbar E))
      (adicLisseRing X (PbcIntegralRing l (pbcFiniteField.{u} l Qbar E)))
      (adicLisseConstantUnit X (PbcIntegralRing l (pbcFiniteField.{u} l Qbar E))) ⋙
    pbcExtend (pbcCompletedScalar X (pbcStageDatum.{u} l Qbar E))

/-- A section enters the associated completed module as the actual tensor 1 tensor m.
Source: Stacks 03EK (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def coefficientUnitSection (E : Padic.FiniteCoefficientFields l Qbar) (X : Scheme.{u})
    (N : Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val)))
    (U : X.ProEtᵒᵖ) (m : N.obj.obj U) :
    ((coefficientFunctor l Qbar E X).obj N).val.obj U :=
  pbcTensorSection (pbcCompletedScalar X (pbcStageDatum.{u} l Qbar E)) _ U 1
    (((PresheafOfModules.sheafificationAdjunction
      (adicLisseConstantUnit X (PbcIntegralRing l (pbcFiniteField.{u} l Qbar E)))).unit.app
        ((ProEtale.finiteCoefficientModulePresheaf X.ProEt
          (PbcIntegralRing l (pbcFiniteField.{u} l Qbar E))).obj
            ((Sheaf.restrictScalars (ProEt.topology X)
              (middleExtensionIntegerMap l Qbar E)).obj N).obj)).app U m)

/-- Finite-level realization in the published completed coefficient presentation.
Source: BS 6.8.4 (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def levelFunctor (E : Padic.FiniteCoefficientFields l Qbar) (X : Scheme.{u}) :=
  ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val)) X ⋙
    coefficientFunctor l Qbar E X

/-- The specified integral diagram, retaining all transition maps.
Source: BS 6.8.4 (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def completedSystem (E : Padic.FiniteCoefficientFields l Qbar) (X : Scheme.{u}) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (levelFunctor l Qbar E X)

/-- Actual integral realization, on objects and morphisms, without separatedness.
Source: BS 6.8.4 (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def realizationSheaf (E : Padic.FiniteCoefficientFields l Qbar) (X : Scheme.{u}) :=
  completedSystem l Qbar E X ⋙ lim

/-- Actual integral complex, in sheaf degree zero.
Source: BS 6.8.4 (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def realization (E : Padic.FiniteCoefficientFields l Qbar) (X : Scheme.{u}) :=
  realizationSheaf l Qbar E X ⋙ DerivedCategory.singleFunctor _ 0

/-- The ordinary coefficient/site mate is uniquely determined on unit tensors.
Source: Stacks 09A6, 03EK (blueprint: lem-fd-finite-etale-adic-cohomology).
Proof: transpose the site-comparison mate through the two scalar-extension
adjunctions. On associated-module sections it sends 1 tensor m to 1 tensor
its image under the comparison mate. Extend by completed linearity and
sheafification. The scalar structure map is the same constant-section map on
every finite quotient, so the extension is balanced. Unit tensors locally
generate before scalar extension, which proves uniqueness and naturality. -/
theorem levelComparison_exists (E : Padic.FiniteCoefficientFields l Qbar)
    {Y X : Scheme.{u}} (f : Y ⟶ X) :
    ∃! η : Etale.lowerStar
        (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val)) f ⋙
          levelFunctor l Qbar E X ⟶
      levelFunctor l Qbar E Y ⋙ pbcActualModulePush f (pbcStageDatum.{u} l Qbar E),
      ∀ (M : Sheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val)))
        (U : X.ProEtᵒᵖ)
        (m : ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val)) X).obj
            ((Etale.lowerStar _ f).obj M)).obj.obj U),
        (η.app M).val.app U
          (coefficientUnitSection l Qbar E X _ U m) =
        coefficientUnitSection l Qbar E Y _
          ((proEtaleBaseChange f).op.obj U)
          ((((ProEtale.lowerStarComparisonUpperStarBaseChange f
            (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val))).app M).hom.app
              U) m) := by
  sorry

/-- The uniquely normalized coefficient/site comparison, with no arbitrary map chosen.
Source: Stacks 09A6 (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def levelComparison (E : Padic.FiniteCoefficientFields l Qbar)
    {Y X : Scheme.{u}} (f : Y ⟶ X) :=
  (levelComparison_exists l Qbar E f).exists.choose

/-- The sheaf comparison obtained by the actual limit and its universal projections.
Source: Stacks 0A07 (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def sheafComparison (E : Padic.FiniteCoefficientFields l Qbar)
    {Y X : Scheme.{u}} (f : Y ⟶ X) (F : AdicIntegralDiagram l E.val Y) :
    (realizationSheaf l Qbar E X).obj ((systemPush l Qbar E f).obj F) ⟶
      (pbcActualModulePush f (pbcStageDatum.{u} l Qbar E)).obj
        ((realizationSheaf l Qbar E Y).obj F) :=
  letI := completedModuleDirectImage_preservesLimits f (pbcStageDatum.{u} l Qbar E)
  lim.map (Functor.whiskerLeft F (levelComparison l Qbar E f)) ≫
    (preservesLimitIso (pbcActualModulePush f (pbcStageDatum.{u} l Qbar E))
      (F ⋙ levelFunctor l Qbar E Y)).inv

/-- The standard comparison from the underived value in degree zero to the
right-derived value, using the universal derived unit on that representing complex.
Source: Stacks 0D6E (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def singlePushUnit (E : Padic.FiniteCoefficientFields l Qbar)
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    (M : pbcModules Y (pbcAdicCompletion Y (pbcStageDatum.{u} l Qbar E))) :=
  DerivedCategory.Q.map
    (((pbcActualModulePush f (pbcStageDatum.{u} l Qbar E)).mapCochainComplexSingleFunctor
      0).inv.app M) ≫
    (DerivedCategory.quotientCompQhIso _).inv.app
      (((pbcActualModulePush f (pbcStageDatum.{u} l Qbar E)).mapHomologicalComplex
        (.up ℤ)).obj ((CochainComplex.singleFunctor _ 0).obj M)) ≫
    DerivedCategory.Qh.map
      (((pbcActualModulePush f (pbcStageDatum.{u} l Qbar E)).mapHomotopyCategoryFactors
        (.up ℤ)).inv.app ((CochainComplex.singleFunctor _ 0).obj M)) ≫
    (pbcActualPushUnit f (pbcStageDatum.{u} l Qbar E)).app
      ((HomotopyCategory.singleFunctor _ 0).obj M)

/-- The canonical integral comparison with ordinary derived direct image.
Source: Stacks 099N (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def derivedComparison (E : Padic.FiniteCoefficientFields l Qbar)
    {Y X : Scheme.{u}} (f : Y ⟶ X) (F : AdicIntegralDiagram l E.val Y) :=
  (DerivedCategory.singleFunctor _ 0).map (sheafComparison l Qbar E f F) ≫
    singlePushUnit l Qbar E f ((realizationSheaf l Qbar E Y).obj F)

/-- The section comparison is fixed by restriction along the terminal-object
comparison. Source: Stacks 0D6E
(blueprint: lem-fd-finite-etale-adic-cohomology).
Proof: base change carries the final object of the X-site to a final object
of the Y-site. Restriction along the inverse final-object isomorphism identifies
their section modules. The constant completed scalar maps agree after each
finite projection, hence agree by the limit universal property. These maps
are linear, natural, inverse, and uniquely fixed by the displayed section formula. -/
theorem sectionsComparison_exists (E : Padic.FiniteCoefficientFields l Qbar)
    {Y X : Scheme.{u}} (f : Y ⟶ X) :
    ∃! e : pbcActualModulePush f (pbcStageDatum.{u} l Qbar E) ⋙
        adicGlobalSections X (pbcStageDatum.{u} l Qbar E) ≅
      adicGlobalSections Y (pbcStageDatum.{u} l Qbar E),
      ∀ (M : pbcModules Y (pbcAdicCompletion Y (pbcStageDatum.{u} l Qbar E)))
        (m : ((pbcActualModulePush f (pbcStageDatum.{u} l Qbar E)).obj M).val.obj
          (op (⊤_ X.ProEt))),
        (e.hom.app M) m = M.val.map
          (inv (terminalComparison (proEtaleBaseChange f))).op m := by
  sorry

/-- The unique ordinary section comparison.
Source: Stacks 0D6E (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def sectionsComparison (E : Padic.FiniteCoefficientFields l Qbar)
    {Y X : Scheme.{u}} (f : Y ⟶ X) :=
  (sectionsComparison_exists l Qbar E f).exists.choose

/-- Completed module direct image for finite etale maps preserves K-injective
complexes. Source: Stacks 04HN, 0D6E
(blueprint: lem-fd-finite-etale-adic-cohomology).
Proof: etale-locally a finite etale map is a finite disjoint union of identities.
The completed coefficient comparison there is the identity, and module inverse
image is the exact diagonal functor. Exactness descends along the covering.
Its recorded right adjoint therefore preserves K-injectives by the exact-adjoint
criterion. The empty union gives the zero functor and satisfies the same criterion. -/
@[instance] theorem push_preservesKInjective (E : Padic.FiniteCoefficientFields l Qbar)
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Etale f] :
    (pbcActualModulePush f (pbcStageDatum.{u} l Qbar E)).PreservesKInjectiveComplexes := by
  sorry

/-- Global sections with the output localization in the same ambient universe as
completed sheaf complexes. This is the same module-valued total right derived
functor, with an enlarged localization universe; the small site's object and
morphism universes remain distinct. Source: Stacks 0D6E
(blueprint: lem-fd-finite-etale-adic-cohomology). -/
def globalSectionsDerived (E : Padic.FiniteCoefficientFields l Qbar) (X : Scheme.{u}) :
    pbcAmbientStage l Qbar X E ⥤
      DerivedCategory.{u + 2} (ModuleCat.{u + 1}
        (PbcIntegralRing l (pbcFiniteField.{u} l Qbar E))) :=
  (adicGlobalSections X (pbcStageDatum.{u} l Qbar E)).rightDerivedFunctor

/-- Canonical localization-universe transport, induced by the identity on all
coefficient module complexes. Source: Stacks 05QC
(blueprint: lem-fd-finite-etale-adic-cohomology). -/
def moduleUniverseTransport (A : Type (u + 1)) [CommRing A] :
    @DerivedCategory.{u + 2} (ModuleCat.{u + 1} A) _ _
        (HasDerivedCategory.standard _) ⥤
      @DerivedCategory.{u + 1} (ModuleCat.{u + 1} A) _ _
        (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _) :=
  @Functor.mapDerivedCategory.{u + 2, u + 1}
    (ModuleCat.{u + 1} A) _ _ (HasDerivedCategory.standard _)
    (ModuleCat.{u + 1} A) _ _ (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _)
    (𝟭 (ModuleCat.{u + 1} A)) _ _ _

/-- The identity transport retains its explicit localization normalization.
Source: Stacks 05QC (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def moduleUniverseFactors (A : Type (u + 1)) [CommRing A] :
    @DerivedCategory.Qh.{u + 2} (ModuleCat.{u + 1} A) _ _
        (HasDerivedCategory.standard _) ⋙ moduleUniverseTransport A ≅
      @DerivedCategory.Qh.{u + 1} (ModuleCat.{u + 1} A) _ _
        (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _) :=
  @Functor.mapDerivedCategoryFactorsh.{u + 2, u + 1}
      (ModuleCat.{u + 1} A) _ _ (HasDerivedCategory.standard _)
      (ModuleCat.{u + 1} A) _ _ (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _)
      (𝟭 (ModuleCat.{u + 1} A)) _ _ _ ≪≫
    Functor.isoWhiskerRight (Functor.mapHomotopyCategoryIdIso (ModuleCat.{u + 1} A) (.up ℤ)) _ ≪≫
    Functor.leftUnitor _

/-- Identity transport between two localizations of the same complexes is an equivalence.
Source: Stacks 05QC (blueprint: lem-fd-finite-etale-adic-cohomology).
Proof: lift the identity in the opposite direction. Both composites have the identity
normalization on complexes, so the localization universal property gives inverse
natural isomorphisms. This does not identify either of the site's two universes. -/
theorem moduleUniverseTransport_isEquivalence (A : Type (u + 1)) [CommRing A] :
    (moduleUniverseTransport A).IsEquivalence := by
  sorry

/-- Universal derived unit for the enlarged output localization.
Source: Stacks 0D6E (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def largeSectionsUnit (E : Padic.FiniteCoefficientFields l Qbar) (X : Scheme.{u}) :
    (adicGlobalSections X (pbcStageDatum.{u} l Qbar E)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ globalSectionsDerived l Qbar E X :=
  (adicGlobalSections X (pbcStageDatum.{u} l Qbar E)).rightDerivedFunctorUnit

/-- Universal derived unit for the recorded smaller module-output localization.
Source: Stacks 0D6E (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def smallSectionsUnit (E : Padic.FiniteCoefficientFields l Qbar) (X : Scheme.{u}) :
    letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
      (ModuleCat.{u + 1} (PbcIntegralRing l (pbcFiniteField.{u} l Qbar E)))
    (adicGlobalSections X (pbcStageDatum.{u} l Qbar E)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh.{u + 1}
          (C := ModuleCat.{u + 1} (PbcIntegralRing l (pbcFiniteField.{u} l Qbar E))) ⟶
      DerivedCategory.Qh.{u + 2} ⋙ adicDerivedGlobalSections X (pbcStageDatum.{u} l Qbar E) :=
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
    (ModuleCat.{u + 1} (PbcIntegralRing l (pbcFiniteField.{u} l Qbar E)))
  (adicGlobalSections X (pbcStageDatum.{u} l Qbar E)).rightDerivedFunctorUnit

/-- The enlarged section model is canonically the recorded ordinary derived sections.
The equality of universal units specifies the comparison uniquely.
Source: Stacks 0D6E, 05QC (blueprint: lem-fd-finite-etale-adic-cohomology).
Proof: transport the enlarged total right derived functor along the identity
localization equivalence. Its universal unit becomes the unit in the smaller
localization via moduleUniverseFactors. It and the recorded section functor
are right derived functors of the same functor, so the universal property gives
one unique unit-compatible natural isomorphism. -/
theorem sectionsUniverseComparison_exists (E : Padic.FiniteCoefficientFields l Qbar)
    (X : Scheme.{u}) :
    ∃! e : globalSectionsDerived l Qbar E X ⋙
        moduleUniverseTransport (PbcIntegralRing l (pbcFiniteField.{u} l Qbar E)) ≅
      adicDerivedGlobalSections X (pbcStageDatum.{u} l Qbar E),
      ∀ I : HomotopyCategory
        (pbcModules X (pbcAdicCompletion X (pbcStageDatum.{u} l Qbar E))) (.up ℤ),
        (moduleUniverseTransport (PbcIntegralRing l (pbcFiniteField.{u} l Qbar E))).map
            ((largeSectionsUnit l Qbar E X).app I) ≫
            e.hom.app (DerivedCategory.Qh.obj I) =
          (moduleUniverseFactors (PbcIntegralRing l (pbcFiniteField.{u} l Qbar E))).hom.app
            (((adicGlobalSections X (pbcStageDatum.{u} l Qbar E)).mapHomotopyCategory
              (.up ℤ)).obj I) ≫ (smallSectionsUnit l Qbar E X).app I := by
  sorry

/-- The unique comparison with the recorded derived global sections.
Source: Stacks 0D6E (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def sectionsUniverseComparison (E : Padic.FiniteCoefficientFields l Qbar) (X : Scheme.{u}) :=
  (sectionsUniverseComparison_exists l Qbar E X).exists.choose

/-- The normalized Leray composition with values in all coefficient modules.
Source: Stacks 0D6E (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def derivedSectionsIso (E : Padic.FiniteCoefficientFields l Qbar)
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Etale f] :
    pbcActualDerivedPush f (pbcStageDatum.{u} l Qbar E) ⋙
        globalSectionsDerived l Qbar E X ≅
      globalSectionsDerived l Qbar E Y :=
  Functor.rightDerivedFunctorCompIso'
    (pbcActualModulePush f (pbcStageDatum.{u} l Qbar E))
    (adicGlobalSections X (pbcStageDatum.{u} l Qbar E))
    (sectionsComparison l Qbar E f)

/-- The canonical integral global-sections comparison, before asserting invertibility.
Source: Stacks 0D6E (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def globalComparison (E : Padic.FiniteCoefficientFields l Qbar)
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Etale f]
    (F : AdicIntegralDiagram l E.val Y) :=
  (globalSectionsDerived l Qbar E X).map
    (derivedComparison l Qbar E f F) ≫
    (derivedSectionsIso l Qbar E f).hom.app ((realization l Qbar E Y).obj F)

/-- The normalized fraction-field scalar map, including the existing integral
coefficient-presentation transport. Source: BS 6.8.14
(blueprint: lem-fd-finite-etale-adic-cohomology). -/
def rationalScalar (E : Padic.FiniteCoefficientFields l Qbar) :
    PbcIntegralRing l (pbcFiniteField.{u} l Qbar E) →+* E.val :=
  (Padic.coefficientExtensionIntegers l E.val).subtype.comp
    (middleExtensionIntegerMap l Qbar E)

/-- The fraction-field scalar map is flat.
Source: BS 6.8.14 (blueprint: lem-fd-finite-etale-adic-cohomology).
Proof: the integral presentation map is an isomorphism of valuation rings,
induced by the coefficient-field equivalence. The inclusion of the valuation
ring in its fraction field is a localization, hence flat. Their composite is flat. -/
theorem rationalScalar_flat (E : Padic.FiniteCoefficientFields l Qbar) :
    (rationalScalar l Qbar E).Flat := by
  sorry

/-- Exact scalar extension in the enlarged output localization. Keeping this
localization universe explicit permits composition with the ambient completed
right-derived functor. Source: Stacks 06YY
(blueprint: lem-fd-finite-etale-adic-cohomology). -/
def scalarDerived {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (h : φ.Flat) :
    DerivedCategory.{u + 2} (ModuleCat.{u + 1} A) ⥤
      DerivedCategory.{u + 2} (ModuleCat.{u + 1} B) :=
  letI : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).left_adjoint_additive
  letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat h
  letI : PreservesColimits (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ) :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).leftAdjoint_preservesColimits
  (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ).mapDerivedCategory

/-- Extension between fields is flat.
Source: elementary field linear algebra (blueprint: lem-fd-finite-etale-adic-cohomology).
Proof: give the target its source-algebra structure through the displayed ring map.
Every module over a field is free and therefore flat; this is precisely ring-map flatness. -/
theorem fieldScalar_flat {K L : Type (u + 1)} [Field K] [Field L] (i : K →+* L) :
    i.Flat := by
  sorry

/-- Rationalization on all module complexes, with the actual tensor functor.
Source: BS 6.8.14 (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def rationalModuleFunctor (E : Padic.FiniteCoefficientFields l Qbar) :=
  scalarDerived (rationalScalar l Qbar E) (rationalScalar_flat l Qbar E)

/-- The common-stage scalar extension on all module complexes.
Source: BS 6.8.14 (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def algebraicModuleFunctor (E : Padic.FiniteCoefficientFields l Qbar) :=
  rationalModuleFunctor l Qbar E ⋙
    scalarDerived E.val.subtype (fieldScalar_flat (K := E.val) (L := Qbar) E.val.subtype)

/-- Rational ordinary cohomology first takes completed integral sections and
then localizes its module complex. Source: BS 6.8.14
(blueprint: lem-fd-finite-etale-adic-cohomology). -/
def rationalSections (E : Padic.FiniteCoefficientFields l Qbar) (X : Scheme.{u}) :=
  globalSectionsDerived l Qbar E X ⋙ rationalModuleFunctor l Qbar E

/-- Common-stage ordinary cohomology has values in all module complexes.
Source: BS 6.8.14 (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def algebraicSections (E : Padic.FiniteCoefficientFields l Qbar) (X : Scheme.{u}) :=
  globalSectionsDerived l Qbar E X ⋙ algebraicModuleFunctor l Qbar E

/-- Rational comparison is the specified scalar extension of the integral arrow.
Source: blueprint first finite-pushforward display
(blueprint: lem-fd-finite-etale-adic-cohomology). -/
def rationalGlobalComparison (E : Padic.FiniteCoefficientFields l Qbar)
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Etale f]
    (F : AdicIntegralDiagram l E.val Y) :=
  (rationalModuleFunctor l Qbar E).map (globalComparison l Qbar E f F)

/-- The common-stage comparison is precisely scalar extension of that rational arrow.
Source: BS 6.8.14 (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def algebraicGlobalComparison (E : Padic.FiniteCoefficientFields l Qbar)
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Etale f]
    (F : AdicIntegralDiagram l E.val Y) :=
  (algebraicModuleFunctor l Qbar E).map (globalComparison l Qbar E f F)

/-- The final-object comparison uses the explicit identity objects used for etale
sections, not an arbitrary chosen terminal object. Source: Stacks 0D6E
(blueprint: lem-fd-finite-etale-adic-cohomology). -/
def etaleFinalComparison {Y X : Scheme.{u}} (f : Y ⟶ X) :=
  ((MorphismProperty.Over.mkIdTerminal @Etale X).isTerminalObj
    (MorphismProperty.Over.pullback @Etale ⊤ f) _).uniqueUpToIso
      (MorphismProperty.Over.mkIdTerminal @Etale Y)

/-- The finite-coefficient section identification, normalized at the final site object.
Source: Stacks 0D6E (blueprint: lem-fd-finite-etale-adic-cohomology).
Proof: restrict sections from the pullback of the final X-object to the final
Y-object along the inverse terminal comparison. Its inverse is restriction along
the terminal comparison. The inverse identities and naturality are functoriality
of each sheaf. This section formula determines the natural isomorphism uniquely. -/
theorem finiteSectionsIso_exists (B : Type (u + 1)) [CommRing B]
    {Y X : Scheme.{u}} (f : Y ⟶ X) :
    ∃! e : Etale.lowerStar (ModuleCat.{u + 1} B) f ⋙
        Etale.sectionsFunctor (ModuleCat.{u + 1} B) X ≅
      Etale.sectionsFunctor (ModuleCat.{u + 1} B) Y,
      ∀ (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))
        (m : ((Etale.lowerStar (ModuleCat.{u + 1} B) f).obj M).obj.obj
          (op (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X)))),
        (e.hom.app M) m = M.obj.map
          (etaleFinalComparison f).inv.op m := by
  sorry

/-- The finite-coefficient section comparison is uniquely fixed, rather than chosen
as an arbitrary isomorphism. Source: Stacks 0D6E
(blueprint: lem-fd-finite-etale-adic-cohomology). -/
def finiteSectionsIso (B : Type (u + 1)) [CommRing B]
    {Y X : Scheme.{u}} (f : Y ⟶ X) := (finiteSectionsIso_exists B f).exists.choose

/-- The canonical finite-coefficient derived global-sections comparison.
Source: Stacks 03QP, 0D6E (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def finiteGlobalComparison (B : Type (u + 1)) [CommRing B]
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) :=
  letI :=
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).preservesKInjectiveComplexes
  (Etale.sectionsFunctor (ModuleCat.{u + 1} B) X).rightDerivedFunctor.map
    (((Etale.lowerStar (ModuleCat.{u + 1} B) f).mapDerivedCategorySingleFunctor 0).inv.app M ≫
      ((Etale.lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctorIsoMapDerivedCategory).inv.app
        ((DerivedCategory.singleFunctor _ 0).obj M)) ≫
    (Functor.rightDerivedFunctorCompIso'
      (Etale.lowerStar (ModuleCat.{u + 1} B) f)
      (Etale.sectionsFunctor (ModuleCat.{u + 1} B) X)
      (finiteSectionsIso B f)).hom.app ((DerivedCategory.singleFunctor _ 0).obj M)

/-- Pullback action on ordinary derived sections, with a specified action on the
coefficient object. Source: blueprint finite-pushforward equivariance
(blueprint: lem-fd-finite-etale-adic-cohomology). -/
def pullAction (E : Padic.FiniteCoefficientFields l Qbar) {Y : Scheme.{u}} (h : Y ≅ Y)
    (K : pbcAmbientStage l Qbar Y E)
    (a : (pbcActualDerivedPull h.hom (pbcStageDatum.{u} l Qbar E)).obj K ⟶ K) :=
  (globalSectionsDerived l Qbar E Y).map
    ((pbcActualDerivedAdjunction h.hom (pbcStageDatum.{u} l Qbar E)).unit.app K) ≫
    (derivedSectionsIso l Qbar E h.hom).hom.app
      ((pbcActualDerivedPull h.hom (pbcStageDatum.{u} l Qbar E)).obj K) ≫
    (globalSectionsDerived l Qbar E Y).map a

/-- The induced action on direct image uses actual direct-image composition and
its given equality over X. Source: blueprint finite-pushforward equivariance
(blueprint: lem-fd-finite-etale-adic-cohomology). -/
def pushAction (E : Padic.FiniteCoefficientFields l Qbar)
    {Y X : Scheme.{u}} (f : Y ⟶ X) (h : Y ≅ Y) (hf : h.hom ≫ f = f)
    (K : pbcAmbientStage l Qbar Y E)
    (a : (pbcActualDerivedPull h.hom (pbcStageDatum.{u} l Qbar E)).obj K ⟶ K) :=
  (pbcActualDerivedPush f (pbcStageDatum.{u} l Qbar E)).map
    ((pbcActualDerivedAdjunction h.hom (pbcStageDatum.{u} l Qbar E)).unit.app K) ≫
    (pbcActualDerivedDirectCompIso h.hom f (pbcStageDatum.{u} l Qbar E)).hom.app
      ((pbcActualDerivedPull h.hom (pbcStageDatum.{u} l Qbar E)).obj K) ≫
    (eqToIso (congrArg (fun g ↦ pbcActualDerivedPush g (pbcStageDatum.{u} l Qbar E)) hf)).hom.app
      ((pbcActualDerivedPull h.hom (pbcStageDatum.{u} l Qbar E)).obj K) ≫
    (pbcActualDerivedPush f (pbcStageDatum.{u} l Qbar E)).map a

section GeometricHypotheses
variable {Y X : Scheme.{u}} [IsNoetherian Y] [IsNoetherian X]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- The published integral-stage inclusion in the common finite-stage category.
Source: BS 6.8.14 (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def integralInclusion (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (E : Padic.FiniteCoefficientFields l Qbar) :=
  pbcStageLocalization.{u, u + 1} l Qbar T E ⋙
    (pbcScalarSystem l Qbar T dT.out iT.out).ι E

/-- Restrict actual derived direct image, changing no object or morphism data.
Source: Stacks 03QP, BS 6.8.14 (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def integralPush (f : Y ⟶ X) (E : Padic.FiniteCoefficientFields l Qbar)
    (hp : ∀ K : pbcIntegralStage l Qbar Y E,
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Qbar E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Qbar E)).obj K.obj)) :=
  pbcConditionalIntegral (pbcStageDatum.{u} l Qbar E)
    (pbcActualDerivedPush f (pbcStageDatum.{u} l Qbar E)) hp

/-- A coefficient-stage morphism is obtained by localizing the same ambient map.
Membership arguments contain proofs only. Source: BS 6.8.14
(blueprint: lem-fd-finite-etale-adic-cohomology). -/
def rationalStageMap (T : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Qbar)
    {M N : pbcAmbientStage l Qbar T E}
    (hM : PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Qbar E) M)
    (hN : PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Qbar E) N) (a : M ⟶ N) :=
  (pbcStageLocalization l Qbar T E).map
    (ObjectProperty.homMk (X := ⟨M, hM⟩) (Y := ⟨N, hN⟩) a)

/-- Common-stage maps use the recorded inclusion of that same finite stage.
Source: BS 6.8.14 (blueprint: lem-fd-finite-etale-adic-cohomology). -/
def algebraicStageMap (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (E : Padic.FiniteCoefficientFields l Qbar) {M N : pbcAmbientStage l Qbar T E}
    (hM : PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Qbar E) M)
    (hN : PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Qbar E) N) (a : M ⟶ N) :=
  (integralInclusion l Qbar T E).map
    (ObjectProperty.homMk (X := ⟨M, hM⟩) (Y := ⟨N, hN⟩) a)

/-- The integral realization has the actual finite quotients, with no higher Tor.
The map to a level is the inverse-limit projection. Source: BS 6.8.4
(blueprint: lem-fd-finite-etale-adic-cohomology). -/
def HasCanonicalQuotients (T : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Qbar)
    (F : AdicIntegralDiagram l E.val T) : Prop :=
  ∀ n : ℕ,
    Mono ((pbcStageUniformizer.{u} l Qbar E) ^ (n + 1) •
      𝟙 ((realizationSheaf l Qbar E T).obj F)) ∧
    Epi (limit.π ((completedSystem l Qbar E T).obj F) (op n)) ∧
    ∃ h : ((pbcStageUniformizer.{u} l Qbar E) ^ (n + 1) •
        𝟙 ((realizationSheaf l Qbar E T).obj F)) ≫
        limit.π ((completedSystem l Qbar E T).obj F) (op n) = 0,
      (ShortComplex.mk _ _ h).Exact

/-- Models on the actual common-stage category, normalized on every integral
object and morphism, with the prescribed canonical section-comparison component.
Linearity extends the normalization to all rational and algebraic coefficient
morphisms. No finiteness condition is placed on global cohomology.
Source: BS 6.8.14; blueprint first finite-pushforward display
(blueprint: lem-fd-finite-etale-adic-cohomology). -/
structure CommonStageComparisons (f : Y ⟶ X) [IsFinite f] [Etale f]
    (hp : ∀ (E : Padic.FiniteCoefficientFields l Qbar) (K : pbcIntegralStage l Qbar Y E),
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Qbar E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Qbar E)).obj K.obj)) where
  /-- Direct image in the recorded common-stage category. -/
  push : pbcQbarCategory l Qbar Y ⥤ pbcQbarCategory l Qbar X
  /-- Ordinary global sections, with all Qbar-module complexes as target. -/
  sectionsX : pbcQbarCategory l Qbar X ⥤ DerivedCategory.{u + 2} (ModuleCat.{u + 1} Qbar)
  /-- Ordinary global sections on Y. -/
  sectionsY : pbcQbarCategory l Qbar Y ⥤ DerivedCategory.{u + 2} (ModuleCat.{u + 1} Qbar)
  /-- All algebraically closed coefficient morphisms have their prescribed scalar action. -/
  push_linear : push.Linear Qbar
  /-- Scalar action on ordinary sections on X. -/
  sectionsX_linear : sectionsX.Linear Qbar
  /-- Scalar action on ordinary sections on Y. -/
  sectionsY_linear : sectionsY.Linear Qbar
  /-- Direct image is the actual integral operation at every finite coefficient stage. -/
  push_stage : ∀ E : Padic.FiniteCoefficientFields l Qbar,
    integralInclusion l Qbar Y E ⋙ push ≅
      integralPush l Qbar f E (hp E) ⋙ integralInclusion l Qbar X E
  /-- Sections at an integral representative are the specified ambient derived sections. -/
  sectionsX_stage : ∀ E : Padic.FiniteCoefficientFields l Qbar,
    integralInclusion l Qbar X E ⋙ sectionsX ≅
      pbcStageInclusion l Qbar X E ⋙ algebraicSections l Qbar E X
  /-- The same normalization on Y. -/
  sectionsY_stage : ∀ E : Padic.FiniteCoefficientFields l Qbar,
    integralInclusion l Qbar Y E ⋙ sectionsY ≅
      pbcStageInclusion l Qbar Y E ⋙ algebraicSections l Qbar E Y
  /-- The ordinary global-sections comparison on the common-stage category. -/
  comparison : push ⋙ sectionsX ≅ sectionsY
  /-- Its components are the actual integral Leray comparisons, scalar extended. -/
  normalization : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (K : pbcIntegralStage l Qbar Y E),
    sectionsX.map ((push_stage E).hom.app K) ≫
        (sectionsX_stage E).hom.app ((integralPush l Qbar f E (hp E)).obj K) ≫
        (algebraicModuleFunctor l Qbar E).map
          ((derivedSectionsIso l Qbar E f).hom.app K.obj) =
      comparison.hom.app ((integralInclusion l Qbar Y E).obj K) ≫
        (sectionsY_stage E).hom.app K

/-- All clauses of finite-etale ordinary adic cohomology, using the specified
canonical maps. The quotient condition is an exact sheaf sequence, so it does
not exchange geometric stalks with inverse limits. The common-stage models are
normalized on integral morphisms and are linear for the recorded Qbar action.
Source: blueprint first finite-pushforward display; Stacks 03QP, 0959; BS 6.8.4, 6.8.14
(blueprint: lem-fd-finite-etale-adic-cohomology). -/
structure CohomologyComparisons (f : Y ⟶ X) [IsFinite f] [Etale f] : Prop where
  /-- Finite direct images preserve the given normalized finite-free systems. -/
  system : ∀ (E : Padic.FiniteCoefficientFields l Qbar) (F : AdicIntegralDiagram l E.val Y),
    IsFiniteFreeSystem l Qbar E Y F →
      IsFiniteFreeSystem l Qbar E X ((systemPush l Qbar E f).obj F)
  /-- Integral realization lies in the published complete constructible category. -/
  integral_mem : ∀ (E : Padic.FiniteCoefficientFields l Qbar) (F : AdicIntegralDiagram l E.val Y),
    IsFiniteFreeSystem l Qbar E Y F →
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Qbar E)
        ((realization l Qbar E Y).obj F)
  /-- The pushed system has its own actual complete integral realization. -/
  pushed_mem : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F : AdicIntegralDiagram l E.val Y), IsFiniteFreeSystem l Qbar E Y F →
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Qbar E)
        ((realization l Qbar E X).obj ((systemPush l Qbar E f).obj F))
  /-- The inverse-limit projections identify every derived reduction with its given level. -/
  quotients : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F : AdicIntegralDiagram l E.val Y), IsFiniteFreeSystem l Qbar E Y F →
      HasCanonicalQuotients l Qbar Y E F ∧
        HasCanonicalQuotients l Qbar X E ((systemPush l Qbar E f).obj F)
  /-- The same object has the detailed derived-complete integral presentation. -/
  detailed_mem : ∀ (E : Padic.FiniteCoefficientFields l Qbar) (F : AdicIntegralDiagram l E.val Y),
    IsFiniteFreeSystem l Qbar E Y F →
      sfIntegralConstructible l (pbcFiniteField.{u} l Qbar E) Y
        ((purCoefficientModel l (pbcFiniteField.{u} l Qbar E) Y).functor.obj
          ((realization l Qbar E Y).obj F))
  /-- The pushed realization also has the exact detailed integral presentation. -/
  detailed_pushed_mem : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F : AdicIntegralDiagram l E.val Y), IsFiniteFreeSystem l Qbar E Y F →
      sfIntegralConstructible l (pbcFiniteField.{u} l Qbar E) X
        ((purCoefficientModel l (pbcFiniteField.{u} l Qbar E) X).functor.obj
          ((realization l Qbar E X).obj ((systemPush l Qbar E f).obj F)))
  /-- Ordinary and derived direct image agree by the canonical map. -/
  direct_iso : ∀ (E : Padic.FiniteCoefficientFields l Qbar) (F : AdicIntegralDiagram l E.val Y),
    IsFiniteFreeSystem l Qbar E Y F → IsIso (derivedComparison l Qbar E f F)
  /-- Actual integral RΓ comparison. -/
  integral_global : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F : AdicIntegralDiagram l E.val Y), IsFiniteFreeSystem l Qbar E Y F →
      IsIso (globalComparison l Qbar E f F)
  /-- Actual rational RΓ comparison, using localization of the integral module complex. -/
  rational_global : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F : AdicIntegralDiagram l E.val Y), IsFiniteFreeSystem l Qbar E Y F →
      IsIso (rationalGlobalComparison l Qbar E f F)
  /-- Common-stage scalar extension of that precise comparison. -/
  algebraic_global : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F : AdicIntegralDiagram l E.val Y), IsFiniteFreeSystem l Qbar E Y F →
      IsIso (algebraicGlobalComparison l Qbar E f F)
  /-- Ordinary cohomology in every nonnegative degree at all three adic stages. -/
  cohomology : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F : AdicIntegralDiagram l E.val Y), IsFiniteFreeSystem l Qbar E Y F → ∀ i : ℕ,
      IsIso ((DerivedCategory.homologyFunctor _ (i : ℤ)).map
        (globalComparison l Qbar E f F)) ∧
      IsIso ((DerivedCategory.homologyFunctor _ (i : ℤ)).map
        (rationalGlobalComparison l Qbar E f F)) ∧
      IsIso ((DerivedCategory.homologyFunctor _ (i : ℤ)).map
        (algebraicGlobalComparison l Qbar E f F))
  /-- The integral diagram has actual A_n-module sheaves at each level. The lifted
  coefficient action is determined uniquely by its restriction along the quotient. -/
  finite_models : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F : AdicIntegralDiagram l E.val Y), IsFiniteFreeSystem l Qbar E Y F → ∀ n : ℕ,
    ∃ M : Sheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E.val (n + 1))),
      Nonempty (((Sheaf.restrictScalars Y.smallEtaleTopology
        (algebraMap (Padic.coefficientExtensionIntegers l E.val)
          (Padic.coefficientExtensionRing l E.val (n + 1)))).obj M) ≅ F.obj (op n))
  /-- Each actual finite-coefficient level, including its ordinary cohomology. -/
  finite_global : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F : AdicIntegralDiagram l E.val Y), IsFiniteFreeSystem l Qbar E Y F → ∀ (n : ℕ)
    (M : Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E.val (n + 1)))),
    Nonempty (((Sheaf.restrictScalars Y.smallEtaleTopology
      (algebraMap (Padic.coefficientExtensionIntegers l E.val)
        (Padic.coefficientExtensionRing l E.val (n + 1)))).obj M) ≅ F.obj (op n)) →
    IsIso (finiteGlobalComparison (Padic.coefficientExtensionRing l E.val (n + 1)) f M) ∧
    ∀ i : ℕ, IsIso ((DerivedCategory.homologyFunctor _ (i : ℤ)).map
      (finiteGlobalComparison (Padic.coefficientExtensionRing l E.val (n + 1)) f M))
  /-- The sheaf direct-image comparison commutes with every actual quotient projection. -/
  projections : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F : AdicIntegralDiagram l E.val Y), IsFiniteFreeSystem l Qbar E Y F → ∀ n : ℕ,
    sheafComparison l Qbar E f F ≫
        (pbcActualModulePush f (pbcStageDatum.{u} l Qbar E)).map
          (limit.π ((completedSystem l Qbar E Y).obj F) (op n)) =
      limit.π ((completedSystem l Qbar E X).obj ((systemPush l Qbar E f).obj F)) (op n) ≫
        (levelComparison l Qbar E f).app (F.obj (op n))
  /-- Naturality includes all coefficient endomorphisms and all defined projectors. -/
  naturality : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F G : AdicIntegralDiagram l E.val Y), IsFiniteFreeSystem l Qbar E Y F →
    IsFiniteFreeSystem l Qbar E Y G → ∀ a : F ⟶ G,
    ((systemPush l Qbar E f ⋙ realization l Qbar E X ⋙
      globalSectionsDerived l Qbar E X).map a) ≫ globalComparison l Qbar E f G =
      globalComparison l Qbar E f F ≫
        ((realization l Qbar E Y ⋙ globalSectionsDerived l Qbar E Y).map a)
  /-- The pullback action of an automorphism over X intertwines with the induced action. -/
  automorphism : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F : AdicIntegralDiagram l E.val Y), IsFiniteFreeSystem l Qbar E Y F →
    ∀ (h : Y ≅ Y) (hf : h.hom ≫ f = f)
    (a : (pbcActualDerivedPull h.hom (pbcStageDatum.{u} l Qbar E)).obj
      ((realization l Qbar E Y).obj F) ⟶ (realization l Qbar E Y).obj F),
    (globalSectionsDerived l Qbar E X).map
        (pushAction l Qbar E f h hf ((realization l Qbar E Y).obj F) a) ≫
        (derivedSectionsIso l Qbar E f).hom.app ((realization l Qbar E Y).obj F) =
      (derivedSectionsIso l Qbar E f).hom.app ((realization l Qbar E Y).obj F) ≫
        pullAction l Qbar E h ((realization l Qbar E Y).obj F) a
  /-- Direct image is defined on every finite integral constructible stage. -/
  push_mem : ∀ (E : Padic.FiniteCoefficientFields l Qbar) (K : pbcIntegralStage l Qbar Y E),
    PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Qbar E)
      ((pbcActualDerivedPush f (pbcStageDatum.{u} l Qbar E)).obj K.obj)
  /-- Both rational and common-stage direct-image comparisons are the same localized arrow. -/
  direct_stages : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F : AdicIntegralDiagram l E.val Y) (hF : IsFiniteFreeSystem l Qbar E Y F),
    IsIso (rationalStageMap l Qbar X E (pushed_mem E F hF)
      (push_mem E ⟨(realization l Qbar E Y).obj F, integral_mem E F hF⟩)
      (derivedComparison l Qbar E f F)) ∧
    IsIso (algebraicStageMap l Qbar X E (pushed_mem E F hF)
      (push_mem E ⟨(realization l Qbar E Y).obj F, integral_mem E F hF⟩)
      (derivedComparison l Qbar E f F))
  /-- The normalized operations and sections descend to the actual common-stage category. -/
  common_stage : Nonempty (CommonStageComparisons l Qbar f push_mem)
  /-- Actual completed exchange for every base change permitted by the statement. -/
  exchange : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F : AdicIntegralDiagram l E.val Y), IsFiniteFreeSystem l Qbar E Y F →
    ∀ (X' Y' : Scheme.{u}) [IsNoetherian X']
      [Fact (∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))]
      [Fact (∀ x : X', IsUnit (l : X'.presheaf.stalk x))]
      (v : Y' ⟶ Y) (f' : Y' ⟶ X') (g : X' ⟶ X)
      (sq : ChosenCartesianSquare v f' f g),
    IsIso ((pbcActualCompletedExchange (pbcStageDatum.{u} l Qbar E) sq).app
      ((realization l Qbar E Y).obj F)) ∧
    IsIso (Etale.baseChangeMap
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val)) sq.toCommSq) ∧
    (∀ n : ℕ, IsIso (Etale.baseChangeMap
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E.val (n + 1))) sq.toCommSq)) ∧
    ∀ e : F ⟶ F,
      ((pbcActualDerivedPush f (pbcStageDatum.{u} l Qbar E) ⋙
        pbcActualCompletedPull g (pbcStageDatum.{u} l Qbar E)).map
          ((realization l Qbar E Y).map e)) ≫
          (pbcActualCompletedExchange (pbcStageDatum.{u} l Qbar E) sq).app
            ((realization l Qbar E Y).obj F) =
        (pbcActualCompletedExchange (pbcStageDatum.{u} l Qbar E) sq).app
          ((realization l Qbar E Y).obj F) ≫
          ((pbcActualCompletedPull v (pbcStageDatum.{u} l Qbar E) ⋙
            pbcActualDerivedPush f' (pbcStageDatum.{u} l Qbar E)).map
              ((realization l Qbar E Y).map e))

  /-- Exchange at the rational and common stages is the image of the actual integral mate. -/
  exchange_stages : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F : AdicIntegralDiagram l E.val Y), IsFiniteFreeSystem l Qbar E Y F →
    ∀ (X' Y' : Scheme.{u}) [IsNoetherian X']
      [Fact (∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))]
      [Fact (∀ x : X', IsUnit (l : X'.presheaf.stalk x))]
      (v : Y' ⟶ Y) (f' : Y' ⟶ X') (g : X' ⟶ X)
      (sq : ChosenCartesianSquare v f' f g),
    ∃ (hs : PbcIsBoundedConstructibleComplete X' (pbcStageDatum.{u} l Qbar E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Qbar E) ⋙
          pbcActualCompletedPull g (pbcStageDatum.{u} l Qbar E)).obj
            ((realization l Qbar E Y).obj F)))
      (ht : PbcIsBoundedConstructibleComplete X' (pbcStageDatum.{u} l Qbar E)
        ((pbcActualCompletedPull v (pbcStageDatum.{u} l Qbar E) ⋙
          pbcActualDerivedPush f' (pbcStageDatum.{u} l Qbar E)).obj
            ((realization l Qbar E Y).obj F))),
      IsIso (rationalStageMap l Qbar X' E hs ht
        ((pbcActualCompletedExchange (pbcStageDatum.{u} l Qbar E) sq).app
          ((realization l Qbar E Y).obj F))) ∧
      IsIso (algebraicStageMap l Qbar X' E hs ht
        ((pbcActualCompletedExchange (pbcStageDatum.{u} l Qbar E) sq).app
          ((realization l Qbar E Y).obj F)))

/-- Finite etale direct image, ordinary adic cohomology, and arbitrary base change.
Source: main-20261015, sec-fourier-transform/sk-lem-as-properties,
lem-fd-cohomology-affine-line-character.proof.md, first display; Stacks 03QP,
0959, 04HN, 09A6, 099N, 0A07, 0D6E; Bhatt--Scholze 6.8.4 and 6.8.14
(blueprint: lem-fd-finite-etale-adic-cohomology).

Proof: etale-locally split the finite etale cover into finitely many identities.
Direct image is a finite product there, so preserves local constancy, finite
freeness and the actual tensor quotient maps, including empty fibres. Pull each
finite system to the pro-etale site. Its transitions are epimorphisms; repleteness
and exact countable products identify its derived limit with its sheaf limit in
degree zero. On affine opens apply lisse-system reconstruction: the limit is
locally finite free over completed coefficients and its ordinary and derived
reductions are exactly the supplied finite levels. Exact slice restriction glues
these projection-induced identifications without requiring global separatedness.
The reductions are constructible in the single interval [0,0], proving both
recorded integral membership predicates. Use the qcqs direct-image comparison
at finite levels and the uniquely tensor-normalized level mate above. Completed
coefficient pushforward commutes with the derived limit, with the specified
projection maps, giving precisely derivedComparison, invertible in degree zero.
The same construction preserves all bounded constructible complete objects by
local finite products. For base change reduce the actual completed exchange
mate using the canonical projection-formula comparisons. Mate pasting identifies
these reductions with finite etale exchange. Both endpoints are complete, so
invertibility of the first reduction implies invertibility by derived Nakayama.
This detects invertibility, without inferring equality of arbitrary derived
maps from their reductions. The quotient diagram itself commutes because all
its arrows were constructed from the same strict tower maps.
Compose direct image with ordinary sections at the ringed topos of a point.
The final-object section formula and universal derived units give the canonical
Leray comparison into all modules. Rationalize this module complex, rather than
taking discrete non-torsion etale cohomology. For a finite coefficient extension,
completed coefficient extension is finite free; the tensor-to-sections comparison
is the identity on a finite direct sum after a basis is chosen, hence is canonical
and basis independent. The tensor associators are coherent, so these functors
and the normalized comparison descend to the recorded common finite-stage
category, with no condition on the size or amplitude of global cohomology.
Taking homology gives every displayed H^i comparison. Naturality holds for all
strict-system maps, hence all quotient transitions and endomorphism projectors.
The adjunction-compatible composition identities give the displayed automorphism
pullback equation; inserting an action map gives the same-system action. Finally
actual scalar-extension coherence transports the same exchange mate and all its
naturality equations to rational and algebraically closed coefficients. -/
theorem finiteEtaleAdicCohomology (f : Y ⟶ X) [IsFinite f] [Etale f] :
    CohomologyComparisons l Qbar f := by
  sorry

end GeometricHypotheses
end FiniteEtaleAdic
end AlgebraicGeometry.Scheme
