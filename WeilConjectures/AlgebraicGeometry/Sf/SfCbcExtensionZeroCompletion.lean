/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.OrderedExchange.ProEtaleConstantReductionTower
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCompletionReduction
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CompletionMap
public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
public import WeilConjectures.Algebra.Homology.SixFunctors.LocalizedModuleExactIndependent
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import Mathlib.Algebra.Homology.Functor
import WeilConjectures.CategoryTheory.Diagram.DiagramSiteRealization
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackAdjunctionSupplement
import WeilConjectures.CategoryTheory.AdicSites.SmallSiteReducedCompletionUnit
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZero
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SixFunctors.LocalizedModuleExactIndependent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.Algebra.Homology.Ringed.RingedSiteEquivalenceTensor
import WeilConjectures.Algebra.Homology.Ringed.RingedOpenFlatResolution
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import WeilConjectures.AlgebraicGeometry.Sf.SfCbcExtensionModel
import all WeilConjectures.AlgebraicGeometry.Sf.SfCbcExtensionModel

/-!
# Strict reduction of completed extension by zero

Source: blueprint fix-lem-exchanges, integral open factor, Steps 1–2;
Stacks Project Tags 099M, 099N and 0941
(blueprint: lem-sf-cbc-extension-zero-completion).
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
universe t
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] sfCbcConstantSliceIso constantSheaf
  sfCbcModelModules sfCbcModelRingMap sfCbcModelDerived
  SheafOfModules.monoidalCategory
  sfCbcOpenExtension sfCbcExtensionModel
attribute [-instance] sfCbcTensorTotal sfCbcSliceTransport_additive

/-- Ordinary tensor projection comparison, as one isomorphism of strict quotient diagrams.
Its equation fixes the map by the actual quotient units, not just its endpoints.
Source: Stacks Tag 0E8I; Step 2 of the node.
Proof: use the ringed-slice tensor projection formula on every quotient.
Both unit composites send m to the extension of 1 tensor m. Quotient units
are epimorphisms, so this equation determines each component uniquely.
Naturality of tensor in the quotient coefficient makes the components commute
with every quotient transition, giving the isomorphism of strict diagrams.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcOrdinaryTensorComparison_existsUnique {U X : Scheme.{t}}
    (j : U ⟶ X) [IsOpenImmersion j] {A : Type t} [CommRing A]
    (d : CompleteCoefficientDatum A) :
    ∃! e : sfCbcModelExtension j A ⋙
        ConstantCompletion.reductionTower (proEtaleModelTopology X)
          (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false ≅
      ConstantCompletion.reductionTower (proEtaleModelTopology U)
        (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false ⋙ sfCbcTowerExtension j A,
      ∀ (M : ConstantCompletion.Mod (sfCbcModelRing U A)) (n : ℕ),
        ((ConstantCompletion.reductionUnit (proEtaleModelTopology X)
            (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false).app
              ((sfCbcModelExtension j A).obj M)).app (op n) ≫
            (e.hom.app M).app (op n) =
          (sfCbcModelExtension j A).map
            (((ConstantCompletion.reductionUnit (proEtaleModelTopology U)
              (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false).app M).app (op n)) := by
  sorry

/-- The unique strict ordinary tensor comparison with the quotient-unit normalization.
Source: Stacks Tag 0E8I (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcOrdinaryTensorComparison {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :=
  (sfCbcOrdinaryTensorComparison_existsUnique j d).exists.choose

attribute [local semireducible] sfCbcModelDerived

/-- Canonical transport of the exact derived extension functor.
Source: Stacks Tags 00VC and 05RU
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcExtensionTransport {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] :
    sfCbcDerivedExtension j A ⋙ (sfCbcModelDerived X A).functor ≅
      (sfCbcModelDerived U A).functor ⋙ sfCbcModelDerivedExtension j A :=
  (Functor.mapDerivedCategoryCompIso (sfCbcOpenExtension j A)
      (sfCbcModelModules X A)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (isoWhiskerRight (sfCbcModelModules U A).asEquivalence.unitIso
        (sfCbcOpenExtension j A ⋙ sfCbcModelModules X A)) ≪≫
    Functor.mapDerivedCategoryCompIso (sfCbcModelModules U A) (sfCbcModelExtension j A)

attribute [local irreducible] sfCbcModelDerived

/-- Zero morphisms on the ordinary extension/reduction route.
Source: Stacks Tags 03DI and 06YY
(blueprint: lem-sf-cbc-extension-zero-completion). -/
instance sfCbcTensorRoute_zero {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :
    (sfCbcModelExtension j A ⋙ ConstantCompletion.reductionTower
      (proEtaleModelTopology X) (ULift.{t + 1, t} A) (sfCbcModelIdeal d)
        false).PreservesZeroMorphisms := by
  let := ConstantCompletion.reductionTower_additive (proEtaleModelTopology X)
    (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false
  infer_instance

/-- Zero morphisms on reduction followed by extension. Source: Stacks Tag 03DI
(blueprint: lem-sf-cbc-extension-zero-completion). -/
instance sfCbcTensorRightRoute_zero {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :
    (ConstantCompletion.reductionTower (proEtaleModelTopology U)
      (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false ⋙
        sfCbcTowerExtension j A).PreservesZeroMorphisms := by
  let := ConstantCompletion.reductionTower_additive (proEtaleModelTopology U)
    (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false
  infer_instance

attribute [local irreducible] sfCbcExtensionTransport sfCbcOrdinaryTensorComparison
  ConstantCompletion.quotientPresentation sfCbcModelExtension
  NatIso.mapHomologicalComplex Functor.mapHomologicalComplexCompIso
  ConstantCompletion.reductionUnit
  ConstantCompletion.reductionTower
  sfCbcModelDerivedFactors sfCbcModelExtensionFactors sfCbcTowerExtensionFactors

/-- Normalization of the derived tensor comparison on every flat-term K-flat complex.
Both sides use the universal quotient counits and the ordinary tensor comparison.
Source: Stacks Tag 06YY; Step 2 of the node
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcTensorComparisonNormalized {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    (e : sfCbcModelDerivedExtension j A ⋙ (sfCbcQuotientPresentation X d).tower ≅
      (sfCbcQuotientPresentation U d).tower ⋙ sfCbcDerivedTowerExtension j A) : Prop := by
  letI := ConstantCompletion.reductionTower_additive (proEtaleModelTopology X)
    (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false
  letI := ConstantCompletion.reductionTower_additive (proEtaleModelTopology U)
    (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false
  let c : (sfCbcModelExtension j A).mapHomologicalComplex (.up ℤ) ⋙
      (ConstantCompletion.reductionTower (proEtaleModelTopology X)
        (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false).mapHomologicalComplex (.up ℤ) ≅
      (ConstantCompletion.reductionTower (proEtaleModelTopology U)
        (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false).mapHomologicalComplex (.up ℤ) ⋙
          (sfCbcTowerExtension j A).mapHomologicalComplex (.up ℤ) :=
    Functor.mapHomologicalComplexCompIso
      (sfCbcOrdinaryTensorComparison j d) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (F := ConstantCompletion.reductionTower (proEtaleModelTopology U)
          (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false)
        (G := sfCbcTowerExtension j A) (Iso.refl _) (.up ℤ)).symm
  exact ∀ P : ConstantCompletion.Cx (sfCbcModelRing U A), P.IsAcyclicTensorKFlat →
    (∀ i : ℤ, SheafOfModules.IsFlat (P.X i)) →
      HEq (e.hom.app ((ConstantCompletion.Q (sfCbcModelRing U A)).obj P) ≫
          (sfCbcDerivedTowerExtension j A).map
            ((sfCbcQuotientPresentation U d).comparison.app P) ≫
          (sfCbcTowerExtensionFactors j A).hom.app
            (ConstantCompletion.reductionComplex (proEtaleModelTopology U)
              (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false P))
        ((sfCbcQuotientPresentation X d).tower.map
            ((sfCbcModelExtensionFactors j A).hom.app P) ≫
          (sfCbcQuotientPresentation X d).comparison.app
            (((sfCbcModelExtension j A).mapHomologicalComplex (.up ℤ)).obj P) ≫
          (ConstantCompletion.TQ (sfCbcModelRing X A)).map
            (c.hom.app P))

/-- The tensor projection comparison descends uniquely to derived strict towers.
Source: Stacks Tags 06YY, 0E8I and 0941; Steps 1–2 of the node.
Proof: extension preserves flat K-flat complexes by Step 1. The ordinary
comparison is a strict quotient-diagram isomorphism. Apply it degreewise on
one such complex and localize in the tower category. The universal quotient
counits give the displayed formula. All complexes have flat K-flat resolutions;
localization at quasi-isomorphisms therefore extends the comparison uniquely,
naturally in the input, and preserves its inverse.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcTensorComparison_existsUnique {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :
    ∃! e : sfCbcModelDerivedExtension j A ⋙ (sfCbcQuotientPresentation X d).tower ≅
      (sfCbcQuotientPresentation U d).tower ⋙ sfCbcDerivedTowerExtension j A,
      sfCbcTensorComparisonNormalized j d e := by
  sorry

/-- The canonical strict derived tensor comparison, transported back to the named scheme.
Source: Stacks Tags 00VC, 06YY and 0E8I
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcTensorComparison {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :
    sfCbcDerivedExtension j A ⋙ sfCbcReduction X d ≅
      sfCbcReduction U d ⋙ sfCbcDerivedTowerExtension j A :=
  isoWhiskerRight (sfCbcExtensionTransport j A) (sfCbcQuotientPresentation X d).tower ≪≫
    isoWhiskerLeft (sfCbcModelDerived U A).functor
      (sfCbcTensorComparison_existsUnique j d).exists.choose

/-- Reduction of the specified completion unit on ordinary extension by zero.
Source: Stacks Tag 099M; Step 3 of the node
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcReducedCompletionUnit {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :
    sfCbcDerivedExtension j A ⋙ sfCbcReduction X d ⟶
      sfCbcDerivedExtension j A ⋙ sfCbcCompletion X d ⋙ sfCbcReduction X d :=
  whiskerLeft (sfCbcDerivedExtension j A)
    (whiskerRight (sfCbcCompletionUnit X d) (sfCbcReduction X d))

private theorem sfCbcTransportedUnit_isIso {C D B : Type*}
    [Category C] [Category D] [Category B] (E : C ≌ D) (G : D ⥤ D)
    (η : 𝟭 D ⟶ G) (T : D ⥤ B) [IsIso (whiskerRight η T)] (K : C) :
    IsIso (T.map (E.functor.map
      (E.unitIso.hom.app K ≫ E.inverse.map (η.app (E.functor.obj K))))) := by
  have hη : E.functor.map
      (E.unitIso.hom.app K ≫ E.inverse.map (η.app (E.functor.obj K))) =
        η.app (E.functor.obj K) ≫ E.counitIso.inv.app (G.obj (E.functor.obj K)) := by
    apply (cancel_mono (E.counitIso.hom.app (G.obj (E.functor.obj K)))).mp
    rw [Functor.map_comp, Category.assoc]
    have hn := E.counitIso.hom.naturality (η.app (E.functor.obj K))
    change E.functor.map (E.inverse.map _) ≫ _ = _ at hn
    rw [hn]
    dsimp only [Functor.id_obj, Functor.id_map]
    rw [← Category.assoc, E.functor_unitIso_comp, Category.id_comp,
      Category.assoc, Iso.inv_hom_id_app]
    dsimp only [Functor.id_obj]
    exact (Category.comp_id _).symm
  rw [hη, Functor.map_comp]
  have : IsIso (T.map (η.app (E.functor.obj K))) :=
    inferInstanceAs (IsIso ((whiskerRight η T).app _))
  infer_instance

private theorem sfCbcTransportedUnitNat_isIso {C D B : Type*}
    [Category C] [Category D] [Category B] (E : C ≌ D) (G : D ⥤ D)
    (η : 𝟭 D ⟶ G) (T : D ⥤ B) [IsIso (whiskerRight η T)] :
    IsIso (whiskerRight
      (E.unitIso.hom ≫ whiskerLeft E.functor (whiskerRight η E.inverse))
      (E.functor ⋙ T)) := by
  exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _
    (whiskerRight
      (E.unitIso.hom ≫ whiskerLeft E.functor (whiskerRight η E.inverse))
      (E.functor ⋙ T))
    (fun K ↦ sfCbcTransportedUnit_isIso E G η T K)

/-- The reduced unit is invertible in the derived category of strict towers.
Source: Stacks Tag 099M; Step 3 of the node.
Proof: apply reductionCompletionUnit_isIso on the AsSmall site with the lifted
Noetherian coefficient ring. Counit naturality and the equivalence triangle
identity identify the transported unit with the model unit followed by the inverse
counit. Reduction preserves that isomorphism. Apply the result to ordinary
extension and assemble the component isomorphisms. No completeness of J K is used.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcReducedCompletionUnit_isIso {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :
    IsIso (sfCbcReducedCompletionUnit j d) := by
  let := d.noetherian
  let : IsNoetherianRing (ULift.{t + 1, t} A) :=
    isNoetherianRing_of_ringEquiv A ULift.ringEquiv.symm
  let S : AdicSites.Site.{t + 1} :=
    ⟨proEtaleSiteModel X, proEtaleModelTopology X⟩
  let E := sfCbcModelDerived X A
  have := AdicSites.reductionCompletionUnit_isIso S
    (ULift.{t + 1, t} A) (sfCbcModelIdeal d)
  let η := S.unit (ULift.{t + 1, t} A) (sfCbcModelIdeal d)
  let T := S.reduction (ULift.{t + 1, t} A) (sfCbcModelIdeal d)
  have := sfCbcTransportedUnitNat_isIso E
    (S.completion (ULift.{t + 1, t} A) (sfCbcModelIdeal d)) η T
  exact inferInstanceAs (IsIso (whiskerLeft (sfCbcDerivedExtension j A)
    (whiskerRight
      (E.unitIso.hom ≫ whiskerLeft E.functor (whiskerRight η E.inverse))
      (E.functor ⋙ T))))

/-- Completed extension is ordinary extension followed by completion.
Source: Stacks Tag 099M; Step 4 of the node
(blueprint: lem-sf-cbc-extension-zero-completion). -/
abbrev sfCbcCompletedExtension {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :=
  sfCbcDerivedExtension j A ⋙ sfCbcCompletion X d

/-- The canonical q-map is inverse reduced unit followed by the tensor comparison.
Source: Step 4 of the node (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcCompletedReductionIso {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :
    sfCbcCompletedExtension j d ⋙ sfCbcReduction X d ≅
      sfCbcReduction U d ⋙ sfCbcDerivedTowerExtension j A :=
  (@asIso _ _ _ _ (sfCbcReducedCompletionUnit j d)
    (sfCbcReducedCompletionUnit_isIso j d)).symm ≪≫ sfCbcTensorComparison j d

/-- The completion presentation, obtained by applying Rlim to the strict tensor comparison.
Source: Stacks Tags 099M and 0941; Step 6 of the node
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcCompletedExtensionPresentation {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :
    sfCbcCompletedExtension j d ≅
      sfCbcReduction U d ⋙ sfCbcDerivedTowerExtension j A ⋙
        ConstantCompletion.rlim (sfCbcModelRing X A) ⋙ (sfCbcModelDerived X A).inverse :=
  isoWhiskerRight (sfCbcTensorComparison j d)
    (ConstantCompletion.rlim (sfCbcModelRing X A) ⋙ (sfCbcModelDerived X A).inverse)

attribute [local instance 1000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

attribute [local semireducible] sfCbcOpenExtension

open Classical in
/-- Insert a section into its factorization summand of the extension presheaf,
then apply module sheafification. This is the actual extension generator.
Source: Stacks Tag 03DI (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcExtensionSection {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] (M : SheafOfModules.{t + 1} (adicModuleRing U A))
    (V : X.ProEt) (a : V ⟶ cbcOpenObject j inferInstance)
    (m : M.val.obj (op ((cbcSliceFunctor X (cbcOpenObject j inferInstance)).obj
      (Over.mk a)))) : ((sfCbcOpenExtension j A).obj M).val.obj (op V) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (adicModuleRing X A).obj)).unit.app
    ((SheafOfModules.extensionByZeroPresheaf.{t + 1} (adicModuleRing X A)
      (cbcOpenObject j inferInstance)).obj
        ((sfCbcConstantModuleToSlice X (cbcOpenObject j inferInstance) A).obj M))).app
          (op V)
            (DirectSum.lof ((adicConstantRing X A).obj.obj (op V))
              (V ⟶ cbcOpenObject j inferInstance)
              (fun b ↦ ((sfCbcConstantModuleToSlice X (cbcOpenObject j inferInstance) A).obj
                M).val.obj (op (Over.mk b))) a m)

attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

attribute [local irreducible] sfCbcOpenExtension

/-- Ordinary scalar restriction commutes with extension by zero by the same summands.
The equality on extension generators fixes the comparison uniquely.
Source: Stacks Tags 03DI and 03D3; Step 5 of the node.
Proof: restriction changes only the scalar action. In each factorization summand
its underlying group is unchanged, and its maps keep the same section.
The identity on these summands respects restrictions and the scalar homomorphism.
Sheafify, using exactness of restriction, and apply the inverse identity on summands.
Local generation gives the two inverse identities and uniqueness, naturally in M.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcRestrictExtensionIso_existsUnique {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A B : Type t} [CommRing A] [CommRing B] (φ : A →+* B) :
    ∃! e : SheafOfModules.restrictScalars (adicModuleMap U φ) ⋙ sfCbcOpenExtension j A ≅
      sfCbcOpenExtension j B ⋙ SheafOfModules.restrictScalars (adicModuleMap X φ),
      ∀ (M : SheafOfModules.{t + 1} (adicModuleRing U B)) (V : X.ProEt)
        (a : V ⟶ cbcOpenObject j inferInstance)
        (m : M.val.obj (op ((cbcSliceFunctor X (cbcOpenObject j inferInstance)).obj
          (Over.mk a)))),
        (e.hom.app M).val.app (op V)
            (sfCbcExtensionSection j A
              ((SheafOfModules.restrictScalars (adicModuleMap U φ)).obj M) V a m) =
          sfCbcExtensionSection j B M V a m := by
  sorry

/-- Canonical restriction/extension comparison, fixed by extension generators.
Source: Stacks Tag 03DI (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcRestrictExtensionIso {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A B : Type t} [CommRing A] [CommRing B] (φ : A →+* B) :=
  (sfCbcRestrictExtensionIso_existsUnique j φ).exists.choose

/-- Exact derived scalar restriction commutes with extension by zero, retaining its
ordinary generator normalization.
Source: Stacks Tags 03DI, 03D3 and 05RU
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcDerivedRestrictExtensionIso {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A B : Type t} [CommRing A] [CommRing B] (φ : A →+* B) :
    adicDerivedRestrict U φ ⋙ sfCbcDerivedExtension j A ≅
      sfCbcDerivedExtension j B ⋙ adicDerivedRestrict X φ := by
  letI := (adicRestrictScalars_exact U φ).1
  letI := (adicRestrictScalars_exact U φ).2
  letI := (adicRestrictScalars_exact X φ).1
  letI := (adicRestrictScalars_exact X φ).2
  exact (Functor.mapDerivedCategoryCompIso
      (SheafOfModules.restrictScalars (adicModuleMap U φ))
      (sfCbcOpenExtension j A)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (sfCbcRestrictExtensionIso j φ) ≪≫
    Functor.mapDerivedCategoryCompIso (sfCbcOpenExtension j B)
      (SheafOfModules.restrictScalars (adicModuleMap X φ))

attribute [local irreducible] sfCbcDerivedRestrictExtensionIso

/-- The finite tensor comparison is the adjoint of the extended quotient unit.
Its target retains the actual quotient coefficient action.
Source: Stacks Tags 03DI, 0E8I and 06YY; Steps 1–2 and 5 of the node
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcFiniteTensorHom {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    {K : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K) (n : ℕ) :
    adicReduction X d (sfCbcExtensionModel j A M) ⟨n + 1, Nat.succ_pos n⟩ ⟶
      (sfCbcDerivedExtension j (A ⧸ d.ideal ^ (n + 1))).obj
        (adicReduction U d M ⟨n + 1, Nat.succ_pos n⟩) :=
  (adicReductionHomEquiv X d (sfCbcExtensionModel j A M) n _).symm
    ((sfCbcDerivedExtension j A).map (adicReductionDerivedUnit U d M n) ≫
      (sfCbcDerivedRestrictExtensionIso j
        (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).hom.app
          (adicReduction U d M ⟨n + 1, Nat.succ_pos n⟩))

/-- The finite tensor comparison is an isomorphism over P_n, with its prescribed action.
Source: Stacks Tags 0E8I and 06YY; Steps 1–2 and 5 of the node.
Proof: compute on the flat K-flat model and its termwise extension. The ringed-slice
tensor formula is P_n-linear by naturality in the quotient coefficient module.
Its unit inserts 1 tensor m, exactly the adjunction formula defining the map above.
The derived scalar adjunction identifies it with that invertible model comparison.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcFiniteTensorHom_isIso {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    {K : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K) (n : ℕ) :
    IsIso (sfCbcFiniteTensorHom j d M n) := by
  sorry

/-- The completion presentation agrees with the recorded Roos model and its unit.
The unit equation determines the isomorphism by the reflector universal property.
Source: Stacks Tags 099M and 0941; Steps 3 and 6 of the node.
Proof: both objects are the total derived limit of the same strict quotient tower
on M. The quotient-unit normalization of the universal reduction counit and the
right-derived-limit comparison identifies their units. Both are derived complete
by lem-sp-completed-pullback-adjunction. Its Hom bijection makes the comparison
unique, and the reverse comparison shows it is an isomorphism.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcCompletionModelIso_existsUnique (X : Scheme.{t}) {A : Type t}
    [CommRing A] (d : CompleteCoefficientDatum A) {K : proEtaleDerivedCategory X A}
    (M : AdicKFlatModel X A K) :
    ∃! c : (sfCbcCompletion X d).obj K ≅ adicCompletionObject X d M,
      (sfCbcCompletionUnit X d).app K ≫ c.hom = adicCompletionMap X d M := by
  sorry

/-- Canonical unit-preserving comparison with the recorded Roos model.
Source: Stacks Tags 099M and 0941
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcCompletionModelIso (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : CompleteCoefficientDatum A) {K : proEtaleDerivedCategory X A}
    (M : AdicKFlatModel X A K) :=
  (sfCbcCompletionModelIso_existsUnique X d M).exists.choose

/-- The finite forward comparison is the adjoint of the actual n-th limit projection,
followed by the tensor comparison. No completeness of the input is assumed.
Source: Stacks Tag 099M; Steps 3–4 of the node
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcFiniteCompletedHom {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    {K : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K)
    (N : AdicKFlatModel X A ((sfCbcCompletedExtension j d).obj K)) (n : ℕ) :
    adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩ ⟶
      (sfCbcDerivedExtension j (A ⧸ d.ideal ^ (n + 1))).obj
        (adicReduction U d M ⟨n + 1, Nat.succ_pos n⟩) :=
  (adicReductionHomEquiv X d N n _).symm
    ((sfCbcCompletionModelIso X d (sfCbcExtensionModel j A M)).hom ≫
      adicCompletionEvaluation X d (sfCbcExtensionModel j A M) n ≫
      (adicDerivedRestrictFactors X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
        (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
          (sfCbcExtensionModel j A M).complex)).inv) ≫ sfCbcFiniteTensorHom j d M n

private theorem sfCbcReductionHomEquiv_apply (X : Scheme.{t}) {A : Type t}
    [CommRing A] (d : CompleteCoefficientDatum A) {K : proEtaleDerivedCategory X A}
    (M : AdicKFlatModel X A K) (n : ℕ)
    (H : proEtaleDerivedCategory X (A ⧸ d.ideal ^ (n + 1)))
    (f : adicReduction X d M ⟨n + 1, Nat.succ_pos n⟩ ⟶ H) :
    adicReductionHomEquiv X d M n H f = adicReductionDerivedUnit X d M n ≫
      (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).map f := rfl

attribute [local irreducible] adicReductionHomEquiv

attribute [local irreducible] adicDerivedRestrictFactors
  adicCompletionEvaluation
  adicDerivedRestrict

private theorem sfCbcTransposeComp
    {C D : Type*} [Category C] [Category D] (R : D ⥤ C)
    {X Y : C} {P Q T : D} (u : X ⟶ R.obj P) (v : Y ⟶ R.obj Q)
    (E : (P ⟶ T) ≃ (X ⟶ R.obj T)) (E' : (Q ⟶ T) ≃ (Y ⟶ R.obj T))
    (hE : ∀ f, E f = u ≫ R.map f) (hE' : ∀ f, E' f = v ≫ R.map f)
    (m : P ⟶ Q) (a : X ⟶ Y) (b : Y ⟶ R.obj T)
    (hm : u ≫ R.map m = a ≫ v) :
    E.symm (a ≫ b) = m ≫ E'.symm b := by
  apply E.injective
  rw [Equiv.apply_symm_apply, hE, CategoryTheory.Functor.map_comp,
    ← Category.assoc, hm, Category.assoc, ← hE', Equiv.apply_symm_apply]

private theorem sfCbcCompletionAdjoint_isIso (X : Scheme.{t}) {A : Type t}
    [CommRing A] (d : CompleteCoefficientDatum A) {K L : proEtaleDerivedCategory X A}
    (M : AdicKFlatModel X A K) (N : AdicKFlatModel X A L)
    (c : L ≅ adicCompletionObject X d M) (n : ℕ) :
    IsIso ((adicReductionHomEquiv X d N n _).symm
      (c.hom ≫ adicCompletionEvaluation X d M n ≫
        (adicDerivedRestrictFactors X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
          (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) M.complex)).inv)) := by
  let N' : AdicKFlatModel X A (adicCompletionObject X d M) :=
    { complex := N.complex
      isKFlat := N.isKFlat
      flatTerms := N.flatTerms
      realization := N.realization ≪≫ c }
  let R := adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  have he : (adicReductionHomEquiv X d N n _).symm
      (c.hom ≫ adicCompletionEvaluation X d M n ≫
        (adicDerivedRestrictFactors X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
          (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) M.complex)).inv) =
      adicReductionMap X d N N' n c.hom ≫ adicCompletionReduction X d M N' n := by
    exact sfCbcTransposeComp R
      (adicReductionDerivedUnit X d N n) (adicReductionDerivedUnit X d N' n)
      (adicReductionHomEquiv X d N n _) (adicReductionHomEquiv X d N' n _)
      (sfCbcReductionHomEquiv_apply X d N n _)
      (sfCbcReductionHomEquiv_apply X d N' n _)
      (adicReductionMap X d N N' n c.hom) c.hom _
      (adicReductionMap_unit X d N N' n c.hom)
  rw [he]
  have := adicReductionMap_isIso X d N N' n c.hom
  have := adicCompletionReduction_isIso X d M N' n
  infer_instance

private theorem sfCbcTransposeCompositeIdentity
    {C D : Type*} [Category C] [Category D] (R : D ⥤ C)
    {X Y : C} {P Q : D} (u : X ⟶ R.obj P) (v : Y ⟶ R.obj Q)
    (E : (P ⟶ P) ≃ (X ⟶ R.obj P)) (E' : (Q ⟶ P) ≃ (Y ⟶ R.obj P))
    (hE : ∀ f, E f = u ≫ R.map f) (hE' : ∀ f, E' f = v ≫ R.map f)
    (m : P ⟶ Q) (a : X ⟶ Y) (b : Y ⟶ R.obj P)
    (hm : u ≫ R.map m = a ≫ v) (hab : a ≫ b = u) :
    m ≫ E'.symm b = 𝟙 P := by
  apply E.injective
  rw [hE, hE, Functor.map_comp, ← Category.assoc, hm, Category.assoc]
  rw [← hE', Equiv.apply_symm_apply, hab, CategoryTheory.Functor.map_id, Category.comp_id]

private theorem sfCbcCompTransport
    {C : Type*} [Category C] {K L M N : C}
    (η : K ⟶ L) (c : L ⟶ M) (p : M ⟶ N) (u : K ⟶ M) (v : K ⟶ N)
    (hc : η ≫ c = u) (hp : u ≫ p = v) : η ≫ (c ≫ p) = v := by
  rw [← Category.assoc, hc, hp]

private theorem sfCbcCompletionProjection_unit (X : Scheme.{t}) {A : Type t}
    [CommRing A] (d : CompleteCoefficientDatum A) {K : proEtaleDerivedCategory X A}
    (M : AdicKFlatModel X A K) (n : ℕ) :
    adicCompletionMap X d M ≫
      (adicCompletionEvaluation X d M n ≫
        (adicDerivedRestrictFactors X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
          (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) M.complex)).inv) =
      adicReductionDerivedUnit X d M n := by
  unfold adicReductionDerivedUnit
  rw [← Category.assoc]
  have hp : adicCompletionMap X d M ≫ adicCompletionEvaluation X d M n =
      M.realization.inv ≫ (adicLocalization X A).map (adicReductionAugmentation X d M n) := by
    simpa only [adicCompletionEvaluation] using adicCompletionMap_projection X d M n
  exact (congrArg (fun f ↦ f ≫
    (adicDerivedRestrictFactors X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
      (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) M.complex)).inv) hp).trans
        (Category.assoc _ _ _)

attribute [local irreducible] adicReductionDerivedUnit

private theorem sfCbcCompletionAdjoint_unit (X : Scheme.{t}) {A : Type t}
    [CommRing A] (d : CompleteCoefficientDatum A) {K L : proEtaleDerivedCategory X A}
    (M : AdicKFlatModel X A K) (N : AdicKFlatModel X A L)
    (c : L ≅ adicCompletionObject X d M) (η : K ⟶ L)
    (hc : η ≫ c.hom = adicCompletionMap X d M) (n : ℕ) :
    adicReductionMap X d M N n η ≫
      (adicReductionHomEquiv X d N n _).symm
        (c.hom ≫ adicCompletionEvaluation X d M n ≫
          (adicDerivedRestrictFactors X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
            (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) M.complex)).inv) =
      𝟙 _ := by
  let R := adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  apply sfCbcTransposeCompositeIdentity R
    (adicReductionDerivedUnit X d M n) (adicReductionDerivedUnit X d N n)
    (adicReductionHomEquiv X d M n _) (adicReductionHomEquiv X d N n _)
    (sfCbcReductionHomEquiv_apply X d M n _)
    (sfCbcReductionHomEquiv_apply X d N n _)
    (adicReductionMap X d M N n η) η _ (adicReductionMap_unit X d M N n η)
  exact sfCbcCompTransport η c.hom _ (adicCompletionMap X d M)
    (adicReductionDerivedUnit X d M n) hc (sfCbcCompletionProjection_unit X d M n)

private theorem sfCbcInverseFormula {C : Type*} [Category C] {P N T : C}
    (u : P ⟶ N) (a : N ⟶ P) (t : P ⟶ T) [IsIso a] [IsIso t]
    (hu : u ≫ a = 𝟙 P) :
    ∃ h : IsIso (a ≫ t), (@asIso _ _ _ _ (a ≫ t) h).inv = inv t ≫ u := by
  refine ⟨inferInstance, ?_⟩
  apply (cancel_mono (a ≫ t)).mp
  change inv (a ≫ t) ≫ (a ≫ t) = _
  rw [IsIso.inv_hom_id]
  symm
  calc
    (inv t ≫ u) ≫ (a ≫ t) = inv t ≫ ((u ≫ a) ≫ t) := by
      simp only [Category.assoc]
    _ = 𝟙 _ := by rw [hu, Category.id_comp, IsIso.inv_hom_id]

/-- Finite completion comparison and its inverse reduced-unit formula, over P_n itself.
Source: Stacks Tag 099M; Steps 3–5 of the node.
Proof: the adjoint of projection is invertible by
lemma-weil-pbc-adic-completion-reduction. Its composite with the reduced completion
unit is identity by the projection identity of that unit and scalar-unit naturality.
Compose with the tensor comparison. The displayed inverse is forced by these two
identities. Every map is P_n-linear, before restriction to A coefficients.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcFiniteCompletedHom_inverse {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    {K : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K)
    (N : AdicKFlatModel X A ((sfCbcCompletedExtension j d).obj K)) (n : ℕ) :
    ∃ h : IsIso (sfCbcFiniteCompletedHom j d M N n),
      (@asIso _ _ _ _ (sfCbcFiniteCompletedHom j d M N n) h).inv =
        (@asIso _ _ _ _ (sfCbcFiniteTensorHom j d M n)
          (sfCbcFiniteTensorHom_isIso j d M n)).inv ≫
          adicReductionMap X d (sfCbcExtensionModel j A M) N n
            ((sfCbcCompletionUnit X d).app ((sfCbcDerivedExtension j A).obj K)) := by
  let P := sfCbcExtensionModel j A M
  let c := sfCbcCompletionModelIso X d P
  let a := (adicReductionHomEquiv X d N n _).symm
    (c.hom ≫ adicCompletionEvaluation X d P n ≫
      (adicDerivedRestrictFactors X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
        (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) P.complex)).inv)
  have ha : IsIso a := sfCbcCompletionAdjoint_isIso X d P N c n
  have ht := sfCbcFiniteTensorHom_isIso j d M n
  have hu : adicReductionMap X d P N n
      ((sfCbcCompletionUnit X d).app ((sfCbcDerivedExtension j A).obj K)) ≫ a = 𝟙 _ :=
    sfCbcCompletionAdjoint_unit X d P N c _
      (sfCbcCompletionModelIso_existsUnique X d P).exists.choose_spec n
  exact sfCbcInverseFormula _ a (sfCbcFiniteTensorHom j d M n) hu

/-- The finite comparison with its specified inverse, as an isomorphism.
Source: Stacks Tag 099M (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcFiniteCompletedIso {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    {K : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K)
    (N : AdicKFlatModel X A ((sfCbcCompletedExtension j d).obj K)) (n : ℕ) :=
  @asIso _ _ _ _ (sfCbcFiniteCompletedHom j d M N n)
    (sfCbcFiniteCompletedHom_inverse j d M N n).choose

/-- The A-linear version of the same finite comparison, using the recorded
restriction-of-scalars factorization and no change of quotient maps.
Source: Stacks Tags 03DI and 099M
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcFiniteUnderlyingHom {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    {K : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K)
    (N : AdicKFlatModel X A ((sfCbcCompletedExtension j d).obj K)) (n : ℕ) :
    adicReductionUnderlying X d N ⟨n + 1, Nat.succ_pos n⟩ ⟶
      (sfCbcDerivedExtension j A).obj
        (adicReductionUnderlying U d M ⟨n + 1, Nat.succ_pos n⟩) :=
  (adicDerivedRestrictFactors X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
    (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) N.complex)).inv ≫
    (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).map
      (sfCbcFiniteCompletedHom j d M N n) ≫
    (sfCbcDerivedRestrictExtensionIso j (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).inv.app
      (adicReduction U d M ⟨n + 1, Nat.succ_pos n⟩) ≫
    (sfCbcDerivedExtension j A).map
      (adicDerivedRestrictFactors U (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
        (adicChange U (Ideal.Quotient.mk (d.ideal ^ (n + 1))) M.complex)).hom

/-- Every quotient transition commutes with the specified finite comparison.
Source: Stacks Tags 0941 and 099M; Step 5 of the node.
Proof: the tensor comparisons commute with all quotient algebra homomorphisms,
by their common 1-tensor-section normalization. Limit projections commute with
those same transitions by the limit cone identity. Transpose these equalities
under the scalar adjunction; its unit is natural. Composing the resulting
squares gives the displayed equality, before any derived limit is applied.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcFiniteUnderlyingHom_transition {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    {K : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K)
    (N : AdicKFlatModel X A ((sfCbcCompletedExtension j d).obj K))
    (m n : ℕ) (h : n ≤ m) :
    adicTransition X d N ⟨m + 1, Nat.succ_pos m⟩ ⟨n + 1, Nat.succ_pos n⟩
        (Nat.succ_le_succ h) ≫ sfCbcFiniteUnderlyingHom j d M N n =
      sfCbcFiniteUnderlyingHom j d M N m ≫
        (sfCbcDerivedExtension j A).map
          (adicTransition U d M ⟨m + 1, Nat.succ_pos m⟩ ⟨n + 1, Nat.succ_pos n⟩
            (Nat.succ_le_succ h)) := by
  sorry

private theorem sfCbcFiniteTensorHom_naturality {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    {K L : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K)
    (M' : AdicKFlatModel U A L) (f : K ⟶ L) (n : ℕ) :
    adicReductionMap X d (sfCbcExtensionModel j A M) (sfCbcExtensionModel j A M') n
        ((sfCbcDerivedExtension j A).map f) ≫ sfCbcFiniteTensorHom j d M' n =
      sfCbcFiniteTensorHom j d M n ≫
        (sfCbcDerivedExtension j (A ⧸ d.ideal ^ (n + 1))).map
          (adicReductionMap U d M M' n f) := by
  let R := adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  let e := sfCbcDerivedRestrictExtensionIso j (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  have ht {H : proEtaleDerivedCategory U A} (P : AdicKFlatModel U A H) :
      adicReductionDerivedUnit X d (sfCbcExtensionModel j A P) n ≫
          R.map (sfCbcFiniteTensorHom j d P n) =
        (sfCbcDerivedExtension j A).map (adicReductionDerivedUnit U d P n) ≫
          e.hom.app (adicReduction U d P ⟨n + 1, Nat.succ_pos n⟩) :=
    by
      simpa only [sfCbcReductionHomEquiv_apply, sfCbcFiniteTensorHom] using
        (adicReductionHomEquiv X d (sfCbcExtensionModel j A P) n _).apply_symm_apply _
  apply (adicReductionHomEquiv X d (sfCbcExtensionModel j A M) n _).injective
  simp only [sfCbcReductionHomEquiv_apply]
  change adicReductionDerivedUnit X d (sfCbcExtensionModel j A M) n ≫ R.map _ =
    adicReductionDerivedUnit X d (sfCbcExtensionModel j A M) n ≫ R.map _
  rw [Functor.map_comp, ← Category.assoc, adicReductionMap_unit, Category.assoc, ht]
  rw [Functor.map_comp]
  simp only [← Category.assoc]
  rw [ht]
  simp only [Category.assoc]
  have he := e.hom.naturality (adicReductionMap U d M M' n f)
  change (sfCbcDerivedExtension j A).map
      ((adicDerivedRestrict U (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).map
        (adicReductionMap U d M M' n f)) ≫ e.hom.app _ =
    e.hom.app _ ≫ R.map
      ((sfCbcDerivedExtension j (A ⧸ d.ideal ^ (n + 1))).map
        (adicReductionMap U d M M' n f)) at he
  rw [← he, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, adicReductionMap_unit]

private theorem sfCbcFiniteCompletedHom_unit {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    {K : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K)
    (N : AdicKFlatModel X A ((sfCbcCompletedExtension j d).obj K)) (n : ℕ) :
    adicReductionMap X d (sfCbcExtensionModel j A M) N n
        ((sfCbcCompletionUnit X d).app ((sfCbcDerivedExtension j A).obj K)) ≫
      sfCbcFiniteCompletedHom j d M N n = sfCbcFiniteTensorHom j d M n := by
  change _ ≫ (_ ≫ _) = _
  rw [← Category.assoc, sfCbcCompletionAdjoint_unit X d
    (sfCbcExtensionModel j A M) N (sfCbcCompletionModelIso X d _) _
    (sfCbcCompletionModelIso_existsUnique X d _).exists.choose_spec n, Category.id_comp]

attribute [local irreducible] sfCbcFiniteCompletedHom sfCbcFiniteTensorHom

/-- Finite comparisons are natural in arbitrary input maps and model choices.
Source: Stacks Tags 06YY and 099M; Step 5 of the node.
Proof: the reduced completion unit and its inverse are natural, as is the tensor
comparison. Equivalently, naturality of the limit projections and the scalar
adjunction gives this equation directly from the definition of the finite map.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcFiniteCompletedHom_naturality {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    {K L : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K)
    (M' : AdicKFlatModel U A L)
    (N : AdicKFlatModel X A ((sfCbcCompletedExtension j d).obj K))
    (N' : AdicKFlatModel X A ((sfCbcCompletedExtension j d).obj L))
    (f : K ⟶ L) (n : ℕ) :
    adicReductionMap X d N N' n ((sfCbcCompletedExtension j d).map f) ≫
        sfCbcFiniteCompletedHom j d M' N' n =
      sfCbcFiniteCompletedHom j d M N n ≫
        (sfCbcDerivedExtension j (A ⧸ d.ideal ^ (n + 1))).map
          (adicReductionMap U d M M' n f) := by
  let P := sfCbcExtensionModel j A M
  let P' := sfCbcExtensionModel j A M'
  let η := sfCbcCompletionUnit X d
  let u := adicReductionMap X d P N n
    (η.app ((sfCbcDerivedExtension j A).obj K))
  have ht := sfCbcFiniteTensorHom_isIso j d M n
  have hc := (sfCbcFiniteCompletedHom_inverse j d M N n).choose
  have hu := sfCbcFiniteCompletedHom_unit j d M N n
  have hui : IsIso u := by
    apply (isIso_comp_right_iff _ (sfCbcFiniteCompletedHom j d M N n)).mp
    rw [show u ≫ sfCbcFiniteCompletedHom j d M N n =
      sfCbcFiniteTensorHom j d M n from hu]
    exact ht
  apply (cancel_epi u).mp
  have hη := η.naturality ((sfCbcDerivedExtension j A).map f)
  have hn : u ≫ adicReductionMap X d N N' n ((sfCbcCompletedExtension j d).map f) =
      adicReductionMap X d P P' n ((sfCbcDerivedExtension j A).map f) ≫
        adicReductionMap X d P' N' n
          (η.app ((sfCbcDerivedExtension j A).obj L)) := by
    rw [← adicReductionMap_comp, ← adicReductionMap_comp]
    exact congrArg (adicReductionMap X d P N' n) hη.symm
  rw [← Category.assoc, hn, Category.assoc, sfCbcFiniteCompletedHom_unit]
  rw [← Category.assoc, hu]
  exact sfCbcFiniteTensorHom_naturality j d M M' f n

/-- Exact evaluation in the actual strict diagram category on the small model.
Source: Stacks Tag 0941 (blueprint: lem-sf-cbc-extension-zero-completion). -/
abbrev sfCbcEvaluateModule (X : Scheme.{t}) (A : Type t) [CommRing A] (n : ℕ) :=
  (CategoryTheory.evaluation ℕᵒᵖ (ConstantCompletion.Mod (sfCbcModelRing X A))).obj (op n)

/-- Evaluation is derived after forming the strict diagram category.
Source: Stacks Tag 0941 (blueprint: lem-sf-cbc-extension-zero-completion). -/
abbrev sfCbcEvaluate (X : Scheme.{t}) (A : Type t) [CommRing A] (n : ℕ) :=
  (sfCbcEvaluateModule X A n).mapDerivedCategory

/-- The standard evaluation factorization with the fixed localization endpoints.
Source: Stacks 05RU and 0941 (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcEvaluateFactors (X : Scheme.{t}) (A : Type t) [CommRing A] (n : ℕ) :
    ConstantCompletion.TQ (sfCbcModelRing X A) ⋙ sfCbcEvaluate X A n ≅
      (sfCbcEvaluateModule X A n).mapHomologicalComplex (.up ℤ) ⋙
        ConstantCompletion.Q (sfCbcModelRing X A) :=
  (sfCbcEvaluateModule X A n).mapDerivedCategoryFactors

attribute [local irreducible] sfCbcEvaluateFactors

set_option backward.isDefEq.respectTransparency true in
/-- The canonical site-model transport preserves flat-term K-flat representatives.
Source: Stacks Tags 00VC and 06YY.
Proof: transport the tensor unit and tensor product along the ringed-site equivalence.
It is exact and preserves direct sums. It therefore transports total tensor products
and acyclic complexes, which proves K-flatness and termwise flatness.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcModelComplex_kflat (X : Scheme.{t}) {A : Type t} [CommRing A]
    {K : proEtaleDerivedCategory X A} (M : AdicKFlatModel X A K) :
    CochainComplex.IsAcyclicTensorKFlat (R := sfCbcModelRing X A)
      (((sfCbcModelModules X A).mapHomologicalComplex (.up ℤ)).obj M.complex) ∧
      ∀ i : ℤ, SheafOfModules.IsFlat
        ((((sfCbcModelModules X A).mapHomologicalComplex (.up ℤ)).obj M.complex).X i) := by
  let R := adicConstantRing X A
  let S := sfCbcModelRing X A
  let e := (AsSmall.equiv.{t, t + 1, t + 1} (C := X.ProEt)).symm
  have : e.functor.IsContinuous (proEtaleModelTopology X) (ProEt.topology X) :=
    inferInstanceAs (AsSmall.down.IsContinuous (proEtaleModelTopology X) (ProEt.topology X))
  have : e.inverse.IsContinuous (ProEt.topology X) (proEtaleModelTopology X) :=
    proEtaleModelUp_isContinuous X
  let hc : IsIso (sfCbcModelRingMap X A) := by
    unfold sfCbcModelRingMap
    exact (sfCbcModelRingMap_existsUnique X A).exists.choose_spec.1
  let c : S ≅ (e.functor.sheafPushforwardContinuous CommRingCat.{t + 1}
      (proEtaleModelTopology X) (ProEt.topology X)).obj R :=
    @asIso _ _ _ _ (sfCbcModelRingMap X A) hc
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients S
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients S
  obtain ⟨q⟩ := SheafOfModules.pushforward_equivalence_tensor_iso
    (proEtaleModelTopology X) (ProEt.topology X) e R S c
  let φ := (sheafCompose (proEtaleModelTopology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map (sfCbcModelRingMap X A)
  let F := SheafOfModules.pushforward.{t + 1} (F := e.functor)
    (J := proEtaleModelTopology X) (K := ProEt.topology X)
    (R := adicModuleRing X A)
    (S := (sheafCompose (proEtaleModelTopology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S) φ
  have h : sfCbcModelModules X A ≅ F := by
    unfold sfCbcModelModules
    exact sfCbcPushforwardRestrictIso (AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt)
      (adicModuleRing X A) _ φ
  have q' : MonoidalCategory.tensor _ ⋙ sfCbcModelModules X A ≅
      (sfCbcModelModules X A).prod (sfCbcModelModules X A) ⋙ MonoidalCategory.tensor _ :=
    isoWhiskerLeft (MonoidalCategory.tensor _) h ≪≫ q ≪≫
      isoWhiskerRight (NatIso.prod h.symm h.symm) (MonoidalCategory.tensor _)
  constructor
  · exact sfCbcKFlatTransport (sfCbcModelModules X A) q' M.complex M.isKFlat
  · intro i
    exact sfCbcFlatTransport (sfCbcModelModules X A) q' (M.complex.X i) (M.flatTerms i)

/-- Ordinary finite reductions commute with the fixed ringed-site equivalence.
The quotient-unit equation in each degree uniquely fixes the tensor comparison.
Source: Stacks Tags 00VC, 03EK and 06YY.
Proof: on constant scalar sections both maps send m to 1 tensor m. Sheafification
and the quotient scalar map give the comparison and its inverse. The augmentation
is an epimorphism in every degree, so the equation determines the chain map uniquely.
Compatibility with differentials is naturality of the scalar unit.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcFiniteModelIso_existsUnique (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : CompleteCoefficientDatum A) {K : proEtaleDerivedCategory X A}
    (M : AdicKFlatModel X A K) (n : ℕ) :
    ∃! e : ((sfCbcEvaluateModule X A n).mapHomologicalComplex (.up ℤ)).obj
        (ConstantCompletion.reductionComplex (proEtaleModelTopology X)
          (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false
          (((sfCbcModelModules X A).mapHomologicalComplex (.up ℤ)).obj M.complex)) ≅
      ((sfCbcModelModules X A).mapHomologicalComplex (.up ℤ)).obj
        (adicReductionComplex X d M n),
      ∀ i : ℤ,
        ((ConstantCompletion.reductionUnit (proEtaleModelTopology X)
          (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false).app
            ((sfCbcModelModules X A).obj (M.complex.X i))).app (op n) ≫ e.hom.f i =
          (sfCbcModelModules X A).map ((adicReductionAugmentation X d M n).f i) := by
  sorry

/-- Model localization at finite level, with its original-coefficient endpoint explicit.
Source: Stacks 05RU and 06YY (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcFiniteModelFactors (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : CompleteCoefficientDatum A) {K : proEtaleDerivedCategory X A}
    (M : AdicKFlatModel X A K) (n : ℕ) :
    (ConstantCompletion.Q (sfCbcModelRing X A)).obj
        (((sfCbcModelModules X A).mapHomologicalComplex (.up ℤ)).obj
          (adicReductionComplex X d M n)) ≅
      (sfCbcModelDerived X A).functor.obj
        (adicReductionUnderlying X d M ⟨n + 1, Nat.succ_pos n⟩) :=
  ((sfCbcModelDerivedFactors X A).app (adicReductionComplex X d M n)).symm

attribute [local irreducible] sfCbcFiniteModelFactors

/-- Canonical evaluation of the strict reduction at finite level. The formula uses
one model, the universal quotient counit, and the unit-normalized ordinary comparison.
Source: Stacks Tags 0941 and 06YY
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcFiniteEvaluationIso (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : CompleteCoefficientDatum A) {K : proEtaleDerivedCategory X A}
    (M : AdicKFlatModel X A K) (n : ℕ) :
    (sfCbcEvaluate X A n).obj ((sfCbcReduction X d).obj K) ≅
      (sfCbcModelDerived X A).functor.obj
        (adicReductionUnderlying X d M ⟨n + 1, Nat.succ_pos n⟩) := by
  let P : ConstantCompletion.Cx (sfCbcModelRing X A) :=
    ((sfCbcModelModules X A).mapHomologicalComplex (.up ℤ)).obj M.complex
  have hP := sfCbcModelComplex_kflat X M
  exact (sfCbcEvaluate X A n).mapIso
    ((sfCbcQuotientPresentation X d).tower.mapIso
      ((sfCbcModelDerived X A).functor.mapIso M.realization.symm ≪≫
        (sfCbcModelDerivedFactors X A).app M.complex) ≪≫
      @asIso _ _ _ _ ((sfCbcQuotientPresentation X d).comparison.app P)
        ((sfCbcQuotientPresentation X d).laws.2.1 P hP.1 hP.2)) ≪≫
    (sfCbcEvaluateFactors X A n).app
      (ConstantCompletion.reductionComplex (proEtaleModelTopology X)
        (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false P) ≪≫
    (ConstantCompletion.Q (sfCbcModelRing X A)).mapIso
      (sfCbcFiniteModelIso_existsUnique X d M n).exists.choose ≪≫
    sfCbcFiniteModelFactors X d M n

/-- Evaluation commutes with termwise extension by the identity natural isomorphism.
Source: Stacks Tag 0941 (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcEvaluateExtensionIso {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] (n : ℕ) :
    sfCbcDerivedTowerExtension j A ⋙ sfCbcEvaluate X A n ≅
      sfCbcEvaluate U A n ⋙ sfCbcModelDerivedExtension j A :=
  (Functor.mapDerivedCategoryCompIso (sfCbcTowerExtension j A)
    (sfCbcEvaluateModule X A n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (whiskeringRightCompEvaluation (sfCbcModelExtension j A) (op n)) ≪≫
      Functor.mapDerivedCategoryCompIso (sfCbcEvaluateModule U A n)
        (sfCbcModelExtension j A)

/-- Evaluating the actual strict q-map gives exactly the prescribed finite
P_n-linear map after scalar restriction, with all comparisons fixed above.
Source: Stacks Tags 0941 and 099M; Steps 3–5 of the node.
Proof: on a flat K-flat model, evaluation of the universal quotient counit is the
ordinary finite quotient complex. The normalized tensor comparison evaluates to
sfCbcFiniteTensorHom, by its scalar-unit characterization. The limit-unit equation
identifies inverse reduced unit with the adjoint of projection. Compose these
identities, using sfCbcFiniteModelIso's quotient-unit equation and exact-derived
factorizations. This gives the displayed square in D(X,A), with no derived limit.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcCompletedReductionIso_evaluation {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    {K : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K)
    (N : AdicKFlatModel X A ((sfCbcCompletedExtension j d).obj K)) (n : ℕ) :
    (sfCbcEvaluate X A n).map ((sfCbcCompletedReductionIso j d).hom.app K) ≫
        (sfCbcEvaluateExtensionIso j A n).hom.app ((sfCbcReduction U d).obj K) ≫
        (sfCbcModelDerivedExtension j A).map (sfCbcFiniteEvaluationIso U d M n).hom ≫
        (sfCbcExtensionTransport j A).inv.app
          (adicReductionUnderlying U d M ⟨n + 1, Nat.succ_pos n⟩) =
      (sfCbcFiniteEvaluationIso X d N n).hom ≫
        (sfCbcModelDerived X A).functor.map (sfCbcFiniteUnderlyingHom j d M N n) := by
  sorry

/-- The geometric localization functor, retaining the underlying schemes and maps.
Source: Stacks Tag 098K (blueprint: lem-sf-cbc-extension-zero-completion). -/
abbrev sfCbcOpenLocalization {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j] :
    U.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)

attribute [local instance 1000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

/-- A fixed-scalar section in the canonical associated module sheaf.
Source: Stacks Tag 00YV (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcRealizationSection (T : Scheme.{t}) (B : Type t) [CommRing B]
    (F : Sheaf (ProEt.topology T) (ModuleCat.{t + 1} (ULift.{t + 1, t} B)))
    (V : T.ProEt) (m : F.obj.obj (op V)) :
    ((etaleOriginRealization T (ULift.{t + 1, t} B)).obj F).val.obj (op V) :=
  ((PresheafOfModules.sheafificationAdjunction
    (etaleOriginScalars T (ULift.{t + 1, t} B))).unit.app
      ((ProEtale.finiteCoefficientModulePresheaf T.ProEt
        (ULift.{t + 1, t} B)).obj F.obj)).app (op V) m

attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

/-- Realization identifies the fixed-coefficient extension with the localized
module extension, with the identity on every extension generator. The HEq only
transports the identical underlying scheme between its two displayed structure maps.
Source: Stacks Tags 03DI and 00YV; Step 7 of the node.
Proof: on a factorization V through U, the Kan-extension unit inserts the section
in its summand. The module extension inserts the same section by DirectSum.lof.
The canonical constant scalar map identifies their scalar actions. Sheafify these
maps; the inverse uses the same summands. Local generation proves the inverse
identities and uniqueness. This is the identity restriction-square conjugate,
not a choice of an unnormalized natural isomorphism.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcRealizationExtensionIso_existsUnique {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : Type t) [CommRing B] [Finite B] :
    ∃! e : ProEtale.openImmersionLowerShriek
        (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) j ⋙
          etaleOriginRealization X (ULift.{t + 1, t} B) ≅
      etaleOriginRealization U (ULift.{t + 1, t} B) ⋙ sfCbcOpenExtension j B,
      ∀ (F : Sheaf (ProEt.topology U) (ModuleCat.{t + 1} (ULift.{t + 1, t} B)))
        (V : X.ProEt) (a : V ⟶ cbcOpenObject j inferInstance)
        (m : F.obj.obj (op ((cbcSliceFunctor X (cbcOpenObject j inferInstance)).obj
          (Over.mk a)))),
        HEq
          ((e.hom.app F).val.app
            (op ((sfCbcOpenLocalization j).obj
              ((cbcSliceFunctor X (cbcOpenObject j inferInstance)).obj (Over.mk a))))
            (sfCbcRealizationSection X B
              ((ProEtale.openImmersionLowerShriek
                (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) j).obj F) _
              (((ProEtale.openImmersionLowerShriekAdjunction
                (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) j).unit.app F).hom.app
                  (op ((cbcSliceFunctor X (cbcOpenObject j inferInstance)).obj
                    (Over.mk a))) m)))
          (sfCbcExtensionSection j B
            ((etaleOriginRealization U (ULift.{t + 1, t} B)).obj F) V a
              (sfCbcRealizationSection U B F _ m)) := by
  sorry

/-- The generator-normalized realization/extension isomorphism.
Source: Stacks Tag 03DI (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcRealizationExtensionIso {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : Type t) [CommRing B] [Finite B] :=
  (sfCbcRealizationExtensionIso_existsUnique j B).exists.choose

/-- The canonical nu/j! comparison with constant-module realization. It is the
published identity-square conjugate followed by the normalized realization comparison.
Source: Stacks Tag 099R (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcEtaleExtensionComparison {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : Type t) [CommRing B] [Finite B] :
    (Functor.mapDerivedCategory
      (Etale.openImmersionLowerShriek (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) j)) ⋙
        etaleOriginComparison X (ULift.{t + 1, t} B) ≅
    etaleOriginComparison U (ULift.{t + 1, t} B) ⋙ sfCbcDerivedExtension j B :=
  (Functor.mapDerivedCategoryCompIso
    (Etale.openImmersionLowerShriek (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) j)
    (ProEtale.comparisonUpperStar (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) X ⋙
      etaleOriginRealization X (ULift.{t + 1, t} B))).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (isoWhiskerRight
          (ProEtale.openImmersionLowerShriekComparisonUpperStarIso
            (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) j)
          (etaleOriginRealization X (ULift.{t + 1, t} B)) ≪≫
        isoWhiskerLeft (ProEtale.comparisonUpperStar
          (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) U)
          (sfCbcRealizationExtensionIso j B)) ≪≫
    Functor.mapDerivedCategoryNatIso
      (Functor.associator
        (ProEtale.comparisonUpperStar (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) U)
        (etaleOriginRealization U (ULift.{t + 1, t} B)) (sfCbcOpenExtension j B)).symm ≪≫
    Functor.mapDerivedCategoryCompIso
      (ProEtale.comparisonUpperStar (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) U ⋙
        etaleOriginRealization U (ULift.{t + 1, t} B)) (sfCbcOpenExtension j B)

/-- Exact etale extension retains bounded-below antecedents.
Source: Stacks Tag 03DI; Step 7 of the node.
Proof: the exact functor acts termwise, so cohomology in every degree is the
extension of the input cohomology. A lower vanishing bound is therefore preserved.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcEtaleExtension_boundedBelow {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (B : Type t) [CommRing B]
    (L : DerivedCategory.Plus
      (Sheaf U.smallEtaleTopology (ModuleCat.{t + 1} (ULift.{t + 1, t} B)))) :
    DerivedCategory.TStructure.t.plus
      ((Etale.openImmersionLowerShriek
        (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) j).mapDerivedCategory.obj L.obj) := by
  obtain ⟨n, hn⟩ := L.property
  exact ⟨n, (Etale.openImmersionLowerShriek
    (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) j).isGE_mapDerivedCategory_obj L.obj n⟩

/-- The transported etale antecedent is the actual termwise j! of the input.
Source: Stacks Tag 03DI (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcEtaleExtensionPlus {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (B : Type t) [CommRing B]
    (L : DerivedCategory.Plus
      (Sheaf U.smallEtaleTopology (ModuleCat.{t + 1} (ULift.{t + 1, t} B)))) :
    DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{t + 1} (ULift.{t + 1, t} B))) :=
  ⟨(Etale.openImmersionLowerShriek
    (ModuleCat.{t + 1} (ULift.{t + 1, t} B)) j).mapDerivedCategory.obj L.obj,
    sfCbcEtaleExtension_boundedBelow j B L⟩

/-- Transport the specified witness isomorphism, retaining the actual antecedent
j! L. The composite is nu_X^* j! L -> J nu_U^* L -> J(K tensor P_n)
-> (Jc K) tensor P_n. The witness is supplied as its two components, without
introducing another definition of etale origin.
Source: Stacks Tags 03DI and 099R; Step 7 of the node
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcTransportEtaleWitnessIso {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    [∀ n : ℕ, Finite (A ⧸ d.ideal ^ (n + 1))]
    {K : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K)
    (N : AdicKFlatModel X A ((sfCbcCompletedExtension j d).obj K)) (n : ℕ)
    (L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1, t} (A ⧸ d.ideal ^ (n + 1))))))
    (α : (etaleOriginComparison U (ULift.{t + 1, t} (A ⧸ d.ideal ^ (n + 1)))).obj
      L.obj ≅ adicReduction U d M ⟨n + 1, Nat.succ_pos n⟩) :
    (etaleOriginComparison X (ULift.{t + 1, t} (A ⧸ d.ideal ^ (n + 1)))).obj
      (sfCbcEtaleExtensionPlus j (A ⧸ d.ideal ^ (n + 1)) L).obj ≅
        adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩ :=
  (sfCbcEtaleExtensionComparison j (A ⧸ d.ideal ^ (n + 1))).app L.obj ≪≫
    (sfCbcDerivedExtension j (A ⧸ d.ideal ^ (n + 1))).mapIso α ≪≫
      (sfCbcFiniteCompletedIso j d M N n).symm

private theorem sfCbcComplete_of_iso
    {S : Type (t + 1)} [SmallCategory S] {J : GrothendieckTopology S}
    {R T : Sheaf J CommRingCat.{t + 1}} (q : R ⟶ T)
    {M N : ConstantCompletion.D R} (e : M ≅ N)
    (hN : ConstantCompletion.IsComplete q N) : ConstantCompletion.IsComplete q M := by
  let : HasDerivedCategory (ConstantCompletion.Mod R) := HasDerivedCategory.standard _
  let : ∀ V : S, HasDerivedCategory (ConstantCompletion.Mod (R.over V)) :=
    fun _ ↦ HasDerivedCategory.standard _
  intro V f hf
  exact (hN V f hf).of_iso ((derivedInternalHom (J.over V) (R.over V)).mapIso
    ((Iso.refl _).prod ((ringedDerivedRestriction R V).mapIso e)))

-- The retained witness binder occurs in the proof but not in its existential conclusion.
set_option linter.unusedVariables false in
/-- Strict reduction of completed extension by zero: the unit normalization,
completeness of the output, and the specified natural derived-limit presentation.
Source: blueprint fix-lem-exchanges, integral open factor; Stacks Tags 099M and 0941.
Proof:
1. Extend a flat-term K-flat model termwise using the exact localized-site extension.
The tensor projection formula proves flatness and K-flatness, as in
sfCbcExtensionModel_existsUnique.
2. Quotient-natural tensor comparison is the strict tower isomorphism
sfCbcTensorComparison, fixed by the ordinary quotient-unit formula and universal counits.
3. Finite reduction of completion identifies each reduced unit with the inverse
of the adjoint of the corresponding limit projection; cones are acyclic levelwise,
so sfCbcReducedCompletionUnit_isIso applies in the derived tower category.
4. The definition of q cancels the reduced unit and gives the displayed equality.
5. Completion is the reflector of lem-sp-completed-pullback-adjunction, so its
output is complete. Apply functorial Rlim to the tensor comparison to obtain exactly
sfCbcCompletedExtensionPresentation. This never commutes ordinary extension with Rlim.
6. A retained witness (L, alpha) is sent by sfCbcTransportEtaleWitnessIso to
(j! L, the specified comparison followed by J alpha and the inverse finite map).
Exactness preserves the lower cohomological bound, so this is a bounded-below
witness with exactly the prescribed antecedent, for each n independently.
7. Every constituent is a natural transformation or a natural isomorphism before
Rlim. Thus all conclusions respect input maps and every quotient transition,
including the identity open, empty open, and zero complex.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcExtensionZeroCompletion {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    [∀ n : ℕ, Finite (A ⧸ d.ideal ^ (n + 1))] :
    IsIso (sfCbcReducedCompletionUnit j d) ∧
    (∀ K : proEtaleDerivedCategory U A,
      (sfCbcReduction X d).map
          ((sfCbcCompletionUnit X d).app ((sfCbcDerivedExtension j A).obj K)) ≫
        (sfCbcCompletedReductionIso j d).hom.app K =
          (sfCbcTensorComparison j d).hom.app K) ∧
    (∀ K : proEtaleDerivedCategory U A,
      sfCbcIsComplete X d ((sfCbcCompletedExtension j d).obj K)) ∧
    (∀ (K : proEtaleDerivedCategory U A) (M : AdicKFlatModel U A K)
      (N : AdicKFlatModel X A ((sfCbcCompletedExtension j d).obj K)) (n : ℕ),
      IsIso (sfCbcFiniteCompletedHom j d M N n) ∧
        ∀ (L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology
          (ModuleCat.{t + 1} (ULift.{t + 1, t} (A ⧸ d.ideal ^ (n + 1))))))
          (α : (etaleOriginComparison U
            (ULift.{t + 1, t} (A ⧸ d.ideal ^ (n + 1)))).obj L.obj ≅
              adicReduction U d M ⟨n + 1, Nat.succ_pos n⟩),
          Nonempty ((etaleOriginComparison X
            (ULift.{t + 1, t} (A ⧸ d.ideal ^ (n + 1)))).obj
              (sfCbcEtaleExtensionPlus j (A ⧸ d.ideal ^ (n + 1)) L).obj ≅
                adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩)) := by
  have := sfCbcReducedCompletionUnit_isIso j d
  constructor
  · exact sfCbcReducedCompletionUnit_isIso j d
  constructor
  · intro K
    change (asIso (sfCbcReducedCompletionUnit j d)).hom.app K ≫
      ((asIso (sfCbcReducedCompletionUnit j d)).inv ≫
        (sfCbcTensorComparison j d).hom).app K = _
    exact (asIso (sfCbcReducedCompletionUnit j d)).hom_inv_id_app_assoc K _
  constructor
  · intro K
    let := d.noetherian
    let : IsNoetherianRing (ULift.{t + 1, t} A) :=
      isNoetherianRing_of_ringEquiv A ULift.ringEquiv.symm
    obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
      (Ideal.fg_of_isNoetherianRing (sfCbcModelIdeal d))
    obtain ⟨P, _, h, _⟩ := ConstantCompletion.koszul_quotient_reflector
      (proEtaleModelTopology X) (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false r a ha
    let E := sfCbcModelDerived X A
    let C := ConstantCompletion.completion (proEtaleModelTopology X)
      (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false
    have hc := h (E.functor.obj ((sfCbcDerivedExtension j A).obj K))
    change ConstantCompletion.IsComplete _
      (E.functor.obj (E.inverse.obj (C.obj
        (E.functor.obj ((sfCbcDerivedExtension j A).obj K)))))
    exact sfCbcComplete_of_iso _
      (E.counitIso.app (C.obj (E.functor.obj ((sfCbcDerivedExtension j A).obj K)))) hc
  · intro K M N n
    exact ⟨(sfCbcFiniteCompletedHom_inverse j d M N n).choose,
      fun L α ↦ ⟨sfCbcTransportEtaleWitnessIso j d M N n L α⟩⟩

end AlgebraicGeometry.Scheme
