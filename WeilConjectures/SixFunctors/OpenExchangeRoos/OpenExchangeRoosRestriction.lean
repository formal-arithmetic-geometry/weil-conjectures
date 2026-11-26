/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenStrictMateIdentification
public import WeilConjectures.AlgebraicGeometry.ImmersionCompletedPullback.SfImmersionCompletedPullbackComparison
public import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorPullModel
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionComparison
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.CategoryTheory.Strict.StrictRoosDerivedLimitComparisonSupplement
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
import WeilConjectures.CategoryTheory.StrictRoosComparison
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.CategoryTheory.StrictRoosDerivation
import WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.Algebra.Homology.RoosComplex
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.StrictRoosNormalization
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.Basic.Denumerable
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosDescent
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosResolution
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosCompatibility
import WeilConjectures.AlgebraicGeometry.Adic.AdicPullbackPresentationTransport
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenExtensionProducts
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses

import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerCanonical
import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenScalars.FiniteOpenExchangeScalars
import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
import WeilConjectures.AlgebraicGeometry.Completed.CompletedRingStrictFiniteExchange
import WeilConjectures.Algebra.Homology.Ringed.RingedOpenFlatResolution
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian

/-! # Restriction of the completed open exchange in strict Roos coordinates

The completed open exchange of an open immersion is the ordered strict derived limit of its
finite open exchanges, and its restriction is the finite-composition comparison
(`openExchangeRoosRestriction`).

## Implementation details

The integral datum is the existing uniformizer datum. Its completed-ring presentation
is transported to integral coefficients by the projection-normalized `transport`.
The strict exchange and completed exchange are the published maps, including their
endpoint comparisons. No equality is tested by separate derived evaluations.
The signed coordinates below are `(y,x)`, the order of `strictRoosCoordinates`;
in these coordinates the augmentation is `(0,gamma)`.

## References

* Stacks Project, Tags 099N, 09BN, 0D6D, 01T1, 01K5
* Bhatt--Scholze, *The pro-étale topology for schemes*, 3.5.2
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u uA vA uB vB
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.OpenExchangeRoos

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The singleton generating tuple for the existing uniformizer ideal. -/
def generators : Fin 1 → PbcIntegralRing l E := fun _ ↦ pbcUniformizer l E

/-- The tuple `generators` generates the uniformizer ideal of the coefficient DVR. -/
theorem generators_span : Ideal.span (Set.range (generators l E)) =
    (pbcIntegralDatum l E).ideal := by
  unfold generators
  rw [Set.range_const]
  rfl

/-- Roos completeness in the coefficient presentation of the completed-open comparison. -/
abbrev complete (W : Scheme.{u}) : ObjectProperty ((pbcIntegralDatum l E).derived W) :=
  fun K ↦ IntegralOnSlice.IsComplete l E W none
    ((ImmersionCompletedPullback.transport l E W).obj K)

/-- The section-normalized open unit, on the ordinary derived category. -/
def openUnit {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  @asIso _ _ _ _ (cbcDerivedOpenAdjunction (pbcIntegralDatum l E) j).unit
    (cbcOpenUnit_isIso (pbcIntegralDatum l E) j)

/-- The completed square has the ordinary square's normalization on the actual units.
The source is the full subcategory of Roos-complete objects. -/
abbrev Square {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (h : X' ⟶ X) :=
  (complete l E X).ι ⋙ (pbcIntegralDatum l E).completedPull h ⋙
      (pbcIntegralDatum l E).pull j' ≅
    (complete l E X).ι ⋙ (pbcIntegralDatum l E).pull j ⋙
      (pbcIntegralDatum l E).completedPull a

/-- The unit equation of a `Square`, using the ordinary compositor and the recorded quotient
unit. -/
def SquareUnit {U' U X' X : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {h : X' ⟶ X} (sq : OpenImmersionSquare a j' j h)
    (c : Square l E a j' j h) : Prop :=
  ∀ H : (complete l E X).FullSubcategory,
    ((pbcIntegralDatum l E).pull j').map
        ((pbcIntegralDatum l E).ordinaryToCompleted h H.obj) ≫ c.hom.app H =
      (cbcSquarePull (pbcIntegralDatum l E) a j' j h sq.w).hom.app H.obj ≫
        (pbcIntegralDatum l E).ordinaryToCompleted a
          (((pbcIntegralDatum l E).pull j).obj H.obj)

/-- The ordinary derived open adjunction used by the constant-coefficient limit model: the
module adjunction descended termwise, with its canonical right-derived comparison. -/
def constantOpenAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  Adjunction.ofNatIsoRight
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (ProEtale.StrictTower.moduleJAdj (PbcIntegralRing l E) j))
    (Functor.rightDerivedFunctorIsoMapDerivedCategory
      (ProEtale.StrictTower.modulePullback (PbcIntegralRing l E) j))

/-- An open immersion into a scheme of finite type over the fixed field is quasi-compact. -/
theorem finiteOpenQC (F : FiniteFieldDatum.{u})
    (U X : Over (Spec (.of F.k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left] : QuasiCompact j.left := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  have : TopologicalSpace.NoetherianSpace U.left :=
    j.left.isOpenEmbedding.isInducing.noetherianSpace
  infer_instance

/-- Clause-by-clause assertion on the fixed completed coefficient presentation.
The square is uniquely determined by its actual unit equation. Its exchange is the
specified one, transported to the fixed strict endpoints. -/
def Assertion {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (h : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] [qc : QuasiCompact j]
    (sq : OpenImmersionSquare a j' j h) : Prop :=
    ∃! c : Square l E a j' j h,
      SquareUnit l E sq c ∧
      ∀ (K : (pbcIntegralDatum l E).derived U), complete l E U K →
        ∃ (hI : cbcCompleteProperty (pbcIntegralDatum l E) U 1 (generators l E)
            (generators_span l E) K)
          (hJ : complete l E X
            ((cbcDerivedOpenShriek (pbcIntegralDatum l E) j inferInstance).obj K)),
          complete l E X' (((pbcIntegralDatum l E).completedPull h).obj
            ((cbcDerivedOpenShriek (pbcIntegralDatum l E) j inferInstance).obj K)) ∧
          complete l E X'
            ((cbcDerivedOpenShriek (pbcIntegralDatum l E) j' inferInstance).obj
              (((pbcIntegralDatum l E).completedPull a).obj K)) ∧
          IsIso ((cbcDatumCompletedExchange (pbcIntegralDatum l E) sq 1 (generators l E)
            (generators_span l E)).app ⟨K, hI⟩) ∧
          (cbcRealizationRes (pbcIntegralDatum l E) X').mapDerivedCategory.map
              ((cbcDatumCompletedExchange (pbcIntegralDatum l E) sq 1 (generators l E)
                (generators_span l E)).app ⟨K, hI⟩) ≫
                (cbcOpenMateCompletedB (pbcIntegralDatum l E)
                  (j' := j') (v := a) K).hom =
            (cbcOpenMateCompletedA (pbcIntegralDatum l E)
                (j := j) (g := h) K).hom ≫
              (completedRlim X'
                (exchangeConstantRing X' (PbcIntegralRing l E))).map
                  (cbcOpenMateBeta (pbcIntegralDatum l E) sq K).hom ≫
              (@cbcRealizationOpenLimit _ _ (pbcIntegralDatum l E) U' X' j'
                inferInstance (cbcOpenMateQC sq)).inv.app
                  ((ProEtale.StrictTower.G (PbcIntegralRing l E) a).obj
                    ((cbcOpenMateM (pbcIntegralDatum l E) (U := U)).obj K)) ∧
          ((pbcIntegralDatum l E).pull j').map
              ((cbcDatumCompletedExchange (pbcIntegralDatum l E) sq 1 (generators l E)
                (generators_span l E)).app ⟨K, hI⟩) ≫
                (openUnit l E j').inv.app
                  (((pbcIntegralDatum l E).completedPull a).obj K) =
            c.hom.app
                ⟨(cbcDerivedOpenShriek (pbcIntegralDatum l E) j inferInstance).obj K, hJ⟩ ≫
              ((pbcIntegralDatum l E).completedPull a).map
                ((openUnit l E j).inv.app K)

/-- The specified completed exchange is the ordered strict derived limit of its finite
open exchanges. Its restriction is the finite-composition comparison, and that
comparison preserves the actual ordinary-to-completed pullback units. -/
theorem openExchangeRoosRestriction (F : FiniteFieldDatum.{u}) (_hl : l ≠ F.p)
    (U' U X' X : Over (Spec (.of F.k)))
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (h : X' ⟶ X)
    [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
    (sq : OpenImmersionSquare a.left j'.left j.left h.left) :
    Assertion l E a.left j'.left j.left h.left
      (qc := finiteOpenQC F U X j) sq := by
  sorry

end WeilConjectures.OpenExchangeRoos
