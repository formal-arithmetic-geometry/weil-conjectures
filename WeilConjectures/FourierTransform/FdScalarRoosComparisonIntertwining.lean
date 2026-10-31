/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdScalarPullbackRealizationIdentification
import WeilConjectures.FourierTransform.FdPullbackAugmentationCounitMatching
public import WeilConjectures.FourierTransform.PullbackCommonStrictTowerModels
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
public import WeilConjectures.CategoryTheory.StrictRoosComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.StrictRoosDerivation
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.RoosComplex
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.R.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.StrictRoosNormalization
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
public import WeilConjectures.FourierTransform.FdCoefficientComparison
public import WeilConjectures.SixFunctors.Integral.IntegralPullbackComparisonRealization
public import WeilConjectures.FourierTransform.FdPullbackComparison
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.CategoryTheory.Finite.FiniteFreeStrictTowerTransport
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.ProperBaseChange.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
import WeilConjectures.CategoryTheory.StrictRoosComparison
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
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
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.Algebra.Homology.RoosComplex
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.R.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.StrictRoosNormalization
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.Logic.Denumerable
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosDescent
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosCompatibility

/-! # Scalar transport of the normalized Roos pullback comparison

Source: trace-definition coefficient-category comparison, extracted whole-tower proof
steps 9--10; Stacks Tag 0941, lemma-derived-limit-is-ok
(blueprint: lem-fd-scalar-roos-comparison-intertwining).

The comparison is the recorded normalized Roos comparison, and the scalar-limit map
is its actual constant-tower/derived-limit adjunct. Rational categories are raw
scalar localizations; no idempotent completion occurs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme SheafOfModules
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

set_option allowUnsafeReducibility true in
attribute [local irreducible] integralOrdinaryScalar HasDerivedCategory.standard
  coefficientConstantTowerLimit integralDetailedTransport

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.Stage

/-- Finite-free scalar transport carries rho to rho, with its canonical diagonal
product map and the entire-tower counit retained.
Source: Stacks 0941, lemma-derived-limit-is-ok; extracted proof steps 1--2
(blueprint: lem-fd-scalar-roos-comparison-intertwining).

Proof: finiteFreeCompletedScalarComparison makes the completed target ring finite free.
Thus ordinary tensor is exact and preserves countable products: after choosing a basis
its underlying functor is a finite direct sum of identities, and the product comparison
is fixed by its projections. ProEt.countableProducts_exact supplies exact products.
Apply exactProductFunctorStrictLimit. Its coordinates (x,z) become our (y,x) by z=-y;
the inclusion is still (0,x) and the product map acts diagonally. Its conjugation formula
is precisely lambda C(rho)=rho kappa below. finiteFreeStrictTowerTransport identifies
lambda with the ordinary limit/tensor map followed by resolution. Component n of its
counit equation is r_n C(pr_n), so localizing gives the displayed entire-tower equality.
No K-injectivity of the scalar image of an injective resolution is assumed. -/
theorem fdScalarRoosTransport (W : Scheme.{u}) [IsNoetherian W]
    (_hdimW : ∃ n : ℕ, topologicalKrullDim W ≤ n)
    (_hinvW : ∀ x : W, IsUnit (l : W.presheaf.stalk x))
    (D : IntegralComparisonSystem.{u} l) :
    (∀ X : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ,
      HEq (fdScalarLimitComparison l E L ι W (DerivedCategory.Q.obj X) ≫
        (coefficientConstantTowerLimit l L W).map
          ((projectionPost (I := ℕᵒᵖ)
            (integralOrdinaryScalar l E L ι W)).mapDerivedCategoryFactors.hom.app X) ≫
        ((D.coefficient L).roos W).comparison.hom.app
          (((projectionPost (I := ℕᵒᵖ) (integralOrdinaryScalar l E L ι W)).mapHomologicalComplex
            (.up ℤ)).obj X))
        ((integralOrdinaryDerivedScalar l E L ι W).map
            (((D.coefficient E).roos W).comparison.hom.app X) ≫
          (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
            (integralOperationsRoos X.asFunctor) ≫
          DerivedCategory.Q.map
            (scalarRoosMap (integralOrdinaryScalar l E L ι W) X.asFunctor))) ∧
    (∀ Q : coefficientSequenceRestrictedDerived l E W,
      (integralComparisonConstantTower l L W).map
          (fdScalarLimitComparison l E L ι W Q) ≫
        (integralComparisonTowerCounit l L W).app ((fdScalarTower l E L ι W).obj Q) =
      (fdScalarConstantSquare l E L ι W).inv.app
          ((coefficientConstantTowerLimit l E W).obj Q) ≫
        (fdScalarTower l E L ι W).map ((integralComparisonTowerCounit l E W).app Q)) := by
  sorry

/-- The ordinary scalar square and its completion conjugate, in the actual ambient
models of the full integral categories. Membership witnesses only allow restriction;
all arrows are the specified normalized comparisons.
Source: Stacks 0941 and the trace-definition coefficient comparison, proof steps 3--4
(blueprint: lem-fd-scalar-roos-comparison-intertwining).

Proof: for X=Q(h,E,P), Y=Q(h,L,P tensor R-L), common strict tower models identify b
with rho. The actual strict d gives delta-s=H(d) kappa and delta-p=Rlim(d) lambda
by fdScalarPullbackRealizationIdentification. Naturality of rho and fdScalarRoosTransport
therefore give rho-Y H(d) kappa=Rlim(d) lambda C(rho-X). Insert the defining realization
maps and coefficient identities to obtain the first equation. The completion formula is
alpha-s=F-s(chi-T) delta-s chi-U inverse. Naturality of b-L at chi-T cancels F-p(chi-T
inverse) b-L F-s(chi-T) to b-L, giving the second equation. Fullness restricts both
identities. No quotient map d-n is inverted, so ramified and identity extensions remain
included. -/
theorem fdScalarRoosIntegralIntertwining
    {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ x : U, IsUnit (l : U.presheaf.stalk x))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))]
    (h : U ≅ T) (cU : FdScalarCoefficientTransport l E L ι U)
    (cT : FdScalarCoefficientTransport l E L ι T)
    (bE : FdCommonStrictTowerModels l E h) (bL : FdCommonStrictTowerModels l L h)
    (K : sfIntegralConstructibleCategory l E T) :
    ∃ (hC : sfIntegralConstructible l L T
        ((integralOrdinaryDerivedScalar l E L ι T).obj K.obj))
      (hS : sfIntegralConstructible l L T ((integralScalarExtension l E L ι T).obj K.obj))
      (hF : IsSfDerivedComplete l E U ((integralDerivedPullback l E h.hom).obj K.obj)),
      ((integralDetailedTransport U l L).map
          ((scalarPullbackOrdinary l E L ι h.hom).hom.app K.obj) ≫
        bL.actual_ambient.hom.app ⟨_, hC⟩ =
        fdScalarActualPbc l E L ι h cU cT bE K) ∧
      ((integralDetailedTransport U l L).map
          (scalarPullbackCompleted l E L ι h.hom K.obj K.property.1 hF).hom ≫
        bL.actual_ambient.hom.app ⟨_, hS⟩ ≫
        (pbcActualCompletedPull h.hom (pbcIntegralDatum l L)).map
          ((integralDetailedTransport T l L).map
            (scalarCompletionIso l E L ι T K.obj K.property.1).inv) =
        (integralDetailedTransport U l L).map
          (scalarCompletionIso l E L ι U _ hF).inv ≫
        fdScalarActualPbc l E L ι h cU cT bE K) := by
  sorry

variable (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Raw rationalization of the completion-conjugated square, with finite-datum
components exactly inverse to localized integral b. Every object is an integral
representative and every map lies in the recorded tensor localization.
Source: trace-definition coefficient comparison, extracted proof step 5; Stacks 0941
(blueprint: lem-fd-scalar-roos-comparison-intertwining).

Proof: fdPullbackAugmentationCounitMatching supplies the normalized finite data:
their ambient and integral components are b inverse, with the actual quotient-unit
chain map and zero shifted coordinate. Raw localization sends f to f tensor 1,
preserves composition and inverses, and keeps the integral objects. The recorded
FdCoefficientComparison chi normalization makes its inverse beta precisely localized
chi inverse. The HEq clauses insert only its recorded finite-functor presentation
identities; they fix bEr and bLr to the same actual rationalized inverse finite data.
PbcScalarExtension identifies localized ordinary scalar extension with PBC rational scalar
functor, and its pullback comparison with the beta of pbcQbarPullFamily. Rationalize
fdScalarRoosIntegralIntertwining and insert these identifications to obtain the square.
The normalization clauses identify the inverse finite datum at both E and L with the
same localized integral b. This uses no Karoubi envelope. -/
theorem fdScalarRoosComparisonIntertwining
    (E₀ L₀ : Padic.FiniteCoefficientFields l Ω) (a : E₀ ≤ L₀)
    {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
    [dU : Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [iU : Fact (∀ x : U, IsUnit (l : U.presheaf.stalk x))]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))]
    (CU : FdCoefficientComparison l Ω U) (CT : FdCoefficientComparison l Ω T)
    (h : U ≅ T) (bE : FdCommonStrictTowerModels l (pbcFiniteField.{u} l Ω E₀) h)
    (bL : FdCommonStrictTowerModels l (pbcFiniteField.{u} l Ω L₀) h) :
    ∃ (dE : FdPullbackComparison l Ω CU CT h E₀)
      (dL : FdPullbackComparison l Ω CU CT h L₀),
      (∀ K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E₀) T,
        HEq (dE.integral.inv.app K).hom (bE.actual_ambient.hom.app K)) ∧
      (∀ K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω L₀) T,
        HEq (dL.integral.inv.app K).hom (bL.actual_ambient.hom.app K)) ∧
      (∀ K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E₀) T,
        HEq (dE.rational.inv.app
          ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E₀) T).obj K))
        ((pbcStageLocalization l Ω U E₀).map (bE.integral.hom.app K))) ∧
      (∀ K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω L₀) T,
        HEq (dL.rational.inv.app
          ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω L₀) T).obj K))
        ((pbcStageLocalization l Ω U L₀).map (bL.integral.hom.app K))) ∧
      ∀ K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E₀,
        ∃ (KE : sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω E₀) T)
          (KL : sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω L₀) T),
          HEq KE K ∧
          HEq KL (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T).T a).obj K) ∧
          ∃ (bEr : (CU.family.Φ E₀).obj
              ((rationalDerivedPullback l
                (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E₀) h.hom).obj K) ≅
            ((pbcQbarPullFamily l Ω h.hom).Φ E₀).obj ((CT.family.Φ E₀).obj K))
            (bLr : (CU.family.Φ L₀).obj
              ((rationalDerivedPullback l
                (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L₀) h.hom).obj
                  (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T).T a).obj K)) ≅
              ((pbcQbarPullFamily l Ω h.hom).Φ L₀).obj
                ((CT.family.Φ L₀).obj
                  (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T).T a).obj K))),
            HEq bEr.hom (dE.rational.inv.app KE) ∧
            HEq bLr.hom (dL.rational.inv.app KL) ∧
            (CU.family.Φ L₀).map
                (commonStagePullbackComparison l Ω h.hom ⟨E₀, K⟩ L₀ a).hom ≫
              bLr.hom ≫
              ((pbcQbarPullFamily l Ω h.hom).Φ L₀).map ((CT.family.β a).inv.app K) =
            (CU.family.β a).inv.app
                ((rationalDerivedPullback l
                  (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E₀) h.hom).obj K) ≫
              ((pbcScalarSystem l Ω U dU.out iU.out).T a).map bEr.hom ≫
              ((pbcQbarPullFamily l Ω h.hom).β a).hom.app ((CT.family.Φ E₀).obj K) := by
  sorry

end WeilConjectures
