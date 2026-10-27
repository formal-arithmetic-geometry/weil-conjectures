module

public import Sheaf.Paper.PurityKappaStages
public import Sheaf.SixFunctors.KappaGeometricComparisons
public import Sheaf.SixFunctors.KappaMixedCoherence
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.Paper.BasicOperationsCoefficientReduction
public import Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality
public import Sheaf.Paper.FrobeniusCoefficientReductionCoherence
import Sheaf.SixFunctors.GeometricTwoIsoScalarPairing
import Sheaf.AlgebraicGeometry.FactorizedProEtalePullbackPasting
import Sheaf.SecSmoothPurity.StrictCoefficientComparisonCalculus
import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackIdentity
import Sheaf.Paper.CompletedOperationTowerSubstitution
import Sheaf.CategoryTheory.SemilinearScalarLocalization

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.SixFunctors.SchemeGeometricFrobenius
public import Sheaf.Paper.PurityTateDatum
public import Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback
public import Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.NormalizedPullbackCompositionTransport
import Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence
import Sheaf.Paper.SimultaneousIntegralPullbackComparisons
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.RamifiedPullbackTowerIdentification

/-!
# Coherence of the specified scheme--geometric Frobenius comparison

Source: the constituent-compatibility paragraph of the current blueprint,
`prop-pur-weil-equivariance-compatibilities.proof.md`, Returned Step 11
(blueprint: lem-pur-weil-kappa-coefficient-coherence).

Every map below is the recorded pro-etale pullback, coefficient comparison,
relative-Frobenius comparison, or its normalized strict-system transport.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped ChangeOfRings TensorProduct

namespace WeilConjectures.PurityFiniteSetting
/-- The specified finitecoefficient equations.
Source: Returned Step 11 (blueprint: lem-pur-weil-kappa-coefficient-coherence). -/
structure KappaFiniteCoefficientCoherence (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom] : Prop where
  finite_quotient : ∀ (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (N : proEtaleDerivedCategory (P.frobeniusFiber T₀).left P.Ring),
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber T₀).left N →
    (P.finiteReduction m hm hmn (P.frobeniusFiber T₀).left).map
        ((Purity.finiteReductionSchemeGeometricFrobeniusComparison P T₀).hom.app N) ≫
      (P.finiteReductionPullbackComparison m hm hmn (P.frobeniusGaloisMap T₀) N).hom =
    (P.finiteReductionPullbackComparison m hm hmn (P.frobeniusSchemeMap T₀) N).hom ≫
      (Purity.finiteReductionSchemeGeometricFrobeniusComparison
        (P.finiteReductionSetting m hm) T₀).hom.app
          ((P.finiteReduction m hm hmn (P.frobeniusFiber T₀).left).obj N)
  simultaneous : ∀ (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (T'₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T'₀.hom] [QuasiCompact T'₀.hom] [IsSeparated T'₀.hom]
    (u₀ : T'₀ ⟶ T₀) (N : proEtaleDerivedCategory (P.frobeniusFiber T₀).left P.Ring),
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber T₀).left N →
    (P.kappaRawReduction m hm hmn (P.frobeniusFiber T'₀).left).map
        ((proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap u₀)).map
          ((P.schemeGeometricFrobeniusComparison T₀).hom.app N)) ≫
      (P.kappaRawReduction m hm hmn (P.frobeniusFiber T'₀).left).map
        ((P.kappaGeometricG u₀).hom.app N) ≫
      (P.kappaRawReductionPullback m hm hmn (P.frobeniusGaloisMap T'₀)).hom.app
        ((proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap u₀)).obj N) ≫
      (proEtaleConstantRingDerivedPullback (P.finiteReductionSetting m hm).Ring
        (P.frobeniusGaloisMap T'₀)).map
          ((P.kappaRawReductionPullback m hm hmn (P.frobeniusMap u₀)).hom.app N) =
    (P.kappaRawReductionPullback m hm hmn (P.frobeniusMap u₀)).hom.app
        ((proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusSchemeMap T₀)).obj N) ≫
      (proEtaleConstantRingDerivedPullback (P.finiteReductionSetting m hm).Ring
        (P.frobeniusMap u₀)).map
          ((P.kappaRawReductionPullback m hm hmn (P.frobeniusSchemeMap T₀)).hom.app N) ≫
      ((P.finiteReductionSetting m hm).kappaGeometricH u₀).hom.app
        ((P.kappaRawReduction m hm hmn (P.frobeniusFiber T₀).left).obj N) ≫
      ((P.finiteReductionSetting m hm).schemeGeometricFrobeniusComparison T'₀).hom.app
        ((proEtaleConstantRingDerivedPullback (P.finiteReductionSetting m hm).Ring
          (P.frobeniusMap u₀)).obj
            ((P.kappaRawReduction m hm hmn (P.frobeniusFiber T₀).left).obj N))
  coefficient_identity : KappaFiniteCoefficientIdentity P T₀
  coefficient_successive : KappaFiniteCoefficientComposition P T₀

/-- The specified geometric equations.
Source: Returned Step 11 (blueprint: lem-pur-weil-kappa-coefficient-coherence). -/
structure KappaGeometricCoherence (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom] : Prop where
  geometric : ∀ (T'₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T'₀.hom] [QuasiCompact T'₀.hom] [IsSeparated T'₀.hom]
    (u₀ : T'₀ ⟶ T₀) (N : proEtaleDerivedCategory (P.frobeniusFiber T₀).left P.Ring),
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber T₀).left N →
    (proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap u₀)).map
        ((P.schemeGeometricFrobeniusComparison T₀).hom.app N) ≫
      (P.kappaGeometricG u₀).hom.app N =
    (P.kappaGeometricH u₀).hom.app N ≫
      (P.schemeGeometricFrobeniusComparison T'₀).hom.app
        ((proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap u₀)).obj N)
  geometric_identity : ∀ (b : Bool)
    (N : proEtaleDerivedCategory (P.frobeniusFiber T₀).left P.Ring),
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber T₀).left N →
    (P.kappaFiniteSquare (𝟙 T₀) b).hom.app N ≫
      (proEtaleConstantRingDerivedPullback P.Ring
        (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).map
          ((P.kappaIdentity T₀).hom.app N) =
    (P.kappaIdentity T₀).hom.app
      ((proEtaleConstantRingDerivedPullback P.Ring
        (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).obj N)
  geometric_successive : ∀ (T'₀ T''₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T'₀.hom] [QuasiCompact T'₀.hom] [IsSeparated T'₀.hom]
    [LocallyOfFiniteType T''₀.hom] [QuasiCompact T''₀.hom] [IsSeparated T''₀.hom]
    (u₀ : T'₀ ⟶ T₀) (v₀ : T''₀ ⟶ T'₀) (b : Bool)
    (N : proEtaleDerivedCategory (P.frobeniusFiber T₀).left P.Ring),
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber T₀).left N →
    (P.kappaPullbackComposition v₀ u₀).hom.app
        ((proEtaleConstantRingDerivedPullback P.Ring
          (if b then P.frobeniusGaloisMap T₀ else P.frobeniusSchemeMap T₀)).obj N) ≫
      (proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap v₀)).map
        ((P.kappaFiniteSquare u₀ b).hom.app N) ≫
      (P.kappaFiniteSquare v₀ b).hom.app
        ((proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap u₀)).obj N) =
    (P.kappaFiniteSquare (v₀ ≫ u₀) b).hom.app N ≫
      (proEtaleConstantRingDerivedPullback P.Ring
        (if b then P.frobeniusGaloisMap T''₀ else P.frobeniusSchemeMap T''₀)).map
          ((P.kappaPullbackComposition v₀ u₀).hom.app N)

/-- The specified integral equations.
Source: Returned Step 11 (blueprint: lem-pur-weil-kappa-coefficient-coherence). -/
structure KappaIntegralCoherence (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom] : Prop where
  integral_reduction : ∀ (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    (N : sfIntegralConstructibleCategory P.coefficients.l E (P.frobeniusFiber T₀).left),
    finiteTorConstructibleIntegral P.coefficients.l E (P.frobeniusFiber T₀).left N.obj →
    ∀ (Q : (integralOperationsGoodComplex P.coefficients.l E
      (P.frobeniusFiber T₀).left).FullSubcategory) (e : DerivedCategory.Q.obj Q.obj ≅ N.obj)
      (n : ℕ),
    (scalarReductionDerivedExtension P.coefficients.l E (P.frobeniusFiber T₀).left n).map
        ((P.kappaIntegral E T₀).hom.app N.obj) ≫
      (integralPullbackReductionIso P.coefficients.l E (P.frobeniusGaloisMap T₀) N Q e n).hom =
    (integralPullbackReductionIso P.coefficients.l E (P.frobeniusSchemeMap T₀) N Q e n).hom ≫
      (P.kappaFiniteFor (Padic.coefficientExtensionRing P.coefficients.l E (n + 1)) T₀).hom.app
        ((scalarReductionDerivedExtension P.coefficients.l E (P.frobeniusFiber T₀).left n).obj
          N.obj)
  integral_scalar : ∀ (E L : Type u) [Field E] [Field L]
    [Algebra (Padic P.coefficients.l) E] [Algebra (Padic P.coefficients.l) L]
    [FiniteDimensional (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) L] (ι : E →ₐ[Padic P.coefficients.l] L)
    (N : sfIntegralConstructibleCategory P.coefficients.l E (P.frobeniusFiber T₀).left),
    finiteTorConstructibleIntegral P.coefficients.l E (P.frobeniusFiber T₀).left N.obj →
    (sfConstructibleIntegralScalarExtension 0 P.coefficients.l
      (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) E L ι
        (P.frobeniusFiber T₀).left).map ((P.kappaConstructible E T₀).hom.app N) ≫
      (integralPullbackScalarComparison P.coefficients.l E L ι
        (P.frobeniusGaloisMap T₀) N).hom =
    (integralPullbackScalarComparison P.coefficients.l E L ι
      (P.frobeniusSchemeMap T₀) N).hom ≫
      (P.kappaConstructible L T₀).hom.app
        ((sfConstructibleIntegralScalarExtension 0 P.coefficients.l
          (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) E L ι
            (P.frobeniusFiber T₀).left).obj N)
  integral_geometric : ∀ (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    (T'₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T'₀.hom] [QuasiCompact T'₀.hom] [IsSeparated T'₀.hom]
    (u₀ : T'₀ ⟶ T₀)
    (N : sfIntegralConstructibleCategory P.coefficients.l E (P.frobeniusFiber T₀).left),
    finiteTorConstructibleIntegral P.coefficients.l E (P.frobeniusFiber T₀).left N.obj →
    (constructibleIntegralPullback P.coefficients.l E (P.frobeniusMap u₀)).map
        ((P.kappaConstructible E T₀).hom.app N) ≫
      (P.kappaIntegralSquare E u₀ true N).hom =
    (P.kappaIntegralSquare E u₀ false N).hom ≫
      (P.kappaConstructible E T'₀).hom.app
        ((constructibleIntegralPullback P.coefficients.l E (P.frobeniusMap u₀)).obj N)

/-- The specified strict equations.
Source: Returned Step 11 (blueprint: lem-pur-weil-kappa-coefficient-coherence). -/
structure KappaStrictCoherence (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom] : Prop where
  sequence_realization : ∀ (E : Type u) [Field E]
    [Algebra (Padic P.coefficients.l) E] [FiniteDimensional (Padic P.coefficients.l) E],
    P.KappaSequenceRealization E T₀
  strict_geometric : ∀ (E : Type u) [Field E]
    [Algebra (Padic P.coefficients.l) E] [FiniteDimensional (Padic P.coefficients.l) E]
    (T'₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T'₀.hom] [QuasiCompact T'₀.hom] [IsSeparated T'₀.hom]
    (u₀ : T'₀ ⟶ T₀)
    (N : sfIntegralConstructibleCategory P.coefficients.l E (P.frobeniusFiber T₀).left)
    (Q : CochainComplex
      (coefficientSequenceModules P.coefficients.l E (P.frobeniusFiber T₀).left) ℤ)
    (_e : DerivedCategory.Q.obj Q ≅
      ((P.kappaRealizationSystem.coefficient E).system
        (P.frobeniusFiber T₀).left).reduction.obj N.obj),
    finiteTorConstructibleIntegral P.coefficients.l E (P.frobeniusFiber T₀).left N.obj →
    ((integralComparisonSequencePullback P.coefficients.l E
      (P.frobeniusMap u₀)).mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex (P.kappaSequence E T₀) (.up ℤ)).hom.app Q) ≫
      (NatIso.mapHomologicalComplex (P.kappaSequenceSquare E u₀ true) (.up ℤ)).hom.app Q =
    (NatIso.mapHomologicalComplex (P.kappaSequenceSquare E u₀ false) (.up ℤ)).hom.app Q ≫
      (NatIso.mapHomologicalComplex (P.kappaSequence E T'₀) (.up ℤ)).hom.app
        (((integralComparisonSequencePullback P.coefficients.l E
          (P.frobeniusMap u₀)).mapHomologicalComplex (.up ℤ)).obj Q)
  strict_geometric_inverse : ∀ (E : Type u) [Field E]
    [Algebra (Padic P.coefficients.l) E] [FiniteDimensional (Padic P.coefficients.l) E]
    (T'₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T'₀.hom] [QuasiCompact T'₀.hom] [IsSeparated T'₀.hom]
    (u₀ : T'₀ ⟶ T₀)
    (N : sfIntegralConstructibleCategory P.coefficients.l E (P.frobeniusFiber T₀).left)
    (Q : CochainComplex
      (coefficientSequenceModules P.coefficients.l E (P.frobeniusFiber T₀).left) ℤ)
    (_e : DerivedCategory.Q.obj Q ≅
      ((P.kappaRealizationSystem.coefficient E).system
        (P.frobeniusFiber T₀).left).reduction.obj N.obj),
    finiteTorConstructibleIntegral P.coefficients.l E (P.frobeniusFiber T₀).left N.obj →
    ((integralComparisonSequencePullback P.coefficients.l E
      (P.frobeniusMap u₀)).mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex (P.kappaSequence E T₀) (.up ℤ)).inv.app Q) ≫
      (NatIso.mapHomologicalComplex (P.kappaSequenceSquare E u₀ false) (.up ℤ)).hom.app Q =
    (NatIso.mapHomologicalComplex (P.kappaSequenceSquare E u₀ true) (.up ℤ)).hom.app Q ≫
      (NatIso.mapHomologicalComplex (P.kappaSequence E T'₀) (.up ℤ)).inv.app
        (((integralComparisonSequencePullback P.coefficients.l E
          (P.frobeniusMap u₀)).mapHomologicalComplex (.up ℤ)).obj Q)
  strict_scalar : ∀ (E L : Type u) [Field E] [Field L]
    [Algebra (Padic P.coefficients.l) E] [Algebra (Padic P.coefficients.l) L]
    [FiniteDimensional (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) L] (ι : E →ₐ[Padic P.coefficients.l] L)
    (Q : (integralOperationsGoodComplex P.coefficients.l E
      (P.frobeniusFiber T₀).left).FullSubcategory),
    finiteTorConstructibleIntegral P.coefficients.l E (P.frobeniusFiber T₀).left
      ((integralOperationsGoodLocalization P.coefficients.l E
        (P.frobeniusFiber T₀).left).obj Q) →
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      ((integralOrdinaryScalar P.coefficients.l E L ι
        (P.frobeniusFiber T₀).left).mapHomologicalComplex (.up ℤ))).map
          ((P.kappaStrict E T₀).hom.app Q.obj) ≫
      (scalarPullbackTower P.coefficients.l E L ι (P.frobeniusGaloisMap T₀)).app Q.obj =
    (scalarPullbackTower P.coefficients.l E L ι (P.frobeniusSchemeMap T₀)).app Q.obj ≫
      (P.kappaStrict L T₀).hom.app
        (((integralOrdinaryScalar P.coefficients.l E L ι
          (P.frobeniusFiber T₀).left).mapHomologicalComplex (.up ℤ)).obj Q.obj)
  strict_scalar_inverse : ∀ (E L : Type u) [Field E] [Field L]
    [Algebra (Padic P.coefficients.l) E] [Algebra (Padic P.coefficients.l) L]
    [FiniteDimensional (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) L] (ι : E →ₐ[Padic P.coefficients.l] L)
    (Q : (integralOperationsGoodComplex P.coefficients.l E
      (P.frobeniusFiber T₀).left).FullSubcategory),
    finiteTorConstructibleIntegral P.coefficients.l E (P.frobeniusFiber T₀).left
      ((integralOperationsGoodLocalization P.coefficients.l E
        (P.frobeniusFiber T₀).left).obj Q) →
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      ((integralOrdinaryScalar P.coefficients.l E L ι
        (P.frobeniusFiber T₀).left).mapHomologicalComplex (.up ℤ))).map
          ((P.kappaStrict E T₀).inv.app Q.obj) ≫
      (scalarPullbackTower P.coefficients.l E L ι (P.frobeniusSchemeMap T₀)).app Q.obj =
    (scalarPullbackTower P.coefficients.l E L ι (P.frobeniusGaloisMap T₀)).app Q.obj ≫
      (P.kappaStrict L T₀).inv.app
        (((integralOrdinaryScalar P.coefficients.l E L ι
          (P.frobeniusFiber T₀).left).mapHomologicalComplex (.up ℤ)).obj Q.obj)
  strict_inverse_normalization : ∀ (E : Type u) [Field E]
    [Algebra (Padic P.coefficients.l) E] [FiniteDimensional (Padic P.coefficients.l) E]
    (Q : (integralOperationsGoodComplex P.coefficients.l E
      (P.frobeniusFiber T₀).left).FullSubcategory) (n : ℕ),
    finiteTorConstructibleIntegral P.coefficients.l E (P.frobeniusFiber T₀).left
      ((integralOperationsGoodLocalization P.coefficients.l E
        (P.frobeniusFiber T₀).left).obj Q) →
    ((P.kappaStrict E T₀).inv.app Q.obj).app (op n) =
      (P.kappaStrictLevel E T₀ n).inv.app Q.obj
  realization : ∀ (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    (Q : (integralOperationsGoodComplex P.coefficients.l E
      (P.frobeniusFiber T₀).left).FullSubcategory),
    finiteTorConstructibleIntegral P.coefficients.l E (P.frobeniusFiber T₀).left
      ((integralOperationsGoodLocalization P.coefficients.l E
        (P.frobeniusFiber T₀).left).obj Q) →
    (integralDerivedPullbackComparison P.coefficients.l E
        (P.frobeniusSchemeMap T₀)).hom.app Q ≫
      DerivedCategory.Q.map
        (integralOperationsRoosFunctor.map ((P.kappaStrict E T₀).hom.app Q.obj)) =
    (P.kappaIntegral E T₀).hom.app
        ((integralOperationsGoodLocalization P.coefficients.l E
          (P.frobeniusFiber T₀).left).obj Q) ≫
      (integralDerivedPullbackComparison P.coefficients.l E
        (P.frobeniusGaloisMap T₀)).hom.app Q

/-- The specified field equations.
Source: Returned Step 11 (blueprint: lem-pur-weil-kappa-coefficient-coherence). -/
structure KappaFieldCoherence (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom] : Prop where
  rational_scalar : ∀ (E L : Type u) [Field E] [Field L]
    [Algebra (Padic P.coefficients.l) E] [Algebra (Padic P.coefficients.l) L]
    [FiniteDimensional (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) L] (ι : E →ₐ[Padic P.coefficients.l] L)
    (N : sfRationalConstructibleCategory P.coefficients.l E (P.frobeniusFiber T₀).left),
    (sfRationalScalarExtension P.coefficients.l E (P.frobeniusFiber T₀).left 0
      (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) L ι).map
        ((P.kappaRational E T₀).hom.app N) ≫
      (rationalPullbackScalarComparison P.coefficients.l E L ι
        (P.frobeniusGaloisMap T₀)).hom.app N =
    (rationalPullbackScalarComparison P.coefficients.l E L ι
      (P.frobeniusSchemeMap T₀)).hom.app N ≫
      (P.kappaRational L T₀).hom.app
        ((sfRationalScalarExtension P.coefficients.l E (P.frobeniusFiber T₀).left 0
          (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) L ι).obj N)
  rationalization : ∀ (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    (N : sfRationalConstructibleCategory P.coefficients.l E (P.frobeniusFiber T₀).left),
    HEq ((P.kappaRational E T₀).hom.app N)
      ((sfRationalConstructibleLocalization P.coefficients.l E
        (P.frobeniusFiber T₀).left).map ((P.kappaConstructible E T₀).hom.app N.obj))
  common_stage : ∀
    (N : generalAlgebraicallyClosedConstructibleCategory
      P.coefficients.l P.coefficients.Qbar (P.frobeniusFiber T₀).left)
    (L : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar)
    (h : N.stage ≤ L),
    HEq ((P.kappaCommon T₀).hom.app N)
      (GeneralAlgebraicallyClosedCoefficients.ofHom
        (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar
          (P.frobeniusSchemeMap T₀) N)
        (commonStagePullbackObject P.coefficients.l P.coefficients.Qbar
          (P.frobeniusGaloisMap T₀) N) L h h
        ((commonStagePullbackComparison P.coefficients.l P.coefficients.Qbar
            (P.frobeniusSchemeMap T₀) N L h).hom ≫
          (P.kappaRational (AlgebraicallyClosedCoefficients.Coefficient.{u}
            P.coefficients.l P.coefficients.Qbar L) T₀).hom.app (N.toStage h) ≫
          (commonStagePullbackComparison P.coefficients.l P.coefficients.Qbar
            (P.frobeniusGaloisMap T₀) N L h).inv))
  rational_geometric : ∀ (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    (T'₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T'₀.hom] [QuasiCompact T'₀.hom] [IsSeparated T'₀.hom]
    (u₀ : T'₀ ⟶ T₀)
    (N : sfRationalConstructibleCategory P.coefficients.l E (P.frobeniusFiber T₀).left),
    (rationalDerivedPullback P.coefficients.l E (P.frobeniusMap u₀)).map
        ((P.kappaRational E T₀).hom.app N) ≫
      (P.kappaRationalSquare E u₀ true).hom.app N =
    (P.kappaRationalSquare E u₀ false).hom.app N ≫
      (P.kappaRational E T'₀).hom.app
        ((rationalDerivedPullback P.coefficients.l E (P.frobeniusMap u₀)).obj N)
  common_geometric : ∀ (T'₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T'₀.hom] [QuasiCompact T'₀.hom] [IsSeparated T'₀.hom]
    (u₀ : T'₀ ⟶ T₀)
    (N : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l
      P.coefficients.Qbar (P.frobeniusFiber T₀).left),
    (commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar
      (P.frobeniusMap u₀)).map ((P.kappaCommon T₀).hom.app N) ≫
        (P.kappaCommonSquare u₀ true).hom.app N =
    (P.kappaCommonSquare u₀ false).hom.app N ≫
      (P.kappaCommon T'₀).hom.app
        ((commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar
          (P.frobeniusMap u₀)).obj N)

/-- The specified mixed equations.
Source: Returned Step 11 (blueprint: lem-pur-weil-kappa-coefficient-coherence). -/
structure KappaMixedCoherence (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom] : Prop where
  integral_coefficient_laws : P.KappaIntegralCoefficientLaws T₀
  rational_coefficient_laws : P.KappaRationalCoefficientLaws T₀
  integral_simultaneous : ∀ (E L : Type u) [Field E] [Field L]
    [Algebra (Padic P.coefficients.l) E] [Algebra (Padic P.coefficients.l) L]
    [FiniteDimensional (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) L] (ι : E →ₐ[Padic P.coefficients.l] L)
    (T'₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T'₀.hom] [QuasiCompact T'₀.hom] [IsSeparated T'₀.hom]
    (u₀ : T'₀ ⟶ T₀)
    (N : sfIntegralConstructibleCategory P.coefficients.l E (P.frobeniusFiber T₀).left),
    finiteTorConstructibleIntegral P.coefficients.l E (P.frobeniusFiber T₀).left N.obj →
    P.KappaIntegralMixed E L ι u₀ N
  rational_simultaneous : ∀ (E L : Type u) [Field E] [Field L]
    [Algebra (Padic P.coefficients.l) E] [Algebra (Padic P.coefficients.l) L]
    [FiniteDimensional (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) L] (ι : E →ₐ[Padic P.coefficients.l] L)
    (T'₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T'₀.hom] [QuasiCompact T'₀.hom] [IsSeparated T'₀.hom]
    (u₀ : T'₀ ⟶ T₀)
    (N : sfRationalConstructibleCategory P.coefficients.l E (P.frobeniusFiber T₀).left),
    P.KappaRationalMixed E L ι u₀ N

/-- The specified equivariant equations.
Source: Returned Step 11 (blueprint: lem-pur-weil-kappa-coefficient-coherence). -/
structure KappaEquivariantCoherence (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom] : Prop where
  equivariant_precomposition : ∀
    (N M : proEtaleDerivedCategory (P.frobeniusFiber T₀).left P.Ring) (z : N ⟶ M)
    (φN : (proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusGaloisMap T₀)).obj N ⟶ N)
    (φM : (proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusGaloisMap T₀)).obj M ⟶ M),
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber T₀).left N →
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber T₀).left M →
    φN ≫ z = (proEtaleConstantRingDerivedPullback P.Ring
      (P.frobeniusGaloisMap T₀)).map z ≫ φM →
    (P.schemeGeometricFrobeniusComparison T₀).hom.app N ≫ φN ≫ z =
      (proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusSchemeMap T₀)).map z ≫
        (P.schemeGeometricFrobeniusComparison T₀).hom.app M ≫ φM
  finite_equivariant_transport : ∀ (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (N : proEtaleDerivedCategory (P.frobeniusFiber T₀).left P.Ring),
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber T₀).left N →
    ∀ φ : (P.finiteReductionPullback (P.frobeniusGaloisMap T₀)).obj N ⟶ N,
    (Purity.finiteReductionSchemeGeometricFrobeniusComparison
        (P.finiteReductionSetting m hm) T₀).hom.app
          ((P.finiteReduction m hm hmn (P.frobeniusFiber T₀).left).obj N) ≫
      (P.finiteReductionPullbackComparison m hm hmn (P.frobeniusGaloisMap T₀) N).inv ≫
      (P.finiteReduction m hm hmn (P.frobeniusFiber T₀).left).map φ =
    (P.finiteReductionPullbackComparison m hm hmn (P.frobeniusSchemeMap T₀) N).inv ≫
      (P.finiteReduction m hm hmn (P.frobeniusFiber T₀).left).map
        ((Purity.finiteReductionSchemeGeometricFrobeniusComparison P T₀).hom.app N ≫ φ)
  geometric_equivariant_transport : ∀ (T'₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T'₀.hom] [QuasiCompact T'₀.hom] [IsSeparated T'₀.hom]
    (u₀ : T'₀ ⟶ T₀) (N : proEtaleDerivedCategory (P.frobeniusFiber T₀).left P.Ring),
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber T₀).left N →
    ∀ φ : (proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusGaloisMap T₀)).obj N ⟶ N,
    (P.schemeGeometricFrobeniusComparison T'₀).hom.app
        ((proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap u₀)).obj N) ≫
      (P.kappaGeometricG u₀).inv.app N ≫
      (proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap u₀)).map φ =
    (P.kappaGeometricH u₀).inv.app N ≫
      (proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap u₀)).map
        ((P.schemeGeometricFrobeniusComparison T₀).hom.app N ≫ φ)
  tensor_restriction : ∀ (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (M : Sheaf (ProEt.topology (P.frobeniusFiber T₀).left)
      (ModuleCat.{u + 1} (ULift.{u + 1} P.Ring)))
    (V : (P.frobeniusFiber T₀).left.ProEt)
    (x : M.obj.obj (op ((proEtaleBaseChange (P.frobeniusAbsoluteMap T₀)).obj V)))
    (b : ULift.{u + 1} (P.finiteReductionSetting m hm).Ring),
    ((ModuleCat.extendScalars (RingHom.ulift (P.finiteReductionRingHom m hm hmn))).map
      (M.obj.map ((P.kappaRelativeFrobenius T₀).hom.app V).op))
        (b ⊗ₜ[ULift.{u + 1} P.Ring, RingHom.ulift (P.finiteReductionRingHom m hm hmn)] x) =
      b ⊗ₜ[ULift.{u + 1} P.Ring, RingHom.ulift (P.finiteReductionRingHom m hm hmn)]
        (M.obj.map ((P.kappaRelativeFrobenius T₀).hom.app V).op x)
  finite_pasting : ∀ (J : Type v) [Category.{v} J] [Finite J]
    [∀ i j : J, Finite (i ⟶ j)]
    (D : J ⥤ proEtaleDerivedCategory (P.frobeniusFiber T₀).left P.Ring),
    (∀ j : J, finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber T₀).left (D.obj j)) →
    ∀ (φ : D ⋙ proEtaleConstantRingDerivedPullback P.Ring
      (P.frobeniusGaloisMap T₀) ⟶ D) (i j : J) (f : i ⟶ j),
    (P.schemeGeometricFrobeniusComparison T₀).hom.app (D.obj i) ≫ φ.app i ≫ D.map f =
      (proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusSchemeMap T₀)).map (D.map f) ≫
        (P.schemeGeometricFrobeniusComparison T₀).hom.app (D.obj j) ≫ φ.app j

/-- All coefficient, geometric, strict-system and equivariant clauses, on their
actual finite-Tor domains and with their specified comparisons.
Source: Returned Step 11 (blueprint: lem-pur-weil-kappa-coefficient-coherence). -/
structure KappaCoefficientCoherence (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom] : Prop where
  finite : KappaFiniteCoefficientCoherence P T₀
  geometric : KappaGeometricCoherence P T₀
  integral : KappaIntegralCoherence P T₀
  strict : KappaStrictCoherence P T₀
  field : KappaFieldCoherence P T₀
  mixed : KappaMixedCoherence P T₀
  equivariant : KappaEquivariantCoherence.{u, v} P T₀

/-- Coherence of the specified κ at all coefficient stages and under arbitrary
geometric base change, including strict-system and equivariant-arrow compatibility.

Source: the constituent-compatibility assembly paragraph in the current blueprint,
`prop-pur-weil-equivariance-compatibilities.proof.md`, Returned Step 11
(blueprint: lem-pur-weil-kappa-coefficient-coherence).

Proof:
1. At finite coefficients use the relative-Frobenius site isomorphism of
   `lem-pur-frobenius-trivialization-pullback`. The geometric two-isomorphism
   scalar-pairing lemma sends each local tensor to the restriction of its module
   factor tensored with the unchanged scalar. Its inverse has the same formula.
   K-flat representative and mate normalization identifies these maps with the
   canonical coefficient/pullback comparisons. Paste with the specified
   compositor in κ = (τ G) d to obtain the finite coefficient square.
2. For u₀ use naturality of absolute Frobenius and the geometric-Galois map to
   form the two commuting squares. Factorized-pullback-square pasting, followed
   by the arbitrary-pullback trivialization equation, gives the geometric square.
   No Cartesianity or smoothness of u₀ is used.
3. Expand both mixed routes into these same d and τ factors. The scalar pairing
   and K-flat normalization identify them. Strict coefficient unit/composition
   equations, derived pullback associativity, and the normalized identity
   pullback give the displayed identity and successive-composition laws.
4. On one flat-term K-flat complex, take every actual positive quotient at once.
   Relative-Frobenius restriction and its inverse commute with each transition
   and differential. The finite equations are therefore equations of the whole
   strict towers. Apply the functorial Roos map, then the recorded good-complex
   localization comparisons. This is exactly `kappaIntegral` and its inverse;
   no faithfulness of individual derived evaluations is used.
5. For E → L use the normalized simultaneous quotient scalar maps and the
   specified λ, μ realization comparisons. The same generator calculation
   proves the strict scalar square and its inverse before Roos realization.
   In a ramified extension the scalar-extended quotient has index e*m; the
   same-index arrow is its transition to m, never an inverted isomorphism.
   Realization gives precisely `integralPullbackScalarComparison`.
6. Semilinear scalar localization preserves these maps, inverses, whiskerings
   and equations. The rational normalization gives `kappaRational`. Represent
   each finite common-stage diagram over one finite field and use scalar
   compatibility under enlargement; this gives `kappaCommon` and its actual
   common-stage square compositor, independently of representatives.
7. Naturality of each actual κ and z φ_N = φ_M G(z) give the displayed
   precomposition chain. The actual algebra equivalences defined in
   `PurityKappaStages` give its inverse, preservation of composition and all
   finite pastings at every stage. Substituting the coefficient or geometric
   square gives the displayed equivariant transport equations; the same
   substitution after strict realization and scalar localization gives them
   at the remaining stages. -/
theorem kappa_coefficient_coherence (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom] :
    KappaCoefficientCoherence.{u, v} P T₀ := by
  sorry

end WeilConjectures.PurityFiniteSetting
