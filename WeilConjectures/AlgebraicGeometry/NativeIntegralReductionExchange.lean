/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower
public import WeilConjectures.AlgebraicGeometry.SmoothPurityNormalizedEquivalence
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGamma
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerExceptionalBaseChange
public import WeilConjectures.AlgebraicGeometry.IntegralModels
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistsOfUniverses
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.SixFunctors.CondensedCompactSupportComposition
public import WeilConjectures.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import WeilConjectures.AlgebraicGeometry.IntegralTwistBaseChangeDefinitions
public import WeilConjectures.AlgebraicGeometry.TwistedPullbackReductionData
import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransportSupplement
import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalization
import WeilConjectures.AlgebraicGeometry.QuotientExpressionKFlatNormalization
import WeilConjectures.AlgebraicGeometry.CompletedLineDerived
import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons

/-! # Native integral reduction, Tate sources, and compact-support exchange

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-purity-bc/sk-prop-sp-purity-bc.proof.md, opening integral paragraph;
DAG comparison refinement, steps 1--8
(blueprint: lem-pur-native-integral-reduction-exchange).

All tower arrows live in the ordinary derived category of strict systems. A natural
index n denotes the positive exponent n+1. The section equivalence is the published
one and every coefficient transition is the actual quotient map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpNativeIntegralReduction

open IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The published completed signed line in native internal-module coordinates. Only
restriction along the normalized coefficient isomorphism and the section equivalence
are applied. Source: integral Tate paragraph
(blueprint: lem-pur-native-integral-reduction-exchange). -/
def nativeLine (s : Presentation l E) (T : Scheme.{u}) (m : ℕ) : Modules l E T :=
  (spIntegralModuleEquivalence l E T).inverse.obj
    ((completedRestriction l E s T).obj (integralTwistLine l E T (m : ℤ)))

/-- The canonical section of the native line corresponding to a completed-line section.
Source: actual coefficient identification, proof step 4
(blueprint: lem-pur-native-integral-reduction-exchange). -/
def lineSection (s : Presentation l E) (T : Scheme.{u}) (m : ℕ) (U : T.ProEtᵒᵖ)
    (x : (integralTwistLine l E T (m : ℤ)).val.obj U) :=
  ((spIntegralModuleEquivalence l E T).counitIso.inv.app
    ((completedRestriction l E s T).obj (integralTwistLine l E T (m : ℤ)))).val.app U x

/-- The native derived Tate tensor; its line is placed in degree zero.
Source: the displayed K(m) formula
(blueprint: lem-pur-native-integral-reduction-exchange). -/
def nativeTwist (s : Presentation l E) (T : Scheme.{u}) (m : ℕ) :
    Integral l E T ⥤ Integral l E T :=
  (tensor l E T).flip.obj
    (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (nativeLine l E s T m)))

/-- The actual finite Tate tensor on the whole strict system category.
Source: tower gamma source, with arbitrary nonnegative twist
(blueprint: lem-pur-native-integral-reduction-exchange). -/
def towerTwist (s : Presentation l E) (T : Scheme.{u})
    (w : SpChartAdmissibility.Twists l E T) (m : ℕ) :=
  Prod.sectL (SpTowerShriek.D l E T)
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (w.tower m))) ⋙
    SpTowerShriek.tensor l E s.base T

/-- The resolving complexes used by the recorded reduction counits.
Source: proof steps 2 and 5, flat-term K-flat resolutions
(blueprint: lem-pur-native-integral-reduction-exchange). -/
def Good (T : Scheme.{u}) (P : CochainComplex (Modules l E T) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T)
    (((spIntegralModuleEquivalence l E T).functor.mapHomologicalComplex (.up ℤ)).obj P) ∧
  ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
    (R := spIntegralSectionRing l E T)
    ((spIntegralModuleEquivalence l E T).functor.obj (P.X i))

set_option maxHeartbeats 0 in
-- Elaborating the section-normalized comparisons retains their full dependent types.
/-- The balanced scalar/tensor comparison on entire system complexes, fixed on every
local tensor summand and by the two localization counits. This is normalization data
for the comparison in this node, not another tensor construction.
Source: proof step 5 (blueprint: lem-pur-native-integral-reduction-exchange). -/
structure TensorReduction (s : Presentation l E) (T : Scheme.{u}) where
  comparison : MonoidalCategory.tensor (Integral l E T) ⋙ derivedReduction l E s T ≅
    (derivedReduction l E s T).prod (derivedReduction l E s T) ⋙
      SpTowerShriek.tensor l E s.base T
  chain : ∀ P Q : CochainComplex (Modules l E T) ℤ,
    ((ordinaryReduction l E s T).mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ≅
      (SemilinearSections.totalTensor.{u + 1, u, u + 1}
        (coefficientSequenceTopology (ProEt.topology T))
        (SemilinearSections.systemRing (ProEt.topology T)
          (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))).obj
        (((ordinaryReduction l E s T).mapHomologicalComplex (.up ℤ)).obj P,
          ((ordinaryReduction l E s T).mapHomologicalComplex (.up ℤ)).obj Q)
  pure : ∀ (P Q : CochainComplex (Modules l E T) ℤ)
    (p q k : ℤ) (hpq : p + q = k) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : (P.X p).X.obj.obj U) (y : (Q.X q).X.obj.obj U)
    (b : (SpTowerShriek.B l E T n).obj.obj U)
    (e : Evaluation l E s),
    ((chain P Q).hom.f k).val.app (op (n, U.unop))
      (((ordinaryReductionEvaluation l E s e T n).inv.app ((P ⊗ Q).X k)).val.app U
        (SheafOfModules.systemModelTmul ((s.towers T).scalar
          (spIntegralReductionScalar l E T (s.reduction T).coefficient n)).model
          ((spIntegralModuleEquivalence l E T).functor.obj ((P ⊗ Q).X k)) U b
          (((CochainComplex.ιMapBifunctor P Q (curriedTensor _) p q k hpq).hom.hom.app U)
            (InternalAbelianSheafModule.comparison_internalTmul (ProEt.topology T)
              (condensedRingObj (spIntegralCondensed l E) T) (P.X p) (Q.X q) U x y)))) =
    (SemilinearSections.tensorSummand.{u + 1, u, u + 1}
      (coefficientSequenceTopology (ProEt.topology T))
      (SemilinearSections.systemRing (ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))
      (((ordinaryReduction l E s T).mapHomologicalComplex (.up ℤ)).obj P)
      (((ordinaryReduction l E s T).mapHomologicalComplex (.up ℤ)).obj Q) p q k hpq).val.app
      (op (n, U.unop))
      (SemilinearSections.tensorSection.{u + 1, u, u + 1}
        (coefficientSequenceTopology (ProEt.topology T))
        (SemilinearSections.systemRing (ProEt.topology T)
          (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))
        ((ordinaryReduction l E s T).obj (P.X p))
        ((ordinaryReduction l E s T).obj (Q.X q)) (op (n, U.unop))
        (((ordinaryReductionEvaluation l E s e T n).inv.app (P.X p)).val.app U
          (SheafOfModules.systemModelTmul ((s.towers T).scalar
            (spIntegralReductionScalar l E T (s.reduction T).coefficient n)).model
            ((spIntegralModuleEquivalence l E T).functor.obj (P.X p)) U b x))
        (((ordinaryReductionEvaluation l E s e T n).inv.app (Q.X q)).val.app U
          (SheafOfModules.systemModelTmul ((s.towers T).scalar
            (spIntegralReductionScalar l E T (s.reduction T).coefficient n)).model
            ((spIntegralModuleEquivalence l E T).functor.obj (Q.X q)) U 1 y)))
  kflat : ∀ P : CochainComplex (Modules l E T) ℤ, Good l E T P →
    CochainComplex.IsKFlatIndependentCoefficients
      (R := SemilinearSections.systemRing (ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))
      (((ordinaryReduction l E s T).mapHomologicalComplex (.up ℤ)).obj P)
  representatives : ∀ (P Q : CochainComplex (Modules l E T) ℤ)
    (hP : Good l E T P) (hQ : Good l E T Q),
    (derivedReduction l E s T).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
        reductionComplexComparison l E s T (P ⊗ Q) ≫ DerivedCategory.Q.map (chain P Q).hom ≫
        ((s.base.calculus T).tensorModels.iso
          (coefficientSequenceTopology (ProEt.topology T))
          (SemilinearSections.systemRing (ProEt.topology T)
            (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))
          (s.base.calculus T).closed _ _ (kflat P hP) (kflat Q hQ)).hom =
      comparison.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (SpTowerShriek.tensor l E s.base T).map
          (Prod.mkHom (reductionComplexComparison l E s T P)
            (reductionComplexComparison l E s T Q))

set_option maxHeartbeats 0 in
-- Elaborating the section-normalized comparisons retains their full dependent types.
/-- The actual quotient normalization of the Tate lines, before and after localization.
The first-power formula uses the root-limit tensor and the literal ell-power quotient.
Source: proof steps 4--5 (blueprint: lem-pur-native-integral-reduction-exchange). -/
structure LineReduction (s : Presentation l E) (e : Evaluation l E s) (T : Scheme.{u}) where
  rootQuotient : ∀ n : ℕ,
    SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (purTwistZlProjection T l n) (purTwistZlModule T l) ≅ purTwistRootsModule T l n
  rootProjection : ∀ (n : ℕ) (U : T.ProEtᵒᵖ)
    (b : (purTwistFiniteRing T l n).obj.obj U) (z : (purTwistZlModule T l).val.obj U),
    (rootQuotient n).hom.val.app U
        (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
          (purTwistZlProjection T l n) (purTwistZlModule T l) U b z) =
      b • (@id ((purTwistRootsModule T l n).val.obj U)
        ((limit.π (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op n)).hom.app U z))
  twists : SpChartAdmissibility.Twists l E T
  quotient : ∀ (n : ℕ) (m : ℤ),
    SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
      (spIntegralEllProjection l E T n) (integralTwistLine l E T (m : ℤ)) ≅
        spEllTwistLine l E T n (m : ℤ)
  first : ∀ (n : ℕ) (U : T.ProEtᵒᵖ)
    (b : (SpTowerShriek.B l E T n).obj.obj U)
    (a : (purTwistIntegralConstant T l E).obj.obj U)
    (z : (purTwistZlModule T l).val.obj U),
    (quotient n 1).hom.val.app U
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        (spIntegralEllProjection l E T n) (integralTwistLine l E T (1 : ℤ)) U b
        (purTwistIntegralTensor T l E U a z)) =
      SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        (spEllTwistQuotient l E T n) (purTwistIntegralOne T l E) U b
        (purTwistIntegralTensor T l E U a z)
  normalized : ∀ n : ℕ,
    SheafOfModules.SignedLineComparisonNormalized.{u + 1, u, u + 1}
      (spIntegralEllProjection l E T n) (purTwistIntegralModule T l E)
      (spEllTwistOne l E T n) (quotient n 1) (quotient n)
  ordinary : ∀ m : ℕ,
    (ordinaryReduction l E s T).obj (nativeLine l E s T m) ≅ twists.tower m
  generators : ∀ (m n : ℕ) (U : T.ProEtᵒᵖ)
    (b : (SpTowerShriek.B l E T n).obj.obj U)
    (x : (integralTwistLine l E T (m : ℤ)).val.obj U),
    ((twists.level n m).hom.val.app U)
      (((SpTowerShriek.ev l E T n).map (ordinary m).hom).val.app U
        (((ordinaryReductionEvaluation l E s e T n).inv.app
          (nativeLine l E s T m)).val.app U
          (SheafOfModules.systemModelTmul ((s.towers T).scalar
            (spIntegralReductionScalar l E T (s.reduction T).coefficient n)).model
            ((spIntegralModuleEquivalence l E T).functor.obj (nativeLine l E s T m)) U b
            (lineSection l E s T m U x)))) =
      (quotient n (m : ℤ)).hom.val.app U
        (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
          (spIntegralEllProjection l E T n) (integralTwistLine l E T (m : ℤ)) U b x)
  derived : ∀ m : ℕ,
    (derivedReduction l E s T).obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
          (nativeLine l E s T m))) ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (twists.tower m))
  derived_normalized : ∀ m : ℕ,
    (derived m).hom = reductionComplexComparison l E s T
        ((CochainComplex.singleFunctor _ 0).obj (nativeLine l E s T m)) ≫
      DerivedCategory.Q.map
        (((ordinaryReduction l E s T).mapCochainComplexSingleFunctor 0).app
          (nativeLine l E s T m) ≪≫
          (CochainComplex.singleFunctor _ 0).mapIso (ordinary m)).hom

/-- The proper counit mate followed by the inverse open-unit mate, in sequence-site
coordinates. It is the canonical b_f before transporting back to the original towers.
Source: proof step 8 (blueprint: lem-pur-native-integral-reduction-exchange). -/
def supportReduction (s : Presentation l E) (q : ReductionGeometry l E s)
    (hq : OpenReductionIsIso l E s q)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (M : Integral l E X) :=
  letI := hq c.i M
  properReduction l E s q c.g ((openD l E c.i).obj M) ≫
    (SpTowerShriek.push l E s.base (s.operations.geometry c.g)).map
      (inv (openReductionInverse l E s q c.i M))

/-- The native proper/open exchange for a Cartesian compactification square.
Source: proof steps 6--8 (blueprint: lem-pur-native-integral-reduction-exchange). -/
def nativeExchange {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {v : Y' ⟶ Y} (sq : IsPullback a f' f v) (c : Compactification f)
    (o : openD l E c.i ⋙ pull l E (pullback.fst c.g v) ≅
      pull l E a ⋙ openD l E (c.ofIsPullback sq).i) (M : Integral l E X) :=
  (CondensedRing.condensedAmbientExchange (spIntegralCondensed l E)
    (CondensedRing.CompactSupportComposition.square (c.isPullback_g_ofIsPullback sq).flip)).app
      ((openD l E c.i).obj M) ≫
    (CondensedRing.moduleObjectDerivedPushforward (spIntegralCondensed l E)
      (c.ofIsPullback sq).g).map (o.hom.app M)

/-- The actual completion unit followed by limit of a_h, with the exact section and
sequence equivalences inserted. Source: proof step 3
(blueprint: lem-pur-native-integral-reduction-exchange). -/
def completedPullback (s : Presentation l E) (q : ReductionGeometry l E s)
    {S T : Scheme.{u}} (h : S ⟶ T) (L : Limit l E s S) (K : Integral l E T) :=
  ((redLimitAdjunction l E s S L).comp (realization l E s S).toAdjunction).unit.app
      ((pull l E h).obj K) ≫
    ((realization l E s S).inverse ⋙ lim l E s S L).map
      ((q.pullback h).derived.hom.app K)


/-- The underlying-line identification supplied by the section equivalence, with no
choice of trivialization. Source: proof step 1
(blueprint: lem-pur-native-integral-reduction-exchange). -/
def lineUnderlyingIso (s : Presentation l E) (T : Scheme.{u}) (m : ℕ) :
    (nativeLine l E s T m).X ≅ integralTwistUnderlying l E T (m : ℤ) :=
  (SheafOfModules.toSheaf _).mapIso
    ((spIntegralModuleEquivalence l E T).counitIso.app
      ((completedRestriction l E s T).obj (integralTwistLine l E T (m : ℤ))))

set_option maxHeartbeats 0 in
-- Elaborating the section-normalized comparisons retains their full dependent types.
/-- Root-normalized native line pullback, with its whole strict-tower counterpart.
The ordinary square fixes the tower map before localization.
Source: proof steps 2, 4 and 5
(blueprint: lem-pur-native-integral-reduction-exchange). -/
structure LinePullback (s : Presentation l E) (q : ReductionGeometry l E s)
    {S T : Scheme.{u}} (h : S ⟶ T)
    (wS : LineReduction l E s q.evaluation S) (wT : LineReduction l E s q.evaluation T) where
  coefficient : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (completedIntegralCommRingSheafUnrestricted l E T) ⟶
    completedIntegralCommRingSheafUnrestricted l E S
  coefficient_normalized : IsPurIntegralCoefficientComparison h l E coefficient
  roots : (proEtaleSheafInverseImage h Ab.{u + 1}).obj (purTwistZlOne T l) ⟶
    purTwistZlOne S l
  roots_normalized : IsPurRootLimitComparison h l roots
  signed : ∀ m : ℤ, (proEtaleSheafInverseImage h Ab.{u + 1}).obj
    (integralTwistUnderlying l E T m) ≅ integralTwistUnderlying l E S m
  signed_normalized : IsIntegralTwistInverseComparison l E h coefficient roots signed
  native : ∀ m : ℕ, (CondensedRing.upperStar (spIntegralCondensed l E) h).obj
      (nativeLine l E s T m) ≅ nativeLine l E s S m
  native_normalized : ∀ m : ℕ,
    HEq (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) h).homEquiv
      _ _) (native m).hom).hom
      ((lineUnderlyingIso l E s T m).hom ≫
        ((proEtaleSheafAdjunction h Ab.{u + 1}).homEquiv _ _) (signed (m : ℤ)).hom ≫
        (proEtaleSheafDirectImage h Ab.{u + 1}).map (lineUnderlyingIso l E s S m).inv)
  tower : ∀ m : ℕ, (s.operations.geometry h).pull.obj (wT.twists.tower m) ≅
    wS.twists.tower m
  tower_normalized : ∀ m : ℕ,
    (q.pullback h).ordinary.hom.app (nativeLine l E s T m) ≫
        (s.operations.geometry h).pull.map (wT.ordinary m).hom ≫ (tower m).hom =
      (ordinaryReduction l E s S).map (native m).hom ≫ (wS.ordinary m).hom

/-- The degree-zero native line pullback, computed using the published exact inverse
image and the root-normalized ordinary comparison. Source: proof steps 4--5
(blueprint: lem-pur-native-integral-reduction-exchange). -/
def LinePullback.nativeDerived (s : Presentation l E) (q : ReductionGeometry l E s)
    {S T : Scheme.{u}} (h : S ⟶ T)
    (wS : LineReduction l E s q.evaluation S) (wT : LineReduction l E s q.evaluation T)
    (a : LinePullback l E s q h wS wT) (m : ℕ) :=
  pullComplexComparison l E h
      ((CochainComplex.singleFunctor _ 0).obj (nativeLine l E s T m)) ≪≫
    DerivedCategory.Q.mapIso
      (((CondensedRing.upperStar (spIntegralCondensed l E) h).mapCochainComplexSingleFunctor
        0).app (nativeLine l E s T m) ≪≫
        (CochainComplex.singleFunctor _ 0).mapIso (a.native m))

/-- The degree-zero whole-tower line pullback, obtained by localizing the specified
ordinary strict-system map. Source: proof steps 4--5
(blueprint: lem-pur-native-integral-reduction-exchange). -/
def LinePullback.towerDerived (s : Presentation l E) (q : ReductionGeometry l E s)
    {S T : Scheme.{u}} (h : S ⟶ T)
    (wS : LineReduction l E s q.evaluation S) (wT : LineReduction l E s q.evaluation T)
    (a : LinePullback l E s q h wS wT) (m : ℕ) :=
  (s.operations.geometry h).pull.mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor _ 0).obj (wT.twists.tower m)) ≪≫
    DerivedCategory.Q.mapIso
      (((s.operations.geometry h).pull.mapCochainComplexSingleFunctor 0).app
        (wT.twists.tower m) ≪≫ (CochainComplex.singleFunctor _ 0).mapIso (a.tower m))

/-- The native pullback/Tate arrow is the specified derived monoidal pullback map
followed by pullback of the actual roots-of-unity line. Source: proof step 5
(blueprint: lem-pur-native-integral-reduction-exchange). -/
def nativeTwistPullback (s : Presentation l E) (q : ReductionGeometry l E s)
    {S T : Scheme.{u}} (h : S ⟶ T)
    (wS : LineReduction l E s q.evaluation S) (wT : LineReduction l E s q.evaluation T)
    (a : LinePullback l E s q h wS wT) (m : ℕ) (K : Integral l E T) :=
  ((CondensedRing.leftDerivedUpperStarTensorIso (spIntegralCondensed l E) h).hom.app K).app
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (nativeLine l E s T m))) ≫
    ((tensor l E S).obj ((pull l E h).obj K)).map
      (a.nativeDerived l E s q h wS wT m).hom

/-- The identical pullback/Tate word on entire strict systems, using the recorded
monoidal and root-tower comparisons. Source: proof step 5
(blueprint: lem-pur-native-integral-reduction-exchange). -/
def towerTwistPullback (s : Presentation l E) (q : ReductionGeometry l E s)
    {S T : Scheme.{u}} (h : S ⟶ T)
    (wS : LineReduction l E s q.evaluation S) (wT : LineReduction l E s q.evaluation T)
    (a : LinePullback l E s q h wS wT) (m : ℕ) (K : SpTowerShriek.D l E T) :=
  (s.operations.geometry h).tensorPullback.hom.app
      (K, DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (wT.twists.tower m))) ≫
    (SpTowerShriek.tensor l E s.base S).map
      (Prod.mkHom (𝟙 _) (a.towerDerived l E s q h wS wT m).hom)

set_option maxHeartbeats 0 in
-- Elaborating the section-normalized comparisons retains their full dependent types.
/-- Simultaneous normalizations and compatibilities of native reduction. These are
maps of whole strict towers; no equality is inferred from equality of evaluations.
Source: all clauses of the DAG comparison refinement, proof steps 1--8
(blueprint: lem-pur-native-integral-reduction-exchange). -/
structure Coherent (D : FiniteFieldDatum.{u}) (s : Presentation l E)
    (q : ReductionGeometry l E s) (hq : OpenReductionIsIso l E s q)
    (L : ∀ T : Scheme.{u}, Limit l E s T) where
  tensors : ∀ T : SepFinType D.k, TensorReduction l E s T.obj.left
  lines : ∀ T : SepFinType D.k, LineReduction l E s q.evaluation T.obj.left
  twist : ∀ (T : SepFinType D.k) (m : ℕ),
    nativeTwist l E s T.obj.left m ⋙ derivedReduction l E s T.obj.left ≅
      derivedReduction l E s T.obj.left ⋙ towerTwist l E s T.obj.left (lines T).twists m
  twist_normalized : ∀ (T : SepFinType D.k) (m : ℕ) (K : Integral l E T.obj.left),
    (twist T m).hom.app K =
      (tensors T).comparison.hom.app
          (K, DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
            (nativeLine l E s T.obj.left m))) ≫
        (SpTowerShriek.tensor l E s.base T.obj.left).map
          (Prod.mkHom (𝟙 _) ((lines T).derived m).hom)
  shift : ∀ (T : SepFinType D.k) (z : ℤ),
    shiftFunctor (Integral l E T.obj.left) z ⋙ derivedReduction l E s T.obj.left ≅
      derivedReduction l E s T.obj.left ⋙ shiftFunctor (SpTowerShriek.D l E T.obj.left) z
  shift_normalized : ∀ (T : SepFinType D.k) (z : ℤ)
    (P : CochainComplex (Modules l E T.obj.left) ℤ), Good l E T.obj.left P →
    (shift T z).hom.app (DerivedCategory.Q.obj P) ≫
        (shiftFunctor _ z).map (reductionComplexComparison l E s T.obj.left P) =
      (derivedReduction l E s T.obj.left).map
          ((DerivedCategory.Q.commShiftIso z).inv.app P) ≫
        reductionComplexComparison l E s T.obj.left (P⟦z⟧) ≫
        DerivedCategory.Q.map
          (((ordinaryReduction l E s T.obj.left).mapHomologicalComplex (.up ℤ)).commShiftIso
            z |>.hom.app P) ≫
        (DerivedCategory.Q.commShiftIso z).hom.app
          (((ordinaryReduction l E s T.obj.left).mapHomologicalComplex (.up ℤ)).obj P)
  linePullback : ∀ {S T : SepFinType D.k} (h : S ⟶ T),
    LinePullback l E s q h.hom.left (lines S) (lines T)
  line_pullback_reduction : ∀ {S T : SepFinType D.k} (h : S ⟶ T) (m : ℕ),
    (derivedReduction l E s S.obj.left).map
        ((linePullback h).nativeDerived l E s q h.hom.left (lines S) (lines T) m).hom ≫
        ((lines S).derived m).hom =
      (q.pullback h.hom.left).derived.hom.app
          (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
            (nativeLine l E s T.obj.left m))) ≫
        (SpTowerShriek.pull l E s.base (s.operations.geometry h.hom.left)).map
          ((lines T).derived m).hom ≫
        ((linePullback h).towerDerived l E s q h.hom.left (lines S) (lines T) m).hom
  twist_pullback : ∀ {S T : SepFinType D.k} (h : S ⟶ T) (m : ℕ)
    (K : Constructible l E T.obj.left),
    (derivedReduction l E s S.obj.left).map
        (nativeTwistPullback l E s q h.hom.left (lines S) (lines T)
          (linePullback h) m K.obj) ≫
        (twist S m).hom.app ((pull l E h.hom.left).obj K.obj) ≫
        (towerTwist l E s S.obj.left (lines S).twists m).map
          ((q.pullback h.hom.left).derived.hom.app K.obj) =
      (q.pullback h.hom.left).derived.hom.app
          ((nativeTwist l E s T.obj.left m).obj K.obj) ≫
        (SpTowerShriek.pull l E s.base (s.operations.geometry h.hom.left)).map
          ((twist T m).hom.app K.obj) ≫
        towerTwistPullback l E s q h.hom.left (lines S) (lines T)
          (linePullback h) m ((derivedReduction l E s T.obj.left).obj K.obj)
  composition : ∀ {S T U : SepFinType D.k} (h : S ⟶ T) (g : T ⟶ U)
    (K : Constructible l E U.obj.left),
    (derivedReduction l E s S.obj.left).map
        ((CondensedRing.leftDerivedUpperStarComp (spIntegralCondensed l E)
          h.hom.left g.hom.left).hom.app K.obj) ≫
        (q.pullback h.hom.left).derived.hom.app ((pull l E g.hom.left).obj K.obj) ≫
        (SpTowerShriek.pull l E s.base (s.operations.geometry h.hom.left)).map
          ((q.pullback g.hom.left).derived.hom.app K.obj) ≫
        (s.operations.comp h.hom.left g.hom.left).hom.app
          ((derivedReduction l E s U.obj.left).obj K.obj) =
      (q.pullback (h.hom.left ≫ g.hom.left)).derived.hom.app K.obj
  completion : ∀ {S T : SepFinType D.k} (h : S ⟶ T) (K : Constructible l E T.obj.left),
    constantModelBoundedConstructible (spIntegralCondensed l E) S.obj.left
        ((pull l E h.hom.left).obj K.obj) ∧
      spNormalizedConstructibleTorTowers l E S.obj.left (s.towers S.obj.left)
        ((realization l E s S.obj.left).inverse.obj
          ((SpTowerShriek.pull l E s.base (s.operations.geometry h.hom.left)).obj
            ((derivedReduction l E s T.obj.left).obj K.obj))) ∧
      IsIso (completedPullback l E s q h.hom.left (L S.obj.left) K.obj)
  cofinal : ∀ T : SepFinType D.k,
    SpTwistedPullback.CofinalModel l E s.base T.obj.left
  cofinal_reduction : ∀ T : SepFinType D.k,
    ∃ A : IntegralStrictReductionModel l E T.obj.left,
      Nonempty (SpTwistedPullback.CofinalReduction l E s.base T.obj.left
        (s.towers T.obj.left) (s.reduction T.obj.left) A (cofinal T))
  cofinal_pullback : ∀ {S T : SepFinType D.k} (h : S ⟶ T),
    SpTwistedPullback.CofinalGeometry l E s.base h.hom.left
      (s.operations.geometry h.hom.left) (cofinal S) (cofinal T)
  compactSupport : ∀ {X Y : SepFinType D.k} (f : X ⟶ Y) (d : ℕ)
    [SmoothOfRelativeDimension d f.hom.left] (c : Compactification f.hom.left),
    ∃ b : (constantModelBoundedConstructible (spIntegralCondensed l E) X.obj.left).ι ⋙
        shriek l E c ⋙ derivedReduction l E s Y.obj.left ≅
      (constantModelBoundedConstructible (spIntegralCondensed l E) X.obj.left).ι ⋙
        derivedReduction l E s X.obj.left ⋙ SpTowerShriek.F l E s.base s.operations c,
      ∀ M : Constructible l E X.obj.left,
        b.hom.app M = supportReduction l E s q hq c M.obj
  exchange : ∀ {X Y X' Y' : SepFinType D.k}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X' ⟶ X) (v : Y' ⟶ Y)
    (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
    (d : ℕ) [SmoothOfRelativeDimension d f.hom.left] (c : Compactification f.hom.left),
    ∃ o : openD l E c.i ⋙ pull l E (pullback.fst c.g v.hom.left) ≅
        pull l E a.hom.left ⋙ openD l E (c.ofIsPullback sq).i,
      o.inv = CondensedRing.CompactSupportComposition.openExchange
          (spIntegralCondensed l E) sq c ∧
      ∀ M : Constructible l E X.obj.left,
        IsIso (nativeExchange l E sq c o M.obj) ∧
        IsIso ((SpTowerShriek.exchange l E s.base s.operations s.exchange sq c).app
          ((derivedReduction l E s X.obj.left).obj M.obj)) ∧
        (derivedReduction l E s Y'.obj.left).map (nativeExchange l E sq c o M.obj) ≫
            supportReduction l E s q hq (c.ofIsPullback sq)
              ((pull l E a.hom.left).obj M.obj) ≫
            (SpTowerShriek.F l E s.base s.operations (c.ofIsPullback sq)).map
              ((q.pullback a.hom.left).derived.hom.app M.obj) =
          (q.pullback v.hom.left).derived.hom.app ((shriek l E c).obj M.obj) ≫
            (SpTowerShriek.pull l E s.base (s.operations.geometry v.hom.left)).map
              (supportReduction l E s q hq c M.obj) ≫
            (SpTowerShriek.exchange l E s.base s.operations s.exchange sq c).app
              ((derivedReduction l E s X.obj.left).obj M.obj)

/-- The displayed twisted and shifted pullback comparison. Every factor is a component
of a specified natural isomorphism, so this formula retains naturality in K.
Source: the displayed r_S(h^*K(m)[s]) formula
(blueprint: lem-pur-native-integral-reduction-exchange). -/
def Coherent.twistedComparison (D : FiniteFieldDatum.{u}) (s : Presentation l E)
    (q : ReductionGeometry l E s) (hq : OpenReductionIsIso l E s q)
    (L : ∀ T : Scheme.{u}, Limit l E s T) (c : Coherent l E D s q hq L)
    {S T : SepFinType D.k} (h : S ⟶ T) (m : ℕ) (z : ℤ)
    (K : Integral l E T.obj.left) :
    (derivedReduction l E s S.obj.left).obj
        (((nativeTwist l E s S.obj.left m).obj ((pull l E h.hom.left).obj K))⟦z⟧) ≅
      ((towerTwist l E s S.obj.left (c.lines S).twists m).obj
        ((SpTowerShriek.pull l E s.base (s.operations.geometry h.hom.left)).obj
          ((derivedReduction l E s T.obj.left).obj K)))⟦z⟧ :=
  (c.shift S z).app
      ((nativeTwist l E s S.obj.left m).obj ((pull l E h.hom.left).obj K)) ≪≫
    (shiftFunctor _ z).mapIso
      ((c.twist S m).app ((pull l E h.hom.left).obj K) ≪≫
        (towerTwist l E s S.obj.left (c.lines S).twists m).mapIso
          ((q.pullback h.hom.left).derived.app K))

/-- Native integral reduction preserves geometric inverse image, all nonnegative Tate
sources and integer shifts, the normalized completion unit, pullback composition,
and the specified compact-support exchange for every smooth relative dimension.
Source: latest blueprint, sk-prop-sp-purity-bc proof, opening integral paragraph;
the DAG comparison refinement (blueprint: lem-pur-native-integral-reduction-exchange).

Proof:
1. Apply internal_module_operations_transport and internal_scalar_pullback_normalization,
with the finite section-action realization. These preserve the proper/open adjunctions.
2. Resolve by a flat-term K-flat complex and reduce it as a single strict quotient system.
The balanced pullback map commutes with every quotient transition. Localizing gives
q.pullback. Tensor generators and the specified monoidal compositors prove composition.
3. The integral-model criterion preserves native constructibility under pullback and
makes its completion unit invertible. Apply the normalized reduction/limit equivalence.
4. Trivialize the compatible root tower locally. The map z tensor b to pr_n(z)b is the
identity in these coordinates; the actual quotient projections make the local maps agree.
Thus the ordinary maps assemble as a strict-system isomorphism before localization.
5. Tensor m copies (the unit for m=0) with the resolving complex. Balanced tensor
reassociation fixes TensorReduction on each summand and its computing counits. The root
pullback formulas identify the native and whole-tower twist arrows. Shift the complexes
with the standard differential signs. Cofinal uniformizer restriction uses s.base.ideals.
6. Take proper-adjunction mates of the commutative pullback/scalar cube. Mate-pasting
identifies both whole-system pastings using the actual units and counits.
7. Repeat with the open adjunction, whose inverse exchange is the transpose of the open
unit. Inverting this open comparison gives the strict open scalar/exchange square.
8. Expand nativeExchange and SpTowerShriek.exchange into their proper/open words.
Paste steps 6 and 7, using naturality of the proper reduction mate. Integral direct image
makes supportReduction invertible on the constructible domain. This proves the displayed
whole-tower equation. No purity, exceptional base-change or trace identity is used. -/
theorem native_integral_reduction_exchange
    (D : FiniteFieldDatum.{u}) (hne : l ≠ D.p) (s : Presentation l E) :
    ∃ (q : ReductionGeometry l E s) (hq : OpenReductionIsIso l E s q)
      (L : ∀ T : Scheme.{u}, Limit l E s T), Nonempty (Coherent l E D s q hq L) := by
  sorry

end AlgebraicGeometry.ProEtale.SpNativeIntegralReduction
