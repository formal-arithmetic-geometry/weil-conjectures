/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.RationalSmoothPurityCanonical.RationalSmoothPurityCanonical
public import WeilConjectures.DeligneLaumon.FieldShriekCompositionQcqs
public import WeilConjectures.DeligneLaumon.FieldWeilShriekShiftData
public import WeilConjectures.SmoothPurity.IntegralSystemRealization.IntegralOperationShiftData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.Data.Nat.Prime.Infinite
import WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusCoefficientTwistsCanonical
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SchemeGeometricFrobenius
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import WeilConjectures.SixFunctors.Orientation.OrientationIntegralCoefficientTwists
import WeilConjectures.SmoothPurity.Integral.Twist.IntegralTwistBaseChange
import WeilConjectures.SmoothPurity.Supporting.SignedTwistReductionComparison
import WeilConjectures.SixFunctors.CanonicalTate.CanonicalTateScalarComparisons
import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
import all WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization.FlatSingleDerivedNormalization
import WeilConjectures.SixFunctors.Supporting.PositiveRootTensorProduct
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted

/-! # Rational purity: LineComparisons

Source: current blueprint, rational purity trace and coherence construction.
Existing declarations are retained in this compilation subdivision.
(blueprint: def-pur-rational-purity-line-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open WeilConjectures

attribute [-instance] integralOperationsSiteSmall
  integralReductionSiteEssentiallySmall
attribute [local irreducible] IntegralOnSlice.completion IntegralOnSlice.completionComparison
  IntegralOnSlice.completionUnit IntegralOnSlice.roosUnit IntegralAmbient.tensorTowerIso
  IntegralOnSlice.tower IntegralOnSlice.augmentation
  integralOperationsTensorTowerFunctor IntegralSystemRealization.tensorShifts

attribute [local irreducible] sfIntegralConstructible finiteTorConstructibleIntegral
  completedIntegralCoefficientSheafUnrestricted
  AlgebraicGeometry.Scheme.residueField
  PurCompactSupport.image sfIntrinsicModuleEquivalence ProEtale.comparisonUpperStar
  IntegralOnSlice.duality integralDerivedPullback integralCompletedTensor
  sfRationalScalarExtension HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Iso.trans Iso.prod Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors Functor.leftAdjoint
attribute [local instance 5000] integralTowerHasDerivedCategory scalarReductionTargetDerived
attribute [local irreducible] ScalarLocalization.composition ScalarLocalization.transportHom

namespace WeilConjectures.RationalPurityCoherence
open FrobeniusCoefficientTwists RationalSmoothPurityCanonical

attribute [local irreducible] integralSource integralTraceTranspose rationalSourceComparison
  smallModelIso rationalIso commonIso

section Lines
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The cartesian root-line map at any morphism, fixed on local scalar/root tensors.
Source: proof Step 4, geometric source comparisons
(blueprint: def-pur-rational-purity-line-comparisons).
Proof: pull back the Kummer root tower, extend coefficients using the specified
coefficient map, and take tensor powers. At zero use the coefficient unit. The
root line is locally free of rank one and its root projections are cartesian,
so these maps are invertible. Local pure tensors determine the maps uniquely. -/
theorem linePull_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃! τ : ∀ d : ℕ, (modulePull l E f).obj (positiveLine l E Y d) ≅
        positiveLine l E X d,
      ∀ (d : ℕ) (V : Y.ProEt)
        (a : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V))
        (x : Fin d → (purTwistZlOne Y l).obj.obj (op V)),
        (τ d).hom.val.app (op ((proEtaleBaseChange f).obj V))
            (moduleSection l E f (positiveLine l E Y d) V
              (generator l E Y (op V) a d x)) =
          generator l E X (op ((proEtaleBaseChange f).obj V))
            ((sfCompletedCoefficientMap l E f).hom.app (op V) a)
            d (fun i ↦ rootSection l f V (x i)) := by
  exact sfOrientationIntegralLineMaps_existsUnique l E f

/-- The uniquely root-normalized nonnegative line pullback.
Source: proof Step 4 (blueprint: def-pur-rational-purity-line-comparisons). -/
@[irreducible]
def linePull {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :=
  (linePull_existsUnique l E f).exists.choose d

section RootTensorProof
attribute [local instance 3000] completedIntegralCoefficientCommRingUnrestricted

attribute [local instance 3000] sectionModule

end RootTensorProof

attribute [local irreducible] Functor.mapIso ordinaryModel

/-- Rank-one root lines are flat-term K-flat representatives.
Source: proof Step 1, uniform finite-Tor domain
(blueprint: def-pur-rational-purity-line-comparisons).
Proof: trivialize the root line on a pro-etale cover. Each power is the coefficient
unit there, hence flat. A degree-zero flat complex is K-flat; these are exactly
the two clauses of integralOperationsGoodComplex. -/
theorem lineSingle_good (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)] (d : ℕ) :
    integralOperationsGoodComplex l E T
      ((CochainComplex.singleFunctor _ 0).obj (positiveLine l E T d)) := by
  let R := completedIntegralCommRingSheafUnrestricted l E T
  have hline := (@coefficientTwistLine_exact T R (purTwistIntegralModule T l E)
    ((pur_twist_sheaf_locally_free.{u, 0} T l E).2.2.1.2.2.1) (d : ℤ)).2
  exact ⟨SheafOfModules.FlatSingleDerivedNormalization.single_kFlat R
    (positiveLine l E T d) hline,
    SheafOfModules.FlatSingleDerivedNormalization.single_flat_terms R
      (positiveLine l E T d) hline⟩

/-- Pullback of a complete rank-one root line has the specified complete augmentation.
Source: proof Step 4, arbitrary geometric base change
(blueprint: def-pur-rational-purity-line-comparisons).
Proof: linePull identifies ordinary inverse image with the target complete line.
Under that identification the strict quotient augmentation is the completeness
unit, whose product projections and second cone component are prescribed. Thus
its localization is invertible, for arbitrary f, without smoothness of f. -/
theorem linePullAugmentation_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :
    IsIso (DerivedCategory.Q.map ((pullbackAugmentation l E f).app
      ((CochainComplex.singleFunctor _ 0).obj (positiveLine l E Y d)))) := by
  exact CanonicalTate.integralPullUnit_isIso l E f d

/-- Integral line pullback from the fixed strict augmentation and local root map.
Source: proof Step 4 (blueprint: def-pur-rational-purity-line-comparisons). -/
@[irreducible]
def integralLinePull {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :
    (integralDerivedPullback l E f).obj (sfIntegralTwistingObject l E Y (d : ℤ)) ≅
      sfIntegralTwistingObject l E X (d : ℤ) :=
  (integralDerivedPullback l E f).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (positiveLine l E Y d)) ≪≫
    (integralDerivedPullbackComparison l E f).app
      ⟨_, lineSingle_good l E Y d⟩ ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map ((pullbackAugmentation l E f).app
      ((CochainComplex.singleFunctor _ 0).obj (positiveLine l E Y d))))
        (linePullAugmentation_isIso l E f d)).symm ≪≫
    ((modulePull l E f).mapDerivedCategoryFactors.app _).symm ≪≫
    ((modulePull l E f).mapDerivedCategorySingleFunctor 0).app (positiveLine l E Y d) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (linePull l E f d)

/-- Rationalization of the specified integral line pullback.
Source: proof Steps 2 and 4 (blueprint: def-pur-rational-purity-line-comparisons). -/
@[irreducible]
def rationalLinePull {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :
    (rationalDerivedPullback l E f).obj (sfRationalTwistingCoefficient l E Y (d : ℤ)) ≅
      sfRationalTwistingCoefficient l E X (d : ℤ) :=
  eqToIso ((rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 _) ≪≫
    (sfRationalConstructibleLocalization l E X).mapIso
      (ObjectProperty.isoMk _ (integralLinePull l E f d))

attribute [local irreducible] rationalDerivedPullback

attribute [local irreducible] coefficientTotalTensor

attribute [local irreducible] rationalDerivedTensor

/-- Pullback of the shifted line, using the normalized pullback shift comparison.
Source: proof Step 4 (blueprint: def-pur-rational-purity-line-comparisons). -/
@[irreducible]
def rationalShiftedLinePull {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :
    (rationalDerivedPullback l E f).obj
        ((sfRationalTwistingCoefficient l E Y (d : ℤ))⟦2*(d : ℤ)⟧) ≅
      (sfRationalTwistingCoefficient l E X (d : ℤ))⟦2*(d : ℤ)⟧ :=
  ((rationalDerivedPullback l E f).commShiftIso (2*(d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2*(d : ℤ))).mapIso (rationalLinePull l E f d)

/-- Pullback around the given Cartesian square, from the two actual compositors.
Source: proof Step 4 (blueprint: def-pur-rational-purity-line-comparisons). -/
@[irreducible]
def rationalSquarePull {X' X Y' Y : Scheme.{u}}
    (a : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (b : Y' ⟶ Y)
    [∀ x : X', Invertible (l : X'.residueField x)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y', Invertible (l : Y'.residueField y)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (sq : IsPullback a f' f b) :
    rationalDerivedPullback l E f ⋙ rationalDerivedPullback l E a ≅
      rationalDerivedPullback l E b ⋙ rationalDerivedPullback l E f' :=
  (fieldRationalPullComp l E a f).symm ≪≫
    eqToIso (congrArg (fun h : X' ⟶ Y ↦ rationalDerivedPullback l E h) sq.w) ≪≫
    fieldRationalPullComp l E f' b

/-- The source base-change isomorphism for any Cartesian square. It uses no purity
map and imposes no smoothness on the horizontal base-change morphism.
Source: proof Step 4 (blueprint: def-pur-rational-purity-line-comparisons). -/
@[irreducible]
def rationalSourceBaseChange {X' X Y' Y : Scheme.{u}}
    (a : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (b : Y' ⟶ Y)
    [∀ x : X', Invertible (l : X'.residueField x)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y', Invertible (l : Y'.residueField y)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (sq : IsPullback a f' f b) (d : ℕ)
    (K : sfRationalConstructibleCategory l E Y) :
    (rationalDerivedPullback l E a).obj ((rationalSource l E f d).obj K) ≅
      (rationalSource l E f' d).obj ((rationalDerivedPullback l E b).obj K) :=
  canonicalRationalPullbackTensor l E a _ _ ≪≫
    (rationalDerivedTensor l E X').mapIso
      (Iso.prod (rationalShiftedLinePull l E a d)
        ((rationalSquarePull l E a f' f b sq).app K))

end Lines

end WeilConjectures.RationalPurityCoherence
