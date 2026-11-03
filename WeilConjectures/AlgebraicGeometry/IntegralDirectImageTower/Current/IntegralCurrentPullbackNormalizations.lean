/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormulaCore
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerCurrentStatement
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek

/-! # Ordinary and derived normalization predicates for reduction and pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The ordinary comparison type, before localizing complexes.
Source: blueprint direct-image proof (2)--(3).
(blueprint: def-sp-current-pullback-normalizations). -/
abbrev OrdinaryPullComparison (s : Coefficients l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
CondensedRing.upperStar (spIntegralCondensed l E) f ⋙
      ordinaryReduction l E s X ≅
    ordinaryReduction l E s Y ⋙ (s.operations.geometry f).pull

/-- The tensor-generator equation that fixes an ordinary comparison.
Source: blueprint direct-image proof (2)--(3).
(blueprint: def-sp-current-pullback-normalizations). -/
def OrdinaryPullNormalized (s : Coefficients l E) (e : Evaluation l E s)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (ordinary : OrdinaryPullComparison l E s f) : Prop :=
  ∀ (M : Modules l E Y) (n : ℕ) (V : Y.ProEt)
    (x : ((spIntegralModuleEquivalence l E Y).functor.obj M).val.obj (op V)),
    ((ordinaryPullLevelMap l E s e f ordinary M n).val.app
      (op ((Scheme.proEtaleBaseChange f).obj V)))
      (systemModelTmul ((s.towers X).scalar
        (spIntegralReductionScalar l E X (s.reduction X).coefficient n)).model
        ((spIntegralModuleEquivalence l E X).functor.obj
          ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M))
        (op ((Scheme.proEtaleBaseChange f).obj V)) 1
        (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
          M).hom.hom.app (op V) x)) =
      (((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).unit.app
        ((ordinaryLevel l E s Y n).obj M)).val.app (op V))
        (systemModelTmul ((s.towers Y).scalar
          (spIntegralReductionScalar l E Y (s.reduction Y).coefficient n)).model
          ((spIntegralModuleEquivalence l E Y).functor.obj M) (op V) 1 x)

/-- The derived comparison type on the ordinary unbounded localizations.
Source: blueprint direct-image proof (2)--(3).
(blueprint: def-sp-current-pullback-normalizations). -/
abbrev DerivedPullComparison (s : Coefficients l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
    pull l E f ⋙ derivedReduction l E s X ≅
    derivedReduction l E s Y ⋙ SpTowerShriek.pull l E s.base (s.operations.geometry f)

/-- The fixed computing-counit equation on flat-term K-flat representatives.
Source: blueprint direct-image proof (2)--(3).
(blueprint: def-sp-current-pullback-normalizations). -/
def DerivedPullNormalized (s : Coefficients l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (ordinary : OrdinaryPullComparison l E s f)
    (derived : DerivedPullComparison l E s f) : Prop :=
  ∀ P : CochainComplex (Modules l E Y) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E Y)
      (((spIntegralModuleEquivalence l E Y).functor.mapHomologicalComplex (.up ℤ)).obj P) →
    (∀ i : ℤ, IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology Y) (R := spIntegralSectionRing l E Y)
      ((spIntegralModuleEquivalence l E Y).functor.obj (P.X i))) →
    derived.hom.app (DerivedCategory.Q.obj P) ≫
      (SpTowerShriek.pull l E s.base (s.operations.geometry f)).map
        (reductionComplexComparison l E s Y P) ≫
      (s.operations.geometry f).pull.mapDerivedCategoryFactors.hom.app
        (((ordinaryReduction l E s Y).mapHomologicalComplex (.up ℤ)).obj P) =
    (derivedReduction l E s X).map ((pullComplexComparison l E f P).hom) ≫
      reductionComplexComparison l E s X
        (((CondensedRing.upperStar (spIntegralCondensed l E) f).mapHomologicalComplex
          (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current
