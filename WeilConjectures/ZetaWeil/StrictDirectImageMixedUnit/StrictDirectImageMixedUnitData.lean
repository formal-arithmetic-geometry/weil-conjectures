/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.SfStrictDirectImageScalar.SfStrictDirectImageScalarComparison
public import WeilConjectures.SmoothPurity.Supporting.MixedReductionUnit
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionModel
public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageRestrictionOfScalars
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.SmoothPurity.Sf.SfIntegralDirectImageConstructible
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-! # Data for the mixed tensor unit of strict direct image

Source: Stacks Tag 0B56, equation-projection-formula-map, and the six-step system
mate calculation in the DAG (blueprint: def-weil-strict-mixed-unit-data).

## Main declarations

* `FiniteLaws`: the finite mixed-unit equation and its unique linear lift.
* `CoherentLaws`: the same equation on normalized whole quotient systems.
The theorem is in `Sheaf.Paper.StrictDirectImageMixedUnit`.

The index n means exponent n+1. All equalities of systems below are equalities
in the ordinary derived category of modules on the ringed sequence site.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived

universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.StrictDirectImageMixedUnit
open SfStrictDirectImageScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual ordinary inverse limit of the restricted quotient system.
Source: Stacks 0941 (blueprint: lem-weil-strict-direct-image-mixed-unit). -/
def ordinaryLimit (W : Scheme.{u}) :
    coefficientSequenceModules l E W ⥤ scalarReductionSource l E W :=
  coefficientSequenceRestriction l E W ⋙ lim

/-- Additivity inherited from exact restriction and the existing additive limit.
Source: Stacks 0941 (blueprint: lem-weil-strict-direct-image-mixed-unit). -/
instance ordinaryLimitAdditive (W : Scheme.{u}) : (ordinaryLimit l E W).Additive :=
  inferInstanceAs (coefficientSequenceRestriction l E W ⋙
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)).Additive

/-- The canonical comparison into total limit, using the exact-restriction factors
and the right-derived inverse-limit unit, on the entire complex.
Source: Stacks 0A07, 0941 (blueprint: lem-weil-strict-direct-image-mixed-unit). -/
def totalUnit (W : Scheme.{u}) (P : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    DerivedCategory.Q.obj (((ordinaryLimit l E W).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj P) :=
  (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W).rightDerivedFunctorUnitQ
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj P) ≫
    (coefficientConstantTowerLimit l E W).map
      ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app P)

set_option genSizeOf false in
set_option genInjectivity false in
/-- The normalized comparison of the two direct-image/limit factorizations.
Its ordinary comparison is fixed on projected sections, and the derived comparison
is fixed on whole complexes by the universal derived units. In particular it is
not specified by a family of equalities after derived evaluation.
Source: Stacks 0D6E, 0A07 (blueprint: lem-weil-strict-direct-image-mixed-unit). -/
structure LimitComparison {X Y : Scheme.{u}} (f : X ⟶ Y) where
  ordinary : integralComparisonSequenceDirectImage l E f ⋙ ordinaryLimit l E Y ≅
    ordinaryLimit l E X ⋙ sfCompletedModuleDirectImage l E f
  projections : ∀ (M : coefficientSequenceModules l E X) (n : ℕ) (V : Y.ProEtᵒᵖ)
    (x : ((ordinaryLimit l E Y).obj
      ((integralComparisonSequenceDirectImage l E f).obj M)).val.obj V),
    HEq (((limit.π ((coefficientSequenceRestriction l E X).obj M) (op n)).val.app
        ((proEtaleBaseChange f).op.obj V)) (((ordinary.hom.app M).val.app V) x))
      (((limit.π ((coefficientSequenceRestriction l E Y).obj
        ((integralComparisonSequenceDirectImage l E f).obj M)) (op n)).val.app V) x)
  derived : FrobeniusExchange.systemDirect l E f ⋙ coefficientSequenceLimit l E Y ≅
    coefficientSequenceLimit l E X ⋙ sfCompletedDerivedDirectImage l E f
  normalization : ∀ P : CochainComplex (coefficientSequenceModules l E X) ℤ,
    totalUnit l E Y
        (((integralComparisonSequenceDirectImage l E f).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (coefficientSequenceLimit l E Y).map
        ((integralComparisonSequenceDirectImage l E f).rightDerivedFunctorUnitQ P) ≫
      derived.hom.app (DerivedCategory.Q.obj P) =
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P) ≫
      (sfCompletedModuleDirectImage l E f).rightDerivedFunctorUnitQ
        (((ordinaryLimit l E X).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (sfCompletedDerivedDirectImage l E f).map (totalUnit l E X P)

/-- Reduction of the specified strict image: transpose its normalized reconstruction
through the actual reduction/total-limit adjunction. This defines a whole-system map.
Source: Stacks 07A6; DAG proof Step 2
(blueprint: lem-weil-strict-direct-image-mixed-unit). -/
def reductionMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SY : CoefficientDerivedSystemCalculus l E Y) (C : LimitComparison l E f)
    (I : IntegralModel l E f) (K : sfIntegralConstructibleCategory l E X) :
    SY.reduction.obj (I.image.obj K).obj ⟶
      (FrobeniusExchange.systemDirect l E f).obj (SX.reduction.obj K.obj) :=
  SY.reduction.map (I.reconstruction.inv.app K ≫
      (sfCompletedDerivedDirectImage l E f).map (SX.adjunction.unit.app K.obj) ≫
      C.derived.inv.app (SX.reduction.obj K.obj)) ≫
    SY.adjunction.counit.app
      ((FrobeniusExchange.systemDirect l E f).obj (SX.reduction.obj K.obj))

/-- The finite geometric reduction mate, transported through strict reconstruction.
Source: Stacks 07A6; DAG proof Step 2
(blueprint: lem-weil-strict-direct-image-mixed-unit). -/
def finiteReduction {X Y : Scheme.{u}} (f : X ⟶ Y) (I : IntegralModel l E f)
    (K : sfIntegralConstructibleCategory l E X) (n : ℕ) :
    (scalarReductionDerivedExtension l E Y n).obj (I.image.obj K).obj ⟶
      sfFiniteDerivedDirectImage l E f K.obj n :=
  (scalarReductionDerivedExtension l E Y n).map (I.reconstruction.inv.app K) ≫
    ((derivedScalarExtensionRestrictionAdjunction l E Y n).choose.homEquiv _ _).symm
      ((sfCompletedDerivedDirectImage l E f).map
        ((derivedScalarExtensionRestrictionAdjunction l E X n).choose.unit.app K.obj) ≫
        (sfDerivedRestrictionComparison l E f n).hom.app
          ((scalarReductionDerivedExtension l E X n).obj K.obj))

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Exact restriction along the actual map of quotient-ring systems.
Source: Stacks 03CZ, 0941 (blueprint: lem-weil-strict-direct-image-mixed-unit). -/
abbrev restriction (W : Scheme.{u}) :=
  SemilinearSections.resD.{u+1, u, u+1}
    (SemilinearSections.systemMap.{u+1, u, u+1} (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
      (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
      (integralScalarQuotientSheafMap l E L ι W)
      (coefficientExtensionQuotient_naturality l E L ι W))

/-- The intrinsic finite restriction comparison with the prescribed K-injective
normalization; the dependency record refers to precisely this theorem.
Source: Stacks 0D6E (blueprint: lem-weil-strict-direct-image-mixed-unit). -/
def finiteRestriction {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
  letI := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.le_add_left 1 n)
  (proEtaleDerivedDirectImage_restrictScalars f
    (integralScalarQuotientMap l E L ι n)).choose

/-- Restriction on the actual abelian coefficient-system categories.
Source: Stacks 03CZ, 0941 (blueprint: lem-weil-strict-direct-image-mixed-unit). -/
abbrev ordinaryRestriction (W : Scheme.{u}) :=
  SemilinearSections.res.{u+1, u, u+1}
    (SemilinearSections.systemMap.{u+1, u, u+1} (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
      (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
      (integralScalarQuotientSheafMap l E L ι W)
      (coefficientExtensionQuotient_naturality l E L ι W))

set_option genSizeOf false in
set_option genInjectivity false in
/-- Evaluation of reconstruction's system mate is the canonical finite geometric
mate. Together with the actual total-limit counit this fixes the projections r_n.
Source: Stacks 07A6, 0A07; DAG proof Step 2
(blueprint: lem-weil-strict-direct-image-mixed-unit). -/
def ReductionEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SY : CoefficientDerivedSystemCalculus l E Y) (C : LimitComparison l E f)
    (I : IntegralModel l E f) : Prop :=
  ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E Y n).map (reductionMap l E f SX SY C I K) ≫
      (FrobeniusExchange.systemDirectEvaluation l E f n).app (SX.reduction.obj K.obj) ≫
      (proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n+1))).map
        ((SX.reductionEvaluation n).hom.app K.obj) =
    (SY.reductionEvaluation n).hom.app (I.image.obj K).obj ≫ finiteReduction l E f I K n

attribute [instance 20000] WeilConjectures.CompletedCoefficientPushforward.modAbelian
attribute [instance 10000] WeilConjectures.CompletedCoefficientPushforward.hasDerived

end WeilConjectures.StrictDirectImageMixedUnit
