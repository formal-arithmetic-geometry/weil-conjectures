/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Algebra.Homology.ScalarInternalHomDataSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralCompactSupportCoefficientData
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniversesSupplement
public import WeilConjectures.SixFunctors.RingedFiniteFreeHomBaseChange
public import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains

import WeilConjectures.Algebra.Homology.RhomGlobalSectionsOfUniverses
import WeilConjectures.AlgebraicGeometry.IntegralDerivedOperationsOnSlices
import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
import WeilConjectures.AlgebraicGeometry.DerivedCompleteOnSlices
import WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
import WeilConjectures.AlgebraicGeometry.WeilCompletedTensorReflector
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.FiniteConstructibleHom
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.CategoryTheory.LocalizedModuleExactIndependent
import WeilConjectures.Algebra.Homology.KFlatSupplement
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
import WeilConjectures.SixFunctors.FiniteCoverCTFLocality
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImageSupplement
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleInternalHom
import WeilConjectures.AlgebraicGeometry.IntegralHomReduction
import WeilConjectures.AlgebraicGeometry.SfIntegralDirectImageConstructible
import WeilConjectures.AlgebraicGeometry.IntegralResidueTor
import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
import WeilConjectures.AlgebraicGeometry.CompactSupportProjectionFormula
import WeilConjectures.AlgebraicGeometry.PullbackTorAmplitude
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientTensorCtf
import WeilConjectures.AlgebraicGeometry.IntegralOperationsPreserveConstructible
import WeilConjectures.AlgebraicGeometry.SfFiniteEtaleProjectionFormula
import WeilConjectures.AlgebraicGeometry.SfProEtaleProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientHomChange
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.ComparisonTorAmplitude
import WeilConjectures.AlgebraicGeometry.EtaleCoefficientSystemAdjoint
import WeilConjectures.AlgebraicGeometry.IntegralOperationsScalarComparisons
import WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.BasicOperationsCoefficientReduction
import WeilConjectures.AlgebraicGeometry.SfRationalizationKaroubi
import WeilConjectures.AlgebraicGeometry.GeneralAlgebraicallyClosedCoefficients

/-!
# Tensor--Hom exchange for the constructible exceptional adjoint

Source: Weil conjectures blueprint, main-20261015, sec-six-functors,
`sk-thm-sf-tensor-hom` (blueprint: sk-thm-sf-tensor-hom).

The exceptional functor is the unconditional constructible adjoint. In particular,
no right adjoint on the entire pro-etale derived category is an input.

## Main definitions

* `RingExchange` records the ambient exchange, boundedness below and signed shifts.
* `CanonicalExchange` fixes the forward map by its projection/counit transpose.
* `Family` records this canonical exchange through all four coefficient regimes.

## Main statements

* `exists_family` supplies this family for the unconditional constructible adjoint.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
-- Keep the chosen valuation ring folded while comparing coefficient categories.
attribute [local irreducible] Padic.coefficientExtensionIntegers

universe u v w v₁ w₁
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace WeilConjectures
namespace ConstructibleTensorHom
open ConstructibleExceptionalCoefficients

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The actual ambient ringed derived category, retaining both small-site universes.
Source: blueprint operations (i)--(ii) (blueprint: sk-thm-sf-tensor-hom). -/
abbrev Ambient (T : Scheme.{u}) (s : RingStage.{u} l) :=
  DerivedCategory (pbcModules T ((s.coefficients l).ring T))

/-- The recorded K-injective internal Hom over the finite or completed ring sheaf.
Source: blueprint operations (i); Stacks 08J7 (blueprint: sk-thm-sf-tensor-hom). -/
abbrev hom (T : Scheme.{u}) (s : RingStage.{u} l) :
    (Ambient l T s)ᵒᵖ × Ambient l T s ⥤ Ambient l T s :=
  CategoryTheory.derivedInternalHomOfUniverses.{u + 1, u, u}
    (ProEt.topology T) ((s.coefficients l).ring T)

/-- The actual ordinary direct image, not the exceptional adjoint.
Source: blueprint operations (ii) (blueprint: sk-thm-sf-tensor-hom). -/
abbrev direct {X Y : Scheme.{u}} (f : X ⟶ Y) (s : RingStage.{u} l) :
    Ambient l X s ⥤ Ambient l Y s :=
  PurCompactSupport.push (s.coefficients l) f

/-- Input pairs have finite Tor amplitude in the recorded full subcategories.
Source: the displayed assertion (blueprint: sk-thm-sf-tensor-hom). -/
abbrev Pairs (X Y : Scheme.{u}) (s : Stage.{u} l) :=
  (C.{u, u} l Ω X s)ᵒᵖ × C.{u, u} l Ω Y s

/-- The left side of exchange, as an actual ambient bifunctor.
Source: the displayed assertion (blueprint: sk-thm-sf-tensor-hom). -/
def source {X Y : Scheme.{u}} (f : X ⟶ Y) (s : RingStage.{u} l)
    (A : Operation.{u, u} l Ω X Y (s.stage l)) :
    Pairs l Ω X Y (s.stage l) ⥤ Ambient l Y s :=
  ((s.inclusion.{u, u} l Ω X).op.prod (A.G ⋙ s.inclusion.{u, u} l Ω X)) ⋙
    hom l X s ⋙ direct l f s

/-- The right side of exchange, as an actual ambient bifunctor.
Source: the displayed assertion (blueprint: sk-thm-sf-tensor-hom). -/
def target {X Y : Scheme.{u}} (s : RingStage.{u} l)
    (A : Operation.{u, u} l Ω X Y (s.stage l)) :
    Pairs l Ω X Y (s.stage l) ⥤ Ambient l Y s :=
  ((A.F ⋙ s.inclusion.{u, u} l Ω Y).op.prod (s.inclusion.{u, u} l Ω Y)) ⋙ hom l Y s

/-- Restrict the existing normalized K-flat tensor comparison to flat-term K-flats.
This changes neither the tensor nor its representative comparison or evaluation.
Source: proof steps 1 and 7, the tensor--Hom bijections
(blueprint: sk-thm-sf-tensor-hom). -/
def tensorPresentation (W : Scheme.{u}) (s : RingStage.{u} l)
    (S : CoefficientClosedStructure (hom l W s))
    (T : CoefficientTensorModels.{u, u + 1, u, u + 2}
      (ProEt.topology W) ((s.coefficients l).ring W) S) :
    ProEtaleTensorModel W ((s.coefficients l).ring W) where
  tensor := S.tensor
  representative := Functor.isoWhiskerLeft
    ((ObjectProperty.ιOfLE
      (P := proEtaleFlatRepresentatives W ((s.coefficients l).ring W))
      (P' := CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (J := ProEt.topology W) (R := (s.coefficients l).ring W))
      (fun _ h ↦ h.1)).prod
    (ObjectProperty.ιOfLE
      (P := proEtaleFlatRepresentatives W ((s.coefficients l).ring W))
      (P' := CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (J := ProEt.topology W) (R := (s.coefficients l).ring W))
      (fun _ h ↦ h.1))) T.comparison

/-- Fix the exchange by its tensor--Hom transpose on every constructible finite-Tor
Yoneda test. For t : pull L tensor M -> G N, transposing t by tensor--Hom and
ordinary pullback/direct image, then applying the exchange and uncurrying, equals
PF followed by compact support of t and the exceptional counit. The two symmetries
only reorder tensor arguments; their signed representative formulas and both closed
adjunctions are fixed by the existing normalized tensor models and coherences.

This is the forward-map form of the five-bijection characterization: invert PF
and the other four bijections to recover the source's Hom-chain Yoneda formula.
At integral coefficients maps to the derived-complete G N and N factor uniquely
through completion, so this same equation expresses the completed tensor chain.
It does not require the uncompleted tensor itself to be constructible.
Source: proof steps 1--2 and 7--9, canonical Yoneda construction
(blueprint: sk-thm-sf-tensor-hom). -/
def CanonicalExchange {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (s : RingStage.{u} l) (A : Operation.{u, u} l Ω X Y (s.stage l))
    (r : LeftRealization.{u, u} l Ω c s A) (e : source l Ω f s A ≅ target l Ω s A) : Prop :=
  ∃ hc : (s.coefficients l).pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      ((s.coefficients l).ring Y) ((s.coefficients l).ring c.Z)
      ((s.coefficients l).ring X) ((s.coefficients l).pull c.g)
      ((s.coefficients l).pull c.i),
  ∀ (SX : CoefficientClosedStructure (hom l X s))
    (TX : CoefficientTensorModels.{u, u + 1, u, u + 2}
      (ProEt.topology X) ((s.coefficients l).ring X) SX)
    (βX : @SymmetricCategory (Ambient l X s) _ SX.monoidal),
    Nonempty (RingedDerivedTensorCoherence.{u + 1, u, u, u + 2}
      (ProEt.topology X) ((s.coefficients l).ring X) SX TX βX) →
  ∀ (SY : CoefficientClosedStructure (hom l Y s))
    (TY : CoefficientTensorModels.{u, u + 1, u, u + 2}
      (ProEt.topology Y) ((s.coefficients l).ring Y) SY)
    (βY : @SymmetricCategory (Ambient l Y s) _ SY.monoidal),
    Nonempty (RingedDerivedTensorCoherence.{u + 1, u, u, u + 2}
      (ProEt.topology Y) ((s.coefficients l).ring Y) SY TY βY) →
  ∀ (aZ : ProEtaleTensorModel c.Z ((s.coefficients l).ring c.Z))
    (M : C.{u, u} l Ω X (s.stage l)) (N L : C.{u, u} l Ω Y (s.stage l))
    (t : SX.tensor.obj
      ((PurCompactSupport.pull (s.coefficients l) f).obj ((s.inclusion.{u, u} l Ω Y).obj L),
        (s.inclusion.{u, u} l Ω X).obj M) ⟶ (s.inclusion.{u, u} l Ω X).obj (A.G.obj N)),
    (SY.transpose ((s.inclusion.{u, u} l Ω Y).obj L) ((s.inclusion.{u, u} l Ω Y).obj (A.F.obj M))
        ((s.inclusion.{u, u} l Ω Y).obj N)).symm
      ((proEtaleRingDerivedAdjunction f ((s.coefficients l).ring Y)
          ((s.coefficients l).ring X) ((s.coefficients l).pull f)).homEquiv _ _
        (SX.transpose _ _ _ t) ≫ e.hom.app (op M, N)) =
      SY.tensor.map (Prod.mkHom (𝟙 _) (r.hom.app M)) ≫
        (βY.toBraidedCategory.braiding _ _).hom ≫
        ((PurCompactSupport.projectionMap (s.coefficients l) c
          (tensorPresentation l X s SX TX) aZ (tensorPresentation l Y s SY TY) hc).app
            ((s.inclusion.{u, u} l Ω X).obj M)).app ((s.inclusion.{u, u} l Ω Y).obj L) ≫
        (PurCompactSupport.image (s.coefficients l) c).map
          ((βX.toBraidedCategory.braiding _ _).hom ≫ t) ≫
        r.inv.app (A.G.obj N) ≫
        (s.inclusion.{u, u} l Ω Y).map (A.adjunction.counit.app N)

/-- The recorded full inclusions carry their inherited shift comparisons.
Source: blueprint full-subcategory convention (blueprint: sk-thm-sf-tensor-hom). -/
instance inclusionCommShift (T : Scheme.{u}) (s : RingStage.{u} l) :
    (s.inclusion.{u, u} l Ω T).CommShift ℤ :=
  match s with
  | .finite E n => ObjectProperty.commShiftι (finiteTorConstructible l E.carrier n n.pos T) (A := ℤ)
  | .integral E => ObjectProperty.commShiftι (finiteTorConstructibleIntegral l E.carrier T) (A := ℤ)

/-- Shift in the contravariant input of the ambient left side, with the actual sign.
Source: proof step 14; Stacks 08JA (blueprint: sk-thm-sf-tensor-hom). -/
def sourceFirstShift {X Y : Scheme.{u}} (f : X ⟶ Y) (s : RingStage.{u} l)
    (A : Operation.{u, u} l Ω X Y (s.stage l))
    (M : C.{u, u} l Ω X (s.stage l)) (N : C.{u, u} l Ω Y (s.stage l)) (a : ℤ) :
    ((source l Ω f s A).obj (op M, N))⟦-a⟧ ⟶
      (source l Ω f s A).obj (op (M⟦a⟧), N) :=
  ((direct l f s).commShiftIso (-a)).inv.app _ ≫
    (direct l f s).map
      ((CategoryTheory.RingedHomUniverses.sourceShift
          (ProEt.topology X) ((s.coefficients l).ring X)
          ((s.inclusion.{u, u} l Ω X).obj M) a).hom.app
            ((s.inclusion.{u, u} l Ω X).obj (A.G.obj N)) ≫
        (hom l X s).map
          (Prod.mkHom (((s.inclusion.{u, u} l Ω X).commShiftIso a).hom.app M).op (𝟙 _)))

/-- Shift in the contravariant input of the right side, through compact support.
Source: proof step 14; Stacks 08JA (blueprint: sk-thm-sf-tensor-hom). -/
def targetFirstShift {X Y : Scheme.{u}} (s : RingStage.{u} l)
    (A : Operation.{u, u} l Ω X Y (s.stage l))
    (M : C.{u, u} l Ω X (s.stage l)) (N : C.{u, u} l Ω Y (s.stage l)) (a : ℤ) :
    ((target l Ω s A).obj (op M, N))⟦-a⟧ ⟶
      (target l Ω s A).obj (op (M⟦a⟧), N) :=
  (CategoryTheory.RingedHomUniverses.sourceShift
      (ProEt.topology Y) ((s.coefficients l).ring Y)
      ((s.inclusion.{u, u} l Ω Y).obj (A.F.obj M)) a).hom.app
        ((s.inclusion.{u, u} l Ω Y).obj N) ≫
    (hom l Y s).map
      (Prod.mkHom
        ((s.inclusion.{u, u} l Ω Y).map ((A.F.commShiftIso a).hom.app M) ≫
          ((s.inclusion.{u, u} l Ω Y).commShiftIso a).hom.app (A.F.obj M)).op (𝟙 _))

/-- Shift in the covariant input of the left side, using the exceptional shift.
Source: proof step 14; Stacks 08JC (blueprint: sk-thm-sf-tensor-hom). -/
def sourceSecondShift {X Y : Scheme.{u}} (f : X ⟶ Y) (s : RingStage.{u} l)
    (A : Operation.{u, u} l Ω X Y (s.stage l))
    (M : C.{u, u} l Ω X (s.stage l)) (N : C.{u, u} l Ω Y (s.stage l)) (b : ℤ) :
    ((source l Ω f s A).obj (op M, N))⟦b⟧ ⟶
      (source l Ω f s A).obj (op M, N⟦b⟧) :=
  ((direct l f s).commShiftIso b).inv.app _ ≫
    (direct l f s).map
      (((CategoryTheory.RingedHomUniverses.hom
          (ProEt.topology X) ((s.coefficients l).ring X)
          ((s.inclusion.{u, u} l Ω X).obj M)).commShiftIso b).inv.app
            ((s.inclusion.{u, u} l Ω X).obj (A.G.obj N)) ≫
        (hom l X s).map
          (Prod.mkHom (𝟙 _) (((s.inclusion.{u, u} l Ω X).commShiftIso b).inv.app
              (A.G.obj N) ≫
            (s.inclusion.{u, u} l Ω X).map ((A.G.commShiftIso b).inv.app N))))

/-- Shift in the covariant input of the ambient right side.
Source: proof step 14; Stacks 08JC (blueprint: sk-thm-sf-tensor-hom). -/
def targetSecondShift {X Y : Scheme.{u}} (s : RingStage.{u} l)
    (A : Operation.{u, u} l Ω X Y (s.stage l))
    (M : C.{u, u} l Ω X (s.stage l)) (N : C.{u, u} l Ω Y (s.stage l)) (b : ℤ) :
    ((target l Ω s A).obj (op M, N))⟦b⟧ ⟶
      (target l Ω s A).obj (op M, N⟦b⟧) :=
  ((CategoryTheory.RingedHomUniverses.hom
      (ProEt.topology Y) ((s.coefficients l).ring Y)
      ((s.inclusion.{u, u} l Ω Y).obj (A.F.obj M))).commShiftIso b).inv.app
        ((s.inclusion.{u, u} l Ω Y).obj N) ≫
    (hom l Y s).map
      (Prod.mkHom (𝟙 _) (((s.inclusion.{u, u} l Ω Y).commShiftIso b).inv.app N))

/-- The unchanged small site is small in its object universe.
Source: blueprint small-site convention (blueprint: sk-thm-sf-tensor-hom). -/
instance siteSmall (W : Scheme.{u}) : EssentiallySmall.{u + 1} W.ProEt :=
  essentiallySmallSelf.{0} W.ProEt

/-- Use the published normalized scalar-Hom data and tensor comparison together.
These presentations always exist by scalarInternalHomAdjunction_exists. They
retain the actual ordinary scalar objects/maps, universal counits, scalar units,
K-flat tensor squares and evaluation; no extra Hom comparison map is supplied.
Source: proof steps 10--13 (blueprint: sk-thm-sf-tensor-hom). -/
abbrev ScalarModel {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (W : Scheme.{u}) :=
  Σ M : CategoryTheory.ScalarHomModels.{u + 1, u, u, u + 2} (ProEt.topology W),
    CategoryTheory.ScalarHomTensorComparison.{u + 1, u, u, u + 2} M (a.map W)

/-- The unique scalar comparison preserving the two normalized adjunction units.
Both right adjoints are the actual restriction of the same coefficient actions.
Source: Stacks 07A6 (blueprint: sk-thm-sf-tensor-hom). -/
def scalarModelComparison {s t : RingStage.{u} l}
    {a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)}
    {W : Scheme.{u}} (D : ScalarModel l a W) :
    (D.1.scalar (a.map W)).derived ≅ pbcDerivedExtend (a.map W) :=
  Adjunction.leftAdjointUniq (D.1.scalar (a.map W)).adjunction
    (pbcDerivedScalarAdjunction (a.map W))

/-- Scalar Hom change is the transpose of scalar extension of evaluation,
transported by the unique normalized scalar-adjunction comparison. Its tensor
comparison is fixed on K-flat pure tensors in the published model.
Source: proof steps 10--13 (blueprint: sk-thm-sf-tensor-hom). -/
def homChange {s t : RingStage.{u} l}
    {a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)}
    {W : Scheme.{u}} (D : ScalarModel l a W) (M N : Ambient l W s) :
    (pbcDerivedExtend (a.map W)).obj ((hom l W s).obj (op M, N)) ⟶
      (hom l W t).obj
        (op ((pbcDerivedExtend (a.map W)).obj M),
          (pbcDerivedExtend (a.map W)).obj N) :=
  (scalarModelComparison l D).inv.app _ ≫
    (D.1.closed ((t.coefficients l).ring W)).transpose _
      ((D.1.scalar (a.map W)).derived.obj M) ((D.1.scalar (a.map W)).derived.obj N)
      (D.2.iso.inv.app ((hom l W s).obj (op M, N), M) ≫
        (D.1.scalar (a.map W)).derived.map
          ((D.1.closed ((s.coefficients l).ring W)).evaluation M N)) ≫
    (hom l W t).map
      (Prod.mkHom ((scalarModelComparison l D).inv.app M).op
        ((scalarModelComparison l D).hom.app N))

/-- The left vertical arrow of the actual coefficient square: the ordinary
pushforward mate followed by scalar extension of evaluation and the exceptional mate.
Source: proof step 13 (blueprint: sk-thm-sf-tensor-hom). -/
def sourceChange {X Y : Scheme.{u}} (f : X ⟶ Y) {s t : RingStage.{u} l}
    {a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)}
    {A : Operation.{u, u} l Ω X Y (s.stage l)} {B : Operation.{u, u} l Ω X Y (t.stage l)}
    (SX : Scalar.{u, u} l Ω a X) (SY : Scalar.{u, u} l Ω a Y)
    (d : Comparison.{u, u} l Ω A B SX.functor SY.functor) (DX : ScalarModel l a X)
    (M : C.{u, u} l Ω X (s.stage l)) (N : C.{u, u} l Ω Y (s.stage l)) :
    (pbcDerivedExtend (a.map Y)).obj ((source l Ω f s A).obj (op M, N)) ⟶
      (source l Ω f t B).obj (op (SX.functor.obj M), SY.functor.obj N) :=
  (PurCompactSupport.properComparison a f).app _ ≫
    (direct l f t).map
      (homChange l DX ((s.inclusion.{u, u} l Ω X).obj M)
          ((s.inclusion.{u, u} l Ω X).obj (A.G.obj N)) ≫
        (hom l X t).map
          (Prod.mkHom (SX.realization.hom.app M).op
            (SX.realization.inv.app (A.G.obj N) ≫
              (t.inclusion.{u, u} l Ω X).map (d.b.hom.app N))))

/-- The right vertical arrow of the actual coefficient square. The compact-support
comparison occurs contravariantly, hence its inverse is used.
Source: proof step 13 (blueprint: sk-thm-sf-tensor-hom). -/
def targetChange {X Y : Scheme.{u}} {s t : RingStage.{u} l}
    {a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)}
    {A : Operation.{u, u} l Ω X Y (s.stage l)} {B : Operation.{u, u} l Ω X Y (t.stage l)}
    (SX : Scalar.{u, u} l Ω a X) (SY : Scalar.{u, u} l Ω a Y)
    (d : Comparison.{u, u} l Ω A B SX.functor SY.functor) (DY : ScalarModel l a Y)
    (M : C.{u, u} l Ω X (s.stage l)) (N : C.{u, u} l Ω Y (s.stage l)) :
    (pbcDerivedExtend (a.map Y)).obj ((target l Ω s A).obj (op M, N)) ⟶
      (target l Ω t B).obj (op (SX.functor.obj M), SY.functor.obj N) :=
  homChange l DY ((s.inclusion.{u, u} l Ω Y).obj (A.F.obj M))
      ((s.inclusion.{u, u} l Ω Y).obj N) ≫
    (hom l Y t).map
      (Prod.mkHom
        ((t.inclusion.{u, u} l Ω Y).map (d.q.inv.app M) ≫
          SY.realization.hom.app (A.F.obj M)).op (SY.realization.inv.app N))

/-- Shift either input; `true` means the contravariant first argument.
Source: proof step 14 (blueprint: sk-thm-sf-tensor-hom). -/
def pairShift (X Y : Scheme.{u}) (s : Stage.{u} l) (first : Bool) (n : ℤ) :
    Pairs l Ω X Y s ⥤ Pairs l Ω X Y s :=
  if first then (shiftFunctor (C.{u, u} l Ω X s) n).op.prod (𝟭 _)
  else (𝟭 _).op.prod (shiftFunctor (C.{u, u} l Ω Y s) n)

/-- Contravariant Hom shifts change sign.
Source: Stacks 08JA (blueprint: sk-thm-sf-tensor-hom). -/
def signedShift (first : Bool) (n : ℤ) : ℤ := if first then -n else n

/-- Shift compatibility expressed as a square of natural transformations.
Source: proof step 14 (blueprint: sk-thm-sf-tensor-hom). -/
structure ShiftExchange {X Y : Scheme.{u}} (s : Stage.{u} l)
    {B : Type v} [Category.{w} B] [HasShift B ℤ]
    (F G : Pairs l Ω X Y s ⥤ B) (e : F ≅ G) where
  left (first : Bool) (n : ℤ) : F ⋙ shiftFunctor B (signedShift first n) ≅
    pairShift l Ω X Y s first n ⋙ F
  right (first : Bool) (n : ℤ) : G ⋙ shiftFunctor B (signedShift first n) ≅
    pairShift l Ω X Y s first n ⋙ G
  square (first : Bool) (n : ℤ) (P : Pairs l Ω X Y s) :
    (e.hom.app P)⟦signedShift first n⟧' ≫ (right first n).hom.app P =
      (left first n).hom.app P ≫
        e.hom.app ((pairShift l Ω X Y s first n).obj P)

/-- The scalar/input shift comparison uses the given coefficient functors' shift maps.
Source: proof steps 14--15 (blueprint: sk-thm-sf-tensor-hom). -/
def scalarPairShift {X Y : Scheme.{u}} {s t : Stage.{u} l}
    (QX : C.{u, u} l Ω X s ⥤ C.{u, u} l Ω X t) (QY : C.{u, u} l Ω Y s ⥤ C.{u, u} l Ω Y t)
    (qX : QX.CommShift ℤ) (qY : QY.CommShift ℤ) (first : Bool) (n : ℤ) :
    QX.op.prod QY ⋙ pairShift l Ω X Y t first n ≅
      pairShift l Ω X Y s first n ⋙ QX.op.prod QY :=
  letI := qX
  letI := qY
  match first with
  | true => NatIso.prod (NatIso.op (QX.commShiftIso n)) (Iso.refl QY)
  | false => NatIso.prod (Iso.refl QX.op) (QY.commShiftIso n).symm

/-- A shift structure descends through scalar extension with its ACTUAL signed
input and output comparisons. This pins the higher-stage shift comparisons to
images of the signed ambient ones, rather than choosing unrelated shift maps.
Source: proof steps 14--15 (blueprint: sk-thm-sf-tensor-hom). -/
def ShiftNormalization {X Y : Scheme.{u}} {s t : Stage.{u} l}
    {B : Type v} [Category.{w} B] [HasShift B ℤ]
    {B' : Type v₁} [Category.{w₁} B'] [HasShift B' ℤ]
    {F G : Pairs l Ω X Y s ⥤ B} {e : F ≅ G}
    {F' G' : Pairs l Ω X Y t ⥤ B'} {e' : F' ≅ G'}
    (S : ShiftExchange l Ω s F G e) (T : ShiftExchange l Ω t F' G' e')
    (QX : C.{u, u} l Ω X s ⥤ C.{u, u} l Ω X t) (QY : C.{u, u} l Ω Y s ⥤ C.{u, u} l Ω Y t)
    (QD : B ⥤ B') (qX : QX.CommShift ℤ) (qY : QY.CommShift ℤ)
    (qD : QD.CommShift ℤ)
    (a : QX.op.prod QY ⋙ F' ≅ F ⋙ QD)
    (b : QX.op.prod QY ⋙ G' ≅ G ⋙ QD) : Prop :=
  letI := qD
  ∀ (first : Bool) (n : ℤ) (P : Pairs l Ω X Y s),
    ((a.hom.app P)⟦signedShift first n⟧' ≫
        (QD.commShiftIso (signedShift first n)).inv.app (F.obj P) ≫
        QD.map ((S.left first n).hom.app P) =
      (T.left first n).hom.app ((QX.op.prod QY).obj P) ≫
        F'.map ((scalarPairShift l Ω QX QY qX qY first n).hom.app P) ≫
        a.hom.app ((pairShift l Ω X Y s first n).obj P)) ∧
    ((b.hom.app P)⟦signedShift first n⟧' ≫
        (QD.commShiftIso (signedShift first n)).inv.app (G.obj P) ≫
        QD.map ((S.right first n).hom.app P) =
      (T.right first n).hom.app ((QX.op.prod QY).obj P) ≫
        G'.map ((scalarPairShift l Ω QX QY qX qY first n).hom.app P) ≫
        b.hom.app ((pairShift l Ω X Y s first n).obj P))

/-- An exchange at a ring stage is a bifunctor isomorphism, with both signed shift
squares. Naturality in both inputs is part of `NatIso`, including all ambient arrows.
Source: assertion and proof step 14 (blueprint: sk-thm-sf-tensor-hom). -/
structure RingExchange {X Y : Scheme.{u}} (f : X ⟶ Y) (s : RingStage.{u} l)
    (A : Operation.{u, u} l Ω X Y (s.stage l)) where
  iso : source l Ω f s A ≅ target l Ω s A
  boundedBelow : ∀ P : Pairs l Ω X Y (s.stage l), ∃ a : ℤ,
    ((source l Ω f s A).obj P).IsGE a ∧ ((target l Ω s A).obj P).IsGE a
  shifts : ShiftExchange l Ω (s.stage l) (source l Ω f s A) (target l Ω s A) iso
  leftFirst : ∀ (M : C.{u, u} l Ω X (s.stage l)) (N : C.{u, u} l Ω Y (s.stage l)) (a : ℤ),
    (shifts.left true a).hom.app (op M, N) = sourceFirstShift l Ω f s A M N a
  rightFirst : ∀ (M : C.{u, u} l Ω X (s.stage l)) (N : C.{u, u} l Ω Y (s.stage l)) (a : ℤ),
    (shifts.right true a).hom.app (op M, N) = targetFirstShift l Ω s A M N a
  leftSecond : ∀ (M : C.{u, u} l Ω X (s.stage l)) (N : C.{u, u} l Ω Y (s.stage l)) (b : ℤ),
    (shifts.left false b).hom.app (op M, N) = sourceSecondShift l Ω f s A M N b
  rightSecond : ∀ (M : C.{u, u} l Ω X (s.stage l)) (N : C.{u, u} l Ω Y (s.stage l)) (b : ℤ),
    (shifts.right false b).hom.app (op M, N) = targetSecondShift l Ω s A M N b
  firstShift : ∀ (M : C.{u, u} l Ω X (s.stage l)) (N : C.{u, u} l Ω Y (s.stage l)) (a : ℤ),
    (iso.hom.app (op M, N))⟦-a⟧' ≫ targetFirstShift l Ω s A M N a =
      sourceFirstShift l Ω f s A M N a ≫ iso.hom.app (op (M⟦a⟧), N)
  secondShift : ∀ (M : C.{u, u} l Ω X (s.stage l)) (N : C.{u, u} l Ω Y (s.stage l)) (b : ℤ),
    (iso.hom.app (op M, N))⟦b⟧' ≫ targetSecondShift l Ω s A M N b =
      sourceSecondShift l Ω f s A M N b ≫ iso.hom.app (op M, N⟦b⟧)

/-- Integral realization of the two ambient composites. Equalities of functors fix
objects AND arrows; the lift is not an arbitrary isomorphic object.
Source: proof steps 6 and 15 (blueprint: sk-thm-sf-tensor-hom). -/
structure IntegralLift {X Y : Scheme.{u}} (f : X ⟶ Y) (E : FieldStage.{u} l)
    (A : Operation.{u, u} l Ω X Y (.integral E))
    (e : RingExchange l Ω f (.integral E) A) where
  left : Pairs l Ω X Y (.integral E) ⥤ sfIntegralConstructibleCategory l E.carrier Y
  right : Pairs l Ω X Y (.integral E) ⥤ sfIntegralConstructibleCategory l E.carrier Y
  left_eq : left ⋙ (sfIntegralConstructible l E.carrier Y).ι =
    source l Ω f (.integral E) A
  right_eq : right ⋙ (sfIntegralConstructible l E.carrier Y).ι =
    target l Ω (.integral E) A
  iso : left ≅ right
  realization : ∀ P : Pairs l Ω X Y (.integral E),
    HEq ((sfIntegralConstructible l E.carrier Y).ι.map (iso.hom.app P))
      (e.iso.hom.app P)
  shifts : ShiftExchange l Ω (.integral E) left right iso
  shift_normalization : ShiftNormalization l Ω shifts e.shifts (𝟭 _) (𝟭 _)
    (sfIntegralConstructible l E.carrier Y).ι inferInstance inferInstance
    (ObjectProperty.commShiftι (sfIntegralConstructible l E.carrier Y) (A := ℤ))
    (eqToIso left_eq).symm (eqToIso right_eq).symm

/-- The actual rational Hom pair functor on the source side. The only supplied
proof is its constructibility domain; the Hom and direct functors are unchanged.
Source: operations (i)--(ii), (vi) (blueprint: sk-thm-sf-tensor-hom). -/
def rationalSource {X Y : Scheme.{u}} (E : FieldStage.{u} l)
    (A : Operation.{u, u} l Ω X Y (.rational E))
    (D : C.{u, u} l Ω X (.rational E) ⥤ C.{u, u} l Ω Y (.rational E))
    (h : ∀ P : Pairs l Ω X Y (.rational E),
      constructibleRationalHomPairs l E.carrier X (op P.1.unop, A.G.obj P.2)) :=
  (constructibleRationalHomPairs l E.carrier X).lift ((𝟭 _).op.prod A.G) h ⋙
    rationalDerivedInternalHom l E.carrier X ⋙ D

/-- The actual rational Hom on the compact-support/target pair.
Source: operations (i) and (vi) (blueprint: sk-thm-sf-tensor-hom). -/
def rationalTarget {X Y : Scheme.{u}} (E : FieldStage.{u} l)
    (A : Operation.{u, u} l Ω X Y (.rational E))
    (h : ∀ P : Pairs l Ω X Y (.rational E),
      constructibleRationalHomPairs l E.carrier Y (op (A.F.obj P.1.unop), P.2)) :=
  (constructibleRationalHomPairs l E.carrier Y).lift (A.F.op.prod (𝟭 _)) h ⋙
    rationalDerivedInternalHom l E.carrier Y

-- Compare the rational functors through their published interfaces. Unfolding their
-- chosen constructions during endpoint unification expands the scalar-localization
-- and derived-pullback models, which are not used by the following declarations.
attribute [local irreducible] rationalDerivedPullback sfRationalConstructibleLocalization
  sfRationalScalarExtension rationalDerivedInternalHom

/-- The rational exchange, descended from the actual integral exchange. Its two
sides use the recorded rational Hom and the ordinary pullback/direct adjunction.
All rational arrows, including arbitrary localized scalars, occur in this NatIso.
The normalization is an equality of arrows, not merely a Nonempty isomorphism
between unspecified endpoints.
Source: proof step 15 (blueprint: sk-thm-sf-tensor-hom). -/
structure RationalDescent {X Y : Scheme.{u}} (f : X ⟶ Y) (E : FieldStage.{u} l)
    {A : Operation.{u, u} l Ω X Y (.integral E)}
    {e : RingExchange l Ω f (.integral E) A}
    (I : IntegralLift l Ω f E A e) (B : Operation.{u, u} l Ω X Y (.rational E))
    (d : FieldComparison.{u, u} l Ω A B (rationalization.{u, u} l Ω E X)
      (rationalization.{u, u} l Ω E Y))
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] where
  direct : C.{u, u} l Ω X (.rational E) ⥤ C.{u, u} l Ω Y (.rational E)
  ordinary : rationalDerivedPullback l E.carrier f ⊣ direct
  leftDomain : ∀ P : Pairs l Ω X Y (.rational E),
    constructibleRationalHomPairs l E.carrier X (op P.1.unop, B.G.obj P.2)
  rightDomain : ∀ P : Pairs l Ω X Y (.rational E),
    constructibleRationalHomPairs l E.carrier Y (op (B.F.obj P.1.unop), P.2)
  iso : rationalSource l Ω E B direct leftDomain ≅ rationalTarget l Ω E B rightDomain
  left : ((rationalization.{u, u} l Ω E X).op.prod (rationalization.{u, u} l Ω E Y)) ⋙
      rationalSource l Ω E B direct leftDomain ≅
    I.left ⋙ sfRationalConstructibleLocalization l E.carrier Y
  right : ((rationalization.{u, u} l Ω E X).op.prod (rationalization.{u, u} l Ω E Y)) ⋙
      rationalTarget l Ω E B rightDomain ≅
    I.right ⋙ sfRationalConstructibleLocalization l E.carrier Y
  normalization : ∀ P : Pairs l Ω X Y (.integral E),
    iso.hom.app (((rationalization.{u, u} l Ω E X).op.prod
        (rationalization.{u, u} l Ω E Y)).obj P) ≫ right.hom.app P =
      left.hom.app P ≫ (sfRationalConstructibleLocalization l E.carrier Y).map
        (I.iso.hom.app P)
  shifts : ShiftExchange l Ω (.rational E)
    (rationalSource l Ω E B direct leftDomain) (rationalTarget l Ω E B rightDomain) iso
  shift_normalization : ShiftNormalization l Ω I.shifts shifts
    (rationalization.{u, u} l Ω E X) (rationalization.{u, u} l Ω E Y)
    (sfRationalConstructibleLocalization l E.carrier Y) d.shiftX d.shiftY inferInstance
    left right

/-- The actual common-stage Hom followed by ordinary direct image.
Source: operations (i)--(ii), (vi) (blueprint: sk-thm-sf-tensor-hom). -/
def commonSource {X Y : Scheme.{u}} (A : Operation.{u, u} l Ω X Y .closed)
    (D : C.{u, u} l Ω X .closed ⥤ C.{u, u} l Ω Y .closed)
    (h : ∀ P : Pairs l Ω X Y .closed,
      commonStageHomPairs l Ω X (op P.1.unop, A.G.obj P.2)) :=
  (commonStageHomPairs l Ω X).lift ((𝟭 _).op.prod A.G) h ⋙
    commonStageDerivedInternalHom l Ω X ⋙ D

/-- The actual common-stage Hom of compact support and the second input.
Source: operations (i) and (vi) (blueprint: sk-thm-sf-tensor-hom). -/
def commonTarget {X Y : Scheme.{u}} (A : Operation.{u, u} l Ω X Y .closed)
    (h : ∀ P : Pairs l Ω X Y .closed,
      commonStageHomPairs l Ω Y (op (A.F.obj P.1.unop), P.2)) :=
  (commonStageHomPairs l Ω Y).lift (A.F.op.prod (𝟭 _)) h ⋙
    commonStageDerivedInternalHom l Ω Y

/-- The ordinary rational direct-image coefficient comparison is the mate of
recorded pullback scalar change, using the actual unit and counit.
Source: proof steps 12--15 (blueprint: sk-thm-sf-tensor-hom). -/
def rationalDirectChange {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (DE : C.{u, u} l Ω X (.rational E) ⥤ C.{u, u} l Ω Y (.rational E))
    (DL : C.{u, u} l Ω X (.rational L) ⥤ C.{u, u} l Ω Y (.rational L))
    (aE : rationalDerivedPullback l E.carrier f ⊣ DE)
    (aL : rationalDerivedPullback l L.carrier f ⊣ DL)
    (K : C.{u, u} l Ω X (.rational E)) :
    (rationalScalar.{u, u} l Ω E L i Y).obj (DE.obj K) ⟶
      DL.obj ((rationalScalar.{u, u} l Ω E L i X).obj K) :=
  aL.unit.app _ ≫ DL.map
    ((rationalPullbackScalarComparison l E.carrier L.carrier i f).inv.app (DE.obj K) ≫
      (rationalScalar.{u, u} l Ω E L i X).map (aE.counit.app K))

/-- The rational left coefficient arrow uses scalar Hom's evaluation transpose,
followed by the exceptional coefficient mate from the recorded system.
Source: proof steps 13 and 15 (blueprint: sk-thm-sf-tensor-hom). -/
def rationalSourceChange {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : Operation.{u, u} l Ω X Y (.rational E)) (B : Operation.{u, u} l Ω X Y (.rational L))
    (d : FieldComparison.{u, u} l Ω A B (rationalScalar.{u, u} l Ω E L i X)
      (rationalScalar.{u, u} l Ω E L i Y))
    (DE : C.{u, u} l Ω X (.rational E) ⥤ C.{u, u} l Ω Y (.rational E))
    (DL : C.{u, u} l Ω X (.rational L) ⥤ C.{u, u} l Ω Y (.rational L))
    (aE : rationalDerivedPullback l E.carrier f ⊣ DE)
    (aL : rationalDerivedPullback l L.carrier f ⊣ DL)
    (hE : ∀ P : Pairs l Ω X Y (.rational E),
      constructibleRationalHomPairs l E.carrier X (op P.1.unop, A.G.obj P.2))
    (hL : ∀ P : Pairs l Ω X Y (.rational L),
      constructibleRationalHomPairs l L.carrier X (op P.1.unop, B.G.obj P.2))
    (M : C.{u, u} l Ω X (.rational E)) (N : C.{u, u} l Ω Y (.rational E)) :
    (rationalScalar.{u, u} l Ω E L i Y).obj ((rationalSource l Ω E A DE hE).obj (op M, N)) ⟶
      (rationalSource l Ω L B DL hL).obj
        (op ((rationalScalar.{u, u} l Ω E L i X).obj M),
          (rationalScalar.{u, u} l Ω E L i Y).obj N) :=
  rationalDirectChange l Ω f E L i DE DL aE aL _ ≫ DL.map
    ((rationalHomScalarComparison l E.carrier L.carrier i X
        ⟨(op M, A.G.obj N), hE (op M, N)⟩).hom ≫
      (rationalDerivedInternalHom l L.carrier X).map
        (ObjectProperty.homMk (X := rationalHomScalarPair l E.carrier L.carrier i X
            ⟨(op M, A.G.obj N), hE (op M, N)⟩)
          (Y := ⟨_, hL (op ((rationalScalar.{u, u} l Ω E L i X).obj M),
            (rationalScalar.{u, u} l Ω E L i Y).obj N)⟩)
          (Prod.mkHom (𝟙 _) (d.b.hom.app N))))

/-- The rational right coefficient arrow uses the inverse compact-support
comparison in the contravariant input of the actual scalar Hom comparison.
Source: proof steps 13 and 15 (blueprint: sk-thm-sf-tensor-hom). -/
def rationalTargetChange {X Y : Scheme.{u}} (E L : FieldStage.{u} l)
    (i : E.carrier →ₐ[Padic l] L.carrier)
    (A : Operation.{u, u} l Ω X Y (.rational E)) (B : Operation.{u, u} l Ω X Y (.rational L))
    (d : FieldComparison.{u, u} l Ω A B (rationalScalar.{u, u} l Ω E L i X)
      (rationalScalar.{u, u} l Ω E L i Y))
    (hE : ∀ P : Pairs l Ω X Y (.rational E),
      constructibleRationalHomPairs l E.carrier Y (op (A.F.obj P.1.unop), P.2))
    (hL : ∀ P : Pairs l Ω X Y (.rational L),
      constructibleRationalHomPairs l L.carrier Y (op (B.F.obj P.1.unop), P.2))
    (M : C.{u, u} l Ω X (.rational E)) (N : C.{u, u} l Ω Y (.rational E)) :
    (rationalScalar.{u, u} l Ω E L i Y).obj ((rationalTarget l Ω E A hE).obj (op M, N)) ⟶
      (rationalTarget l Ω L B hL).obj
        (op ((rationalScalar.{u, u} l Ω E L i X).obj M),
          (rationalScalar.{u, u} l Ω E L i Y).obj N) :=
  (rationalHomScalarComparison l E.carrier L.carrier i Y
      ⟨(op (A.F.obj M), N), hE (op M, N)⟩).hom ≫
    (rationalDerivedInternalHom l L.carrier Y).map
      (ObjectProperty.homMk (X := rationalHomScalarPair l E.carrier L.carrier i Y
          ⟨(op (A.F.obj M), N), hE (op M, N)⟩)
        (Y := ⟨_, hL (op ((rationalScalar.{u, u} l Ω E L i X).obj M),
          (rationalScalar.{u, u} l Ω E L i Y).obj N)⟩)
        (Prod.mkHom (d.q.inv.app M).op (𝟙 _)))

section Family
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} (f : X ⟶ Y)
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- One joint exchange family. Coefficient compatibility is a commuting square
for the actual quotient, retained ramified, reduction, completed-inclusion,
identity and composite changes, using the normalized scalar tensor models.
The `canonical` field fixes its map by the projection/counit tensor--Hom equation.
Rationalization and every common-stage inclusion preserve the SAME family.
Source: the assertion, proof steps 10--15 (blueprint: sk-thm-sf-tensor-hom). -/
structure Family (R : System.{u, u} l Ω D hl (f := f)) (c : Compactification f) where
  [unitsX : ∀ x : X, Invertible (l : X.residueField x)]
  [unitsY : ∀ y : Y, Invertible (l : Y.residueField y)]
  ring (s : RingStage.{u} l) : RingExchange l Ω f s (R.ring.operation c (s.stage l))
  canonical (s : RingStage.{u} l) :
    CanonicalExchange l Ω c s (R.ring.operation c (s.stage l))
      (R.ring.left c s) (ring s).iso
  coefficient {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) (DX : ScalarModel l a X) (DY : ScalarModel l a Y)
      (M : C.{u, u} l Ω X (s.stage l)) (N : C.{u, u} l Ω Y (s.stage l)) :
    (pbcDerivedExtend (a.map Y)).map ((ring s).iso.hom.app (op M, N)) ≫
        targetChange l Ω (R.ring.scalar a ha true) (R.ring.scalar a ha false)
          (R.ring.comparison c a ha) DY M N =
      sourceChange l Ω f (R.ring.scalar a ha true) (R.ring.scalar a ha false)
          (R.ring.comparison c a ha) DX M N ≫
        (ring t).iso.hom.app
          (op ((R.ring.scalar a ha true).functor.obj M),
            (R.ring.scalar a ha false).functor.obj N)
  integral (E : FieldStage.{u} l) :
    IntegralLift l Ω f E (R.ring.operation c (.integral E)) (ring (.integral E))
  rational (E : FieldStage.{u} l) :
    RationalDescent l Ω f E (integral E) (R.ring.operation c (.rational E))
      (R.fields.rationalizationComparison c E)
  rationalCoefficient (E L : FieldStage.{u} l)
      (i : E.carrier →ₐ[Padic l] L.carrier)
      (M : C.{u, u} l Ω X (.rational E)) (N : C.{u, u} l Ω Y (.rational E)) :
    (rationalScalar.{u, u} l Ω E L i Y).map ((rational E).iso.hom.app (op M, N)) ≫
        rationalTargetChange l Ω E L i _ _ (R.fields.rationalComparison c E L i)
          (rational E).rightDomain (rational L).rightDomain M N =
      rationalSourceChange l Ω f E L i _ _ (R.fields.rationalComparison c E L i)
          (rational E).direct (rational L).direct (rational E).ordinary
          (rational L).ordinary (rational E).leftDomain (rational L).leftDomain M N ≫
        (rational L).iso.hom.app
          (op ((rationalScalar.{u, u} l Ω E L i X).obj M),
            (rationalScalar.{u, u} l Ω E L i Y).obj N)
  commonDirect : C.{u, u} l Ω X .closed ⥤ C.{u, u} l Ω Y .closed
  commonOrdinary : commonStageDerivedPullback l Ω f ⊣ commonDirect
  commonLeftDomain : ∀ P : Pairs l Ω X Y .closed,
    commonStageHomPairs l Ω X
      (op P.1.unop, (R.ring.operation c .closed).G.obj P.2)
  commonRightDomain : ∀ P : Pairs l Ω X Y .closed,
    commonStageHomPairs l Ω Y
      (op ((R.ring.operation c .closed).F.obj P.1.unop), P.2)
  commonIso : commonSource l Ω (R.ring.operation c .closed) commonDirect
      commonLeftDomain ≅
    commonTarget l Ω (R.ring.operation c .closed) commonRightDomain
  commonLeft (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    ((commonInclusion.{u, u} l Ω X i).op.prod (commonInclusion.{u, u} l Ω Y i)) ⋙
        commonSource l Ω (R.ring.operation c .closed) commonDirect commonLeftDomain ≅
      rationalSource l Ω (commonField.{u, u} l Ω i) (R.ring.operation c (.rational
        (commonField.{u, u} l Ω i))) (rational (commonField.{u, u} l Ω i)).direct
        (rational (commonField.{u, u} l Ω i)).leftDomain ⋙ commonInclusion.{u, u} l Ω Y i
  commonRight (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    ((commonInclusion.{u, u} l Ω X i).op.prod (commonInclusion.{u, u} l Ω Y i)) ⋙
        commonTarget l Ω (R.ring.operation c .closed) commonRightDomain ≅
      rationalTarget l Ω (commonField.{u, u} l Ω i) (R.ring.operation c (.rational
        (commonField.{u, u} l Ω i))) (rational (commonField.{u, u} l Ω i)).rightDomain ⋙
          commonInclusion.{u, u} l Ω Y i
  commonNormalization (i : AlgebraicallyClosedCoefficients.Index l Ω)
      (P : Pairs l Ω X Y (.rational (commonField.{u, u} l Ω i))) :
    commonIso.hom.app (((commonInclusion.{u, u} l Ω X i).op.prod
        (commonInclusion.{u, u} l Ω Y i)).obj P) ≫ (commonRight i).hom.app P =
      (commonLeft i).hom.app P ≫ (commonInclusion.{u, u} l Ω Y i).map
        ((rational (commonField.{u, u} l Ω i)).iso.hom.app P)
  commonShifts : ShiftExchange l Ω .closed
    (commonSource l Ω (R.ring.operation c .closed) commonDirect commonLeftDomain)
    (commonTarget l Ω (R.ring.operation c .closed) commonRightDomain) commonIso
  commonShiftNormalization (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    ShiftNormalization l Ω (rational (commonField.{u, u} l Ω i)).shifts commonShifts
      (commonInclusion.{u, u} l Ω X i) (commonInclusion.{u, u} l Ω Y i)
      (commonInclusion.{u, u} l Ω Y i)
      (R.common.commonComparison c i).shiftX (R.common.commonComparison c i).shiftY
      (R.common.commonComparison c i).shiftY (commonLeft i) (commonRight i)

/-- The canonical Tensor--Hom exchange for the unconditional constructible adjoint,
with naturality in both arguments, both shifts, all finite and integral coefficient
changes, raw rationalization and every common field of definition. The normalized
operation system is supplied in the conclusion, using the published
`ConstructibleExceptionalCoefficients.exists_system`; it is not a hypothesis.
Every compactification specifies a model of `Rf_!`, not admissibility data.
Source: main-20261015, sec-six-functors, sk-thm-sf-tensor-hom
(blueprint: sk-thm-sf-tensor-hom).

Proof, following the node's fifteen steps:
1. On each ringed small site, derive the ordinary tensor--Hom adjunction using
K-flat first arguments and K-injective second arguments; no perfectness is used.
2. For integral coefficients, apply the completion reflector to ordinary tensor.
A derived-complete target identifies maps out of this reflection with maps out of
ordinary tensor. Thus COMPLETED tensor has the required closed adjunction.
3--5. At finite coefficients, use the unconditional constructible adjunction for
Rf_! and f^!. On a finite affine cover, finite constructible Hom, the dimension
bound and fixed Tor intervals show that both Homs and ordinary pushforward remain
bounded constructible of finite Tor amplitude. The finite disjoint refinement
glues constructibility even if the schemes are not separated over the base.
6. Integrally use internal-Hom completeness, its evaluation-defined reduction,
the same finite uniform bounds and integral direct-image constructibility. The
residue-Tor theorem supplies the common integral interval. This gives `integral`.
7--9. For every constructible finite-Tor L on Y, compose the five Hom bijections:
Hom(L,H(FM,N)) = Hom(FM tensor L,N) = Hom(F(M tensor pull L),N)
= Hom(M tensor pull L,GN) = Hom(pull L,H(M,GN))
= Hom(L,direct H(M,GN)). Precompose by the INVERSE projection isomorphism at the
second step. The ordinary and exceptional adjunctions and the closed adjunctions
supply the other steps. Yoneda on the full constructible finite-Tor category gives
the inverse of the displayed bijection as `ring.iso`. The `canonical` field states
its forward-map projection/counit equation after tensor--Hom transposition and
the ordinary adjunction, so the map is fixed, including its sign. At integral
coefficients the completion universal property identifies this equation with the
completed Hom chain. All steps are natural in M,N.
10. Reduce using the actual scalar tensor comparison and evaluation transpose.
The direct-image comparison is the proper counit mate on the etale-origin input.
Integral reduction uses the complete Hom and actual whole-system projection.
11. For finite coefficient fields use the evaluation-normalized finite-free Hom
comparison at retained level en, followed by the prescribed quotient maps.
12. Integral finite-free scalar extension is ordinary tensor by the finite-free
completed coefficient sheaf. K-injective direct image commutes with the resulting
finite biproducts. Compare WHOLE strict systems before taking the homotopy limit.
13. Transpose each coefficient square along the very same five bijections. The
normalized exceptional unit/counit equations, projection comparison and ordinary
counit mate give equal arrows; hence `coefficient` holds for every scalar model.
14. The normalized signed Hom shifts, exact completion, and shift-compatible
units, counits and projection give `firstShift` and `secondShift`. Their composition
gives the b-a shift for simultaneous shifts of M and N.
15. Apply raw scalar localization to the integral inverse pair, extend naturality
from integral arrows to arbitrary scalar tensors and sums, and descend at every
common finite field. The coefficient squares identify enlargements, giving the
common-stage NatIso and its normalization for EVERY index i. No Karoubi completion
or choice of an unrelated isomorphism is introduced. -/
theorem exists_family :
    ∃ R : System.{u, u} l Ω D hl (f := f), ∀ c : Compactification f,
      Nonempty (Family l Ω D hl f R c) := by
  sorry

end Family
end ConstructibleTensorHom
end WeilConjectures
