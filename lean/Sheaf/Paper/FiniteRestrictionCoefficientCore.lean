/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.PointSectionsScalarExtension
public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import Sheaf.Paper.FiniteCounitRestrictionTowers
public import Sheaf.Paper.SfStrictDirectImageScalarComparison
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.CategoryTheory.StageSystemFunctorDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-!
# Integral finite restriction coefficient diagram

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15; the finite-stalk
step of the blueprint finite pushforward proof (blueprint:
def-zl-finite-restriction-integral-diagram).

## Main definitions

- `WeilConjectures.FiniteRestrictionCoefficient.IntegralComparisons`: integral finite
restriction coefficient diagram.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteRestrictionCoefficient
open FiniteCounitTowers
/-- The standard K-injective model on the actual sequence site.
Source: Stacks 079P (blueprint: def-zl-finite-restriction-integral-diagram). -/
instance sequenceKInjectives (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : Scheme.{u}) :
    Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E W) := by
  let : IsGrothendieckAbelian.{u+1} (coefficientSequenceModules l E W) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u+1, u, u+1, u} _ _
  infer_instance

/-- Canonical simultaneous strict derived reduction.
Source: Bhatt--Scholze 6.8.14
(blueprint: def-zl-finite-restriction-integral-diagram). -/
@[irreducible] def reduction (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : Scheme.{u}) :=
  (coefficientDerivedSystemEvaluationCalculus l E W).choose.reduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y)
/-- The exchange source, reconstructed from the whole strict coefficient system.
Source: Stacks 0959 (blueprint: def-zl-finite-restriction-integral-diagram). -/
def source := reduction l E X ⋙ (push l E f ⋙ pull l E y).rightDerivedFunctor ⋙
  coefficientSequenceLimit l E s
/-- The exchange target, reconstructed from the whole strict coefficient system.
Source: Stacks 0959 (blueprint: def-zl-finite-restriction-integral-diagram). -/
def middle := reduction l E X ⋙
  (pull l E (pullback.fst f y) ⋙ push l E (pullback.snd f y)).rightDerivedFunctor ⋙
    coefficientSequenceLimit l E s
/-- The finite family of point inverse images; the empty family gives zero.
Source: Stacks 03QP (blueprint: def-zl-finite-restriction-integral-diagram). -/
def target := reduction l E X ⋙ (pointSum l E f y).rightDerivedFunctor ⋙
  coefficientSequenceLimit l E s
/-- The specified counit-mate exchange on whole derived systems, followed by Rlim.
Source: Stacks 0959 (blueprint: def-zl-finite-restriction-integral-diagram). -/
def exchange : source l E f y ⟶ middle l E f y :=
  Functor.whiskerLeft (reduction l E X)
    (Functor.whiskerRight
      (Functor.rightDerivedFunctorNatTrans (FiniteCounitTowers.exchange l E f y))
      (coefficientSequenceLimit l E s))
/-- The specified family of counit restrictions, followed by Rlim.
Source: Stacks 03QP (blueprint: def-zl-finite-restriction-integral-diagram). -/
def restriction : middle l E f y ⟶ target l E f y :=
  Functor.whiskerLeft (reduction l E X)
    (Functor.whiskerRight
      (Functor.rightDerivedFunctorNatTrans (FiniteCounitTowers.restriction l E f y))
      (coefficientSequenceLimit l E s))

/-- Indices for the source, middle and target of the two actual arrows.
Source: Bhatt--Scholze 6.8.14, finite-fibre step
(blueprint: def-zl-finite-restriction-integral-diagram). -/
inductive Vertex | source | middle | target

/-- The three specified whole-system functors, before constructible restriction.
Source: Stacks 0959, 03QP
(blueprint: def-zl-finite-restriction-integral-diagram). -/
def ambient (q : Vertex) : DerivedCategory (scalarReductionSource l E X) ⥤
    DerivedCategory (scalarReductionSource l E s) :=
  match q with
  | .source => source l E f y
  | .middle => middle l E f y
  | .target => target l E f y

/-- Restriction of this diagram to its actual integral constructible objects.
The inclusion comparison is literal, not a choice of isomorphic objects.
Source: Bhatt--Scholze 6.8.14, 6.8.15
(blueprint: def-zl-finite-restriction-integral-diagram). -/
structure IntegralDiagram where
  preserves : ∀ (q : Vertex) (K : sfIntegralConstructibleCategory l E X),
    sfIntegralConstructible l E s ((ambient l E f y q).obj K.obj)

variable {l E f y}

/-- The actual full-subcategory lift of the canonical whole-system functor.
Source: Bhatt--Scholze 6.8.14
(blueprint: def-zl-finite-restriction-integral-diagram). -/
def IntegralDiagram.functor (I : IntegralDiagram l E f y) (q : Vertex) :=
  (sfIntegralConstructible l E s).lift
    ((sfIntegralConstructible l E X).ι ⋙ ambient l E f y q) (I.preserves q)

/-- The lifted exchange has precisely the already specified ambient component.
Source: Stacks 0959 (blueprint: def-zl-finite-restriction-integral-diagram). -/
def IntegralDiagram.exchange (I : IntegralDiagram l E f y) :
    I.functor .source ⟶ I.functor .middle where
  app K := ObjectProperty.homMk ((FiniteRestrictionCoefficient.exchange l E f y).app K.obj)
  naturality {K M} g := by
    ext : 1
    exact (FiniteRestrictionCoefficient.exchange l E f y).naturality g.hom

/-- The lifted counit restriction has precisely the already specified component.
Source: Stacks 03QP (blueprint: def-zl-finite-restriction-integral-diagram). -/
def IntegralDiagram.restriction (I : IntegralDiagram l E f y) :
    I.functor .middle ⟶ I.functor .target where
  app K := ObjectProperty.homMk ((FiniteRestrictionCoefficient.restriction l E f y).app K.obj)
  naturality {K M} g := by
    ext : 1
    exact (FiniteRestrictionCoefficient.restriction l E f y).naturality g.hom

variable (l f y)
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage integralTransition transition stageSystem)
open TensorProduct

/-- The existing integral coefficient category at a finite field of definition.
Source: Bhatt--Scholze 6.8.14
(blueprint: def-zl-finite-restriction-integral-diagram). -/
abbrev IntegralStage (W : Scheme.{u}) (A : Index l Ω) :=
  sfIntegralConstructibleCategory l (Coefficient.{u} l Ω A) W

/-- The recorded raw localization at a finite stage.
Source: Bhatt--Scholze 6.8.14
(blueprint: def-zl-finite-restriction-integral-diagram). -/
abbrev localization (W : Scheme.{u}) (A : Index l Ω) :=
  sfRationalConstructibleLocalization l (Coefficient.{u} l Ω A) W


attribute [local irreducible] IntegralDiagram.functor IntegralDiagram.exchange
  IntegralDiagram.restriction source middle target ambient
  sfIntegralConstructible sfConstructibleIntegralScalarExtension
  SfStrictDirectImageScalar.integralUnit
  HasDerivedCategory.standard sfIntegralScalarUnit sfRationalScalarComp sfRationalScalarUnit
  GeneralAlgebraicallyClosedCoefficients.associator
  GeneralAlgebraicallyClosedCoefficients.unitor
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
/-- The integral balanced associator, followed by the actual inclusion-composition
identity. No equality between different uniformizer quotient exponents is required.
Source: Bhatt--Scholze 6.8.14; normalized scalar tensor composition
(blueprint: def-zl-finite-restriction-integral-diagram). -/
def integralAssociator (W : Scheme.{u}) (A B C : Index l Ω) (h : A ≤ B) (j : B ≤ C) :
    integralTransition l Ω W A B h ⋙ integralTransition l Ω W B C j ≅
      integralTransition l Ω W A C (h.trans j) :=
  sfIntegralScalarComp l (Coefficient.{u} l Ω A) (Coefficient.{u} l Ω B)
    (coefficientInclusion l Ω A B h) W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
    (Coefficient.{u} l Ω C) (coefficientInclusion l Ω B C j) ≪≫
    eqToIso (congrArg
      (fun i ↦ sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω A)
        (Coefficient.{u} l Ω C) i W)
      ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 A B C h j))

set_option genSizeOf false in
set_option genInjectivity false in
/-- Integral coefficient comparisons and their two actual arrow squares.
The identity comparison is the multiplication unit. The triple comparison uses
balanced tensor multiplication, with the genuine inclusions of finite subfields.
Source: Bhatt--Scholze 6.8.14, 6.8.15; Stacks 099N
(blueprint: def-zl-finite-restriction-integral-diagram). -/
structure IntegralComparisons where
  diagram : ∀ A : Index l Ω, IntegralDiagram l (Coefficient.{u} l Ω A) f y
  beta : ∀ (q : Vertex) (A B : Index l Ω) (h : A ≤ B),
    (diagram A).functor q ⋙ integralTransition l Ω s A B h ≅
      integralTransition l Ω X A B h ⋙ (diagram B).functor q

/-- Identity and both actual arrow squares for integral scalar change.
Source: Bhatt--Scholze 6.8.14, 6.8.15
(blueprint: def-zl-finite-restriction-integral-diagram). -/
def IntegralComparisons.Laws (I : IntegralComparisons l f y Ω) : Prop :=
  (∀ (q : Vertex) (A : Index l Ω) (K : IntegralStage l Ω X A),
    (I.beta q A A le_rfl).hom.app K ≫
        ((I.diagram A).functor q).map
          ((SfStrictDirectImageScalar.integralUnit l Ω X A).hom.app K) =
      (SfStrictDirectImageScalar.integralUnit l Ω s A).hom.app
        (((I.diagram A).functor q).obj K)) ∧
  (∀ (A B : Index l Ω) (h : A ≤ B) (K : IntegralStage l Ω X A),
    (integralTransition l Ω s A B h).map ((I.diagram A).exchange.app K) ≫
        (I.beta .middle A B h).hom.app K =
      (I.beta .source A B h).hom.app K ≫
        (I.diagram B).exchange.app ((integralTransition l Ω X A B h).obj K)) ∧
  (∀ (A B : Index l Ω) (h : A ≤ B) (K : IntegralStage l Ω X A),
    (integralTransition l Ω s A B h).map ((I.diagram A).restriction.app K) ≫
        (I.beta .target A B h).hom.app K =
      (I.beta .middle A B h).hom.app K ≫
        (I.diagram B).restriction.app ((integralTransition l Ω X A B h).obj K))

/-- The full integral coefficient tower equation, before rationalization.
Source: Bhatt--Scholze 6.8.14; balanced tensor associativity
(blueprint: def-zl-finite-restriction-integral-diagram). -/
def IntegralComparisons.Coherent (I : IntegralComparisons l f y Ω) : Prop :=
  ∀ (q : Vertex) (A B C : Index l Ω) (h : A ≤ B) (j : B ≤ C)
    (K : IntegralStage l Ω X A),
    (integralTransition l Ω s B C j).map ((I.beta q A B h).hom.app K) ≫
        (I.beta q B C j).hom.app ((integralTransition l Ω X A B h).obj K) ≫
        ((I.diagram C).functor q).map ((integralAssociator l Ω X A B C h j).hom.app K) =
      (integralAssociator l Ω s A B C h j).hom.app (((I.diagram A).functor q).obj K) ≫
        (I.beta q A C (h.trans j)).hom.app K

end WeilConjectures.FiniteRestrictionCoefficient
