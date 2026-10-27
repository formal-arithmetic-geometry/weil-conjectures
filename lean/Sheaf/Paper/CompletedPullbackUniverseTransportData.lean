/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.Paper.IntegralCompletedTowerPullbackUniverses
public import Sheaf.Paper.SfImmersionCompletedPullbackComparison
public import Sheaf.Paper.CompletedPullbackReduction

/-! # Published completed-pullback universe transport

Source: Stacks 03EK/03EL, 099N(5)
(blueprint: def-a1-completed-pullback-universe-transport-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u r s v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
attribute [local irreducible] WeilConjectures.unrestrictedIntegralReductionFunctor
  WeilConjectures.CompletedTowerIndependent.pull
open WeilConjectures.CompletedTowerIndependent
namespace WeilConjectures.CompletedPullbackUniverseTransportData

/-- A genuine change of module universe: additive equivalences of every section,
commuting with restrictions and with the given coefficient equivalences.
Source: Stacks 03CZ, 03EL (blueprint: def-a1-completed-pullback-universe-transport-data). -/
structure SectionTransport (W : Scheme.{t})
    (R : Sheaf (Scheme.ProEt.topology W) RingCat.{r})
    (S : Sheaf (Scheme.ProEt.topology W) RingCat.{s})
    (coeff : ∀ U : W.ProEtᵒᵖ, R.obj.obj U ≃+* S.obj.obj U)
    (M : SheafOfModules.{v} R) (N : SheafOfModules.{w} S) where
  app : ∀ U : W.ProEtᵒᵖ, M.val.obj U ≃+ N.val.obj U
  naturality : ∀ {U V : W.ProEtᵒᵖ} (f : U ⟶ V) (x : M.val.obj U),
    app V (M.val.map f x) = N.val.map f (app U x)
  smul : ∀ (U : W.ProEtᵒᵖ) (a : R.obj.obj U) (x : M.val.obj U),
    app U (a • x) = coeff U a • app U x


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The recorded ordinary reduction, with its specified completed scalar action.
Source: Stacks 099N(5) (blueprint: def-a1-completed-pullback-universe-transport-data). -/
def ordinaryReduction (W : Scheme.{t}) (n : ℕ) : Modules l E W ⥤ Modules l E W :=
  unrestrictedIntegralReductionFunctor l E W n ⋙
    SheafOfModules.restrictScalars
      (limit.π (integralCoefficientSheafSystem l E W) (op n))

variable {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- The fixed finite pullback of reduction, restricted along the actual projection.
Source: Stacks 099N(5) (blueprint: def-a1-completed-pullback-universe-transport-data). -/
def ordinaryFinite (n : ℕ) : Modules l E Y ⥤ Modules l E X :=
  unrestrictedIntegralReductionFunctor l E Y n ⋙ integralOperationsLevelPullback l E g n ⋙
    SheafOfModules.restrictScalars
      (limit.π (integralCoefficientSheafSystem l E X) (op n))

/-- The ordinary comparison has the fixed quotient-unit value, including every outer scalar.
This is the integral independent-universe form of
HasCompletedReductionOrdinaryComparisonNormalization under the projection-normalized
coefficient transport: b tensor g^-1(x tensor 1) maps to the finite generator times pi(b).
Source: Stacks 03EL (blueprint: def-a1-completed-pullback-universe-transport-data). -/
def OrdinaryNormalization (n : ℕ)
    (e : ordinaryReduction l E Y n ⋙ pull l E g ≅ ordinaryFinite l E g n) : Prop :=
  ∀ (M : Modules l E Y) (V : Y.ProEt) (x : M.val.obj (op V))
      (b : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
        (op ((Scheme.proEtaleBaseChange g).obj V))),
    ((e.hom.app M).val.app (op ((Scheme.proEtaleBaseChange g).obj V)))
      (b • (@id (((pull l E g).obj ((ordinaryReduction l E Y n).obj M)).val.obj
        (op ((Scheme.proEtaleBaseChange g).obj V)))
        ((((adjunction l E g).unit.app ((ordinaryReduction l E Y n).obj M)).val.app
          (op V)) (unrestrictedIntegralTensorSection l E Y n M (op V) 1 x)))) =
      b • (@id (((ordinaryFinite l E g n).obj M).val.obj
        (op ((Scheme.proEtaleBaseChange g).obj V)))
        (integralOperationsPullbackGenerator l E g n
          ((unrestrictedIntegralReductionFunctor l E Y n).obj M) V
          (unrestrictedIntegralTensorSection l E Y n M (op V) 1 x)))


/-- Sectionwise coefficient transport across the two independent universes.
It preserves every restriction, finite projection, and structural map. Thus it is
an isomorphism of the actual ringed coefficient systems. Its completed and finite
components factor through the recorded ImmersionCompletedPullback coefficient isomorphisms.
Restriction along the inverse completed component is precisely the published transport.
Source: Stacks 03EL, 099N(5)
(blueprint: def-a1-completed-pullback-universe-transport-data). -/
structure PublishedCoefficients (F : Type t) [Field F] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) F] where
  completed : ∀ (W : Scheme.{t}) (U : W.ProEtᵒᵖ),
    (Scheme.pbcAdicCompletion W (pbcIntegralDatum l F)).obj.obj U ≃+*
      (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U
  quotient : ∀ (W : Scheme.{t}) (n : ℕ) (U : W.ProEtᵒᵖ),
    (Scheme.reductionCoefficient W (pbcIntegralDatum l F) n).obj.obj U ≃+*
      (integralCoefficientSheaf l E W n).obj.obj U
  integralCompleted : ∀ (W : Scheme.{t}) (U : W.ProEtᵒᵖ),
    (completedIntegralCoefficientSheafUnrestricted l F W).obj.obj U ≃+*
      (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U
  integralQuotient : ∀ (W : Scheme.{t}) (n : ℕ) (U : W.ProEtᵒᵖ),
    (integralCoefficientSheaf l F W n).obj.obj U ≃+*
      (integralCoefficientSheaf l E W n).obj.obj U
  completed_transport : ∀ (W : Scheme.{t}) (U : W.ProEtᵒᵖ)
      (a : (Scheme.pbcAdicCompletion W (pbcIntegralDatum l F)).obj.obj U),
    completed W U a = integralCompleted W U
      ((ImmersionCompletedPullback.completedRingIso l F W).hom.hom.app U a)
  quotient_transport : ∀ (W : Scheme.{t}) (n : ℕ) (U : W.ProEtᵒᵖ)
      (a : (Scheme.reductionCoefficient W (pbcIntegralDatum l F) n).obj.obj U),
    quotient W n U a = integralQuotient W n U
      ((ImmersionCompletedPullback.finiteRingIso l F W n).hom.hom.app U a)
  completed_naturality : ∀ (W : Scheme.{t}) {U V : W.ProEtᵒᵖ} (f : U ⟶ V)
      (a : (Scheme.pbcAdicCompletion W (pbcIntegralDatum l F)).obj.obj U),
    completed W V ((Scheme.pbcAdicCompletion W (pbcIntegralDatum l F)).obj.map f a) =
      (completedIntegralCoefficientSheafUnrestricted l E W).obj.map f (completed W U a)
  quotient_naturality : ∀ (W : Scheme.{t}) (n : ℕ) {U V : W.ProEtᵒᵖ} (f : U ⟶ V)
      (a : (Scheme.reductionCoefficient W (pbcIntegralDatum l F) n).obj.obj U),
    quotient W n V ((Scheme.reductionCoefficient W (pbcIntegralDatum l F) n).obj.map f a) =
      (integralCoefficientSheaf l E W n).obj.map f (quotient W n U a)
  projection : ∀ (W : Scheme.{t}) (n : ℕ) (U : W.ProEtᵒᵖ)
      (a : (Scheme.pbcAdicCompletion W (pbcIntegralDatum l F)).obj.obj U),
    quotient W n U ((Scheme.completedReductionProjection W (pbcIntegralDatum l F) n).hom.app
      U a) = (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom.app U
        (completed W U a)
  structural : ∀ {W Z : Scheme.{t}} (f : W ⟶ Z) (V : Z.ProEt)
      (a : (Scheme.pbcAdicCompletion Z (pbcIntegralDatum l F)).obj.obj (op V)),
    completed W (op ((Scheme.proEtaleBaseChange f).obj V))
      ((((Scheme.proEtaleSheafAdjunction f CommRingCat.{t + 1}).homEquiv _ _)
        (Scheme.completedCoefficientMap f (pbcIntegralDatum l F))).hom.app (op V) a) =
      (directRingMap l E f).hom.app (op V) (completed Z (op V) a)

/-- Published ordinary source, with its genuine quotient tower and pullback.
Source: Stacks 099N(5)
(blueprint: def-a1-completed-pullback-universe-transport-data). -/
def publishedSource (F : Type t) [Field F] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) F] (n : ℕ) :
    Scheme.pbcModules Y (Scheme.pbcAdicCompletion Y (pbcIntegralDatum l F)) ⥤
      Scheme.pbcModules X (Scheme.pbcAdicCompletion X (pbcIntegralDatum l F)) :=
  Scheme.completedReductionModuleTowerFunctor Y (pbcIntegralDatum l F) ⋙
    Scheme.completedTowerModulePullback g (pbcIntegralDatum l F) ⋙
      (CategoryTheory.evaluation ℕᵒᵖ
        (Scheme.pbcModules X (Scheme.pbcAdicCompletion X (pbcIntegralDatum l F)))).obj (op n)

/-- Published finite target, restricted along its specified projection.
Source: Stacks 099N(5)
(blueprint: def-a1-completed-pullback-universe-transport-data). -/
def publishedTarget (F : Type t) [Field F] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) F] (n : ℕ) :
    Scheme.pbcModules Y (Scheme.pbcAdicCompletion Y (pbcIntegralDatum l F)) ⥤
      Scheme.pbcModules X (Scheme.pbcAdicCompletion X (pbcIntegralDatum l F)) :=
  Scheme.reductionChange Y (Scheme.completedReductionProjection Y (pbcIntegralDatum l F) n) ⋙
    Scheme.completedReductionFiniteModules g (pbcIntegralDatum l F) n ⋙
      SheafOfModules.restrictScalars
        ((Scheme.adicLisseForget X).map
          (Scheme.completedReductionProjection X (pbcIntegralDatum l F) n))


/-- The pulled quotient-unit generator at an arbitrary target site object.
Source: Stacks 03EL
(blueprint: def-a1-completed-pullback-universe-transport-data). -/
def ordinarySourceGenerator (n : ℕ) (M : Modules l E Y) (V : Y.ProEt) (U : X.ProEt)
    (f : U ⟶ (Scheme.proEtaleBaseChange g).obj V)
    (b : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj (op U))
    (x : M.val.obj (op V)) :
    (((ordinaryReduction l E Y n ⋙ pull l E g).obj M).val.obj (op U)) :=
  b • (((pull l E g).obj ((ordinaryReduction l E Y n).obj M)).val.map f.op
    ((((adjunction l E g).unit.app ((ordinaryReduction l E Y n).obj M)).val.app
      (op V) (unrestrictedIntegralTensorSection l E Y n M (op V) 1 x))))

/-- A transport of the published ordinary comparison's source and target.
Both section equivalences commute with restrictions and scalars. The two explicit
unit formulas uniquely pin them on sheafified tensor generators, across universes.
Source: Stacks 03EK/03EL, published finite generators
(blueprint: def-a1-completed-pullback-universe-transport-data). -/
structure PublishedOrdinaryTransport (F : Type t) [Field F] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) F] (p : PublishedCoefficients l E F) (n : ℕ)
    (M₀ : Scheme.pbcModules Y (Scheme.pbcAdicCompletion Y (pbcIntegralDatum l F)))
    (M : Modules l E Y)
    (m : SectionTransport Y _ _ (p.completed Y) M₀ M) where
  source : SectionTransport X _ _ (p.completed X)
    ((publishedSource l g F n).obj M₀) ((ordinaryReduction l E Y n ⋙ pull l E g).obj M)
  target : SectionTransport X _ _ (p.completed X)
    ((publishedTarget l g F n).obj M₀) ((ordinaryFinite l E g n).obj M)
  source_unit : ∀ (V : Y.ProEt) (U : X.ProEt)
      (f : U ⟶ (Scheme.proEtaleBaseChange g).obj V)
      (b : (Scheme.pbcAdicCompletion X (pbcIntegralDatum l F)).obj.obj (op U))
      (x : M₀.val.obj (op V)),
    source.app (op U)
      (Scheme.reductionTensorSection X (Scheme.completedCoefficientMap g (pbcIntegralDatum l F))
        _ (op U) b
        (Scheme.completedReductionInverseImageGenerator g
          (Scheme.pbcAdicCompletion Y (pbcIntegralDatum l F))
          (((Scheme.completedReductionModuleTowerFunctor Y (pbcIntegralDatum l F)).obj M₀).obj
            (op n)) V U f
          ((((Scheme.completedReductionModuleUnit (pbcIntegralDatum l F) Y).app M₀).app
            (op n)).val.app (op V) x))) =
      ordinarySourceGenerator l E g n M V U f
        (p.completed X (op U) b) (m.app (op V) x)
  target_tensor : ∀ (V : Y.ProEt) (U : X.ProEt)
      (f : U ⟶ (Scheme.proEtaleBaseChange g).obj V)
      (s : (Scheme.reductionCoefficient X (pbcIntegralDatum l F) n).obj.obj (op U))
      (z : (Scheme.reductionCoefficient Y (pbcIntegralDatum l F) n).obj.obj (op V))
      (x : M₀.val.obj (op V)),
    target.app (op U)
      (Scheme.completedReductionFiniteGenerator g (pbcIntegralDatum l F) n M₀ V U f s z x) =
      (@id (((ordinaryFinite l E g n).obj M).val.obj (op U))
        ((p.quotient X n (op U) s) •
          (((integralOperationsLevelPullback l E g n).obj
            ((unrestrictedIntegralReductionFunctor l E Y n).obj M)).val.map f.op
            (integralOperationsPullbackGenerator l E g n
              ((unrestrictedIntegralReductionFunctor l E Y n).obj M) V
              (unrestrictedIntegralTensorSection l E Y n M (op V)
                (p.quotient Y n (op V) z) (m.app (op V) x))))))

/-- Literal conjugation to the published completedReductionOrdinaryComparison.
This quantifies over actual sectionwise universe transports, normalized on every
source unit and target tensor; it cannot hide a finite-evaluation automorphism.
Source: Stacks 03EL, 099N(5)
(blueprint: def-a1-completed-pullback-universe-transport-data). -/
def PublishedCompatibility (n : ℕ)
    (e : ordinaryReduction l E Y n ⋙ pull l E g ≅ ordinaryFinite l E g n) : Prop :=
  ∀ (F : Type t) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (p : PublishedCoefficients l E F)
    (M₀ : Scheme.pbcModules Y (Scheme.pbcAdicCompletion Y (pbcIntegralDatum l F)))
    (M : Modules l E Y) (m : SectionTransport Y _ _ (p.completed Y) M₀ M),
    ∃! tr : PublishedOrdinaryTransport l E g F p n M₀ M m,
      ∀ (U : X.ProEtᵒᵖ) (x : ((publishedSource l g F n).obj M₀).val.obj U),
        tr.target.app U
          (((Scheme.completedReductionOrdinaryComparison g (pbcIntegralDatum l F) n).hom.app
            M₀).val.app U x) =
          (e.hom.app M).val.app U (tr.source.app U x)

end WeilConjectures.CompletedPullbackUniverseTransportData
