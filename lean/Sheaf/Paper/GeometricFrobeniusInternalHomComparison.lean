/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module


public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.SixFunctors.SchemeFrobenius
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SitePerfectComplex
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.SixFunctors.InternalHomPullback

import Sheaf.Paper.IntegralConstructibleInternalHom
import Sheaf.SixFunctors.CoefMonoidalSquareHomTransport
import Sheaf.Paper.IsomorphismDerivedPullback
import Sheaf.AlgebraicGeometry.IsomorphismDerivedPullbackEquivalence
import Sheaf.CategoryTheory.MateIsoAlongEquivalences
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import WeilConjectures.SixFunctors.Etale.Derived.Exchange
import Sheaf.Paper.BasicOperationsCoefficientReduction
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.InternalHomPullback
import Sheaf.Paper.SfRationalizationKaroubi



/-!
# Geometric Frobenius and internal Hom

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
`sk-def-sf-weil-complexes/def-pod-dual-tate-datum.md`, first displayed arrow
(blueprint: lem-pod-geometric-frobenius-internal-hom-comparison).

The comparison is the tensor--Hom transpose of the evaluation map after the
specified pullback tensor isomorphism.  The same transpose is used at finite,
completed integral, rational, and common-stage coefficients; the postponed
statement records its naturality and all quotient and scalar-extension squares.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option warn.sorry false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option linter.all false
set_option linter.unusedVariables false

universe u v a b c d

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open WeilConjectures

namespace WeilConjectures

/-- The finite-level transpose occurring in the Frobenius comparison.
Source: the first displayed arrow of `def-pod-dual-tate-datum` (blueprint:
lem-pod-geometric-frobenius-internal-hom-comparison). -/
noncomputable def finiteGeometricFrobeniusInternalHomComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X : Scheme.{u}} (g : X ⟶ X) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    (M N : normalizedDVRDerived l E X n) :
    (finiteDerivedPullback l E n g).obj
        ((finiteIntrinsicDerivedInternalHom l E X n).obj (op M, N)) ⟶
      (finiteIntrinsicDerivedInternalHom l E X n).obj
        (op ((finiteDerivedPullback l E n g).obj M),
          (finiteDerivedPullback l E n g).obj N) :=
  finiteIntrinsicTranspose l E X n
      ((finiteDerivedPullback l E n g).obj
        ((finiteIntrinsicDerivedInternalHom l E X n).obj (op M, N)))
      ((finiteDerivedPullback l E n g).obj M)
      ((finiteDerivedPullback l E n g).obj N)
      ((canonicalFinitePullbackTensor l E g n
        ((finiteIntrinsicDerivedInternalHom l E X n).obj (op M, N)) M).inv ≫
        (finiteDerivedPullback l E n g).map
          (finiteIntrinsicEvaluation l E X n M N))

/-- Explicit comparison laws on the recorded domain of permitted Hom pairs.
All fields constrain actual arrows; evaluation is normalized separately below.
Source: `def-pod-dual-tate-datum`, first arrow and coefficient paragraphs
(blueprint: lem-pod-geometric-frobenius-internal-hom-comparison). -/
structure FrobeniusHomStage
    {C : Type a} [Category.{b} C] (P : ObjectProperty (Cᵒᵖ × C))
    (H : P.FullSubcategory ⥤ C) (F : C ⥤ C) (T : C × C ⥤ C)
    (μ : ∀ M N : C, F.obj (T.obj (M, N)) ≅ T.obj (F.obj M, F.obj N)) where
  pullback_permitted : ∀ p : P.FullSubcategory,
    P (op (F.obj p.obj.1.unop), F.obj p.obj.2)
  evaluation : ∀ p : P.FullSubcategory, T.obj (H.obj p, p.obj.1.unop) ⟶ p.obj.2
  comparison : ∀ p : P.FullSubcategory,
    F.obj (H.obj p) ⟶ H.obj
      ⟨(op (F.obj p.obj.1.unop), F.obj p.obj.2), pullback_permitted p⟩
  comparison_isIso : ∀ p, IsIso (comparison p)
  naturality : ∀ (p q : P.FullSubcategory)
    (f : q.obj.1.unop ⟶ p.obj.1.unop) (h : p.obj.2 ⟶ q.obj.2),
    F.map (H.map (ObjectProperty.homMk (Prod.mkHom f.op h))) ≫ comparison q =
      comparison p ≫ H.map (ObjectProperty.homMk
        (Prod.mkHom (F.map f).op (F.map h)))
  evaluation_identity : ∀ p : P.FullSubcategory,
    T.map (Prod.mkHom (comparison p) (𝟙 _)) ≫
      evaluation ⟨(op (F.obj p.obj.1.unop), F.obj p.obj.2), pullback_permitted p⟩ =
    (μ (H.obj p) p.obj.1.unop).inv ≫ F.map (evaluation p)
  comparison_unique : ∀ (p : P.FullSubcategory)
    (c : F.obj (H.obj p) ⟶ H.obj
      ⟨(op (F.obj p.obj.1.unop), F.obj p.obj.2), pullback_permitted p⟩),
    T.map (Prod.mkHom c (𝟙 _)) ≫
        evaluation ⟨(op (F.obj p.obj.1.unop), F.obj p.obj.2), pullback_permitted p⟩ =
      (μ (H.obj p) p.obj.1.unop).inv ≫ F.map (evaluation p) → c = comparison p

/-- The pulled permitted pair, including its proven domain membership.
Source: `def-pod-dual-tate-datum`, first arrow
(blueprint: lem-pod-geometric-frobenius-internal-hom-comparison). -/
def FrobeniusHomStage.pullbackPair
    {C : Type a} [Category.{b} C] {P : ObjectProperty (Cᵒᵖ × C)}
    {H : P.FullSubcategory ⥤ C} {F : C ⥤ C} {T : C × C ⥤ C}
    {μ : ∀ M N : C, F.obj (T.obj (M, N)) ≅ T.obj (F.obj M, F.obj N)}
    (s : FrobeniusHomStage P H F T μ) (p : P.FullSubcategory) : P.FullSubcategory :=
  ⟨(op (F.obj p.obj.1.unop), F.obj p.obj.2), s.pullback_permitted p⟩

section CoefficientStages
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : Scheme.{u}) (g : X ⟶ X)
  [hX : ∀ x : X, Invertible (l : X.residueField x)]

/-- The integral laws use completed tensor and the ambient integral Hom on its
recorded constructible-pair domain.
Source: `def-pod-dual-tate-datum`, integral paragraph
(blueprint: lem-pod-geometric-frobenius-internal-hom-comparison). -/
abbrev FrobeniusIntegralHomStage :=
  FrobeniusHomStage (constructibleIntegralHomPairs l E X)
    (constructibleIntegralHom l E X) (constructibleIntegralPullback l E g)
    (constructibleIntegralTensor l E X) (canonicalIntegralPullbackTensor l E g)

/-- The rational laws use the raw scalar localization, without a perfect lattice
hypothesis or a Karoubi completion.
Source: `def-pod-dual-tate-datum`, rational paragraph
(blueprint: lem-pod-geometric-frobenius-internal-hom-comparison). -/
abbrev FrobeniusRationalHomStage :=
  FrobeniusHomStage (constructibleRationalHomPairs l E X)
    (rationalDerivedInternalHom l E X) (rationalDerivedPullback l E g)
    (rationalDerivedTensor l E X) (canonicalRationalPullbackTensor l E g)

/-- Integral evaluation is fixed in the coherent system category, before any
finite projection: reduce Hom, evaluate, and apply the specified total limit.
Composing with the reconstruction unit fixes the unique map into a complete target.
Source: `def-pod-dual-tate-datum`, integral paragraph; Stacks 0941 and 08J9
(blueprint: lem-pod-geometric-frobenius-internal-hom-comparison). -/
def FrobeniusIntegralEvaluationNormalized (s : FrobeniusIntegralHomStage l E X g) : Prop :=
  ∀ p : (constructibleIntegralHomPairs l E X).FullSubcategory,
    (s.evaluation p).hom ≫
      (pullbackTensorCalculus l E X).adjunction.unit.app p.obj.2.obj =
    (pullbackTensorIntegralTensorModel l E X).hom.app
        (((constructibleIntegralHom l E X).obj p).obj, p.obj.1.unop.obj) ≫
      (coefficientSequenceLimit l E X).map
        ((pullbackTensorCalculus l E X).systemClosed.tensor.map
          (Prod.mkHom
            (coefficientBaseChangeHom (pullbackTensorCalculus l E X).integralClosed
              (pullbackTensorCalculus l E X).systemClosed
              (pullbackTensorCalculus l E X).reduction
              (pullbackTensorCalculus l E X).reductionTensor
              p.obj.1.unop.obj p.obj.2.obj) (𝟙 _)) ≫
          (pullbackTensorCalculus l E X).systemClosed.evaluation
            ((pullbackTensorCalculus l E X).reduction.obj p.obj.1.unop.obj)
            ((pullbackTensorCalculus l E X).reduction.obj p.obj.2.obj))

/-- Canonical integral-to-finite pullback comparison, using the coherent counit
and the recorded exact evaluation comparison, rather than an arbitrary isomorphism.
Source: `def-pod-dual-tate-datum`, reduction paragraph; Stacks 0941
(blueprint: lem-pod-geometric-frobenius-internal-hom-comparison). -/
def frobeniusIntegralReductionPullback (n : ℕ)
    (M : sfIntegralConstructibleCategory l E X) :
    (coefficientFiniteDerivedExtension l E X n).obj
        ((constructibleIntegralPullback l E g).obj M).obj ≅
      (finiteDerivedPullback l E n g).obj
        ((coefficientFiniteDerivedExtension l E X n).obj M.obj) :=
  (((pullbackTensorCalculus l E X).reductionEvaluation n).app _).symm ≪≫
    (coefficientSequenceDerivedEvaluation l E X n).mapIso
      (pullbackTensorIntegralReductionPullback l E g M) ≪≫
    (pullbackTensorDerivedEvaluation l E g n).app _ ≪≫
    (finiteDerivedPullback l E n g).mapIso
      (((pullbackTensorCalculus l E X).reductionEvaluation n).app M.obj)

/-- The canonical reduction/internal-Hom arrow, transposing reduced ambient evaluation.
Source: `def-pod-dual-tate-datum`, reduction paragraph; Stacks 08J9
(blueprint: lem-pod-geometric-frobenius-internal-hom-comparison). -/
def frobeniusIntegralReductionHom (n : ℕ)
    (M N : sfIntegralConstructibleCategory l E X) :=
  coefficientBaseChangeHom (pullbackTensorCalculus l E X).integralClosed
    ((pullbackTensorCalculus l E X).finiteClosed n)
    (coefficientFiniteDerivedExtension l E X n)
    ((pullbackTensorCalculus l E X).finiteTensor n) M.obj N.obj

end CoefficientStages

/-- The coefficient-change square for the specified comparison, including the inverse
of the pullback comparison in the contravariant slot of Hom.
Source: `def-pod-dual-tate-datum`, scalar-extension paragraph
(blueprint: lem-pod-geometric-frobenius-internal-hom-comparison). -/
def FrobeniusHomScalarSquare
    {C : Type a} [Category.{b} C] {D : Type u} [Category.{v} D]
    {P : ObjectProperty (Cᵒᵖ × C)} {Q : ObjectProperty (Dᵒᵖ × D)}
    {H : P.FullSubcategory ⥤ C} {H' : Q.FullSubcategory ⥤ D}
    {F : C ⥤ C} {F' : D ⥤ D} {T : C × C ⥤ C} {T' : D × D ⥤ D}
    {μ : ∀ M N, F.obj (T.obj (M, N)) ≅ T.obj (F.obj M, F.obj N)}
    {μ' : ∀ M N, F'.obj (T'.obj (M, N)) ≅ T'.obj (F'.obj M, F'.obj N)}
    (s : FrobeniusHomStage P H F T μ) (s' : FrobeniusHomStage Q H' F' T' μ')
    (S : C ⥤ D) (ρ : ∀ M, S.obj (F.obj M) ≅ F'.obj (S.obj M))
    (q : ∀ p : P.FullSubcategory, Q (op (S.obj p.obj.1.unop), S.obj p.obj.2))
    (β : ∀ p : P.FullSubcategory, S.obj (H.obj p) ≅
      H'.obj ⟨(op (S.obj p.obj.1.unop), S.obj p.obj.2), q p⟩) : Prop :=
  ∀ p : P.FullSubcategory,
    S.map (s.comparison p) ≫ (β (s.pullbackPair p)).hom ≫
      H'.map
        (X := ⟨(op (S.obj (F.obj p.obj.1.unop)), S.obj (F.obj p.obj.2)),
          q (s.pullbackPair p)⟩)
        (Y := s'.pullbackPair
          ⟨(op (S.obj p.obj.1.unop), S.obj p.obj.2), q p⟩)
        (ObjectProperty.homMk
          (Prod.mkHom (ρ p.obj.1.unop).inv.op (ρ p.obj.2).hom)) =
    (ρ (H.obj p)).hom ≫ F'.map (β p).hom ≫
      s'.comparison ⟨(op (S.obj p.obj.1.unop), S.obj p.obj.2), q p⟩

/-- Finite Frobenius laws constrain the explicit transpose, including both variances
and the evaluation equation, at every positive quotient.
Source: `def-pod-dual-tate-datum`, finite comparison
(blueprint: lem-pod-geometric-frobenius-internal-hom-comparison). -/
def FrobeniusFiniteHomLaws
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (g : X ⟶ X) (n : ℕ)
    [∀ x : X, Invertible (l : X.residueField x)] : Prop :=
  (∀ M N : normalizedDVRDerived l E X n,
    IsIso (finiteGeometricFrobeniusInternalHomComparison l E g n M N)) ∧
  (∀ (M M' N N' : normalizedDVRDerived l E X n) (a : M' ⟶ M) (b : N ⟶ N'),
    (finiteDerivedPullback l E n g).map
        ((finiteIntrinsicDerivedInternalHom l E X n).map (Prod.mkHom a.op b)) ≫
      finiteGeometricFrobeniusInternalHomComparison l E g n M' N' =
    finiteGeometricFrobeniusInternalHomComparison l E g n M N ≫
      (finiteIntrinsicDerivedInternalHom l E X n).map
        (Prod.mkHom ((finiteDerivedPullback l E n g).map a).op
          ((finiteDerivedPullback l E n g).map b))) ∧
  (∀ M N : normalizedDVRDerived l E X n,
    (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom (finiteGeometricFrobeniusInternalHomComparison l E g n M N) (𝟙 _)) ≫
      finiteIntrinsicEvaluation l E X n
        ((finiteDerivedPullback l E n g).obj M) ((finiteDerivedPullback l E n g).obj N) =
    (canonicalFinitePullbackTensor l E g n
        ((finiteIntrinsicDerivedInternalHom l E X n).obj (op M, N)) M).inv ≫
      (finiteDerivedPullback l E n g).map (finiteIntrinsicEvaluation l E X n M N))

section CommonStageRepresentatives
open GeneralAlgebraicallyClosedCoefficients
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (X : Scheme.{u}) (g : X ⟶ X)
  [hX : ∀ x : X, Invertible (l : X.residueField x)]

/-- Equality-only transport of an object to a larger coefficient stage.
Source: `def-pod-dual-tate-datum`, common-stage paragraph
(blueprint: lem-pod-geometric-frobenius-internal-hom-comparison). -/
def frobeniusToStageEq
    {A B : generalAlgebraicallyClosedConstructibleCategory l Ω X} (e : A = B)
    (L : WeilConjectures.AlgebraicallyClosedCoefficients.Index l Ω) (h : A.stage ≤ L) :
    A.toStage h ≅ B.toStage
      ((congrArg (fun C : generalAlgebraicallyClosedConstructibleCategory l Ω X ↦
        C.stage ≤ L) e).mp h) :=
  match e with
  | rfl => Iso.refl _

/-- Transport a stage bound along the prescribed pullback object equality.
Source: `def-pod-dual-tate-datum`, common-stage paragraph
(blueprint: lem-pod-geometric-frobenius-internal-hom-comparison). -/
abbrev frobeniusCommonPullbackBound
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω X) (L :
      WeilConjectures.AlgebraicallyClosedCoefficients.Index l Ω)
    (h : ((commonStageDerivedPullback l Ω g).obj M).stage ≤ L) : M.stage ≤ L :=
  (congrArg (fun A : generalAlgebraicallyClosedConstructibleCategory l Ω X ↦ A.stage ≤ L)
    ((commonStageDerivedPullback_existsUnique l Ω g).exists.choose_spec.1 M)).mp h

/-- The actual pullback object at a stage, with only equality transport followed
by the recorded canonical comparison. The data are not chosen from mere existence.
Source: `def-pod-dual-tate-datum`, common-stage paragraph
(blueprint: lem-pod-geometric-frobenius-internal-hom-comparison). -/
def frobeniusCommonPullbackAtStage
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω X) (L :
      WeilConjectures.AlgebraicallyClosedCoefficients.Index l Ω)
    (h : ((commonStageDerivedPullback l Ω g).obj M).stage ≤ L) :
    ((commonStageDerivedPullback l Ω g).obj M).toStage h ≅
      (rationalDerivedPullback l (WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l
        Ω L) g).obj
        (M.toStage (frobeniusCommonPullbackBound l Ω X g M L h)) :=
  frobeniusToStageEq l Ω X
    ((commonStageDerivedPullback_existsUnique l Ω g).exists.choose_spec.1 M) L h ≪≫
    commonStagePullbackComparison l Ω g M L (frobeniusCommonPullbackBound l Ω X g M L h)

/-- Transport a bound along the recorded internal-Hom object equality.
Source: `def-pod-dual-tate-datum`, common-stage paragraph
(blueprint: lem-pod-geometric-frobenius-internal-hom-comparison). -/
abbrev frobeniusCommonHomBound (p : (commonStageHomPairs l Ω X).FullSubcategory)
    (L : WeilConjectures.AlgebraicallyClosedCoefficients.Index l Ω) (h :
      ((commonStageDerivedInternalHom l Ω X).obj p).stage ≤ L) :
    (commonStageHomObject l Ω X p).stage ≤ L :=
  (congrArg (fun A : generalAlgebraicallyClosedConstructibleCategory l Ω X ↦ A.stage ≤ L)
    ((commonStageDerivedInternalHom_existsUnique l Ω X).exists.choose_spec.1 p)).mp h

/-- Canonical Hom comparison for the actual functor object, including the inverse
first-variable scalar associator built into `commonStageHomComparison`.
Source: `def-pod-dual-tate-datum`, common-stage paragraph
(blueprint: lem-pod-geometric-frobenius-internal-hom-comparison). -/
def frobeniusCommonHomAtStage (p : (commonStageHomPairs l Ω X).FullSubcategory)
    (L : WeilConjectures.AlgebraicallyClosedCoefficients.Index l Ω) (h :
      ((commonStageDerivedInternalHom l Ω X).obj p).stage ≤ L) :
    ((commonStageDerivedInternalHom l Ω X).obj p).toStage h ≅
      (rationalDerivedInternalHom l (WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u}
        l Ω L) X).obj
        (commonStageHomPairAtStage l Ω X p L (frobeniusCommonHomBound l Ω X p L h)) :=
  frobeniusToStageEq l Ω X
    ((commonStageDerivedInternalHom_existsUnique l Ω X).exists.choose_spec.1 p) L h ≪≫
    commonStageHomComparison l Ω X p L (frobeniusCommonHomBound l Ω X p L h)

/-- Transport a stage bound along the recorded tensor object formula.
Source: `def-pod-dual-tate-datum`, common-stage paragraph
(blueprint: lem-pod-geometric-frobenius-internal-hom-comparison). -/
abbrev frobeniusCommonTensorBound
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω X) (L :
      WeilConjectures.AlgebraicallyClosedCoefficients.Index l Ω)
    (h : ((commonStageDerivedTensor l Ω X).obj (M, N)).stage ≤ L) :
    (commonStageTensorObject l Ω X M N).stage ≤ L :=
  (congrArg (fun A : generalAlgebraicallyClosedConstructibleCategory l Ω X ↦ A.stage ≤ L)
    ((commonStageDerivedTensor_existsUnique l Ω X).exists.choose_spec.1 M N)).mp h

/-- The canonical common-stage tensor comparison with equality-only object transport.
Source: `def-pod-dual-tate-datum`, common-stage paragraph
(blueprint: lem-pod-geometric-frobenius-internal-hom-comparison). -/
def frobeniusCommonTensorAtStage
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω X) (L :
      WeilConjectures.AlgebraicallyClosedCoefficients.Index l Ω)
    (h : ((commonStageDerivedTensor l Ω X).obj (M, N)).stage ≤ L) :
    ((commonStageDerivedTensor l Ω X).obj (M, N)).toStage h ≅
      (rationalDerivedTensor l (WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
        L) X).obj
        (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).1.trans
          (frobeniusCommonTensorBound l Ω X M N L h)),
        N.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).2.trans
          (frobeniusCommonTensorBound l Ω X M N L h))) :=
  frobeniusToStageEq l Ω X
    ((commonStageDerivedTensor_existsUnique l Ω X).exists.choose_spec.1 M N) L h ≪≫
    commonStageTensorComparison l Ω X M N L (frobeniusCommonTensorBound l Ω X M N L h)

/-- Evaluation at any larger finite field: tensor comparison, Hom comparison,
then the rational evaluation. All object transports are fixed above.
Source: `def-pod-dual-tate-datum`, common-stage paragraph
(blueprint: lem-pod-geometric-frobenius-internal-hom-comparison). -/
def frobeniusCommonEvaluationAtStage
    (r : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      FrobeniusRationalHomStage l E X g)
    (p : (commonStageHomPairs l Ω X).FullSubcategory) (L :
      WeilConjectures.AlgebraicallyClosedCoefficients.Index l Ω)
    (hA : ((commonStageDerivedTensor l Ω X).obj
      ((commonStageDerivedInternalHom l Ω X).obj p, p.obj.1.unop)).stage ≤ L)
    (hN : p.obj.2.stage ≤ L) :
    ((commonStageDerivedTensor l Ω X).obj
      ((commonStageDerivedInternalHom l Ω X).obj p, p.obj.1.unop)).toStage hA ⟶
      p.obj.2.toStage hN :=
  let hH := ((Padic.finiteCoefficientFields_properties l Ω).1
    ((commonStageDerivedInternalHom l Ω X).obj p).stage p.obj.1.unop.stage).1.trans
      (frobeniusCommonTensorBound l Ω X _ _ L hA)
  let hp := frobeniusCommonHomBound l Ω X p L hH
  (frobeniusCommonTensorAtStage l Ω X _ _ L hA).hom ≫
    (rationalDerivedTensor l (WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
      X).map
      (Prod.mkHom (frobeniusCommonHomAtStage l Ω X p L hH).hom (𝟙 _)) ≫
    (r (WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).evaluation
      (commonStageHomPairAtStage l Ω X p L hp)

/-- The rational comparison transported to the actual source and target at any
common field. The inverse comparison is in the target's covariant Hom slot.
Source: `def-pod-dual-tate-datum`, common-stage paragraph
(blueprint: lem-pod-geometric-frobenius-internal-hom-comparison). -/
def frobeniusCommonComparisonAtStage
    (r : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      FrobeniusRationalHomStage l E X g)
    (s : FrobeniusHomStage (commonStageHomPairs l Ω X)
      (commonStageDerivedInternalHom l Ω X) (commonStageDerivedPullback l Ω g)
      (commonStageDerivedTensor l Ω X) (canonicalCommonStagePullbackTensor l Ω g))
    (p : (commonStageHomPairs l Ω X).FullSubcategory) (L :
      WeilConjectures.AlgebraicallyClosedCoefficients.Index l Ω)
    (hA : ((commonStageDerivedPullback l Ω g).obj
      ((commonStageDerivedInternalHom l Ω X).obj p)).stage ≤ L)
    (hB : ((commonStageDerivedInternalHom l Ω X).obj (s.pullbackPair p)).stage ≤ L) :
    ((commonStageDerivedPullback l Ω g).obj
        ((commonStageDerivedInternalHom l Ω X).obj p)).toStage hA ⟶
      ((commonStageDerivedInternalHom l Ω X).obj (s.pullbackPair p)).toStage hB :=
  let hH := frobeniusCommonPullbackBound l Ω X g _ L hA
  let hp := frobeniusCommonHomBound l Ω X p L hH
  let pL := commonStageHomPairAtStage l Ω X p L hp
  let pF := s.pullbackPair p
  let hpF := frobeniusCommonHomBound l Ω X pF L hB
  let hM := ((Padic.finiteCoefficientFields_properties l Ω).1
    pF.obj.1.unop.stage pF.obj.2.stage).1.trans hpF
  let hN := ((Padic.finiteCoefficientFields_properties l Ω).1
    pF.obj.1.unop.stage pF.obj.2.stage).2.trans hpF
  (frobeniusCommonPullbackAtStage l Ω X g _ L hA).hom ≫
    (rationalDerivedPullback l (WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
      L) g).map
      (frobeniusCommonHomAtStage l Ω X p L hH).hom ≫
    (r (WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).comparison pL ≫
    (rationalDerivedInternalHom l (WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l
      Ω L) X).map
      (X := (r (WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).pullbackPair
        pL)
      (Y := commonStageHomPairAtStage l Ω X pF L hpF)
      (ObjectProperty.homMk (Prod.mkHom
        (frobeniusCommonPullbackAtStage l Ω X g p.obj.1.unop L hM).hom.op
        (frobeniusCommonPullbackAtStage l Ω X g p.obj.2 L hN).inv)) ≫
    (frobeniusCommonHomAtStage l Ω X pF L hB).inv

end CommonStageRepresentatives

/-- The all-stage assertion is over the actual recorded coefficient categories.
The integral evaluation normalization and the rationalization equations fix its
counits; no field is an unconstrained proposition. The scalar squares are stated for
every embedding, so the identity embedding `AlgHom.id` and composite embeddings
`j.comp ι` are instances of `integral_scalar` and `rational_scalar`; successive
finite quotients are `quotient_reduction`.
Source: `def-pod-dual-tate-datum`, first displayed arrow and coefficient paragraphs
(blueprint: lem-pod-geometric-frobenius-internal-hom-comparison). -/
structure GeometricFrobeniusInternalHomComparison
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) (g : X ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] where
  finite : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ), FrobeniusFiniteHomLaws l E X g n
  integral : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
    FrobeniusIntegralHomStage l E X g
  integral_hom_permitted : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (M N : sfIntegralConstructibleCategory l E X),
    constructibleIntegralHomPairs l E X (op M, N)
  integral_evaluation : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], FrobeniusIntegralEvaluationNormalized l E X g (integral E)
  rational : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
    FrobeniusRationalHomStage l E X g
  rational_evaluation : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (p : (constructibleRationalHomPairs l E X).FullSubcategory),
    HEq ((rational E).evaluation p)
      ((sfRationalConstructibleLocalization l E X).map
        ((integral E).evaluation (integralPairOfRationalHomPair l E X p)))
  rationalization : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (p : (constructibleRationalHomPairs l E X).FullSubcategory),
    HEq ((rational E).comparison p)
      ((sfRationalConstructibleLocalization l E X).map
        ((integral E).comparison (integralPairOfRationalHomPair l E X p)))
  integral_reduction : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ)
    (p : (constructibleIntegralHomPairs l E X).FullSubcategory),
    (coefficientFiniteDerivedExtension l E X n).map ((integral E).comparison p).hom ≫
      frobeniusIntegralReductionHom l E X n
        ((constructibleIntegralPullback l E g).obj p.obj.1.unop)
        ((constructibleIntegralPullback l E g).obj p.obj.2) ≫
      (finiteIntrinsicDerivedInternalHom l E X n).map
        (Prod.mkHom (frobeniusIntegralReductionPullback l E X g n p.obj.1.unop).inv.op
          (frobeniusIntegralReductionPullback l E X g n p.obj.2).hom) =
    (frobeniusIntegralReductionPullback l E X g n
        ((constructibleIntegralHom l E X).obj p)).hom ≫
      (finiteDerivedPullback l E n g).map
        (frobeniusIntegralReductionHom l E X n p.obj.1.unop p.obj.2) ≫
      finiteGeometricFrobeniusInternalHomComparison l E g n
        ((coefficientFiniteDerivedExtension l E X n).obj p.obj.1.unop.obj)
        ((coefficientFiniteDerivedExtension l E X n).obj p.obj.2.obj)
  integral_reduction_hom_isIso : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ)
    (p : (constructibleIntegralHomPairs l E X).FullSubcategory),
    IsIso (frobeniusIntegralReductionHom l E X n p.obj.1.unop p.obj.2)
  integral_scalar : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L),
    FrobeniusHomScalarSquare (integral E) (integral L)
      (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        E L ι X)
      (integralPullbackScalarComparison l E L ι g)
      (integralHomScalarPair_permitted l E L ι X)
      (integralHomScalarComparison l E L ι X)
  rational_scalar : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L),
    FrobeniusHomScalarSquare (rational E) (rational L)
      (sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι)
      (fun M ↦ (rationalPullbackScalarComparison l E L ι g).app M)
      (rationalHomScalarPair_permitted l E L ι X)
      (rationalHomScalarComparison l E L ι X)
  common_stage : FrobeniusHomStage (commonStageHomPairs l Ω X)
    (commonStageDerivedInternalHom l Ω X) (commonStageDerivedPullback l Ω g)
    (commonStageDerivedTensor l Ω X) (canonicalCommonStagePullbackTensor l Ω g)
  finite_identification : ∀ (T : TraceFormulaCoefficientConventions.{u})
    (M N : T.homPullbackCategory T.geometricBaseChange),
    finiteGeometricFrobeniusInternalHomComparison
        T.coefficients.l T.coefficientField
        (T.datum.geometricGaloisFrobenius T.X₀) (T.level - 1)
        (hX := T.homPullbackUnits T.structureMap) M N =
      T.internalHomPullbackComparison (T.datum.geometricGaloisFrobenius T.X₀) M N
  quotient_reduction : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {m n : ℕ} (h : n ≤ m)
    (M N : normalizedDVRDerived l E X m),
    IsFiniteCoefficientSitePerfect l E X m M →
    (coefficientFiniteQuotientDerived l E X h).map
        (finiteGeometricFrobeniusInternalHomComparison l E g m M N) ≫
      finiteIntrinsicReductionHom l E X h
        ((finiteDerivedPullback l E m g).obj M) ((finiteDerivedPullback l E m g).obj N) ≫
      (finiteIntrinsicDerivedInternalHom l E X n).map
        (Prod.mkHom ((pullbackTensorQuotient l E g h).app M).inv.op
          ((pullbackTensorQuotient l E g h).app N).hom) =
    ((pullbackTensorQuotient l E g h).app
        ((finiteIntrinsicDerivedInternalHom l E X m).obj (op M, N))).hom ≫
      (finiteDerivedPullback l E n g).map (finiteIntrinsicReductionHom l E X h M N) ≫
      finiteGeometricFrobeniusInternalHomComparison l E g n
        ((coefficientFiniteQuotientDerived l E X h).obj M)
        ((coefficientFiniteQuotientDerived l E X h).obj N)
  common_evaluation : ∀ (p : (commonStageHomPairs l Ω X).FullSubcategory)
    (L : WeilConjectures.AlgebraicallyClosedCoefficients.Index l Ω)
    (hA : ((commonStageDerivedTensor l Ω X).obj
      ((commonStageDerivedInternalHom l Ω X).obj p, p.obj.1.unop)).stage ≤ L)
    (hN : p.obj.2.stage ≤ L),
    common_stage.evaluation p = GeneralAlgebraicallyClosedCoefficients.ofHom
      ((commonStageDerivedTensor l Ω X).obj
        ((commonStageDerivedInternalHom l Ω X).obj p, p.obj.1.unop))
      p.obj.2 L hA hN
      (frobeniusCommonEvaluationAtStage l Ω X g rational p L hA hN)
  common_representative : ∀ (p : (commonStageHomPairs l Ω X).FullSubcategory)
    (L : WeilConjectures.AlgebraicallyClosedCoefficients.Index l Ω)
    (hA : ((commonStageDerivedPullback l Ω g).obj
      ((commonStageDerivedInternalHom l Ω X).obj p)).stage ≤ L)
    (hB : ((commonStageDerivedInternalHom l Ω X).obj
      (common_stage.pullbackPair p)).stage ≤ L),
    common_stage.comparison p = GeneralAlgebraicallyClosedCoefficients.ofHom
      ((commonStageDerivedPullback l Ω g).obj
        ((commonStageDerivedInternalHom l Ω X).obj p))
      ((commonStageDerivedInternalHom l Ω X).obj (common_stage.pullbackPair p)) L hA hB
      (frobeniusCommonComparisonAtStage l Ω X g rational common_stage p L hA hB)
  common_stage_independence : ∀ (p : (commonStageHomPairs l Ω X).FullSubcategory)
    (L L' : WeilConjectures.AlgebraicallyClosedCoefficients.Index l Ω)
    (hA : ((commonStageDerivedPullback l Ω g).obj
      ((commonStageDerivedInternalHom l Ω X).obj p)).stage ≤ L)
    (hB : ((commonStageDerivedInternalHom l Ω X).obj
      (common_stage.pullbackPair p)).stage ≤ L)
    (hA' : ((commonStageDerivedPullback l Ω g).obj
      ((commonStageDerivedInternalHom l Ω X).obj p)).stage ≤ L')
    (hB' : ((commonStageDerivedInternalHom l Ω X).obj
      (common_stage.pullbackPair p)).stage ≤ L'),
    GeneralAlgebraicallyClosedCoefficients.ofHom
        ((commonStageDerivedPullback l Ω g).obj
          ((commonStageDerivedInternalHom l Ω X).obj p))
        ((commonStageDerivedInternalHom l Ω X).obj (common_stage.pullbackPair p)) L hA hB
        (frobeniusCommonComparisonAtStage l Ω X g rational common_stage p L hA hB) =
      GeneralAlgebraicallyClosedCoefficients.ofHom
        ((commonStageDerivedPullback l Ω g).obj
          ((commonStageDerivedInternalHom l Ω X).obj p))
        ((commonStageDerivedInternalHom l Ω X).obj (common_stage.pullbackPair p)) L' hA' hB'
        (frobeniusCommonComparisonAtStage l Ω X g rational common_stage p L' hA' hB')

/-- Install the canonical residue-field invertibility supplied by the finite-field
datum, without making it an extra hypothesis on the theorem.
Source: `def-pod-dual-tate-datum`, fixed setting and first arrow
(blueprint: lem-pod-geometric-frobenius-internal-hom-comparison). -/
def geometricFrobeniusInternalHomComparisonType
    (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] :=
  letI := D.schemeFrobeniusCoefficientInvertible X₀ l hl
  GeometricFrobeniusInternalHomComparison l (D.geometricFiber X₀).left
    (D.geometricGaloisFrobenius X₀) Ω

/-- Geometric Frobenius commutes with the recorded internal Hom at finite,
completed integral, rational and algebraically closed coefficients. Each comparison
is uniquely characterized by its explicit evaluation equation.

Source: main-20261015, `def-pod-dual-tate-datum`, first displayed arrow and
coefficient paragraphs (blueprint: lem-pod-geometric-frobenius-internal-hom-comparison).

Proof:
1. Use cor-coef-integral-internal-hom and
   lem-pur-integral-operations-preserve-constructible to place the ambient Hom,
   completed tensor and pullback in the full integral constructible category.
   The completed evaluation is the coherent reduction/limit map in
   FrobeniusIntegralEvaluationNormalized. The completed transpose bijection of
   lem-coef-completed-tensor-hom-transpose identifies its adjunction.
2. The Frobenius scheme automorphism has inverse induced by z -> z^q.
   lem-weil-isomorphism-derived-pullback-equivalence gives the finite equivalence.
   lem-weil-isomorphism-derived-pullback identifies completed pullback with exact
   inverse image. The site relabelling, completed ring and inverse identities of
   lem-weil-proetale-isomorphism-inverse-image give its integral inverse.
3. Apply lem-weil-mate-iso-along-equivalences to tensor-Hom adjunctions, with
   both vertical equivalences equal to pullback and tensorator the inverse of
   lem-pur-derived-pullback-tensor-iso. The mate is exactly the displayed
   evaluation transpose, hence invertible. At finite coefficients its defining
   formula is thm-trf-internal-hom-pullback's internalHomPullbackComparison.
4. Uncurry the two-variable naturality square. Naturality of tensor comparison
   and evaluation identifies both sides with pulled-back evaluation after the
   two input maps. Injectivity of transposition proves the equality and uniqueness.
5. Reduce that same pairing modulo each positive uniformizer power. The
   evaluation-preserving comparisons of lem-fix-operation-reduction and the
   tensor reduction identity identify both sides of integral_reduction.
   Between successive quotients, reduction and pullback preserve the local
   finite-projective representatives of the first input. The same transposition
   argument proves quotient_reduction, including equal and nonflat quotients.
6. Localize the integral comparison on all permitted constructible pairs.
   Images of the inverse identities prove rational invertibility. The rational
   tensor-Hom bijection identifies its evaluation transpose. Extend naturality
   from integral maps to pure scalar tensors and their sums. This uses no
   perfect integral lattice for a rational perfect object.
7. Use lem-coef-monoidal-square-hom-transport with the canonical scalar
   comparisons of lem-pur-integral-operations-scalar-extension and their
   rationalizations. Uncurrying gives exactly FrobeniusHomScalarSquare, with
   inverse pullback comparison in the contravariant slot. The normalized unit
   and composition comparisons identify identity and pasted field-extension
   squares with their direct squares.
8. Represent every pair and finite collection of arrows over a common finite
   field by def-weil-algebraically-closed-coefficients. Transport the rational
   comparison by the recorded Hom and pullback stage comparisons, giving
   frobeniusCommonComparisonAtStage. Step 7 identifies these maps after every
   field enlargement; two choices agree over their compositum. The inverse
   and evaluation descend by the same representative formulas. This proves
   common_representative, common_stage_independence and the common-stage
   evaluation and naturality equations. -/
theorem geometricFrobeniusInternalHomComparison
    (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] :
    Nonempty (geometricFrobeniusInternalHomComparisonType D X₀ l hl Ω) := by
  sorry

end WeilConjectures
