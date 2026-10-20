/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Sheaf.Paper.RationalSmoothPurityCanonical
public import Sheaf.Paper.FrobeniusCoefficientTwistsCanonical
public import Sheaf.Paper.ZlFrobeniusCompactSupportComparison
public import Sheaf.Paper.FieldWeilShriekShiftData
import Sheaf.Paper.SfWeilSheafComplex
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.SixFunctors.SchemeGeometricFrobenius
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
import Sheaf.Paper.SmoothPurityMap
import Sheaf.Paper.IntegralDirectImageTower
import Sheaf.Paper.IntegralResidueTor
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.IntrinsicQbarCategory
import Sheaf.Paper.PbcDescentFunctors
import Sheaf.Paper.PbcRationalCategory
import Sheaf.Paper.PbcRationalTransport
import Sheaf.Paper.RationalCompactSupportCoefficientCoherence
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.Paper.SmoothPurityNormalizedEquivalence
import Sheaf.SixFunctors.FrobeniusSquareCartesian
import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
import Sheaf.SixFunctors.RationalOperations
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
/-! # Rational purity and the geometric-Frobenius adjunction mate

Source: main-20261015, sec-poincare-duality/sk-lem-finite,
prop-weil-operations.proof.md, sentences 3--4
(blueprint: lem-pur-rational-weil-naturality-mate).
-/

@[expose] public noncomputable section
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
universe u v uX uY vX vY
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme CategoryTheory.Endofunctor MonoidalCategory
namespace WeilConjectures

/-- The component formula for the exceptional Frobenius comparison through purity.
The order is the inverse pulled-back purity, the pullback/twist comparison, and purity
at the pulled-back argument. This helper performs only the displayed composition;
the geometric statement must identify its inputs with the specified canonical maps.
Source: prop-weil-operations proof, sentences 3--4
(blueprint: lem-pur-rational-weil-naturality-mate). -/
def purityFrobeniusConjugate {CX : Type uX} {CY : Type uY}
    [Category.{vX} CX] [Category.{vY} CY]
    (PX : CX ⥤ CX) (PY : CY ⥤ CY) (H G : CY ⥤ CX)
    (γ : ∀ K : CY, H.obj K ≅ G.obj K)
    (b : ∀ K : CY, PX.obj (H.obj K) ≅ H.obj (PY.obj K)) (K : CY) :
    PX.obj (G.obj K) ≅ G.obj (PY.obj K) :=
  (PX.mapIso (γ K)).symm ≪≫ b K ≪≫ γ (PY.obj K)

/-- The two identities of the node, written once for either coefficient category.
The second is the counit characterization of the right mate of inverse exchange.
Source: prop-weil-operations proof, sentences 3--4
(blueprint: lem-pur-rational-weil-naturality-mate). -/
def PurityNaturalityMate {CX : Type uX} {CY : Type uY}
    [Category.{vX} CX] [Category.{vY} CY]
    (PX : CX ⥤ CX) (PY : CY ⥤ CY) (H : CY ⥤ CX)
    (F : CX ⥤ CY) (G : CY ⥤ CX) (adj : F ⊣ G)
    (γ : ∀ K : CY, H.obj K ≅ G.obj K)
    (b : ∀ K : CY, PX.obj (H.obj K) ≅ H.obj (PY.obj K))
    (β : F ⋙ PY ≅ PX ⋙ F) : Prop :=
  (∀ {K L : CY} (a : K ⟶ L),
    (γ K).hom ≫ G.map a = H.map a ≫ (γ L).hom) ∧
  ∀ K : CY,
    F.map (purityFrobeniusConjugate PX PY H G γ b K).hom ≫
      adj.counit.app (PY.obj K) =
    β.inv.app (G.obj K) ≫ PY.map (adj.counit.app K)

namespace RationalWeilPurity
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (f₀ : X₀ ⟶ Y₀)
  [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Lf*(-)(d)[2d] in the actual geometric-fibre rational categories.
The only instance data supplied here are the inherited prime inverses.
Source: node, definition of H
(blueprint: lem-pur-rational-weil-naturality-mate). -/
def H (d : ℕ) :=
  letI : ∀ x : (D.geometricFiber X₀).left,
    Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
      fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI : ∀ y : (D.geometricFiber Y₀).left,
    Invertible (l : (D.geometricFiber Y₀).left.residueField y) :=
      fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  RationalSmoothPurityCanonical.rationalSource l E (zlFiberMap D f₀) d

/-- The specified b: tensor comparison, shifted root-line comparison, and pullback
composition around g_X f = f g_Y. All factors are the published canonical ones.
Source: node, definition of b
(blueprint: lem-pur-rational-weil-naturality-mate). -/
def b (d : ℕ) (K : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :
    (sfWeilFrobeniusPullback D l hl X₀ E).obj ((H D l hl f₀ E d).obj K) ≅
      (H D l hl f₀ E d).obj ((sfWeilFrobeniusPullback D l hl Y₀ E).obj K) :=
  letI : ∀ x : (D.geometricFiber X₀).left,
    Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
      fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI : ∀ y : (D.geometricFiber Y₀).left,
    Invertible (l : (D.geometricFiber Y₀).left.residueField y) :=
      fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  canonicalRationalPullbackTensor l E (D.geometricFrobenius X₀).hom
      ((sfRationalTwistingCoefficient l E (D.geometricFiber X₀).left (d : ℤ))⟦2*(d : ℤ)⟧)
      ((rationalDerivedPullback l E (zlFiberMap D f₀)).obj K) ≪≫
    (rationalDerivedTensor l E (D.geometricFiber X₀).left).mapIso
      (Iso.prod
        ((Functor.commShiftIso (rationalDerivedPullback l E
          (D.geometricFrobenius X₀).hom) (2*(d : ℤ))).app _ ≪≫
          (shiftFunctor _ (2*(d : ℤ))).mapIso
            (FrobeniusCoefficientTwists.rationalDerivedLineMap l E
              (D.geometricFrobenius X₀).hom (d : ℤ)))
        ((pullbackTensorRationalComposition l E (zlFiberMap D f₀)
          (D.geometricFrobenius X₀).hom K).symm ≪≫
          eqToIso (congrArg (fun g ↦ (rationalDerivedPullback l E g).obj K)
            (zlFrobenius_naturality D f₀)) ≪≫
          pullbackTensorRationalComposition l E (D.geometricFrobenius Y₀).hom
            (zlFiberMap D f₀) K))

/-- Integral Frobenius pullback with the inherited prime inverses supplied explicitly.
Source: node, completed integral coordinates of exchange
(blueprint: lem-pur-rational-weil-naturality-mate). -/
def integralFrobenius (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :=
  @constructibleIntegralPullback l _ E _ _ _ _ _ (D.geometricFrobenius T₀).hom
    (fun x ↦ sfWeilPrimeInvertible D l hl T₀ x)
    (fun x ↦ sfWeilPrimeInvertible D l hl T₀ x)

/-- Integral compact-support exchange in completed constructible coordinates.
It is obtained from the actual open/proper mates using the fixed Roos-normalized
lambda and compact-support realization, rather than a chosen exchange isomorphism.
Source: node, definition of beta
(blueprint: lem-pur-rational-weil-naturality-mate). -/
def integralExchange (c₀ : Compactification f₀.left)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) :
    (integralFrobenius D l hl E Y₀).obj
      ((sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl)
        (zlGeometricCompactification D f₀ c₀) E).obj M) ≅
    (sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl)
      (zlGeometricCompactification D f₀ c₀) E).obj
        ((integralFrobenius D l hl E X₀).obj M) :=
  letI : ∀ x : (D.geometricFiber X₀).left,
    Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
      fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI : ∀ y : (D.geometricFiber Y₀).left,
    Invertible (l : (D.geometricFiber Y₀).left.residueField y) :=
      fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  let c := zlGeometricCompactification D f₀ c₀
  let F := sfCompactSupportFiniteIntegralFunctor l D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) c E
  let PX := constructibleIntegralPullback l E (D.geometricFrobenius X₀).hom
  ObjectProperty.isoMk (sfIntegralConstructible l E (D.geometricFiber Y₀).left)
    ((FrobeniusCoefficientTwists.completedToOrdinary l E
        (D.geometricFrobenius Y₀).hom).app (F.obj M) ≪≫
      (zlAmbientFrobenius D l E Y₀).mapIso
        ((sfQcqsCompactSupportRealization l E D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c).app M).symm ≪≫
      (zlCompactSupportFrobenius D f₀ c₀ l E).app M.obj ≪≫
      (PurCompactSupport.image (PurCompactSupport.completed l E) c).mapIso
        ((FrobeniusCoefficientTwists.completedToOrdinary l E
          (D.geometricFrobenius X₀).hom).app M).symm ≪≫
      (sfQcqsCompactSupportRealization l E D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c).app (PX.obj M))

/-- Localization of the actual integral compact-support exchange, on each object.
Source: node, rational beta
(blueprint: lem-pur-rational-weil-naturality-mate).
Proof: both rational object functors retain the specified integral representatives.
Localize integralExchange and its inverse. The rational pullback object formulas
identify its endpoints with those in the statement. The displayed equality fixes
the resulting map uniquely, so no exchange normalization is lost. -/
theorem rationalExchange_existsUnique (c₀ : Compactification f₀.left)
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) :
    ∃! e : (sfWeilFrobeniusPullback D l hl Y₀ E).obj
        ((sfCompactSupportFiniteFunctor l D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
          (zlGeometricCompactification D f₀ c₀) E).obj K) ≅
      (sfCompactSupportFiniteFunctor l D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
        (zlGeometricCompactification D f₀ c₀) E).obj
          ((sfWeilFrobeniusPullback D l hl X₀ E).obj K),
      HEq e.hom ((sfRationalConstructibleLocalization l E (D.geometricFiber Y₀).left).map
        (integralExchange D l hl f₀ E c₀ K.obj).hom) := by
  sorry

/-- Rational exchange with its integral representative normalization retained.
Source: node, rational beta
(blueprint: lem-pur-rational-weil-naturality-mate). -/
def rationalExchange (c₀ : Compactification f₀.left)
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) :=
  (rationalExchange_existsUnique D l hl f₀ E c₀ K).exists.choose

variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (c₀ : Compactification f₀.left)
  (S : ConstructibleExceptionalCoefficients.System l Ω D hl (f := zlFiberMap D f₀))

/-- Exchange transported to the specified constructible adjoint's left functor.
Source: node, beta and the specified F
(blueprint: lem-pur-rational-weil-naturality-mate). -/
def betaComponent
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) :
    (sfWeilFrobeniusPullback D l hl Y₀ E).obj
      ((S.ring.operation (zlGeometricCompactification D f₀ c₀)
        (.rational ⟨E⟩)).F.obj K) ≅
    (S.ring.operation (zlGeometricCompactification D f₀ c₀)
      (.rational ⟨E⟩)).F.obj ((sfWeilFrobeniusPullback D l hl X₀ E).obj K) :=
  (sfWeilFrobeniusPullback D l hl Y₀ E).mapIso
    ((S.ring.rationalLeft (zlGeometricCompactification D f₀ c₀) ⟨E⟩).app K) ≪≫
    rationalExchange D l hl f₀ E c₀ K ≪≫
    ((S.ring.rationalLeft (zlGeometricCompactification D f₀ c₀) ⟨E⟩).app
      ((sfWeilFrobeniusPullback D l hl X₀ E).obj K)).symm

/-- The constructed exchange is natural for every localized rational arrow.
Source: node, canonical compact-support exchange
(blueprint: lem-pur-rational-weil-naturality-mate).
Proof: the open and proper mates are natural transformations. The normalized lambda
and realization are natural too. Their composite integralExchange is therefore natural
on integral maps. Localization is linear, so its square holds on pure scalar tensors
and on their sums. Conjugating by rationalLeft preserves that square. -/
theorem beta_naturality {K L : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left}
    (a : K ⟶ L) :
    (sfWeilFrobeniusPullback D l hl Y₀ E).map
      ((S.ring.operation (zlGeometricCompactification D f₀ c₀)
        (.rational ⟨E⟩)).F.map a) ≫ (betaComponent D l hl f₀ E Ω c₀ S L).hom =
    (betaComponent D l hl f₀ E Ω c₀ S K).hom ≫
      (S.ring.operation (zlGeometricCompactification D f₀ c₀)
        (.rational ⟨E⟩)).F.map ((sfWeilFrobeniusPullback D l hl X₀ E).map a) := by
  sorry

/-- The actual compact-support exchange as a natural isomorphism.
Source: node, beta
(blueprint: lem-pur-rational-weil-naturality-mate). -/
def beta : (S.ring.operation (zlGeometricCompactification D f₀ c₀)
      (.rational ⟨E⟩)).F ⋙ sfWeilFrobeniusPullback D l hl Y₀ E ≅
    sfWeilFrobeniusPullback D l hl X₀ E ⋙
      (S.ring.operation (zlGeometricCompactification D f₀ c₀) (.rational ⟨E⟩)).F :=
  NatIso.ofComponents (betaComponent D l hl f₀ E Ω c₀ S)
    (fun a ↦ beta_naturality D l hl f₀ E Ω c₀ S a)

end RationalWeilPurity

namespace CommonWeilPurity
open AlgebraicallyClosedCoefficients GeneralAlgebraicallyClosedCoefficients
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (f₀ : X₀ ⟶ Y₀)
  [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The same H in the recorded common-stage category.
Source: node, Qbar clause
(blueprint: lem-pur-rational-weil-naturality-mate). -/
def H (d : ℕ) :=
  letI : ∀ x : (D.geometricFiber X₀).left,
    Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
      fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI : ∀ y : (D.geometricFiber Y₀).left,
    Invertible (l : (D.geometricFiber Y₀).left.residueField y) :=
      fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  RationalSmoothPurityCanonical.commonSource l Ω (zlFiberMap D f₀) d

/-- Frobenius on the literal shifted line at the least finite stage.
Source: node, the shift and canonical Tate-line factor of b
(blueprint: lem-pur-rational-weil-naturality-mate). -/
def shiftedLineFrobenius (d : ℕ) :=
  letI : ∀ x : (D.geometricFiber X₀).left,
    Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
      fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let L := Padic.finiteCoefficientBase l Ω
  let E := Coefficient.{u} l Ω L
  let T := sfRationalTwistingCoefficient l E (D.geometricFiber X₀).left (d : ℤ)
  sfWeilStagePullbackIdentification D l hl X₀ Ω L (T⟦2*(d : ℤ)⟧) ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion L).mapIso
      ((Functor.commShiftIso (rationalDerivedPullback l E
        (D.geometricFrobenius X₀).hom) (2*(d : ℤ))).app T ≪≫
        (shiftFunctor _ (2*(d : ℤ))).mapIso
          (FrobeniusCoefficientTwists.rationalDerivedLineMap l E
            (D.geometricFrobenius X₀).hom (d : ℤ)))

/-- The common-stage b uses the same normalized tensor comparison and root line,
with the actual semilinear pullback-composition square.
Source: node, definition of b
(blueprint: lem-pur-rational-weil-naturality-mate). -/
def b (d : ℕ)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left) :
    (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).obj ((H D l hl f₀ Ω d).obj K) ≅
      (H D l hl f₀ Ω d).obj ((sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).obj K) :=
  letI : ∀ x : (D.geometricFiber X₀).left,
    Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
      fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI : ∀ y : (D.geometricFiber Y₀).left,
    Invertible (l : (D.geometricFiber Y₀).left.residueField y) :=
      fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  canonicalCommonStagePullbackTensor l Ω (D.geometricFrobenius X₀).hom
      (RationalSmoothPurityCanonical.commonShiftedLine l Ω (D.geometricFiber X₀).left d)
      ((commonStageDerivedPullback l Ω (zlFiberMap D f₀)).obj K) ≪≫
    (commonStageDerivedTensor l Ω (D.geometricFiber X₀).left).mapIso
      (Iso.prod (shiftedLineFrobenius D l hl (X₀ := X₀) Ω d)
        ((zlFrobeniusSquare D l hl Ω f₀).app K))

variable (c₀ : Compactification f₀.left)
  (S : ConstructibleExceptionalCoefficients.System l Ω D hl (f := zlFiberMap D f₀))

/-- Common-stage compact-support exchange, represented at the literal stage of K.
The stage pullback identifications and q components are retained in their actual order.
Source: node, common-stage beta
(blueprint: lem-pur-rational-weil-naturality-mate). -/
def betaComponent
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left) :
    (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).obj
      ((S.ring.operation (zlGeometricCompactification D f₀ c₀) .closed).F.obj K) ≅
    (S.ring.operation (zlGeometricCompactification D f₀ c₀) .closed).F.obj
      ((sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).obj K) :=
  let c := zlGeometricCompactification D f₀ c₀
  let q := (S.common.commonComparison c K.stage).q
  let F := (S.ring.operation c .closed).F
  (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).mapIso (q.app K.obj).symm ≪≫
    sfWeilStagePullbackIdentification D l hl Y₀ Ω K.stage _ ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion K.stage).mapIso
      ((RationalWeilPurity.beta D l hl f₀ (Coefficient.{u} l Ω K.stage) Ω c₀ S).app K.obj) ≪≫
    q.app ((sfWeilFrobeniusPullback D l hl X₀ (Coefficient.{u} l Ω K.stage)).obj K.obj) ≪≫
    F.mapIso (sfWeilStagePullbackIdentification D l hl X₀ Ω K.stage K.obj).symm

/-- The normalized finite-stage exchange squares descend to every common-stage arrow.
Source: node, common-stage beta
(blueprint: lem-pur-rational-weil-naturality-mate).
Proof: represent an arrow over one finite field containing both endpoint stages.
Compact-support coefficient coherence intertwines the actual rational exchanges
with q, and the pullback scalar cocycles intertwine the stage identifications.
Rational beta_naturality at that field gives the square of representatives.
The common-stage quotient takes it to the displayed equality. -/
theorem beta_naturality
    {K L : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left}
    (a : K ⟶ L) :
    (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).map
      ((S.ring.operation (zlGeometricCompactification D f₀ c₀) .closed).F.map a) ≫
        (betaComponent D l hl f₀ Ω c₀ S L).hom =
    (betaComponent D l hl f₀ Ω c₀ S K).hom ≫
      (S.ring.operation (zlGeometricCompactification D f₀ c₀) .closed).F.map
        ((sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).map a) := by
  sorry

/-- The specified common-stage compact-support exchange as a natural isomorphism.
Source: node, common-stage beta
(blueprint: lem-pur-rational-weil-naturality-mate). -/
def beta : (S.ring.operation (zlGeometricCompactification D f₀ c₀) .closed).F ⋙
    sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω ≅
    sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ⋙
      (S.ring.operation (zlGeometricCompactification D f₀ c₀) .closed).F :=
  NatIso.ofComponents (betaComponent D l hl f₀ Ω c₀ S)
    (fun a ↦ beta_naturality D l hl f₀ Ω c₀ S a)

end CommonWeilPurity


section Main
variable (P : PurityFiniteSetting.{u})
  {X₀ Y₀ : Over (Spec (.of P.field.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (f₀ : X₀ ⟶ Y₀)
  [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
  (c₀ : Compactification f₀.left)
  (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
    P.field P.coefficients.different (f := zlFiberMap P.field f₀))

/-- The canonical rational purity family on the geometric fibre.
The prime inverses are inherited from the finite-field datum.
Source: node, gamma from rational purity
(blueprint: lem-pur-rational-weil-naturality-mate). -/
def rationalWeilPurityGamma (d : ℕ)
    [SmoothOfRelativeDimension d (zlFiberMap P.field f₀)]
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension
      (P.field.geometricFiber Y₀).left) :=
  letI hXsep : IsSeparated ((P.field.geometricFiber X₀).left ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (IsSeparated (CategoryTheory.Limits.pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k)))))
  letI hYsep : IsSeparated ((P.field.geometricFiber Y₀).left ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (IsSeparated (CategoryTheory.Limits.pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k)))))
  letI : ∀ x : (P.field.geometricFiber X₀).left,
    Invertible (P.coefficients.l : (P.field.geometricFiber X₀).left.residueField x) :=
      fun x ↦ sfWeilPrimeInvertible P.field P.coefficients.l P.coefficients.different X₀ x
  letI : ∀ y : (P.field.geometricFiber Y₀).left,
    Invertible (P.coefficients.l : (P.field.geometricFiber Y₀).left.residueField y) :=
      fun y ↦ sfWeilPrimeInvertible P.field P.coefficients.l P.coefficients.different Y₀ y
  @RationalSmoothPurityCanonical.rationalIso P
    (P.field.geometricFiber X₀).left (P.field.geometricFiber Y₀).left
    _ _ _ _ hXsep _ _ hYsep _ _ (zlFiberMap P.field f₀) _ _ _ _
    (zlGeometricCompactification P.field f₀ c₀) S d _ K

/-- The canonical common-stage purity family, with its specified finite-field comparisons.
Source: node, gamma from rational/common-stage purity
(blueprint: lem-pur-rational-weil-naturality-mate). -/
def commonWeilPurityGamma (d : ℕ)
    [SmoothOfRelativeDimension d (zlFiberMap P.field f₀)]
    (K : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l P.coefficients.Qbar
      (P.field.geometricFiber Y₀).left) :=
  letI hXsep : IsSeparated ((P.field.geometricFiber X₀).left ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (IsSeparated (CategoryTheory.Limits.pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k)))))
  letI hYsep : IsSeparated ((P.field.geometricFiber Y₀).left ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (IsSeparated (CategoryTheory.Limits.pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k)))))
  letI : ∀ x : (P.field.geometricFiber X₀).left,
    Invertible (P.coefficients.l : (P.field.geometricFiber X₀).left.residueField x) :=
      fun x ↦ sfWeilPrimeInvertible P.field P.coefficients.l P.coefficients.different X₀ x
  letI : ∀ y : (P.field.geometricFiber Y₀).left,
    Invertible (P.coefficients.l : (P.field.geometricFiber Y₀).left.residueField y) :=
      fun y ↦ sfWeilPrimeInvertible P.field P.coefficients.l P.coefficients.different Y₀ y
  @RationalSmoothPurityCanonical.commonIso P
    (P.field.geometricFiber X₀).left (P.field.geometricFiber Y₀).left
    _ _ _ _ hXsep _ _ hYsep _ _ (zlFiberMap P.field f₀) _ _ _ _
    (zlGeometricCompactification P.field f₀ c₀) S d _ K

/-- Rational/common-stage purity is natural on every arrow and its Frobenius conjugate
is the specified compact-support counit mate.
Source: main-20261015, prop-weil-operations proof, sentences 3--4
(blueprint: lem-pur-rational-weil-naturality-mate).
Proof:

All schemes in the statement are separated finite type over $k$. They are Noetherian by [lem-
weil-pbc-finite-type-over-noetherian] (a field is Noetherian), and finite-dimensional by [lem-
kun-dimension-finite-type]; $\ell$ is invertible since $\ell\ne p$. Thus they satisfy the scheme
hypotheses of the integral and rational categories. By [def-weil-pbc-rational-category] an
$E$-object is an integral object viewed in a scalar localization; this choice of an underlying
integral object does not equip it with an integral Weil structure.

Identify the integral presentation of Step 1 with [def-weil-derived-complete-integral-detailed]
by [lem-weil-pbc-integral-stratified-perfect-characterization]. For such an integral
constructible object $K$, [lem-coef-integral-residue-tor] gives a single Tor-amplitude interval
for all its derived reductions; hence its reduction tower lies in the domain of [det-sp-tower-
gamma]. The powers $\ell^n$ used there are a cofinal subsystem of uniformizer powers: in the DVR
$\ell$ is a unit times $\varpi_E^{e(E/\mathbf Q_\ell)}$, so $\mathcal O_E/(\ell^n)=\mathcal
O_E/(\varpi_E^{en})$. No additional finite-Tor condition on a rational object is being imposed.

Apply the naturality assertion in clause (2) of [det-sp-tower-gamma] to the actual derived
reduction of an integral arrow $v:K\to L$. Apply the functor $R\varprojlim$ to that equality.
The natural Hom bijections and purity formula of [det-sp-integral-adjunction-bijection] identify
the result with $G(v)\gamma_K=\gamma_LH(v)$ for the integral purity maps. Identify its right
adjoint $H_{f,\mathcal O_E}$ with the specified $Rf^!$ using their constructible adjunctions
[def-weil-exceptional-inverse-image] and the unique counit-preserving natural isomorphism [det-
sp-unique-right-adjoint]. This fixes the adjunction normalization used below.

The square with horizontal arrows $g_X,g_Y$ is Cartesian as a square of schemes by [def-pur-
scheme-geometric-frobenius]. To apply a theorem stated for $k$-morphisms, give its source copy
of each $T=X,Y$ the structure map $a_Tg_T=\operatorname{Spec}(\gamma)a_T$; call it
$T^{\langle\gamma\rangle}$. Then $g_T:T^{\langle\gamma\rangle}\to T$ is a $k$-isomorphism, and
the left vertical arrow is the same underlying $f$, now $f^{\langle\gamma\rangle}$. The source
schemes remain separated finite type and this arrow remains smooth of dimension $d$, since these
changes compose structural maps with a field isomorphism. The canonical twist comparison for
this square is precisely the roots-of-unity pullback comparison specified in [def-weil-
frobenius-coefficient-twists]. In particular the square does not replace geometric Frobenius by
a $k$-linear absolute-Frobenius endomorphism.

Choose the compactification $c$ of the statement as follows. Since $Y_0$ is of finite type over
a field it is quasi-compact and quasi-separated, so [thm-nagata-compactification] gives a
compactification $X_0\xrightarrow{j_0}\overline X_0\xrightarrow{\bar f_0}Y_0$ of the separated
finite-type $f_0$; its base change $c=(j,\bar f)$ to $k$ is a compactification of $f$ [def-weil-
compactifications-refinements], by base change of open immersions and proper morphisms [lem-
weil-pbc-open-immersion-base-change, lem-weil-pbc-proper-base-change]. By [lem-weil-frobenius-
square-cartesian] for $\bar f_0$, the square $\bar fg_{\overline X}=g_Y\bar f$ is Cartesian, and
$jg_X=g_{\overline X}j$ since both are base changes of $j_0$. Hence the pullback of $c$ along
$g_Y$, used by [det-sp-tower-exceptional-bc], is identified by $g_{\overline X}$ with the same
underlying compactification $(j,\bar f)$ of the retagged $f^{\langle\gamma\rangle}$, which is
the compactification used in [lem-pur-tower-purity-ground-field-retagging]. Work first in the
ordinary derived category of coefficient towers, retaining its transition maps. Apply [det-sp-
purity-bc-factors] to the retagged $k$-Cartesian square of Step 4. Its $e_\bullet$ is the
transpose of inverse compact-support exchange by [det-sp-tower-exceptional-bc], not merely an
isomorphism with the same endpoints. Its conclusion is $$e_{\bullet,K}\,P_X\gamma_{\bullet,K}=\g
amma_{f^{\langle\gamma\rangle},\bullet,P_YK}\,b_{\bullet,K}.$$ By [lem-pur-tower-purity-ground-
field-retagging], identify the retagged purity on the right with $\gamma_{f,\bullet,P_YK}$,
using the identity of the underlying sites, the same compactification, and the counit-preserving
right-adjoint comparison. Multiplying on the right by $(P_X\gamma_{\bullet,K})^{-1}$ proves the
displayed purity formula for the actual tower mate. This is an equality in the derived category
of towers, not a conclusion from equality of its separate evaluations.

Realize the normalized towers of Step 5 in the integral category by [det-sp-normalized-
equivalence]. The pullback and compact-support identifications are the natural ones of [det-sp-
integral-direct-image-tower]. The compatibility with the actual compactification exchange,
including its open/proper maps and units/counits before evaluation, is [lem-sf-integral-
compactification-system-realization], applied to the $k$-morphisms in the retagged square. The
integral adjunction of [det-sp-integral-adjunction-bijection] has precisely the realized tower
counit. Consequently applying this functor to the tower transpose equation gives
$$\varepsilon_{P_YK}F(e_K)=P_Y(\varepsilon_K)\beta_{GK}^{-1}$$ in the integral category.
Applying it to the equality in Step 5 gives $e_K=\gamma_{P_YK}b_K(P_X\gamma_K)^{-1}$. The
counit-preserving comparison in Step 3 identifies these with the specified $G$ and $\gamma$.
These two conclusions use functorial realization of tower arrows; they do not use faithfulness
of finite-level evaluation.

Keep the maps constructed in Steps 3–6 distinct from the already specified purity: denote the
former by $\gamma^T$. Apply [lem-pur-tower-trace-purity-comparison] to $f$ with the same
compactification, normalized reductions and counit-preserving right-adjoint comparison. Its
integral comparison is $\gamma^{\mathrm{tr}}_{E,K}=\gamma^T_{E,K}$, where $\gamma^{\mathrm{tr}}$
uses any reconstructed unit orientation, its scalar-extended trace and the projection transpose.
Its rational conclusion identifies the actual chosen maps of [thm-pur-rational-and-qbar-purity]:
$\gamma^{\mathrm{rat}}_{f,Q_EK}=Q_E(\gamma^T_{E,K})$, with the stated coefficient comparisons.
Hence the naturality and counit equations proved above for $\gamma^T$ apply to the intended
family after localization. This uses a comparison of the unit orientation and of the actual
transposes; equality of arbitrary coherent lifts is not assumed.

Pass to $E$ by [prop-weil-pbc-rational-transport], using the rational operations on arrows of
[def-weil-derived-pullback-tensor-hom, def-weil-exceptional-inverse-image] and the actual
purity-family identification established in Step 7. For any rational arrow write
$u=\varpi_E^{-N}v$ with $v$ integral, possible by [def-weil-pbc-rational-category]. Both $H_E$
and $G_E$ act by this scalar-extension rule. Thus Steps 3 and 7 give, in the localized Hom
group,
$$G_E(u)\gamma_K=\varpi_E^{-N}G_E(v)\gamma_K=\varpi_E^{-N}\gamma_LH_E(v)=\gamma_LH_E(u).$$ This
proves naturality for every rational arrow, whether or not it lifts to an integral isomorphism.

Apply the localization functor also to the two integral equations of Step 6. It preserves
composites and inverses, so $e_E=\gamma_{P_YK}b_K(P_X\gamma_K)^{-1}$ and
$\varepsilon_{P_YK}F_E(e_E)=P_Y(\varepsilon_K)\beta_{G_EK}^{-1}$ remain equalities. The rational
adjunction is the one whose units and counits agree with this passage, by [lem-coef-rational-
operations]. Take $L_1=L_2=F_E$, $R_1=R_2=G_E$, and the connecting functors $P_X,P_Y$ in [def-
weil-pbc-adjunction-mate]. Its transpose characterization says exactly that the latter equation
identifies $e_E$ with the mate of $\beta^{-1}:F_EP_X\to P_YF_E$. This checks the direction of
the inverse exchange as well as the adjunction normalization.

For $\Qlb$, use the common-stage categories of [def-weil-pbc-qbar-category]. Clauses (2)–(3) of
[det-sp-field-extension-towers] intertwine the actual tower purity, preserve its units and
counits, and give coefficient-composition compatibility. Step 7 identifies its rational image
with the intended purity, with precisely these coefficient comparisons. The adjunction
identifications preserve units and counits under finite scalar extension by [lem-coef-rational-
operations], and the actual rational compact-support exchange satisfies its scalar comparison
equation by [lem-cbc-rational-compact-support-coefficient-coherence]. The pullback/twist
comparisons and their action on common-stage arrows are those of [def-weil-derived-pullback-
tensor-hom, def-weil-frobenius-coefficient-twists]. Therefore the expressions in Steps 8–9 are
compatible natural transformations and their equations descend by [prop-weil-pbc-descent-
functors]. Concretely, represent an arbitrary arrow $u$ over one common finite extension $M$,
apply Step 8 at $M$, and conjugate the two sides by the same scalar comparison isomorphisms. For
the mate equation take the representative at the stage of $K$ and apply Step 9. The resulting
equalities of representatives give exactly the asserted equalities of morphism classes.

Finally let $\theta:P_YK\xrightarrow{\sim}K$ be any Weil structure in the category of [def-weil-
weil-sheaf-complex]. Apply Step 8 or 10 with $u=\theta$ and $K$ there replaced by $P_YK$:
$G(\theta)\gamma_{P_YK}=\gamma_KH(\theta)$. Substitute the formula for $e_K$ and cancel
$P_X\gamma_K$ to obtain $$G(\theta)e_KP_X\gamma_K=\gamma_KH(\theta)b_K.$$ Thus the purity
comparison intertwines the Weil structure made from the adjunction mate with the pullback/twist
Weil structure. No step selected a lattice stable under $\theta$; the fraction calculation
treated $\theta$ itself as an arbitrary rational arrow.
-/
theorem rational_weil_purity_naturality_mate (d : ℕ)
    [SmoothOfRelativeDimension d (zlFiberMap P.field f₀)] :
    PurityNaturalityMate
      (sfWeilFrobeniusPullback P.field P.coefficients.l P.coefficients.different X₀ P.extension)
      (sfWeilFrobeniusPullback P.field P.coefficients.l P.coefficients.different Y₀ P.extension)
      (RationalWeilPurity.H P.field P.coefficients.l P.coefficients.different f₀ P.extension d)
      (S.ring.operation (zlGeometricCompactification P.field f₀ c₀)
        (.rational ⟨P.extension⟩)).F
      (S.ring.operation (zlGeometricCompactification P.field f₀ c₀)
        (.rational ⟨P.extension⟩)).G
      (S.ring.operation (zlGeometricCompactification P.field f₀ c₀)
        (.rational ⟨P.extension⟩)).adjunction
      (rationalWeilPurityGamma P f₀ c₀ S d)
      (RationalWeilPurity.b P.field P.coefficients.l P.coefficients.different f₀ P.extension d)
      (RationalWeilPurity.beta P.field P.coefficients.l P.coefficients.different f₀ P.extension
        P.coefficients.Qbar c₀ S) ∧
    PurityNaturalityMate
      (sfCommonStageWeilFrobeniusPullback P.field P.coefficients.l P.coefficients.different
        X₀ P.coefficients.Qbar)
      (sfCommonStageWeilFrobeniusPullback P.field P.coefficients.l P.coefficients.different
        Y₀ P.coefficients.Qbar)
      (CommonWeilPurity.H P.field P.coefficients.l P.coefficients.different f₀
        P.coefficients.Qbar d)
      (S.ring.operation (zlGeometricCompactification P.field f₀ c₀) .closed).F
      (S.ring.operation (zlGeometricCompactification P.field f₀ c₀) .closed).G
      (S.ring.operation (zlGeometricCompactification P.field f₀ c₀) .closed).adjunction
      (commonWeilPurityGamma P f₀ c₀ S d)
      (CommonWeilPurity.b P.field P.coefficients.l P.coefficients.different f₀
        P.coefficients.Qbar d)
      (CommonWeilPurity.beta P.field P.coefficients.l P.coefficients.different f₀
        P.coefficients.Qbar c₀ S) := by
  sorry

end Main
end WeilConjectures
