/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module
public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.FiniteRingCompactSupportProjectionMap
public import Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange
public import Sheaf.Paper.ZlFrobeniusCompactSupportComparison
public import Sheaf.Paper.FieldWeilShriekShiftData
public import Sheaf.Paper.RationalCoefficientCategoryComparison
public import Sheaf.Paper.WfTensorCompletionFrobenius
public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.Paper.ProjectionTensorCoefficientComparison
public import Sheaf.Paper.ConstructibleProjectionMates
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.CompatibleCompactificationTriangle
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Sheaf.Paper.BasicOperationsCoefficientReduction
import Sheaf.Paper.CanonicalOriginCompactSupportComposition
import Sheaf.Paper.CompactificationCoherence
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.DerivedNakayama
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.EtaleCompactSupportCoefficientChange
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.Paper.FiniteCoefficientTensorCtf
import Sheaf.Paper.FiniteDirectImageComposition
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.IntegralResidueTor
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.IntrinsicCompletionCompleted
import Sheaf.Paper.PbcWeilCategory
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.PullbackTorAmplitude
import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.Paper.RefinementComparisonIsomorphism
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.ScalarExtensionExactIntrinsic
import Sheaf.Paper.SfIntegralCompactSupportConstructible
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.WeilTensorProduct
import Sheaf.SixFunctors.CompositionProjectionMate
import Sheaf.SixFunctors.ConstructibleTensorCompletion
import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
import Sheaf.SixFunctors.ProperOpenProjectionMate
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius
/-! # Compact-support projection formula at every coefficient stage
Source: blueprint main-20261015, sec-six-functors/sk-rem-sf-pf-done,
fix-prop-projection-formula (blueprint: fix-prop-projection-formula).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
universe u v w v' w' a b c d ha hb hc hd
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open CategoryTheory.SuppliedExchangeProjection
open scoped CategoryTheory.Functor
namespace WeilConjectures



/-- The projection formula at the coefficient stages of the specified six-functor
construction, including naturality, compactifications, composition and its pentagon,
and the proper counit identification. Finite coefficients retain arbitrary bounded
constructible first inputs. Integral coefficients retain precisely the uniform
finite-Tor second-input domain; field coefficients have the entire second domain.
Source: blueprint main-20261015, sk-rem-sf-pf-done, statement and proof
(blueprint: fix-prop-projection-formula).
Proof (postponed): choose bounded constructible etale origins at each finite level.
Comparison preserves and reflects the second input's finite Tor interval and
identifies the specified proper counit and inverse open projection with the
etale projection map. The etale projection formula proves invertibility without
a Tor hypothesis on the first input. Reduction of the completed integral mate is
this finite map, by the normalized reduction, tensor, unit and counit squares.
Its cone is complete and constructible; derived Nakayama proves invertibility.
Rationalization maps the inverse to the inverse. At algebraically closed
coefficients represent both inputs over a common finite coefficient field and
include this inverse. For proper composition, transpose both maps under the
composite adjunction: the two resulting counit composites agree. The K-flat
pullback/tensor comparisons agree on every pure tensor, including signs. The
open unit mate gives the analogous open formula. For a proper/open interchange
or a non-Cartesian refinement, transpose again and use the clopen comparison;
checking after open restriction gives the same tensor map. Common refinements
then give compactification independence. The compatible compactification
triangle and normalized compositor give the displayed composition square;
threefold mate pasting gives the associativity pentagon. At integral coefficients
these equations first hold as maps of coherent derived systems: apply the fixed
system realization and total limit, conjugating by their specified comparisons.
This proves equality of maps, without inferring it from finite-level evaluation.
Finally the identity-open compactification and its normalized unit identify the
proper compact-support projection with exactly the direct-image counit mate. -/
theorem compactSupportProjectionFormula
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn) :
    CompactSupportFiniteProjection.Laws S.toSixFunctorFiniteOperations ∧
    CompactSupportProjectionLaws S.higher.integral S.higher.integralTensor
      S.higher.integralExchange S.integralFiniteTorDomain ∧
    CompactSupportProjectionLaws S.higher.rational S.higher.rationalTensor
      S.higher.rationalExchange (fun _ _ ↦ True) ∧
    CompactSupportProjectionLaws S.closure.commonStage S.closure.commonStageTensor
      S.closure.commonStageExchange (fun _ _ ↦ True) ∧
    (∀ m : ℕ, CompactSupportFiniteProjection.Laws
      (S.integralNormalization.finiteLevels m)) ∧
    ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
      CompactSupportProjectionLaws (S.closure.coefficientStages E₀).integral
        (S.closure.coefficientStages E₀).integralTensor
        (S.closure.coefficientStages E₀).integralExchange
        (fun X K ↦ finiteTorConstructibleIntegral C.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X.obj.left K.obj) ∧
      CompactSupportProjectionLaws (S.closure.coefficientStages E₀).rational
        (S.closure.coefficientStages E₀).rationalTensor
        (S.closure.coefficientStages E₀).rationalExchange (fun _ _ ↦ True) ∧
      ∀ m : ℕ, CompactSupportFiniteProjection.Laws
        ((S.coefficientIntegralNormalization E₀).finiteLevels m) := by
  sorry

/-- The actual scalar-change square for projection, in ordinary tensor coordinates.
The scalar/tensor and scalar/pullback maps are the published normalized maps, and
support comparison is their adjunction mate. Composition of coefficient pullback
is asserted, rather than assumed. Completed tensor uses the same equation after
its completion units. Source: finite reduction and scalar extension clauses
(blueprint: fix-prop-projection-formula). -/
def CompactSupportProjectionChange
    {R S : PurCompactSupport.Coefficients.{u}} (a : PurCompactSupport.Change R S)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (proEtaleRingModules X (R.ring X)))
    (L : DerivedCategory (proEtaleRingModules Y (R.ring Y))) : Prop :=
  let HR := R.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
    (R.ring Y) (R.ring c.Z) (R.ring X) (R.pull c.g) (R.pull c.i)
  let HS := S.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
    (S.ring Y) (S.ring c.Z) (S.ring X) (S.pull c.g) (S.pull c.i)
  Nonempty HR ∧ Nonempty HS ∧ ∀ (hR : HR) (hS : HS)
    (aX : ProEtaleTensorModel X (R.ring X))
    (aZ : ProEtaleTensorModel c.Z (R.ring c.Z))
    (aY : ProEtaleTensorModel Y (R.ring Y))
    (bX : ProEtaleTensorModel X (S.ring X))
    (bZ : ProEtaleTensorModel c.Z (S.ring c.Z))
    (bY : ProEtaleTensorModel Y (S.ring Y)),
    let CX := pbcDerivedExtend (a.map X)
    let CY := pbcDerivedExtend (a.map Y)
    let PR := PurCompactSupport.image R c
    let PS := PurCompactSupport.image S c
    let piR := PurCompactSupport.projectionMap R c aX aZ aY hR
    let piS := PurCompactSupport.projectionMap S c bX bZ bY hS
    CY.map ((piR.app K).app L) ≫
        (PurCompactSupport.comparison a c).app
          (aX.tensor.obj (K, (PurCompactSupport.pull R f).obj L)) ≫
        PS.map ((PurCompactSupport.scalarTensor (a.map X) aX bX).hom.app
          (K, (PurCompactSupport.pull R f).obj L) ≫
            bX.tensor.map (Prod.mkHom (𝟙 _) ((PurCompactSupport.scalarPull a f).hom.app L))) =
      (PurCompactSupport.scalarTensor (a.map Y) aY bY).hom.app (PR.obj K, L) ≫
        bY.tensor.map (Prod.mkHom ((PurCompactSupport.comparison a c).app K) (𝟙 _)) ≫
          (piS.app (CX.obj K)).app (CY.obj L)

/-- Compatibility of the specified projection with every positive finite reduction,
finite coefficient inclusion (including ramification), and integral scalar extension.
Rational and algebraically closed compatibility is its localization and inclusion,
as recorded by SixFunctorExchangeComparison.projection in the operation datum.
Source: blueprint proof steps 3--6 (blueprint: fix-prop-projection-formula).
Proof (postponed): the coefficient changes are the actual quotient or integer-ring
maps. Their pullback-composition identities hold on constant sections and hence
after sheafification; at the completed stage compose with all quotient projections.
Transpose the two routes in the displayed square under the proper adjunction.
The scalar comparisons are the normalized mates of restriction, so mate pasting
reduces the square to associativity of the ordinary tensor and compatibility of its
unit sections. The signed K-flat total tensor gives exactly these comparisons on
complexes. The open adjunction unit gives the open factor square, and composing
it with the proper square gives the assertion. Finite-Tor bounds ensure the
reductions and support comparisons lie in their prescribed bounded constructible
domains. The same coherent system equation commutes with completion units, so
uniqueness of extension across those units proves the completed square. Applying
raw rationalization preserves this equality, including all denominators. Applying
a common-stage inclusion preserves it for arbitrary initial coefficient fields. -/
theorem compactSupportProjectionFormula_coefficients
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left) :
    (∀ (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (h : n ≤ m)
      (K : finiteTorConstructibleCategory C.l E m hm X.obj.left)
      (L : finiteTorConstructibleCategory C.l E m hm Y.obj.left),
      CompactSupportProjectionChange (PurCompactSupport.finiteQuotientChange C.l E m n hm hn h)
        c K.obj L.obj) ∧
    (∀ (n : ℕ) (hn : 1 ≤ n)
      (K : sfIntegralConstructibleCategory C.l E X.obj.left)
      (L : sfIntegralConstructibleCategory C.l E Y.obj.left),
      finiteTorConstructibleIntegral C.l E X.obj.left K.obj →
      finiteTorConstructibleIntegral C.l E Y.obj.left L.obj →
      CompactSupportProjectionChange (PurCompactSupport.reduction C.l E n hn) c K.obj L.obj) ∧
    (∀ (F : Type u) [Field F] [Algebra (Padic C.l) F]
      [FiniteDimensional (Padic C.l) F] (i : E →ₐ[Padic C.l] F)
      (K : sfIntegralConstructibleCategory C.l E X.obj.left)
      (L : sfIntegralConstructibleCategory C.l E Y.obj.left),
      finiteTorConstructibleIntegral C.l E Y.obj.left L.obj →
      CompactSupportProjectionChange (PurCompactSupport.completedChange C.l E F i)
        c K.obj L.obj) ∧
    (∀ (F : Type u) [Field F] [Algebra (Padic C.l) F]
      [FiniteDimensional (Padic C.l) F] (i : E →ₐ[Padic C.l] F)
      (e : ℕ) (he : PurCompactSupport.Ramification C.l E F i e) (hepos : 1 ≤ e)
      (n : ℕ) (hn : 1 ≤ n)
      (K : sixFunctorFiniteCategory D C E n hn X)
      (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left),
      CompactSupportProjectionChange
        (PurCompactSupport.finiteChange C.l E F i e he hepos n hn) c K.obj L.obj) := by
  sorry
open CategoryTheory.Endofunctor

/-- A component of the counit projection mate, in product coordinates.
Source: def-exchange-projection, proper factor
(blueprint: fix-prop-projection-formula). -/
def compactProjectionProperMate {A : Type a} {B : Type b}
    [Category.{ha} A] [Category.{hb} B]
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) {F : B ⥤ A} {G : A ⥤ B}
    (adj : F ⊣ G) (mu : ∀ M N : B,
      F.obj (TB.obj (M, N)) ≅ TA.obj (F.obj M, F.obj N)) (K : A) (L : B) :
    TB.obj (G.obj K, L) ⟶ G.obj (TA.obj (K, F.obj L)) :=
  adj.homEquiv _ _ ((mu (G.obj K) L).hom ≫
    TA.map (Prod.mkHom (adj.counit.app K) (𝟙 _)))

/-- The forward open projection mate; compact support uses its inverse.
Source: def-exchange-projection, open factor
(blueprint: fix-prop-projection-formula). -/
def compactProjectionOpenMate {A : Type a} {B : Type b}
    [Category.{ha} A] [Category.{hb} B]
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) {J : A ⥤ B} {F : B ⥤ A}
    (adj : J ⊣ F) (mu : ∀ M N : B,
      F.obj (TB.obj (M, N)) ≅ TA.obj (F.obj M, F.obj N)) (K : A) (L : B) :
    J.obj (TA.obj (K, F.obj L)) ⟶ TB.obj (J.obj K, L) :=
  (adj.homEquiv _ _).symm
    (TA.map (Prod.mkHom (adj.unit.app K) (𝟙 _)) ≫ (mu (J.obj K) L).inv)

/-- Tensor of fixed pairs with the specified pullback/tensor comparison.
Source: step 13, tensor structure formula
(blueprint: fix-prop-projection-formula). -/
def compactProjectionTensorPair {A : Type a} [Category.{ha} A]
    (P : A ⥤ A) (T : A × A ⥤ A)
    (mu : ∀ M N : A, P.obj (T.obj (M, N)) ≅ T.obj (P.obj M, P.obj N))
    (K L : IsoAlgebra P) : IsoAlgebra P :=
  IsoAlgebra.mk (T.obj (K.carrier, L.carrier))
    (mu K.carrier L.carrier ≪≫ T.mapIso (K.str.prod L.str))

namespace CompactSupportWeilProjection
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The prescribed rational tensor on a geometric fibre, with inherited prime units.
Source: def-weil-derived-pullback-tensor-hom
(blueprint: fix-prop-projection-formula). -/
def tensor (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :
    sfRationalConstructibleCategory l E (D.geometricFiber T₀).left ×
      sfRationalConstructibleCategory l E (D.geometricFiber T₀).left ⥤
        sfRationalConstructibleCategory l E (D.geometricFiber T₀).left :=
  letI := sfWeilPrimeInvertible D l hl T₀
  rationalDerivedTensor l E (D.geometricFiber T₀).left

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical tensor/pullback comparison on the geometric morphism.
Source: completed quotient-tensor normalization
(blueprint: fix-prop-projection-formula). -/
def mu {U₀ T₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] (h₀ : U₀ ⟶ T₀)
    (K L : sfRationalConstructibleCategory l E (D.geometricFiber T₀).left) :
    (fieldWeilPull D l hl E h₀).obj ((tensor D l hl E T₀).obj (K, L)) ≅
      (tensor D l hl E U₀).obj
        ((fieldWeilPull D l hl E h₀).obj K, (fieldWeilPull D l hl E h₀).obj L) :=
  letI := sfWeilPrimeInvertible D l hl U₀
  letI := sfWeilPrimeInvertible D l hl T₀
  canonicalRationalPullbackTensor l E (zlFiberMap D h₀) K L

/-- Tensor on the actual framework Weil pairs, before the normalized PBC comparison.
Source: step 13, mu followed by tensor of the two Weil maps
(blueprint: fix-prop-projection-formula). -/
def tensorPair (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (K L : sfWeilComplex D l hl T₀ E) : sfWeilComplex D l hl T₀ E :=
  letI := sfWeilPrimeInvertible D l hl T₀
  compactProjectionTensorPair (sfWeilFrobeniusPullback D l hl T₀ E)
    (tensor D l hl E T₀)
    (canonicalRationalPullbackTensor l E (D.geometricFrobenius T₀).hom) K L
variable {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (f₀ : X₀ ⟶ Y₀) (c₀ : Compactification f₀.left)

/-- The open mate for the retained model compactification.
Source: step 13, canonical open factor
(blueprint: fix-prop-projection-formula). -/
def openMate
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left)
    (L : sfRationalConstructibleCategory l E
      (D.geometricFiber (zlCompactificationMiddle D f₀ c₀)).left) :
    (fieldWeilOpen D l hl E (zlCompactificationOpen D f₀ c₀)).obj
        ((tensor D l hl E X₀).obj
          (K, (fieldWeilPull D l hl E (zlCompactificationOpen D f₀ c₀)).obj L)) ⟶
      (tensor D l hl E (zlCompactificationMiddle D f₀ c₀)).obj
        ((fieldWeilOpen D l hl E (zlCompactificationOpen D f₀ c₀)).obj K, L) :=
  compactProjectionOpenMate (tensor D l hl E X₀)
    (tensor D l hl E (zlCompactificationMiddle D f₀ c₀))
    (fieldWeilOpenAdj D l hl E (zlCompactificationOpen D f₀ c₀))
    (mu D l hl E (zlCompactificationOpen D f₀ c₀)) K L

/-- The inverse open factor is legitimate on every rational constructible pair.
Source: step 13 and open projection formula
(blueprint: fix-prop-projection-formula).
Proof: restrict the map along the open immersion. The adjunction unit is an
isomorphism and the displayed tensor comparison identifies the result with the
identity. On the complementary closed part both sides are zero. The open/closed
localization triangle detects its cone, proving that this particular mate is an
isomorphism. Rationalization preserves the same inverse. -/
theorem openMate_isIso
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left)
    (L : sfRationalConstructibleCategory l E
      (D.geometricFiber (zlCompactificationMiddle D f₀ c₀)).left) :
    IsIso (openMate D l hl E f₀ c₀ K L) := by
  sorry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized factorization of inverse image along the compactification.
Source: pullback composition, with the actual factorization equality
(blueprint: fix-prop-projection-formula). -/
def pullFactor : fieldWeilPull D l hl E f₀ ≅
    fieldWeilPull D l hl E (zlCompactificationProper D f₀ c₀) ⋙
      fieldWeilPull D l hl E (zlCompactificationOpen D f₀ c₀) :=
  letI := sfWeilPrimeInvertible D l hl X₀
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := sfWeilPrimeInvertible D l hl (zlCompactificationMiddle D f₀ c₀)
  eqToIso (congrArg (fun g ↦ rationalDerivedPullback l E g)
    (zlGeometricCompactification_comm D f₀ c₀)) ≪≫
    fieldRationalPullComp l E
      (zlFiberMap D (zlCompactificationOpen D f₀ c₀))
      (zlFiberMap D (zlCompactificationProper D f₀ c₀))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The exact proper-counit/open-inverse projection, in canonical adjoint coordinates.
Source: projection transformation, steps 13--14
(blueprint: fix-prop-projection-formula). -/
def component
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left)
    (L : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :
    (tensor D l hl E Y₀).obj ((fieldWeilShriek D l hl E f₀ c₀).obj K, L) ⟶
      (fieldWeilShriek D l hl E f₀ c₀).obj
        ((tensor D l hl E X₀).obj (K, (fieldWeilPull D l hl E f₀).obj L)) :=
  letI : IsProper (zlCompactificationProper D f₀ c₀).left :=
    inferInstanceAs (IsProper c₀.g)
  letI := openMate_isIso D l hl E f₀ c₀ K
    ((fieldWeilPull D l hl E (zlCompactificationProper D f₀ c₀)).obj L)
  compactProjectionProperMate
      (tensor D l hl E (zlCompactificationMiddle D f₀ c₀)) (tensor D l hl E Y₀)
      (fieldWeilProperAdj D l hl E (zlCompactificationProper D f₀ c₀))
      (mu D l hl E (zlCompactificationProper D f₀ c₀))
      ((fieldWeilOpen D l hl E (zlCompactificationOpen D f₀ c₀)).obj K) L ≫
    (fieldWeilProper D l hl E (zlCompactificationProper D f₀ c₀)).map
      (inv (openMate D l hl E f₀ c₀ K
        ((fieldWeilPull D l hl E (zlCompactificationProper D f₀ c₀)).obj L))) ≫
    (fieldWeilShriek D l hl E f₀ c₀).map
      ((tensor D l hl E X₀).map (Prod.mkHom (𝟙 _) ((pullFactor D l hl E f₀ c₀).inv.app L)))

/-- The prescribed compact-support functor on fixed pairs.
Source: Ex! followed by Rf!(theta)
(blueprint: fix-prop-projection-formula). -/
def supportPair : sfWeilComplex D l hl X₀ E ⥤ sfWeilComplex D l hl Y₀ E :=
  IsoAlgebra.mapOfNatIso (fieldWeilShriekExchange D l hl E f₀ c₀)

/-- The prescribed pullback functor on fixed pairs.
Source: inverse-image composition around the geometric Frobenius square
(blueprint: fix-prop-projection-formula). -/
def pullPair : sfWeilComplex D l hl Y₀ E ⥤ sfWeilComplex D l hl X₀ E :=
  IsoAlgebra.mapOfNatIso (fieldWeilPullSquare D l hl E f₀)

/-- The canonical projection is an isomorphism of the prescribed fixed pairs.
No integral lift of either rational structure is required.
Source: projection-formula steps 13--15
(blueprint: fix-prop-projection-formula).
Proof: tensor, pullback and support have exactly their displayed Frobenius maps.
Transpose the proper projection square under the proper adjunction. The counit
mate identity and composition-compatible tensor comparison identify the two
transposes. The open unit calculation gives the same equation for the open mate
and hence its inverse. Pasting gives equivariance of component. Invertibility
follows from the rational projection formula, transported along the unique
proper/open adjoint comparisons and the recorded compact-support realization.
The inverse of an equivariant isomorphism is equivariant. The faithful forgetful
functor fixes both forward and inverse arrows uniquely. This calculation uses
the actual rational structure isomorphisms and their naturality, so clearing
localized denominators does not require an integral Weil lattice. -/
theorem restriction
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (K : sfWeilComplex D l hl X₀ E) (L : sfWeilComplex D l hl Y₀ E) :
    ∃! e : tensorPair D l hl E Y₀ ((supportPair D l hl E f₀ c₀).obj K) L ≅
        (supportPair D l hl E f₀ c₀).obj
          (tensorPair D l hl E X₀ K ((pullPair D l hl E f₀).obj L)),
      e.hom.hom.f = component D l hl E f₀ c₀ K.carrier L.carrier := by
  sorry

/-- The unique fixed-pair isomorphism with the specified projection as forward map.
Source: projection-formula Weil clause, steps 13--15
(blueprint: fix-prop-projection-formula). -/
def iso [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (K : sfWeilComplex D l hl X₀ E) (L : sfWeilComplex D l hl Y₀ E) :
    tensorPair D l hl E Y₀ ((supportPair D l hl E f₀ c₀).obj K) L ≅
      (supportPair D l hl E f₀ c₀).obj
        (tensorPair D l hl E X₀ K ((pullPair D l hl E f₀).obj L)) :=
  (restriction D l hl E f₀ c₀ K L).exists.choose

end CompactSupportWeilProjection



namespace CompactSupportPbcTransport
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (T₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
  (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)

/-- Completed Frobenius preserves the integral constructible domain.
Source: step 13, exact transport/completion comparison
(blueprint: fix-prop-projection-formula).
Proof: the actual completed pullback identifies with exact Frobenius transport by
pbcIsoCompletedPullback_identification. Exact transport preserves every integral
stratum, reduction and uniform bound. Invariance under that isomorphism gives the
stated membership, without identifying completion with ordinary transport. -/
theorem integral_mem (K : pbcIntegralStage C.l C.Qbar (D.geometricFiber T₀).left E₀) :
    PbcIsBoundedConstructibleComplete (D.geometricFiber T₀).left
      (pbcStageDatum.{u} C.l C.Qbar E₀)
      (completedPullbackObject (D.geometricFrobenius T₀).hom
        (pbcStageDatum.{u} C.l C.Qbar E₀) K.obj) := by
  sorry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction of the published normalized completion/transport comparison.
Source: step 13, canonical completion unit
(blueprint: fix-prop-projection-formula). -/
def integralBridge (K : pbcIntegralStage C.l C.Qbar (D.geometricFiber T₀).left E₀) :
    (⟨completedPullbackObject (D.geometricFrobenius T₀).hom
      (pbcStageDatum.{u} C.l C.Qbar E₀) K.obj,
        integral_mem D C T₀ E₀ K⟩ :
      pbcIntegralStage C.l C.Qbar (D.geometricFiber T₀).left E₀) ≅
    (pbcIsoIntegralPullback (D.geometricFrobenius T₀).hom
      (pbcStageDatum.{u} C.l C.Qbar E₀)).obj K :=
  ObjectProperty.isoMk _ (pbcIsoCompletedPullback_identification
    (D.geometricFrobenius T₀).hom (pbcStageDatum.{u} C.l C.Qbar E₀) K)
variable (F : FdCoefficientComparisonSystem.{u} C.l C.Qbar)
  (W : FdFrobeniusComparison C.l C.Qbar D C.different F T₀)

/-- Completed Frobenius in the comparison's original coefficient presentation.
Source: step 13, common-stage coefficient convention
(blueprint: fix-prop-projection-formula). -/
def completedFrobenius : pbcStageCategory C.l C.Qbar (D.geometricFiber T₀).left E₀ ⥤
    pbcStageCategory C.l C.Qbar (D.geometricFiber T₀).left E₀ :=
  letI := W.noetherian
  letI := W.dimension
  letI := W.invertible
  (pbcQbarPullFamily C.l C.Qbar (D.geometricFrobenius T₀).hom).Φ E₀

/-- The exact Weil convention and the completed comparison convention are related
by the localization of the actual completion/transport isomorphism.
Source: step 13 (blueprint: fix-prop-projection-formula).
Proof: localize integralBridge and its inverse. The completed-family defining
formula identifies the source objects and maps; exact transport is the prescribed
pbcRationalIsoPullback. Naturality on integral maps extends by linearity to every
localized arrow. Every rational object retains an integral representative, so the
normalization determines all components and hence the natural isomorphism uniquely. -/
theorem bridge_existsUnique :
    ∃! b : completedFrobenius D C T₀ E₀ F W ≅ weilFrobeniusPullback D C T₀ E₀,
      ∀ K : pbcIntegralStage C.l C.Qbar (D.geometricFiber T₀).left E₀,
        HEq (b.hom.app ((pbcStageLocalization C.l C.Qbar
          (D.geometricFiber T₀).left E₀).obj K))
          (fdRawTensor (pbcStageUniformizer.{u} C.l C.Qbar E₀) 1
            (integralBridge D C T₀ E₀ K).hom) := by
  sorry

/-- The uniquely normalized bridge, retaining the completion comparison.
Source: step 13 (blueprint: fix-prop-projection-formula). -/
def bridge : completedFrobenius D C T₀ E₀ F W ≅ weilFrobeniusPullback D C T₀ E₀ :=
  (bridge_existsUnique D C T₀ E₀ F W).exists.choose

/-- Convert completed fixed pairs to the exact WeilD convention. Carriers and
arrows are unchanged; only the prescribed structure comparison is inserted.
Source: step 13 (blueprint: fix-prop-projection-formula). -/
def toExact : IsoAlgebra (completedFrobenius D C T₀ E₀ F W) ⥤ WeilD D C T₀ E₀ :=
  IsoAlgebra.mapOfNatIso
    ((weilFrobeniusPullback D C T₀ E₀).leftUnitor ≪≫
      (bridge D C T₀ E₀ F W).symm ≪≫
        (completedFrobenius D C T₀ E₀ F W).rightUnitor.symm)

/-- Inverse transport of fixed pairs along the same bridge.
Source: step 13 (blueprint: fix-prop-projection-formula). -/
def fromExact : WeilD D C T₀ E₀ ⥤ IsoAlgebra (completedFrobenius D C T₀ E₀ F W) :=
  IsoAlgebra.mapOfNatIso
    ((completedFrobenius D C T₀ E₀ F W).leftUnitor ≪≫
      bridge D C T₀ E₀ F W ≪≫ (weilFrobeniusPullback D C T₀ E₀).rightUnitor.symm)

/-- The named rational coefficient comparison with its inherited geometric facts.
Source: step 13 (blueprint: fix-prop-projection-formula). -/
def realization : sfRationalConstructibleCategory C.l
    (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left ⥤
      pbcStageCategory C.l C.Qbar (D.geometricFiber T₀).left E₀ :=
  letI := W.noetherian
  letI := W.dimension
  letI := W.invertible
  ((F.coefficients (D.geometricFiber T₀).left).stage E₀).rational.functor

/-- The coefficient realization followed by the normalized exact-pair bridge.
Source: step 13 (blueprint: fix-prop-projection-formula). -/
def pairRealization : sfWeilComplex D C.l C.different T₀
    (pbcFiniteField C.l C.Qbar E₀) ⥤ WeilD D C T₀ E₀ :=
  (W.finite E₀).functor ⋙ toExact D C T₀ E₀ F W

/-- The inverse coefficient realization after undoing the exact-pair bridge.
Source: step 13 (blueprint: fix-prop-projection-formula). -/
def pairInverse : WeilD D C T₀ E₀ ⥤ sfWeilComplex D C.l C.different T₀
    (pbcFiniteField C.l C.Qbar E₀) :=
  fromExact D C T₀ E₀ F W ⋙ (W.finite E₀).inverse


/-- The raw coefficient realization of the inverse Weil presentation cancels
by the actual finite equivalence counit; exact/completed transport leaves its
carrier unchanged.
Source: step 13 (blueprint: fix-prop-projection-formula).
Proof: use finite_functors to identify the underlying functor of W.finite with
the recorded rational realization. Apply its counit at fromExact K. Inserting
toExact cancels the same bridge with its inverse, without changing carriers.
This fixes the raw counit arrow, and forgetting Weil structures is faithful. -/
theorem cancellation_existsUnique (K : WeilD D C T₀ E₀) :
    ∃! e : (realization D C T₀ E₀ F W).obj
        ((pairInverse D C T₀ E₀ F W).obj K).carrier ≅ K.carrier,
      HEq e.hom
        (((W.finite E₀).counitIso.hom.app ((fromExact D C T₀ E₀ F W).obj K)).hom.f) := by
  sorry

/-- The raw finite-counit cancellation with its fixed underlying arrow.
Source: step 13 (blueprint: fix-prop-projection-formula). -/
def cancellation (K : WeilD D C T₀ E₀) :
    (realization D C T₀ E₀ F W).obj
      ((pairInverse D C T₀ E₀ F W).obj K).carrier ≅ K.carrier :=
  (cancellation_existsUnique D C T₀ E₀ F W K).exists.choose

end CompactSupportPbcTransport

namespace CompactSupportPbcProjection
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (F : FdCoefficientComparisonSystem.{u} C.l C.Qbar)
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (WX : FdFrobeniusComparison C.l C.Qbar D C.different F X₀)
  (WY : FdFrobeniusComparison C.l C.Qbar D C.different F Y₀)
  (f₀ : X₀ ⟶ Y₀) (c₀ : Compactification f₀.left)
  (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)

/-- Source of projection in the actual WeilD category under the normalized coefficient
comparison. The two input Weil isomorphisms are entirely arbitrary rational arrows.
Source: step 13, coefficient-category comparison
(blueprint: fix-prop-projection-formula). -/
def source (K : WeilD D C X₀ E₀) (L : WeilD D C Y₀ E₀) : WeilD D C Y₀ E₀ :=
  (CompactSupportPbcTransport.pairRealization D C Y₀ E₀ F WY).obj
    (CompactSupportWeilProjection.tensorPair D C.l C.different
      (pbcFiniteField C.l C.Qbar E₀) Y₀
      ((CompactSupportWeilProjection.supportPair D C.l C.different
        (pbcFiniteField C.l C.Qbar E₀) f₀ c₀).obj
        ((CompactSupportPbcTransport.pairInverse D C X₀ E₀ F WX).obj K))
      ((CompactSupportPbcTransport.pairInverse D C Y₀ E₀ F WY).obj L))

/-- Target of projection in actual WeilD, using the canonical support and pullback
Frobenius exchanges, and the same tensor comparison as at the source.
Source: step 13, coefficient-category comparison
(blueprint: fix-prop-projection-formula). -/
def target (K : WeilD D C X₀ E₀) (L : WeilD D C Y₀ E₀) : WeilD D C Y₀ E₀ :=
  (CompactSupportPbcTransport.pairRealization D C Y₀ E₀ F WY).obj
    ((CompactSupportWeilProjection.supportPair D C.l C.different
      (pbcFiniteField C.l C.Qbar E₀) f₀ c₀).obj
      (CompactSupportWeilProjection.tensorPair D C.l C.different
        (pbcFiniteField C.l C.Qbar E₀) X₀
        ((CompactSupportPbcTransport.pairInverse D C X₀ E₀ F WX).obj K)
        ((CompactSupportWeilProjection.pullPair D C.l C.different
          (pbcFiniteField C.l C.Qbar E₀) f₀).obj
          ((CompactSupportPbcTransport.pairInverse D C Y₀ E₀ F WY).obj L))))

/-- There is a unique Weil isomorphism whose forward arrow is the normalized
coefficient image of the proper/open
projection, not a replacement isomorphism. The fixed-pair comparison acts on underlying
arrows by the recorded raw-localization comparison.
Source: steps 13--15 (blueprint: fix-prop-projection-formula).
Proof: the unique defining equation for the framework iso identifies its forward
arrow with component. Apply the coefficient functor. The finite_functors equation
in the Frobenius comparison identifies this with the underlying fixed-pair map.
The objects and localized tensors of FdRationalStageComparison retain the same
integral representatives and all rational denominators, giving precisely HEq. -/
theorem forward [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (K : WeilD D C X₀ E₀) (L : WeilD D C Y₀ E₀) :
    ∃! e : source D C F WX WY f₀ c₀ E₀ K L ≅ target D C F WX WY f₀ c₀ E₀ K L,
      HEq e.hom.hom.f
      ((CompactSupportPbcTransport.realization D C Y₀ E₀ F WY).map
        (CompactSupportWeilProjection.component D C.l C.different
          (pbcFiniteField C.l C.Qbar E₀) f₀ c₀
          ((CompactSupportPbcTransport.pairInverse D C X₀ E₀ F WX).obj K).carrier
          ((CompactSupportPbcTransport.pairInverse D C Y₀ E₀ F WY).obj L).carrier)) := by
  sorry

/-- The canonical projection isomorphism on actual WeilD. Its underlying arrow
is fixed uniquely by forward, so this definition selects no arbitrary map.
Source: steps 13--15 (blueprint: fix-prop-projection-formula). -/
def iso [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (K : WeilD D C X₀ E₀) (L : WeilD D C Y₀ E₀) :
    source D C F WX WY f₀ c₀ E₀ K L ≅ target D C F WX WY f₀ c₀ E₀ K L :=
  (forward D C F WX WY f₀ c₀ E₀ K L).exists.choose


/-- The specified tensor-comparison arrow, with its category exposed explicitly.
It is the integral-normalized coefficient tensor comparison, then the actual
finite-equivalence counit cancellations, then R.chi.
Source: projection-formula proof step 13 (blueprint: fix-prop-projection-formula). -/
def tensorComparisonArrow
    (R : WfTensorCompletion.RationalComparison D C Y₀ E₀)
    (hR : R.Normalized D C Y₀ E₀) (K L : WeilD D C Y₀ E₀) :
    (CompactSupportCoefficientTensor.rational D C Y₀ E₀ F WY).obj
        ((CompactSupportCoefficientTensor.rationalTensor D C Y₀ E₀).obj
          (((CompactSupportPbcTransport.pairInverse D C Y₀ E₀ F WY).obj K).carrier,
            ((CompactSupportPbcTransport.pairInverse D C Y₀ E₀ F WY).obj L).carrier)) ⟶
      R.completed.obj (K.carrier, L.carrier) :=
  (CompactSupportCoefficientTensor.comparison D C Y₀ E₀ F WY R hR).hom.app
            (((CompactSupportPbcTransport.pairInverse D C Y₀ E₀ F WY).obj K).carrier,
              ((CompactSupportPbcTransport.pairInverse D C Y₀ E₀ F WY).obj L).carrier) ≫
          R.ordinary.map (Prod.mkHom
            (CompactSupportPbcTransport.cancellation D C Y₀ E₀ F WY K).hom
            (CompactSupportPbcTransport.cancellation D C Y₀ E₀ F WY L).hom) ≫
          R.chi.hom.app (K.carrier, L.carrier)

/-- The canonical tensor-presentation comparison: the coefficient tensor map
normalized on integral representatives, the W.finite/bridge counit cancellation,
and finally R.chi. The ambient carrier equality is stated explicitly before
identifying the two structure-map types.
Source: step 13 (blueprint: fix-prop-projection-formula).
Proof: the coefficient comparison is fixed on homogeneous local pure tensors,
then on K-flat representatives and by the inverse quotient completion unit.
Its integral comparison localizes to comparison. The finite equivalence counits
cancel the two inverse presentations; the bridge and its inverse cancel in the
Weil structures. Apply R.ordinary to these two counits and compose with R.chi.
The Frobenius compatibility of each normalized comparison proves equivariance
for arbitrary rational structure maps. Fullness lifts that specific underlying
isomorphism, and faithfulness proves uniqueness. The normalization of R.completed
on unchanged integral representatives identifies its ambient carrier with the
wfTensor object; its completedMu normalization identifies its structure map
with wfTensorFrobenius on that same object. -/
theorem tensor_identification
    (R : WfTensorCompletion.RationalComparison D C Y₀ E₀)
    (hR : R.Normalized D C Y₀ E₀)
    (K L : WeilD D C Y₀ E₀) :
    (∃! e : (CompactSupportPbcTransport.pairRealization D C Y₀ E₀ F WY).obj
        (CompactSupportWeilProjection.tensorPair D C.l C.different
          (pbcFiniteField C.l C.Qbar E₀) Y₀
          ((CompactSupportPbcTransport.pairInverse D C Y₀ E₀ F WY).obj K)
          ((CompactSupportPbcTransport.pairInverse D C Y₀ E₀ F WY).obj L)) ≅
        R.completedPair D C Y₀ E₀ K L,
      HEq e.hom.hom.f
        (tensorComparisonArrow D C F WY E₀ R hR K L)) ∧
    wfWeilCarrier D C Y₀ E₀ (R.completedPair D C Y₀ E₀ K L) =
      (wfTensor D C Y₀ E₀).obj
        (wfWeilCarrier D C Y₀ E₀ K, wfWeilCarrier D C Y₀ E₀ L) ∧
    HEq (wfWeilStructure D C Y₀ E₀ (R.completedPair D C Y₀ E₀ K L)).hom
      (wfTensorFrobenius D C Y₀ E₀ K L).hom := by
  sorry

/-- Inclusion of the canonical finite-stage projection in the actual common-stage
WeilDQbar category. All choices of a common finite field are allowed, including an
identity extension; the input objects retain their actual Weil maps.
Source: step 14, common-stage prescription
(blueprint: fix-prop-projection-formula). -/
def commonIso [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (K : WeilDQbar D C X₀) (L : WeilDQbar D C Y₀)
    (hK : K.stage ≤ E₀) (hL : L.stage ≤ E₀) :
    ((weilScalarSystem D C Y₀).ι E₀).obj
        (source D C F WX WY f₀ c₀ E₀
          (((weilScalarSystem D C X₀).T hK).obj K.obj)
          (((weilScalarSystem D C Y₀).T hL).obj L.obj)) ≅
      ((weilScalarSystem D C Y₀).ι E₀).obj
        (target D C F WX WY f₀ c₀ E₀
          (((weilScalarSystem D C X₀).T hK).obj K.obj)
          (((weilScalarSystem D C Y₀).T hL).obj L.obj)) :=
  ((weilScalarSystem D C Y₀).ι E₀).mapIso
    (iso D C F WX WY f₀ c₀ E₀
      (((weilScalarSystem D C X₀).T hK).obj K.obj)
      (((weilScalarSystem D C Y₀).T hL).obj L.obj))

end CompactSupportPbcProjection
end WeilConjectures
