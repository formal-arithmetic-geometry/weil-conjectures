/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.FrobeniusCoefficientTwistsCanonical
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison

/-! # Canonical source transports for smooth purity

Source: main-20261015, prop-weil-operations.proof.md, sentences 3--4;
sk-prop-sp-rational, Steps 1--2, and thm-pur-adic-reconstruction
(blueprint: def-pur-canonical-purity-source-transports).

The source functors retain the actual localization, coefficient and shift
comparisons. Completed-to-ordinary tensor is fixed on strict Roos representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme CategoryTheory.Endofunctor MonoidalCategory
namespace WeilConjectures

namespace RationalSmoothPurityCanonical
/-- The actual rational twisted-pullback functor. The even shift is on the line;
canonical symmetry and shift constraints identify this with Lf*(-)(d)[2d].
Source: rational purity statement
(blueprint: def-pur-canonical-purity-source-transports). -/
def rationalSource (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :=
  ((Functor.const (sfRationalConstructibleCategory l E Y)).obj
      ((sfRationalTwistingCoefficient l E X (d : ℤ))⟦2 * (d : ℤ)⟧)).prod'
        (rationalDerivedPullback l E f) ⋙ rationalDerivedTensor l E X

section CoefficientTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (a : E →ₐ[Padic l] L)

/-- The integral scalar shift inherited from the normalized ordinary comparison.
Source: rational purity proof Step 2, scalar compatibility
(blueprint: def-pur-canonical-purity-source-transports). -/
def integralScalarShift (T : Scheme.{u}) (n : ℤ) :=
  letI := (GeneralAlgebraicallyClosedCoefficients.integralScalarCommShift_existsUnique
    l E L a T).exists.choose
  (sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero E L a T).commShiftIso n

/-- The rational scalar shift is uniquely determined by its integral degree-one components.
Source: rational purity proof Step 2, scalar compatibility
(blueprint: def-pur-canonical-purity-source-transports).
Proof: localize integralScalarShift and its inverse. Naturality on integral arrows
extends to all fractions. The integral zero and addition identities localize too.
The shift and localization are pinned at one. Coherence determines every integer
comparison, and the degree-one component formula gives uniqueness. -/
theorem scalarShift_existsUnique (T : Scheme.{u}) :
    ∃! c : (sfRationalScalarExtension l E T 0 (Fact.out : l.Prime).ne_zero L a).CommShift ℤ,
      (fun [h : (sfRationalScalarExtension l E T 0
          (Fact.out : l.Prime).ne_zero L a).CommShift ℤ] ↦
        ∀ K : sfRationalConstructibleCategory l E T,
          HEq (((sfRationalScalarExtension l E T 0
            (Fact.out : l.Prime).ne_zero L a).commShiftIso (1 : ℤ)).hom.app K)
            ((sfRationalConstructibleLocalization l L T).map
              ((integralScalarShift l E L a T (1 : ℤ)).hom.app K.obj))) (h := c) := by
  sorry

/-- The scalar shift fixed by localization of the ordinary integral comparison.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-purity-source-transports). -/
@[instance_reducible]
def scalarShift (T : Scheme.{u}) :
    (sfRationalScalarExtension l E T 0 (Fact.out : l.Prime).ne_zero L a).CommShift ℤ :=
  (scalarShift_existsUnique l E L a T).exists.choose

/-- Scalar transport of the degree-zero line in ambient derived coordinates.
Every factor is fixed by completion, single-complex descent, and the signed root-line
scalar comparison; it is not a new line trivialization.
Source: rational purity proof Step 2, finite coefficient extension
(blueprint: def-pur-canonical-purity-source-transports). -/
def lineScalarAmbient (T : Scheme.{u}) [∀ x : T, Invertible (l : T.residueField x)]
    (m : ℤ) :=
  (scalarCompletionIso l E L a T (sfIntegralTwistingObject l E T m)
    (sfIntegralTwistingObject_mem l E T m).1).symm ≪≫
    ((integralOrdinaryScalar l E L a T).mapDerivedCategorySingleFunctor 0).app
      (integralTwistLine l E T m) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (twistLineScalarIso l E T L a m)

/-- The line scalar comparison in intrinsic integral representatives retains that map.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-purity-source-transports).
Proof: the rational scalar functor's object clause is the literal completed integral
scalar extension. The preceding ambient comparison therefore has these underlying
objects. Lift it through the full subcategory inclusion. Faithfulness and the displayed
underlying hom condition give uniqueness. -/
theorem lineScalarIntegral_existsUnique (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)] (m : ℤ) :
    ∃! e : ((sfRationalScalarExtension l E T 0 (Fact.out : l.Prime).ne_zero L a).obj
        (sfRationalTwistingCoefficient l E T m)).obj ≅ sfIntegralTwistingCoefficient l L T m,
      HEq e.hom.hom (lineScalarAmbient l E L a T m).hom := by
  sorry

/-- The rational scalar comparison on the coefficient line.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-purity-source-transports). -/
def lineScalar (T : Scheme.{u}) [∀ x : T, Invertible (l : T.residueField x)] (m : ℤ) :
    (sfRationalScalarExtension l E T 0 (Fact.out : l.Prime).ne_zero L a).obj
      (sfRationalTwistingCoefficient l E T m) ≅ sfRationalTwistingCoefficient l L T m :=
  (sfRationalConstructibleLocalization l L T).mapIso
    (lineScalarIntegral_existsUnique l E L a T m).exists.choose

/-- The canonical pullback/tensor/line/shift comparison for finite scalar extension.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-purity-source-transports). -/
def sourceScalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ)
    (K : sfRationalConstructibleCategory l E Y) :
    (sfRationalScalarExtension l E X 0 (Fact.out : l.Prime).ne_zero L a).obj
        ((rationalSource l E f d).obj K) ≅
      (rationalSource l L f d).obj
        ((sfRationalScalarExtension l E Y 0 (Fact.out : l.Prime).ne_zero L a).obj K) :=
  (rationalTensorScalarComparison l E L a X).app
      ((sfRationalTwistingCoefficient l E X (d : ℤ))⟦2*(d : ℤ)⟧,
        (rationalDerivedPullback l E f).obj K) ≪≫
    (rationalDerivedTensor l L X).mapIso
      (Iso.prod
        ((Functor.commShiftIso
          (sfRationalScalarExtension l E X 0 (Fact.out : l.Prime).ne_zero L a)
          (self := scalarShift l E L a X) (2*(d : ℤ))).app _ ≪≫
          (shiftFunctor _ (2*(d : ℤ))).mapIso (lineScalar l E L a X (d : ℤ)))
        ((rationalPullbackScalarComparison l E L a f).app K))

end CoefficientTransport

section CommonSource
open AlgebraicallyClosedCoefficients GeneralAlgebraicallyClosedCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The shifted coefficient line as a literal pair at the least finite stage.
This is the canonical stage presentation of the existing Qbar Tate line and its shift.
Source: rational purity proof Step 2, common-stage presentation
(blueprint: def-pur-canonical-purity-source-transports). -/
def commonShiftedLine (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (d : ℕ) : generalAlgebraicallyClosedConstructibleCategory l Ω X :=
  ⟨Padic.finiteCoefficientBase l Ω,
    (sfRationalTwistingCoefficient l (Coefficient.{u} l Ω
      (Padic.finiteCoefficientBase l Ω)) X (d : ℤ))⟦2*(d : ℤ)⟧⟩

/-- The actual common-stage tensor and pullback with that shifted coefficient line.
Source: rational purity statement, Qbar source
(blueprint: def-pur-canonical-purity-source-transports). -/
def commonSource {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :=
  ((Functor.const (generalAlgebraicallyClosedConstructibleCategory l Ω Y)).obj
    (commonShiftedLine l Ω X d)).prod' (commonStageDerivedPullback l Ω f) ⋙
      commonStageDerivedTensor l Ω X

/-- The least coefficient stage is contained in every finite stage.
Source: rational purity proof Step 2, the coefficient directed set
(blueprint: def-pur-canonical-purity-source-transports).
Proof: the underlying field of finiteCoefficientBase is bottom, so the inclusion
is bottom_le. The subtype order is the underlying intermediate-field order. -/
theorem base_le (L : Index l Ω) : Padic.finiteCoefficientBase l Ω ≤ L := by
  sorry

/-- The normalized self-transition unitor in the actual stage-system presentation.
Source: rational purity proof Step 2, common-stage identity normalization
(blueprint: def-pur-canonical-purity-source-transports). -/
def selfStageUnit (X : Scheme.{u}) (L : Index l Ω) :
    (stageSystem l Ω X).T (le_rfl : L ≤ L) ≅ 𝟭 (Stage l Ω X L) :=
  operationStageTransitionIso l Ω X L L le_rfl ≪≫ unitor l Ω X L

/-- Scalar transport of the shifted root line to a finite stage.
Source: rational purity proof Step 2, canonical line comparisons
(blueprint: def-pur-canonical-purity-source-transports). -/
def shiftedLineToStage (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (d : ℕ) (L : Index l Ω) :
    (commonShiftedLine l Ω X d).toStage (base_le l Ω L) ≅
      (sfRationalTwistingCoefficient l (Coefficient.{u} l Ω L) X (d : ℤ))⟦2*(d : ℤ)⟧ :=
  (operationStageTransitionIso l Ω X (Padic.finiteCoefficientBase l Ω) L
    (base_le l Ω L)).app _ ≪≫
    (Functor.commShiftIso
      (GeneralAlgebraicallyClosedCoefficients.transition l Ω X
        (Padic.finiteCoefficientBase l Ω) L (base_le l Ω L))
      (self := GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω X
        (Padic.finiteCoefficientBase l Ω) L
        (base_le l Ω L)) (2*(d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2*(d : ℤ))).mapIso
      (lineScalar l (Coefficient.{u} l Ω (Padic.finiteCoefficientBase l Ω))
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω _ L (base_le l Ω L)) X (d : ℤ))

/-- The literal tensor-stage object of the common source.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-purity-source-transports). -/
def commonSourceObject {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :=
  commonStageTensorObject l Ω X (commonShiftedLine l Ω X d)
    (commonStagePullbackObject l Ω f K)

/-- Both selected operation functors retain their specified literal object formulas.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-purity-source-transports).
Proof: use the object clauses of commonStageDerivedPullback_existsUnique and
commonStageDerivedTensor_existsUnique. Substitution gives precisely commonSourceObject. -/
theorem commonSource_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    (commonSource l Ω f d).obj K = commonSourceObject l Ω f d K := by
  sorry

/-- The compositum with the least coefficient field is contained in K's own stage.
Source: rational purity proof Step 2, one-stage presentation
(blueprint: def-pur-canonical-purity-source-transports).
Proof: the two tensor inputs have stages bottom and K.stage, respectively.
Their compositum is the supremum. Apply sup_le with bottom_le and le_rfl. -/
theorem commonSource_stage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    (commonSourceObject l Ω f d K).stage ≤ K.stage := by
  sorry

/-- The source represented over the object's own finite field, with all scalar
associators, root-line comparisons, and self-transition unitors retained.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-purity-source-transports). -/
def commonSourceStageComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    (commonSourceObject l Ω f d K).toStage (commonSource_stage l Ω f d K) ≅
      (rationalSource l (Coefficient.{u} l Ω K.stage) f d).obj K.obj :=
  commonStageTensorComparison l Ω X (commonShiftedLine l Ω X d)
    (commonStagePullbackObject l Ω f K) K.stage (commonSource_stage l Ω f d K) ≪≫
    (rationalDerivedTensor l (Coefficient.{u} l Ω K.stage) X).mapIso
      (Iso.prod (shiftedLineToStage l Ω X d K.stage)
        ((selfStageUnit l Ω X K.stage).app _))

/-- Canonical identification of common-source objects with their rational stage.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-purity-source-transports). -/
def commonSourceComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    (commonSource l Ω f d).obj K ≅
      (GeneralAlgebraicallyClosedCoefficients.inclusion K.stage).obj
        ((rationalSource l (Coefficient.{u} l Ω K.stage) f d).obj K.obj) :=
  eqToIso (commonSource_obj l Ω f d K) ≪≫
    (stageSystem l Ω X).isoToStage (commonSourceObject l Ω f d K)
      (commonSource_stage l Ω f d K) ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion K.stage).mapIso
      (commonSourceStageComparison l Ω f d K)

end CommonSource

end RationalSmoothPurityCanonical

namespace RationalSmoothPurityCanonical

/-- The ordinary K-flat total tensor, before completion.
Source: rational purity proof, integral representatives
(blueprint: def-pur-canonical-purity-source-transports). -/
abbrev ordinaryTotal (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :=
  coefficientTotalTensor.{u, u + 1, u} (ProEt.topology T)
    (completedIntegralCommRingSheafUnrestricted l E T)

/-- The ordinary-to-completed tensor map is the strict quotient augmentation.
Its product component is fixed on all pure total tensors, and its second cone
component is zero. This specifies the full Roos map before localization.
Source: rational purity proof Step 1, completed tensor convention
(blueprint: def-pur-canonical-purity-source-transports).
Proof: send x tensor y to the tensor of their images in each positive quotient.
Balanced tensors and total-summand injections extend this to a chain map to the
product tower. Compatibility with quotient transitions annihilates 1-s.
The mapping-cocone lift with second component zero exists and is unique.
The generator equations and zero second component prove naturality and uniqueness. -/
theorem tensorAugmentation_existsUnique (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :
    ∃! eta : ordinaryTotal l E T ⟶ integralOperationsTensorComplexFunctor l E T,
      (∀ (P Q : CochainComplex (integralTowerModules l E T) ℤ)
        (p q : ℤ) (n : ℕ) (U : T.ProEtᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        (((eta.app (P,Q)).f (p + q) ≫
          (CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism
              (K := fun j ↦ ((integralOperationsTensorTowerFunctor l E T).obj
                (P,Q)).obj (op j))
              (integralOperationsTowerStep
                ((integralOperationsTensorTowerFunctor l E T).obj (P,Q))))).f (p + q) ≫
          (Pi.π (fun j ↦ ((integralOperationsTensorTowerFunctor l E T).obj
            (P,Q)).obj (op j)) n).f (p + q)).val.app U)
            (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology T)
              (completedIntegralCommRingSheafUnrestricted l E T) P Q p q (p+q) rfl U x y) =
          integralOperationsTotalTensorSection l E T n P Q p q U
            (unrestrictedIntegralTensorSection l E T n (P.X p) U 1 x)
            (unrestrictedIntegralTensorSection l E T n (Q.X q) U 1 y)) ∧
      ∀ (P Q : CochainComplex (integralTowerModules l E T) ℤ) (i : ℤ),
        (eta.app (P,Q)).f i ≫
          (CochainComplex.mappingCocone.snd
            (towerTransitionEndomorphism
              (K := fun j ↦ ((integralOperationsTensorTowerFunctor l E T).obj
                (P,Q)).obj (op j))
              (integralOperationsTowerStep
                ((integralOperationsTensorTowerFunctor l E T).obj (P,Q))))).v
                  i (i - 1) (by omega) = 0 := by
  sorry

/-- The fixed tensor augmentation, including both strict cone components.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-purity-source-transports). -/
def tensorAugmentation (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :=
  (tensorAugmentation_existsUnique l E T).exists.choose

/-- The ordinary tensor model belonging to the recorded coherent coefficient calculus.
Its representative is fixed by that calculus's ordinary total-tensor comparison.
Source: rational purity proof, projection-formula transpose
(blueprint: def-pur-canonical-purity-source-transports).
Proof: restrict the calculus's K-flat comparison to flat-term K-flat complexes.
The ordinary totals in the two interfaces are the same signed direct-sum total;
transport across that definitional presentation equality. This produces a natural
isomorphism and fixes it uniquely at every pair of representatives. -/
theorem ordinaryModel_existsUnique (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :
    ∃! a : ProEtaleTensorModel T (completedIntegralCommRingSheafUnrestricted l E T),
      a.tensor = (@RingedSiteDualityModel.closed.{u + 1, u, u, u + 2}
      _ _ _ (IntegralOnSlice.abSheafify.{u, u} T none)
      (IntegralOnSlice.abLocallyBijective.{u, u} T none) _ _
      (IntegralOnSlice.duality.{u, u} l E T none)).tensor ∧
      ∀ (P Q : (proEtaleFlatRepresentatives T
        (completedIntegralCommRingSheafUnrestricted l E T)).FullSubcategory),
        ∀ (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          T.ProEt _ (essentiallySmallSelf.{0, u, u + 1} T.ProEt) (ProEt.topology T)
          (completedIntegralCommRingSheafUnrestricted l E T) P.obj)
          (hQ : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          T.ProEt _ (essentiallySmallSelf.{0, u, u + 1} T.ProEt) (ProEt.topology T)
          (completedIntegralCommRingSheafUnrestricted l E T) Q.obj),
        HEq (a.representative.app (P,Q))
          (@CoefficientTensorModels.iso.{u, u + 1, u, u + 2} _ _ _
            (IntegralOnSlice.abSheafify.{u, u} T none)
            (IntegralOnSlice.abLocallyBijective.{u, u} T none) _ _ _
            (@RingedSiteDualityModel.models.{u + 1, u, u, u + 2}
      _ _ _ (IntegralOnSlice.abSheafify.{u, u} T none)
      (IntegralOnSlice.abLocallyBijective.{u, u} T none) _ _
      (IntegralOnSlice.duality.{u, u} l E T none)) P.obj Q.obj hP hQ) := by
  sorry

/-- The ordinary derived tensor with its fixed representative data.
Source: rational purity proof, tensor transpose
(blueprint: def-pur-canonical-purity-source-transports). -/
def ordinaryModel (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :=
  (ordinaryModel_existsUnique l E T).exists.choose

/-- The two existing K-flat encodings agree for the fixed ordinary module tensor.
Source: rational purity proof, K-flat representatives
(blueprint: def-pur-canonical-purity-source-transports).
Proof: unfold both K-flat predicates. Their test functors are the same signed total
tensor with the same sheaf monoidal structure; the flat-term conjunct is identical. -/
theorem goodOrdinary (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (P : CochainComplex (integralTowerModules l E T) ℤ)
    (hP : integralOperationsGoodComplex l E T P) :
    proEtaleFlatRepresentatives T
      (completedIntegralCommRingSheafUnrestricted l E T) P := by
  sorry

/-- On the constructible finite-Tor domain the ordinary tensor is already complete.
The map asserted invertible is the fixed strict quotient augmentation.
Source: rational purity proof, completed tensor on integral representatives
(blueprint: def-pur-canonical-purity-source-transports).
Proof: choose bounded flat models on a finite constructible stratification. Tensor
with each bounded finite-projective term preserves derived completeness and the
common Tor bounds. Glue the strata by the localization triangles. The strict Roos
augmentation is the completion unit, hence a quasi-isomorphism. -/
theorem tensorAugmentation_isIso (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E T) ℤ)
    (hP : integralOperationsGoodComplex l E T P)
    (hQ : integralOperationsGoodComplex l E T Q)
    (hM : finiteTorConstructibleIntegral l E T (DerivedCategory.Q.obj P))
    (hN : finiteTorConstructibleIntegral l E T (DerivedCategory.Q.obj Q)) :
    IsIso (DerivedCategory.Q.map ((tensorAugmentation l E T).app (P,Q))) := by
  sorry

/-- The completion comparison on good finite-Tor representatives.
Source: rational purity proof, projection transpose
(blueprint: def-pur-canonical-purity-source-transports). -/
def tensorToOrdinaryOnGood (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E T) ℤ)
    (hP : integralOperationsGoodComplex l E T P)
    (hQ : integralOperationsGoodComplex l E T Q)
    (hM : finiteTorConstructibleIntegral l E T (DerivedCategory.Q.obj P))
    (hN : finiteTorConstructibleIntegral l E T (DerivedCategory.Q.obj Q)) :
    (integralCompletedTensor l E T).obj (DerivedCategory.Q.obj P,
      DerivedCategory.Q.obj Q) ≅
    (ordinaryModel l E T).tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
  (integralCompletedTensorComparison l E T).app (⟨P,hP⟩,⟨Q,hQ⟩) ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map ((tensorAugmentation l E T).app (P,Q)))
      (tensorAugmentation_isIso l E T P Q hP hQ hM hN)).symm ≪≫
    (ordinaryModel l E T).representative.app
      (⟨P,goodOrdinary l E T P hP⟩,⟨Q,goodOrdinary l E T Q hQ⟩)

/-- Completion-to-ordinary tensor is fixed on every pair of good representatives.
Source: rational purity proof, tensor transpose
(blueprint: def-pur-canonical-purity-source-transports).
Proof: use flat K-flat resolutions of M and N and the preceding strict augmentation.
Naturality of that augmentation and the representative comparisons makes the result
independent of both resolutions and their isomorphisms. Every pair admits such
resolutions. This proves existence and uniqueness with the displayed normalization. -/
theorem tensorToOrdinary_existsUnique (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (M N : finiteTorConstructibleIntegralCategory l E T) :
    ∃! e : (integralCompletedTensor l E T).obj (M.obj,N.obj) ≅
        (ordinaryModel l E T).tensor.obj (M.obj,N.obj),
      ∀ (P Q : CochainComplex (integralTowerModules l E T) ℤ)
        (hP : integralOperationsGoodComplex l E T P)
        (hQ : integralOperationsGoodComplex l E T Q)
        (hM : finiteTorConstructibleIntegral l E T (DerivedCategory.Q.obj P))
        (hN : finiteTorConstructibleIntegral l E T (DerivedCategory.Q.obj Q))
        (eP : DerivedCategory.Q.obj P ≅ M.obj) (eQ : DerivedCategory.Q.obj Q ≅ N.obj),
        e = (integralCompletedTensor l E T).mapIso (Iso.prod eP.symm eQ.symm) ≪≫
          tensorToOrdinaryOnGood l E T P Q hP hQ hM hN ≪≫
          (ordinaryModel l E T).tensor.mapIso (Iso.prod eP eQ) := by
  sorry

/-- The uniquely normalized comparison from completed to ordinary tensor.
Source: rational purity proof, tensor transpose
(blueprint: def-pur-canonical-purity-source-transports). -/
def tensorToOrdinary (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (M N : finiteTorConstructibleIntegralCategory l E T) :=
  (tensorToOrdinary_existsUnique l E T M N).exists.choose

end RationalSmoothPurityCanonical
end WeilConjectures
