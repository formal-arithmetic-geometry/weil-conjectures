/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.Paper.IntrinsicQbarCategory
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfBidualityClass
public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.SixFunctors.CoefQbarVerdier
public import Sheaf.Paper.SfCommonStageDirectImage
public import Sheaf.Paper.FieldWeilShriekShiftData
public import Sheaf.Paper.DerivedAutomorphismHomEvaluation
public import Sheaf.Paper.AdicClosedConstructible
public import Sheaf.Paper.CompactSupportCoefficientAction
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.PbcRationalCategory
import Sheaf.Paper.FiniteResidueDualizing
import Sheaf.Paper.IntegralHomReduction
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Paper.SfIntegralDirectImageConstructible
import Sheaf.Paper.SfIntegralCompactSupportConstructible
import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.Paper.PbcScalarExtension
import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
import Sheaf.CategoryTheory.StageSystemFunctorDescent
import Sheaf.Paper.AdicExceptionalProjection

/-! # Relative Verdier duality over an arbitrary field

Source: Bhatt--Scholze, Lemmas 6.7.13, 6.7.14, 6.7.19 and 6.7.20,
Proposition 6.8.14 and Remark 6.8.15; relative dimension normalization as in BBD 4.0
(blueprint: lem-per-qbar-arbitrary-field-duality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

namespace WeilConjectures

attribute [local instance 1100] CategoryTheory.instOverClass

section OrdinaryImage
variable (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
  [Fact (IsUnit (l : k))]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))]

/-- The given common-stage inverse image has the adic direct image as right adjoint.
Source: Bhatt--Scholze, Lemmas 6.7.2 and 6.7.14, Proposition 6.8.14(2)
(blueprint: lem-per-qbar-arbitrary-field-duality).
Proof: the completed-ring inverse/direct-image adjunction is identified with the
specified reduction tower by CompletedCoefficientPushforwardComparison. The tower
is bounded constructible by sfIntegralDirectImage_constructible. Restrict the
adjunction, rationalize its Hom bijections, and descend them with their coefficient
unit and tower equations to the common-stage Hom colimits. The descended left
adjoint is exactly commonStageDerivedPullback by its representative formula.
No finite-field, separable-closedness or cohomological-dimension assumption is used. -/
theorem arbitraryFieldPullback_isLeftAdjoint :
    (@commonStageDerivedPullback l _ Ω _ _ _ X Y f
      (AdicClosed.residueInvertible l k X)
      (AdicClosed.residueInvertible l k Y)).IsLeftAdjoint := by
  sorry

/-- The actual adic direct image, characterized by the recorded inverse image.
Source: Bhatt--Scholze, Proposition 6.8.14(2)
(blueprint: lem-per-qbar-arbitrary-field-duality). -/
def arbitraryFieldDerivedPush :
    generalAlgebraicallyClosedConstructibleCategory l Ω X ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω Y :=
  @Functor.rightAdjoint _ _ _ _
    (@commonStageDerivedPullback l _ Ω _ _ _ X Y f
      (AdicClosed.residueInvertible l k X) (AdicClosed.residueInvertible l k Y))
    (arbitraryFieldPullback_isLeftAdjoint l k Ω f)

/-- The unit and counit retained by the canonical direct image.
Source: Bhatt--Scholze, Proposition 6.8.14(2)
(blueprint: lem-per-qbar-arbitrary-field-duality). -/
def arbitraryFieldDerivedAdjunction :
    @commonStageDerivedPullback l _ Ω _ _ _ X Y f
        (AdicClosed.residueInvertible l k X) (AdicClosed.residueInvertible l k Y) ⊣
      arbitraryFieldDerivedPush l k Ω f :=
  @Adjunction.ofIsLeftAdjoint _ _ _ _
    (@commonStageDerivedPullback l _ Ω _ _ _ X Y f
      (AdicClosed.residueInvertible l k X) (AdicClosed.residueInvertible l k Y))
    (arbitraryFieldPullback_isLeftAdjoint l k Ω f)

end OrdinaryImage

/-- The canonical coefficient embedding induced by a structure morphism to a field.
Source: BBD 4.0 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
noncomputable def relativeResidueFieldAlgebraMap
    {k : Type u} [Field k] {T : Scheme.{u}}
    (aT : T ⟶ Spec (.of k)) (t : T) : k →+* T.residueField t :=
  (CommRingCat.ofHom (algebraMap (CommRingCat.of k)
      (aT.base t).asIdeal.ResidueField) ≫
    (Spec.residueFieldIso (.of k) (aT.base t)).inv ≫ aT.residueFieldMap t).hom

/-- Relative transcendence degree function used to normalize dualizing objects.
Source: BBD 4.0 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
noncomputable def relativeTranscendenceDegree
    {k : Type u} [Field k] {T : Scheme.{u}}
    (aT : T ⟶ Spec (.of k)) (t : T) : Cardinal :=
  letI := (relativeResidueFieldAlgebraMap aT t).toAlgebra
  Algebra.trdeg k (T.residueField t)

/-- Residue-field invertibility with the proposition-level hypothesis exposed by the item.
Source: BBD 4.0 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
@[instance_reducible]
noncomputable def residueInvertibleWithUnit
    {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : k))
    (T : Scheme.{u}) [T.Over (Spec (.of k))] :
    ∀ t : T, Invertible (l : T.residueField t) :=
  letI : Fact (IsUnit (l : k)) := ⟨hl⟩
  AdicClosed.residueInvertible l k T

/-- The arbitrary-field direct image with the explicitly supplied unit hypothesis.
Source: Bhatt--Scholze 6.8.14 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
noncomputable def arbitraryFieldDerivedPushWithUnit
    {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : k))
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] :
    generalAlgebraicallyClosedConstructibleCategory l Ω X ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω Y :=
  letI : Fact (IsUnit (l : k)) := ⟨hl⟩
  arbitraryFieldDerivedPush l k Ω f

namespace ArbitraryFieldVerdier

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition)

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : k))
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The recorded completed tensor, with the actual residue-field inverses.
Source: Bhatt--Scholze 6.7.12 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def tensor (T : Scheme.{u}) [T.Over (Spec (.of k))] :=
  @commonStageDerivedTensor l _ Ω _ _ _ T (residueInvertibleWithUnit l hl T)

/-- The specified coefficient unit, represented by the completed regular module.
Source: Bhatt--Scholze 6.8.14 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def unit (T : Scheme.{u}) [T.Over (Spec (.of k))] :=
  @pullbackTensorCommonUnit l _ Ω _ _ _ T (residueInvertibleWithUnit l hl T)

/-- The actual inverse image used in the ordinary direct-image adjunction.
Source: Bhatt--Scholze 6.7.2 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def pull {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    (f : X ⟶ Y) :=
  @commonStageDerivedPullback l _ Ω _ _ _ X Y f
    (residueInvertibleWithUnit l hl X) (residueInvertibleWithUnit l hl Y)

/-- The same ordinary adjunction as in the repaired direct-image dependency.
Source: Bhatt--Scholze 6.7.2 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def ordinaryAdjunction
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] :
    pull l hl Ω f ⊣ arbitraryFieldDerivedPushWithUnit l hl Ω f :=
  letI : Fact (IsUnit (l : k)) := ⟨hl⟩
  arbitraryFieldDerivedAdjunction l k Ω f

/-- The ordinary-image shift is the mate of the representative-normalized inverse-image
shift, not a shift structure transported along Verdier exchange.
Source: Bhatt--Scholze 6.7.2 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
@[instance_reducible] def pushShift
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] :
    (arbitraryFieldDerivedPushWithUnit l hl Ω f).CommShift ℤ :=
  letI := residueInvertibleWithUnit l hl X
  letI := residueInvertibleWithUnit l hl Y
  letI : (pull l hl Ω f).CommShift ℤ := fieldCommonPullShift l Ω f
  (ordinaryAdjunction l hl Ω f).rightAdjointCommShift ℤ

variable (T : Scheme.{u}) [T.Over (Spec (.of k))]
  [IsSeparated (T ↘ Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
  [QuasiCompact (T ↘ Spec (.of k))]

/-- Internal Hom on all constructible pairs, with precisely the dependency's arrow action.
Its only input beyond that functor is a proof that all its pairs are permitted.
Source: Bhatt--Scholze 6.7.13 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def hom (h : ∀ P, commonStageHomPairs l Ω T P) :=
  (commonStageHomPairs l Ω T).lift (𝟭 _) h ⋙ commonStageDerivedInternalHom l Ω T

/-- Rational evaluation is the localization of the canonical completed evaluation.
The two endpoint transports are the recorded tensor and Hom object formulas.
Source: Bhatt--Scholze 6.7.13; Stacks 08J9
(blueprint: lem-per-qbar-arbitrary-field-duality). -/
def rationalEvaluation (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (P : (constructibleRationalHomPairs l E T).FullSubcategory) :
    (@rationalDerivedTensor l _ E _ _ _ T (residueInvertibleWithUnit l hl T)).obj
        ((rationalDerivedInternalHom l E T).obj P, P.obj.1.unop) ⟶ P.obj.2 :=
  letI : Fact (IsUnit (l : k)) := ⟨hl⟩
  eqToHom (congrArg
    (fun H ↦ (@rationalDerivedTensor l _ E _ _ _ T
      (residueInvertibleWithUnit l hl T)).obj (H, P.obj.1.unop))
    ((rationalDerivedInternalHom_existsUnique l E T).exists.choose_spec.1 P)) ≫
  eqToHom ((@rationalDerivedTensor_existsUnique l _ E _ _ _ T
    (residueInvertibleWithUnit l hl T)).exists.choose_spec.1 _) ≫
  (sfRationalConstructibleLocalization l E T).map
    (ObjectProperty.homMk (AdicClosed.evaluation l k T E P.obj.1.unop.obj P.obj.2.obj))

/-- The literal tensor object at the compositum, using the specified residue inverses.
Source: Bhatt--Scholze 6.8.14 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def tensorObject (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω T) :=
  @commonStageTensorObject l _ Ω _ _ _ T (residueInvertibleWithUnit l hl T) P Q

/-- Evaluation at a common finite stage, with the actual Hom and tensor comparisons.
Every factor comes from the normalized coefficient operations; this is a map,
not an arbitrarily chosen pairing or an assumed isomorphism.
Source: Bhatt--Scholze 6.8.14 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def evaluationAtStage (P : (commonStageHomPairs l Ω T).FullSubcategory)
    (L : Index l Ω) (h : (commonStageHomObject l Ω T P).stage ≤ L) :
    ((tensorObject l hl Ω T (commonStageHomObject l Ω T P) P.obj.1.unop).toStage
      (sup_le (α := IntermediateField (Padic l) Ω) h
        (((Padic.finiteCoefficientFields_properties l Ω).1
          P.obj.1.unop.stage P.obj.2.stage).1.trans h))) ⟶
    P.obj.2.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
      P.obj.1.unop.stage P.obj.2.stage).2.trans h) :=
  letI := residueInvertibleWithUnit l hl T
  (commonStageTensorComparison l Ω T (commonStageHomObject l Ω T P) P.obj.1.unop L
    (sup_le (α := IntermediateField (Padic l) Ω) h
      (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).1.trans h))).hom ≫
  (rationalDerivedTensor l (Coefficient.{u} l Ω L) T).map
    (Prod.mkHom (commonStageHomComparison l Ω T P L h).hom (𝟙 _)) ≫
  rationalEvaluation l hl T (Coefficient.{u} l Ω L) (commonStageHomPairAtStage l Ω T P L h)

/-- Closed structure on the actual common-stage Hom, pinned on finite representatives.
In particular evaluation is fixed to completed ordinary evaluation, whose reductions
are finiteIntrinsicEvaluation. The symmetry is the recorded Koszul symmetry.
Source: Bhatt--Scholze 6.7.13 and 6.8.14
(blueprint: lem-per-qbar-arbitrary-field-duality). -/
structure Closed where
  permitted : ∀ P, commonStageHomPairs l Ω T P
  closed : CoefficientClosedStructure (hom l Ω T permitted)
  tensor_eq : closed.tensor = tensor l hl Ω T
  unit_eq : closed.monoidal.tensorUnit = unit l hl Ω T
  symmetric : @SymmetricCategory _ _ closed.monoidal
  symmetry_eq (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω T) :
    HEq (symmetric.braiding P Q).hom
      (@pullbackTensorCommonBraiding l _ Ω _ _ _ T
        (residueInvertibleWithUnit l hl T) P Q).hom
  evaluation_eq (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω T)
      (L : Index l Ω)
      (h : (commonStageHomObject l Ω T ⟨(op P, Q), permitted (op P, Q)⟩).stage ≤ L) :
    HEq (closed.evaluation P Q)
      (GeneralAlgebraicallyClosedCoefficients.ofHom
        (tensorObject l hl Ω T
          (commonStageHomObject l Ω T ⟨(op P, Q), permitted (op P, Q)⟩) P) Q L
        (sup_le (α := IntermediateField (Padic l) Ω) h
          (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1.trans h))
        (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2.trans h)
        (evaluationAtStage l hl Ω T ⟨(op P, Q), permitted (op P, Q)⟩ L h))

/-- The Verdier functor is literally the dependency's internal Hom into omega.
Source: Bhatt--Scholze 6.7.20 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def dual (B : Closed l hl Ω T)
    (omega : generalAlgebraicallyClosedConstructibleCategory l Ω T) :=
  CoefQbarVerdier.homDual l Ω T omega (fun K ↦ B.permitted (op K, omega))

/-- The bidual arrow is the transpose of Koszul-swapped evaluation.
Source: Bhatt--Scholze 6.7.20; Stacks 0A97
(blueprint: lem-per-qbar-arbitrary-field-duality). -/
def bidual (B : Closed l hl Ω T)
    (omega : generalAlgebraicallyClosedConstructibleCategory l Ω T)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω T) :
    K ⟶ (dual l hl Ω T B omega).obj (op ((dual l hl Ω T B omega).obj (op K))) :=
  CategoryTheory.ringedSiteBidual B.closed B.symmetric omega K



section Support
variable {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  [IsSeparated (Z ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]

/-- Open extension is the left adjoint of the actual common-stage restriction.
Source: Bhatt--Scholze 6.7.6 (blueprint: lem-per-qbar-arbitrary-field-duality).
Proof: extension by zero on completed modules is exact, preserves the specified
finite reductions and constructibility, and is left adjoint to open restriction.
Rationalize the adjunction and descend its units and counits at finite stages.
The triangle equations descend because they hold on all representatives. -/
theorem openRestriction_isRightAdjoint (j : X ⟶ Z) [IsOpenImmersion j] :
    (pull l hl Ω j).IsRightAdjoint := by
  sorry

/-- The open functor is selected by its adjunction to actual restriction.
Source: Bhatt--Scholze 6.7.6 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def openExtension (j : X ⟶ Z) [IsOpenImmersion j] :=
  @Functor.leftAdjoint _ _ _ _ (pull l hl Ω j)
    (openRestriction_isRightAdjoint l hl Ω j)

/-- The same open adjunction, retaining the normalization of its unit.
Source: Bhatt--Scholze 6.7.6 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def openAdjunction (j : X ⟶ Z) [IsOpenImmersion j] :
    openExtension l hl Ω j ⊣ pull l hl Ω j :=
  @Adjunction.ofIsRightAdjoint _ _ _ _ (pull l hl Ω j)
    (openRestriction_isRightAdjoint l hl Ω j)

/-- Actual tensor pullback, fixed on K-flat pure tensors by the dependency.
Source: Bhatt--Scholze 6.7.12 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def tensorPull (g : X ⟶ Y) (M N : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :=
  @canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y g
    (residueInvertibleWithUnit l hl X) (residueInvertibleWithUnit l hl Y) M N

/-- The proper projection arrow is the ordinary counit mate, before inversion.
Source: Bhatt--Scholze 6.7.7 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def properProjection (p : Z ⟶ Y) [p.IsOver (Spec (.of k))]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (N : generalAlgebraicallyClosedConstructibleCategory l Ω Z) :
    (tensor l hl Ω Y).obj (M, (arbitraryFieldDerivedPushWithUnit l hl Ω p).obj N) ⟶
      (arbitraryFieldDerivedPushWithUnit l hl Ω p).obj
        ((tensor l hl Ω Z).obj ((pull l hl Ω p).obj M, N)) :=
  (ordinaryAdjunction l hl Ω p).homEquiv _ _
    ((tensorPull l hl Ω p M _).hom ≫
      (tensor l hl Ω Z).map
        (Prod.mkHom (𝟙 _) ((ordinaryAdjunction l hl Ω p).counit.app N)))

/-- Proper projection is invertible on these constructible objects.
Source: Bhatt--Scholze 6.7.7 (blueprint: lem-per-qbar-arbitrary-field-duality).
Proof: reduce the counit-defined projection to the finite coefficient proper
projection on each quotient. Proper base change and finite Tor give its inverse.
The reduction cone is zero; completeness kills the integral cone. Rationalize
and descend both inverse maps with their coefficient comparisons. -/
theorem properProjection_isIso (p : Z ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (N : generalAlgebraicallyClosedConstructibleCategory l Ω Z) :
    IsIso (properProjection l hl Ω p M N) := by
  sorry

/-- Open projection is the transpose of the open unit and inverse tensor pullback.
Source: Bhatt--Scholze 6.7.6 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def openProjection (j : X ⟶ Z) [IsOpenImmersion j]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω Z)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) :
    (openExtension l hl Ω j).obj ((tensor l hl Ω X).obj ((pull l hl Ω j).obj M, K)) ⟶
      (tensor l hl Ω Z).obj (M, (openExtension l hl Ω j).obj K) :=
  ((openAdjunction l hl Ω j).homEquiv _ _).symm
    ((tensor l hl Ω X).map
      (Prod.mkHom (𝟙 _) ((openAdjunction l hl Ω j).unit.app K)) ≫
        (tensorPull l hl Ω j M _).inv)

/-- The proper/open composite, with no unspecified direct-image field.
Source: Bhatt--Scholze 6.7.6 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def support (j : X ⟶ Z) [IsOpenImmersion j]
    (p : Z ⟶ Y) [p.IsOver (Spec (.of k))] :=
  openExtension l hl Ω j ⋙ arbitraryFieldDerivedPushWithUnit l hl Ω p

/-- Canonical compactification projection, open-unit mate followed by the inverse
proper-counit mate. Source: Bhatt--Scholze 6.7.7
(blueprint: lem-per-qbar-arbitrary-field-duality). -/
def supportProjection (j : X ⟶ Z) [IsOpenImmersion j]
    (p : Z ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) :
    (support l hl Ω j p).obj
        ((tensor l hl Ω X).obj ((pull l hl Ω (j ≫ p)).obj M, K)) ⟶
      (tensor l hl Ω Y).obj (M, (support l hl Ω j p).obj K) :=
  (support l hl Ω j p).map
    ((tensor l hl Ω X).map
      (Prod.mkHom
        (@pullbackTensorCommonComposition l _ Ω _ _ _ Z Y X p j
          (residueInvertibleWithUnit l hl Z) (residueInvertibleWithUnit l hl Y)
          (residueInvertibleWithUnit l hl X) M).hom (𝟙 K))) ≫
  (arbitraryFieldDerivedPushWithUnit l hl Ω p).map
    (openProjection l hl Ω j ((pull l hl Ω p).obj M) K) ≫
  @inv _ _ _ _ (properProjection l hl Ω p M ((openExtension l hl Ω j).obj K))
    (properProjection_isIso l hl Ω p M ((openExtension l hl Ω j).obj K))

end Support



/-- Compactification with its canonical field structures exposed as output witnesses.
Source: Bhatt--Scholze 6.7.6 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
structure Factorization {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] (f : X ⟶ Y) where
  compactification : Compactification f
  [schemeOver : compactification.Z.Over (Spec (.of k))]
  [separated : IsSeparated (compactification.Z ↘ Spec (.of k))]
  [finiteType : LocallyOfFiniteType (compactification.Z ↘ Spec (.of k))]
  [quasiCompact : QuasiCompact (compactification.Z ↘ Spec (.of k))]
  [properOver : compactification.g.IsOver (Spec (.of k))]
  [openOver : compactification.i.IsOver (Spec (.of k))]

attribute [instance] Factorization.schemeOver Factorization.separated Factorization.finiteType
  Factorization.quasiCompact Factorization.properOver Factorization.openOver

section Factorized
variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  {f : X ⟶ Y}

/-- Compact support is the actual proper/open functor of this compactification.
Source: Bhatt--Scholze 6.7.6 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def shriek (c : Factorization (k := k) f) :=
  support l hl Ω c.compactification.i c.compactification.g

/-- Compact-support shifts are the composite of the open adjunction mate and the
ordinary proper-image mate. Both start from the prescribed inverse-image shifts.
Source: Bhatt--Scholze 6.7.6 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
@[instance_reducible] def shriekShift (c : Factorization (k := k) f) :
    (shriek l hl Ω c).CommShift ℤ :=
  letI := residueInvertibleWithUnit l hl X
  letI := residueInvertibleWithUnit l hl c.compactification.Z
  letI : (pull l hl Ω c.compactification.i).CommShift ℤ :=
    fieldCommonPullShift l Ω c.compactification.i
  letI : (openExtension l hl Ω c.compactification.i).CommShift ℤ :=
    (openAdjunction l hl Ω c.compactification.i).leftAdjointCommShift ℤ
  letI := pushShift l hl Ω c.compactification.g
  inferInstanceAs ((openExtension l hl Ω c.compactification.i ⋙
    arbitraryFieldDerivedPushWithUnit l hl Ω c.compactification.g).CommShift ℤ)

/-- The canonical projection after the equality identifying the factorization with f.
Source: Bhatt--Scholze 6.7.7 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def projection (c : Factorization (k := k) f)
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) :
    (shriek l hl Ω c).obj ((tensor l hl Ω X).obj ((pull l hl Ω f).obj M, K)) ⟶
      (tensor l hl Ω Y).obj (M, (shriek l hl Ω c).obj K) :=
  (shriek l hl Ω c).map ((tensor l hl Ω X).map
    (Prod.mkHom
      (eqToHom (congrArg (fun g : X ⟶ Y ↦ (pull l hl Ω g).obj M)
        c.compactification.comm)) (𝟙 K))) ≫
    supportProjection l hl Ω c.compactification.i c.compactification.g M K

end Factorized

section Conclusion
variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Adjoints of actual compact-support functors, with the actual closed structures.
The X structure functor is the composite Rf! followed by RaY!, so its right
adjoint computes the same relative dualizing object without a free compositor.
Source: Bhatt--Scholze 6.7.19--20 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
structure Datum where
  factorF : Factorization (k := k) f
  factorY : Factorization (k := k) (Y ↘ Spec (.of k))
  closedX : Closed l hl Ω X
  closedY : Closed l hl Ω Y
  rightY : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of k)) ⥤
    generalAlgebraicallyClosedConstructibleCategory l Ω Y
  adjY : shriek l hl Ω factorY ⊣ rightY
  rightX : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of k)) ⥤
    generalAlgebraicallyClosedConstructibleCategory l Ω X
  adjX : shriek l hl Ω factorF ⋙ shriek l hl Ω factorY ⊣ rightX

namespace Datum
variable {f} (B : Datum l hl Ω f)

/-- The relative dualizing object on X is RaX! of the specified base coefficient unit.
Source: Bhatt--Scholze 6.7.19 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def omegaX := B.rightX.obj (unit l hl Ω (Spec (.of k)))

/-- The relative dualizing object on Y, using the same coefficient unit.
Source: Bhatt--Scholze 6.7.19 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def omegaY := B.rightY.obj (unit l hl Ω (Spec (.of k)))

/-- The dual is the existing common-stage internal Hom into RaX! of the unit.
Source: Bhatt--Scholze 6.7.20 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def dualX := dual l hl Ω X B.closedX (B.omegaX l hl Ω)

/-- The dual on Y uses precisely the same recorded internal-Hom operation.
Source: Bhatt--Scholze 6.7.20 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def dualY := dual l hl Ω Y B.closedY (B.omegaY l hl Ω)

/-- Evaluation followed by the actual structure-map counit is the relative trace pairing.
Source: Bhatt--Scholze 6.7.19 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def pairing (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) :
    (shriek l hl Ω B.factorF ⋙ shriek l hl Ω B.factorY).obj
      ((tensor l hl Ω X).obj
        ((pull l hl Ω f).obj
          ((B.dualY l hl Ω).obj (op ((shriek l hl Ω B.factorF).obj K))), K)) ⟶
      unit l hl Ω (Spec (.of k)) :=
  (shriek l hl Ω B.factorY).map
    (projection l hl Ω B.factorF _ K ≫
      eqToHom (congrArg
        (fun F ↦ F.obj
          ((B.dualY l hl Ω).obj (op ((shriek l hl Ω B.factorF).obj K)),
            (shriek l hl Ω B.factorF).obj K)) B.closedY.tensor_eq.symm) ≫
      B.closedY.closed.evaluation ((shriek l hl Ω B.factorF).obj K) (B.omegaY l hl Ω)) ≫
    B.adjY.counit.app (unit l hl Ω (Spec (.of k)))

/-- The exchange arrow is the three actual adjunction transposes of projection,
evaluation and trace. No exchange map or isomorphism is a field of Datum.
Source: Bhatt--Scholze 6.7.19 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def exchange (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) :
    (B.dualY l hl Ω).obj (op ((shriek l hl Ω B.factorF).obj K)) ⟶
      (arbitraryFieldDerivedPushWithUnit l hl Ω f).obj ((B.dualX l hl Ω).obj (op K)) :=
  (ordinaryAdjunction l hl Ω f).homEquiv _ _
    (B.closedX.closed.transpose _ K (B.omegaX l hl Ω)
      (eqToHom (congrArg
        (fun F ↦ F.obj
          ((pull l hl Ω f).obj
            ((B.dualY l hl Ω).obj (op ((shriek l hl Ω B.factorF).obj K))), K))
        B.closedX.tensor_eq) ≫
        B.adjX.homEquiv _ _ (B.pairing l hl Ω K)))

end Datum
end Conclusion



namespace Rational
variable (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

/-- Rational completed tensor with the same prescribed residue inverses.
Source: Bhatt--Scholze 6.8.14 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def tensor (T : Scheme.{u}) [T.Over (Spec (.of k))] :=
  @rationalDerivedTensor l _ E _ _ _ T (residueInvertibleWithUnit l hl T)

/-- The rational coefficient unit, the localization of the completed regular module.
Source: Bhatt--Scholze 6.8.14 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def unit (T : Scheme.{u}) [T.Over (Spec (.of k))] :=
  @pullbackTensorRationalUnit l _ E _ _ _ T (residueInvertibleWithUnit l hl T)

/-- The recorded rational inverse image.
Source: Bhatt--Scholze 6.7.2 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def pull {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    (f : X ⟶ Y) :=
  @rationalDerivedPullback l _ E _ _ _ X Y f
    (residueInvertibleWithUnit l hl X) (residueInvertibleWithUnit l hl Y)

/-- Constructible rational inverse image has the ordinary adic right adjoint.
Source: Bhatt--Scholze 6.7.2, 6.7.14, 6.8.14
(blueprint: lem-per-qbar-arbitrary-field-duality).
Proof: restrict the completed-ring inverse/direct-image adjunction using integral
constructible finiteness. Tensor its inverse Hom bijections with E. Balancing,
naturality and the triangle identities pass to the raw rational Hom groups. -/
theorem pull_isLeftAdjoint
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] :
    (pull l hl E f).IsLeftAdjoint := by
  sorry

/-- Rational ordinary image, determined by its adjunction to actual inverse image.
Source: Bhatt--Scholze 6.8.14 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def push
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] :=
  @Functor.rightAdjoint _ _ _ _ (pull l hl E f) (pull_isLeftAdjoint l hl E f)

/-- The rational ordinary adjunction, including its specified unit and counit.
Source: Bhatt--Scholze 6.8.14 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def ordinaryAdjunction
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] :
    pull l hl E f ⊣ push l hl E f :=
  @Adjunction.ofIsLeftAdjoint _ _ _ _ (pull l hl E f) (pull_isLeftAdjoint l hl E f)

variable (T : Scheme.{u}) [T.Over (Spec (.of k))]
  [IsSeparated (T ↘ Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
  [QuasiCompact (T ↘ Spec (.of k))]

/-- The actual rational internal Hom on all constructible pairs.
Source: Bhatt--Scholze 6.7.13 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def hom (h : ∀ P, constructibleRationalHomPairs l E T P) :=
  (constructibleRationalHomPairs l E T).lift (𝟭 _) h ⋙ rationalDerivedInternalHom l E T

/-- Rational closed structure, whose tensor and evaluation are the recorded operations.
Source: Bhatt--Scholze 6.7.13, 6.8.14
(blueprint: lem-per-qbar-arbitrary-field-duality). -/
structure Closed where
  permitted : ∀ P, constructibleRationalHomPairs l E T P
  closed : CoefficientClosedStructure (hom l E T permitted)
  tensor_eq : closed.tensor = tensor l hl E T
  unit_eq : closed.monoidal.tensorUnit = unit l hl E T
  evaluation_eq (P Q : sfRationalConstructibleCategory l E T) :
    HEq (closed.evaluation P Q)
      (ArbitraryFieldVerdier.rationalEvaluation l hl T E
        ⟨(op P, Q), permitted (op P, Q)⟩)

set_option linter.defProp false in
/-- Every rational Hom pair is permitted by arbitrary-field integral finiteness.
Source: Bhatt--Scholze 6.7.13 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def permitted (P : (sfRationalConstructibleCategory l E T)ᵒᵖ ×
    sfRationalConstructibleCategory l E T) : constructibleRationalHomPairs l E T P :=
  letI : Fact (IsUnit (l : k)) := ⟨hl⟩
  AdicClosed.hom_constructible l k T E P.1.unop.obj P.2.obj

/-- The rational-to-integral Hom identification is the recorded literal object formula.
Source: Bhatt--Scholze 6.8.14 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def homIntegral (P : (constructibleRationalHomPairs l E T).FullSubcategory) :
    (rationalDerivedInternalHom l E T).obj P ≅
      (sfRationalConstructibleLocalization l E T).obj
        ((constructibleIntegralHom l E T).obj (integralPairOfRationalHomPair l E T P)) :=
  eqToIso ((rationalDerivedInternalHom_existsUnique l E T).exists.choose_spec.1 P)

/-- The signed Hom shift is the localization of the prescribed product-reindexing
map, with both localization shift comparisons inserted. The integral comparison
uses the sign (-1)^(a*k) in Hom degree k.
Source: Stacks 08JA; Bhatt--Scholze 6.7.13
(blueprint: lem-per-qbar-arbitrary-field-duality). -/
def homShift (M N : sfRationalConstructibleCategory l E T) (a b : ℤ) :
    ((hom l E T (permitted l hl E T)).obj (op M, N))⟦b - a⟧ ≅
      (hom l E T (permitted l hl E T)).obj (op (M⟦a⟧), N⟦b⟧) :=
  letI := residueInvertibleWithUnit l hl T
  let P : (constructibleRationalHomPairs l E T).FullSubcategory :=
    ⟨(op M, N), permitted l hl E T (op M, N)⟩
  let I := integralPairOfRationalHomPair l E T P
  let P' : (constructibleRationalHomPairs l E T).FullSubcategory :=
    ⟨(op ((sfRationalConstructibleLocalization l E T).obj (M.obj⟦a⟧)),
      (sfRationalConstructibleLocalization l E T).obj (N.obj⟦b⟧)),
      permitted l hl E T _⟩
  (shiftFunctor _ (b - a)).mapIso (homIntegral l E T P) ≪≫
    ((sfRationalConstructibleLocalization l E T).commShiftIso (b - a)).symm.app _ ≪≫
    (sfRationalConstructibleLocalization l E T).mapIso (podIntegralHomShift l E I a b) ≪≫
    (homIntegral l E T P').symm ≪≫
    (rationalDerivedInternalHom l E T).mapIso
      (ObjectProperty.isoMk _ (Iso.prod
        (((sfRationalConstructibleLocalization l E T).commShiftIso a).app M.obj).symm.op
        (((sfRationalConstructibleLocalization l E T).commShiftIso b).app N.obj)))

/-- Rational duality uses the recorded Hom functor into the exceptional unit image.
Source: Bhatt--Scholze 6.7.20 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def dual (B : Closed l hl E T) (omega : sfRationalConstructibleCategory l E T) :=
  ((𝟭 _).prod' ((Functor.const _).obj omega)) ⋙ hom l E T B.permitted

section Support
variable {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  [IsSeparated (Z ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]

/-- Open extension is the left adjoint of the actual common-stage restriction.
Source: Bhatt--Scholze 6.7.6 (blueprint: lem-per-qbar-arbitrary-field-duality).
Proof: extension by zero on completed modules is exact, preserves the specified
finite reductions and constructibility, and is left adjoint to open restriction.
Rationalize the adjunction and descend its units and counits at finite stages.
The triangle equations descend because they hold on all representatives. -/
theorem openRestriction_isRightAdjoint (j : X ⟶ Z) [IsOpenImmersion j] :
    (pull l hl E j).IsRightAdjoint := by
  sorry

/-- The open functor is selected by its adjunction to actual restriction.
Source: Bhatt--Scholze 6.7.6 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def openExtension (j : X ⟶ Z) [IsOpenImmersion j] :=
  @Functor.leftAdjoint _ _ _ _ (pull l hl E j)
    (openRestriction_isRightAdjoint l hl E j)

/-- The same open adjunction, retaining the normalization of its unit.
Source: Bhatt--Scholze 6.7.6 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def openAdjunction (j : X ⟶ Z) [IsOpenImmersion j] :
    openExtension l hl E j ⊣ pull l hl E j :=
  @Adjunction.ofIsRightAdjoint _ _ _ _ (pull l hl E j)
    (openRestriction_isRightAdjoint l hl E j)

/-- Actual tensor pullback, fixed on K-flat pure tensors by the dependency.
Source: Bhatt--Scholze 6.7.12 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def tensorPull (g : X ⟶ Y) (M N : sfRationalConstructibleCategory l E Y) :=
  @canonicalRationalPullbackTensor l _ E _ _ _ X Y g
    (residueInvertibleWithUnit l hl X) (residueInvertibleWithUnit l hl Y) M N

/-- The proper projection arrow is the ordinary counit mate, before inversion.
Source: Bhatt--Scholze 6.7.7 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def properProjection (p : Z ⟶ Y) [p.IsOver (Spec (.of k))]
    (M : sfRationalConstructibleCategory l E Y)
    (N : sfRationalConstructibleCategory l E Z) :
    (tensor l hl E Y).obj (M, (push l hl E p).obj N) ⟶
      (push l hl E p).obj
        ((tensor l hl E Z).obj ((pull l hl E p).obj M, N)) :=
  (ordinaryAdjunction l hl E p).homEquiv _ _
    ((tensorPull l hl E p M _).hom ≫
      (tensor l hl E Z).map
        (Prod.mkHom (𝟙 _) ((ordinaryAdjunction l hl E p).counit.app N)))

/-- Proper projection is invertible on these constructible objects.
Source: Bhatt--Scholze 6.7.7 (blueprint: lem-per-qbar-arbitrary-field-duality).
Proof: reduce the counit-defined projection to the finite coefficient proper
projection on each quotient. Proper base change and finite Tor give its inverse.
The reduction cone is zero; completeness kills the integral cone. Rationalize
and descend both inverse maps with their coefficient comparisons. -/
theorem properProjection_isIso (p : Z ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (M : sfRationalConstructibleCategory l E Y)
    (N : sfRationalConstructibleCategory l E Z) :
    IsIso (properProjection l hl E p M N) := by
  sorry

/-- Open projection is the transpose of the open unit and inverse tensor pullback.
Source: Bhatt--Scholze 6.7.6 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def openProjection (j : X ⟶ Z) [IsOpenImmersion j]
    (M : sfRationalConstructibleCategory l E Z)
    (K : sfRationalConstructibleCategory l E X) :
    (openExtension l hl E j).obj ((tensor l hl E X).obj ((pull l hl E j).obj M, K)) ⟶
      (tensor l hl E Z).obj (M, (openExtension l hl E j).obj K) :=
  ((openAdjunction l hl E j).homEquiv _ _).symm
    ((tensor l hl E X).map
      (Prod.mkHom (𝟙 _) ((openAdjunction l hl E j).unit.app K)) ≫
        (tensorPull l hl E j M _).inv)

/-- The proper/open composite, with no unspecified direct-image field.
Source: Bhatt--Scholze 6.7.6 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def support (j : X ⟶ Z) [IsOpenImmersion j]
    (p : Z ⟶ Y) [p.IsOver (Spec (.of k))] :=
  openExtension l hl E j ⋙ push l hl E p

/-- Canonical compactification projection, open-unit mate followed by the inverse
proper-counit mate. Source: Bhatt--Scholze 6.7.7
(blueprint: lem-per-qbar-arbitrary-field-duality). -/
def supportProjection (j : X ⟶ Z) [IsOpenImmersion j]
    (p : Z ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (M : sfRationalConstructibleCategory l E Y)
    (K : sfRationalConstructibleCategory l E X) :
    (support l hl E j p).obj
        ((tensor l hl E X).obj ((pull l hl E (j ≫ p)).obj M, K)) ⟶
      (tensor l hl E Y).obj (M, (support l hl E j p).obj K) :=
  (support l hl E j p).map
    ((tensor l hl E X).map
      (Prod.mkHom
        (@pullbackTensorRationalComposition l _ E _ _ _ Z Y X p j
          (residueInvertibleWithUnit l hl Z) (residueInvertibleWithUnit l hl Y)
          (residueInvertibleWithUnit l hl X) M).hom (𝟙 K))) ≫
  (push l hl E p).map
    (openProjection l hl E j ((pull l hl E p).obj M) K) ≫
  @inv _ _ _ _ (properProjection l hl E p M ((openExtension l hl E j).obj K))
    (properProjection_isIso l hl E p M ((openExtension l hl E j).obj K))

end Support

section Factorized
variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  {f : X ⟶ Y}

/-- Compact support is the actual proper/open functor of this compactification.
Source: Bhatt--Scholze 6.7.6 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def shriek (c : Factorization (k := k) f) :=
  support l hl E c.compactification.i c.compactification.g

/-- The canonical projection after the equality identifying the factorization with f.
Source: Bhatt--Scholze 6.7.7 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def projection (c : Factorization (k := k) f)
    (M : sfRationalConstructibleCategory l E Y)
    (K : sfRationalConstructibleCategory l E X) :
    (shriek l hl E c).obj ((tensor l hl E X).obj ((pull l hl E f).obj M, K)) ⟶
      (tensor l hl E Y).obj (M, (shriek l hl E c).obj K) :=
  (shriek l hl E c).map ((tensor l hl E X).map
    (Prod.mkHom
      (eqToHom (congrArg (fun g : X ⟶ Y ↦ (pull l hl E g).obj M)
        c.compactification.comm)) (𝟙 K))) ≫
    supportProjection l hl E c.compactification.i c.compactification.g M K

end Factorized

section Conclusion
variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Adjoints of actual compact-support functors, with the actual closed structures.
The X structure functor is the composite Rf! followed by RaY!, so its right
adjoint computes the same relative dualizing object without a free compositor.
Source: Bhatt--Scholze 6.7.19--20 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
structure Datum (cF : Factorization (k := k) f)
    (cY : Factorization (k := k) (Y ↘ Spec (.of k))) where
  closedX : Closed l hl E X
  closedY : Closed l hl E Y
  rightY : sfRationalConstructibleCategory l E (Spec (.of k)) ⥤
    sfRationalConstructibleCategory l E Y
  adjY : shriek l hl E cY ⊣ rightY
  rightX : sfRationalConstructibleCategory l E (Spec (.of k)) ⥤
    sfRationalConstructibleCategory l E X
  adjX : shriek l hl E cF ⋙ shriek l hl E cY ⊣ rightX

namespace Datum
variable {f} {cF : Factorization (k := k) f}
  {cY : Factorization (k := k) (Y ↘ Spec (.of k))} (B : Datum l hl E f cF cY)

/-- The relative dualizing object on X is RaX! of the specified base coefficient unit.
Source: Bhatt--Scholze 6.7.19 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def omegaX := B.rightX.obj (unit l hl E (Spec (.of k)))

/-- The relative dualizing object on Y, using the same coefficient unit.
Source: Bhatt--Scholze 6.7.19 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def omegaY := B.rightY.obj (unit l hl E (Spec (.of k)))

/-- The dual is the existing common-stage internal Hom into RaX! of the unit.
Source: Bhatt--Scholze 6.7.20 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def dualX := dual l hl E X B.closedX (B.omegaX l hl E)

/-- The dual on Y uses precisely the same recorded internal-Hom operation.
Source: Bhatt--Scholze 6.7.20 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def dualY := dual l hl E Y B.closedY (B.omegaY l hl E)

/-- Evaluation followed by the actual structure-map counit is the relative trace pairing.
Source: Bhatt--Scholze 6.7.19 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def pairing (K : sfRationalConstructibleCategory l E X) :
    (shriek l hl E cF ⋙ shriek l hl E cY).obj
      ((tensor l hl E X).obj
        ((pull l hl E f).obj
          ((B.dualY l hl E).obj (op ((shriek l hl E cF).obj K))), K)) ⟶
      unit l hl E (Spec (.of k)) :=
  (shriek l hl E cY).map
    (projection l hl E cF _ K ≫
      eqToHom (congrArg
        (fun F ↦ F.obj
          ((B.dualY l hl E).obj (op ((shriek l hl E cF).obj K)),
            (shriek l hl E cF).obj K)) B.closedY.tensor_eq.symm) ≫
      B.closedY.closed.evaluation ((shriek l hl E cF).obj K) (B.omegaY l hl E)) ≫
    B.adjY.counit.app (unit l hl E (Spec (.of k)))

/-- The exchange arrow is the three actual adjunction transposes of projection,
evaluation and trace. No exchange map or isomorphism is a field of Datum.
Source: Bhatt--Scholze 6.7.19 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def exchange (K : sfRationalConstructibleCategory l E X) :
    (B.dualY l hl E).obj (op ((shriek l hl E cF).obj K)) ⟶
      (push l hl E f).obj ((B.dualX l hl E).obj (op K)) :=
  (ordinaryAdjunction l hl E f).homEquiv _ _
    (B.closedX.closed.transpose _ K (B.omegaX l hl E)
      (eqToHom (congrArg
        (fun F ↦ F.obj
          ((pull l hl E f).obj
            ((B.dualY l hl E).obj (op ((shriek l hl E cF).obj K))), K))
        B.closedX.tensor_eq) ≫
        B.adjX.homEquiv _ _ (B.pairing l hl E K)))

end Datum
end Conclusion
end Rational

/-- Canonical tensor comparison from one finite stage to the common-stage tensor.
It is built from the actual tensor scalar comparison at the compositum, the actual
pair inclusion transition, and the specified object formula for common-stage tensor.
Source: blueprint thm-coef-qbar-verdier, evaluation descent
(blueprint: lem-per-qbar-arbitrary-field-duality). -/
def tensorInclusion (T : Scheme.{u}) [T.Over (Spec (.of k))]
    (E : Index l Ω) (K M : Stage l Ω T E) :
    (inclusion E).obj ((Rational.tensor l hl (Coefficient.{u} l Ω E) T).obj (K, M)) ≅
      (tensor l hl Ω T).obj ((inclusion E).obj K, (inclusion E).obj M) := by
  letI := residueInvertibleWithUnit l hl T
  exact
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T).transIso
      ((Padic.finiteCoefficientFields_properties l Ω).1 E E).1).symm.app _ ≪≫
    (inclusion (Padic.finiteCoefficientCompositum l Ω E E)).mapIso
      (((operationStageTransitionIso l Ω T E _
          ((Padic.finiteCoefficientFields_properties l Ω).1 E E).1).app _) ≪≫
        (rationalTensorScalarComparison l (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω E E))
          (coefficientInclusion l Ω E _
            ((Padic.finiteCoefficientFields_properties l Ω).1 E E).1) T).app (K, M) ≪≫
        (rationalDerivedTensor l
          (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω E E)) T).mapIso
          (Iso.prod
            ((operationStageTransitionIso l Ω T E _
              ((Padic.finiteCoefficientFields_properties l Ω).1 E E).1).app K).symm
            ((operationStageTransitionIso l Ω T E _
              ((Padic.finiteCoefficientFields_properties l Ω).1 E E).2).app M).symm)) ≪≫
    eqToIso (((commonStageDerivedTensor_existsUnique l Ω T).exists.choose_spec.1
      ((inclusion E).obj K) ((inclusion E).obj M)).symm)

section SignedHom
variable (T : Scheme.{u}) [T.Over (Spec (.of k))]
  [IsSeparated (T ↘ Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
  [QuasiCompact (T ↘ Spec (.of k))] (B : Closed l hl Ω T)

/-- The inclusion comparison for Hom is uniquely fixed by the actual evaluations.
Source: Bhatt--Scholze 6.7.13, 6.8.14
(blueprint: lem-per-qbar-arbitrary-field-duality).
Proof: the rational coefficient Hom comparison is the transpose of extended
evaluation. Its normalized identity and tower laws define this map on common-stage
representatives. The common-stage Hom adjunction makes the displayed equation
unique. Invertibility follows from the finite free Hom comparison. -/
theorem homInclusion_existsUnique (E : Index l Ω) (M N : Stage l Ω T E) :
    ∃! e : (inclusion E).obj
        ((Rational.hom l (Coefficient.{u} l Ω E) T
          (Rational.permitted l hl (Coefficient.{u} l Ω E) T)).obj (op M, N)) ≅
      (hom l Ω T B.permitted).obj (op ((inclusion E).obj M), (inclusion E).obj N),
      (tensor l hl Ω T).map (Prod.mkHom e.hom (𝟙 _)) ≫
        eqToHom (congrArg (fun F ↦ F.obj
          ((hom l Ω T B.permitted).obj
            (op ((inclusion E).obj M), (inclusion E).obj N), (inclusion E).obj M))
          B.tensor_eq.symm) ≫
        B.closed.evaluation ((inclusion E).obj M) ((inclusion E).obj N) =
      (tensorInclusion l hl Ω T E _ M).inv ≫
        (inclusion E).map (rationalEvaluation l hl T (Coefficient.{u} l Ω E)
          ⟨(op M, N), Rational.permitted l hl (Coefficient.{u} l Ω E) T _⟩) := by
  sorry

/-- The evaluation-normalized inclusion comparison, with no free comparison field.
Source: Bhatt--Scholze 6.8.14 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def homInclusion (E : Index l Ω) (M N : Stage l Ω T E) :=
  (homInclusion_existsUnique l hl Ω T B E M N).exists.choose

/-- The common-stage signed Hom comparison is determined by the localized signed
complex comparison at every finite field, including identity stages.
Source: Bhatt--Scholze 6.7.13, 6.8.14; Stacks 08JA
(blueprint: lem-per-qbar-arbitrary-field-duality).
Proof: use the rational Hom shift fixed by the integral product-reindexing map.
Its scalar compatibility follows projectionwise on Hom complexes, including the
sign (-1)^(a*k). The evaluation-normalized Hom inclusion comparisons identify its
images at every larger field. Thus these maps descend to the common-stage Hom
colimits. Naturality descends from the finite maps and forces uniqueness, since
every pair of common-stage objects is represented at a common finite field. -/
theorem homShift_existsUnique :
    ∃! σ : ∀ (M N : generalAlgebraicallyClosedConstructibleCategory l Ω T) (a b : ℤ),
        ((hom l Ω T B.permitted).obj (op M, N))⟦b - a⟧ ≅
          (hom l Ω T B.permitted).obj (op (M⟦a⟧), N⟦b⟧),
      (∀ (M N M' N' : generalAlgebraicallyClosedConstructibleCategory l Ω T)
          (a b : ℤ) (f : M' ⟶ M) (g : N ⟶ N'),
        ((hom l Ω T B.permitted).map (Prod.mkHom f.op g))⟦b - a⟧' ≫
          (σ M' N' a b).hom =
        (σ M N a b).hom ≫ (hom l Ω T B.permitted).map
          (Prod.mkHom (f⟦a⟧').op (g⟦b⟧'))) ∧
      ∀ (E : Index l Ω) (M N : Stage l Ω T E) (a b : ℤ),
        ((homInclusion l hl Ω T B E M N).hom)⟦b - a⟧' ≫
          (σ ((inclusion E).obj M) ((inclusion E).obj N) a b).hom =
        ((inclusion E : Stage l Ω T E ⥤ _).commShiftIso (b - a)).inv.app _ ≫
          (inclusion E).map (Rational.homShift l hl (Coefficient.{u} l Ω E) T M N a b).hom ≫
          (homInclusion l hl Ω T B E (M⟦a⟧) (N⟦b⟧)).hom ≫
          (hom l Ω T B.permitted).map
            (Prod.mkHom
              (((inclusion E : Stage l Ω T E ⥤ _).commShiftIso a).inv.app M).op
              (((inclusion E : Stage l Ω T E ⥤ _).commShiftIso b).hom.app N)) := by
  sorry

/-- The canonical common-stage Hom shift, fixed by its full signed normalization.
Source: Stacks 08JA; Bhatt--Scholze 6.8.14
(blueprint: lem-per-qbar-arbitrary-field-duality). -/
def homShift := (homShift_existsUnique l hl Ω T B).exists.choose

/-- The contravariant duality shift is the inverse signed source-Hom comparison.
The zero shift on omega is removed by its canonical zero-shift isomorphism.
Source: Bhatt--Scholze 6.7.20 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def dualShift (omega K : generalAlgebraicallyClosedConstructibleCategory l Ω T) (n : ℤ) :
    (dual l hl Ω T B omega).obj (op (K⟦n⟧)) ≅
      ((dual l hl Ω T B omega).obj (op K))⟦-n⟧ := by
  change (hom l Ω T B.permitted).obj (op (K⟦n⟧), omega) ≅
    ((hom l Ω T B.permitted).obj (op K, omega))⟦-n⟧
  simpa only [zero_sub, Functor.id_obj] using (hom l Ω T B.permitted).mapIso
    (Iso.prod (Iso.refl (op (K⟦n⟧))) ((shiftFunctorZero _ ℤ).app omega).symm) ≪≫
    (homShift l hl Ω T B K omega n 0).symm

end SignedHom

section StageImages
variable {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  [IsSeparated (Z ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
  (E : Index l Ω)

/-- The pullback inclusion comparison is the recorded literal pair formula.
Source: Bhatt--Scholze 6.8.14 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def pullInclusion (f : X ⟶ Y) (M : Stage l Ω Y E) :
    (inclusion E).obj ((Rational.pull l hl (Coefficient.{u} l Ω E) f).obj M) ≅
      (pull l hl Ω f).obj ((inclusion E).obj M) :=
  letI := residueInvertibleWithUnit l hl X
  letI := residueInvertibleWithUnit l hl Y
  eqToIso (((commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1
    ((inclusion E).obj M)).symm)

/-- Ordinary-image inclusion is the counit mate of the fixed pullback comparison.
Source: Bhatt--Scholze 6.7.2, 6.8.14
(blueprint: lem-per-qbar-arbitrary-field-duality). -/
def pushInclusionArrow (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (N : Stage l Ω X E) :
    (inclusion E).obj ((Rational.push l hl (Coefficient.{u} l Ω E) f).obj N) ⟶
      (arbitraryFieldDerivedPushWithUnit l hl Ω f).obj ((inclusion E).obj N) :=
  (ordinaryAdjunction l hl Ω f).homEquiv _ _
    ((pullInclusion l hl Ω E f _).inv ≫
      (inclusion E).map ((Rational.ordinaryAdjunction l hl
        (Coefficient.{u} l Ω E) f).counit.app N))

/-- Open-extension inclusion is the unit mate, with its direction reversed below.
Source: Bhatt--Scholze 6.7.6, 6.8.14
(blueprint: lem-per-qbar-arbitrary-field-duality). -/
def openInclusionArrow (j : X ⟶ Z) [IsOpenImmersion j] (K : Stage l Ω X E) :
    (openExtension l hl Ω j).obj ((inclusion E).obj K) ⟶
      (inclusion E).obj ((Rational.openExtension l hl (Coefficient.{u} l Ω E) j).obj K) :=
  ((openAdjunction l hl Ω j).homEquiv _ _).symm
    ((inclusion E).map ((Rational.openAdjunction l hl
      (Coefficient.{u} l Ω E) j).unit.app K) ≫ (pullInclusion l hl Ω E j _).hom)

/-- These canonical inclusion mates are isomorphisms on the constructible categories.
Source: Bhatt--Scholze 6.7.6, 6.7.14, 6.8.14
(blueprint: lem-per-qbar-arbitrary-field-duality).
Proof: the completed scalar comparisons preserve the ordinary adjunction counit
and the open-extension unit. Rationalize these equations; their isomorphisms give
exactly the displayed mates. Descent to common stages preserves both inverses. -/
theorem inclusionMates_isIso :
    (∀ (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (N : Stage l Ω X E),
      IsIso (pushInclusionArrow l hl Ω E f N)) ∧
    (∀ (j : X ⟶ Z) [IsOpenImmersion j] (K : Stage l Ω X E),
      IsIso (openInclusionArrow l hl Ω E j K)) := by
  sorry

/-- The canonical ordinary-image comparison, with its counit-mate normalization.
Source: Bhatt--Scholze 6.8.14 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def pushInclusion (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (N : Stage l Ω X E) :=
  @asIso _ _ _ _ (pushInclusionArrow l hl Ω E f N)
    ((inclusionMates_isIso l hl Ω (Z := X) E).1 f N)

/-- The proper/open comparison is the composite of the two specified inclusion mates.
Source: Bhatt--Scholze 6.8.14 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def shriekInclusion {f : X ⟶ Y} (c : Factorization (k := k) f) (K : Stage l Ω X E) :
    (inclusion E).obj ((Rational.shriek l hl (Coefficient.{u} l Ω E) c).obj K) ≅
      (shriek l hl Ω c).obj ((inclusion E).obj K) :=
  pushInclusion l hl Ω E c.compactification.g _ ≪≫
    (arbitraryFieldDerivedPushWithUnit l hl Ω c.compactification.g).mapIso
      (@asIso _ _ _ _ (openInclusionArrow l hl Ω E c.compactification.i K)
        ((inclusionMates_isIso l hl Ω (Y := X) E).2 c.compactification.i K)).symm

end StageImages

/-- Actual evaluation duality, with shift reversal and canonical bidual arrows.
Source: Bhatt--Scholze 6.7.20 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
structure Duality (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))] (B : Closed l hl Ω T)
    (omega : generalAlgebraicallyClosedConstructibleCategory l Ω T) where
  equivalence : (dual l hl Ω T B omega).IsEquivalence
  exact : ∃ s : (dual l hl Ω T B omega).CommShift ℤ,
    ∀ A : Triangle (generalAlgebraicallyClosedConstructibleCategory l Ω T)ᵒᵖ,
      A ∈ distTriang _ →
      Triangle.mk ((dual l hl Ω T B omega).map A.mor₁)
        ((dual l hl Ω T B omega).map A.mor₂)
        ((dual l hl Ω T B omega).map A.mor₃ ≫
          (s.commShiftIso (1 : ℤ)).hom.app A.obj₁) ∈ distTriang _
  bidual_isIso (K : generalAlgebraicallyClosedConstructibleCategory l Ω T) :
    IsIso (bidual l hl Ω T B omega K)
  bidual_natural (K L : generalAlgebraicallyClosedConstructibleCategory l Ω T) (a : K ⟶ L) :
    a ≫ bidual l hl Ω T B omega L = bidual l hl Ω T B omega K ≫
      (dual l hl Ω T B omega).map ((dual l hl Ω T B omega).map a.op).op
/-- Relative normalization is pinned by Ra! of the base unit and the trdeg-indexed
smooth-open purity formula. The structure-map adjunction already determines omega
on singular schemes too; the chart formula specifies the relative dimension sign
and Tate twist, rather than leaving the dimension function unused.
Source: BBD 4.0; Bhatt--Scholze 6.7.19
(blueprint: lem-per-qbar-arbitrary-field-duality). -/
def Normalization (T : Scheme.{u}) [T.Over (Spec (.of k))]
    (omega : generalAlgebraicallyClosedConstructibleCategory l Ω T) : Prop :=
  (∀ [IsIso (T ↘ Spec (.of k))],
    Nonempty (omega ≅ (pull l hl Ω (T ↘ Spec (.of k))).obj
      (unit l hl Ω (Spec (.of k))))) ∧
  (∀ (U : Scheme.{u}) [U.Over (Spec (.of k))] (j : U ⟶ T)
    [j.IsOver (Spec (.of k))] [IsOpenImmersion j]
    [Smooth (U ↘ Spec (.of k))] [IrreducibleSpace U]
    (t : U) (_ht : IsGenericPoint t Set.univ) (d : ℕ),
    relativeTranscendenceDegree (U ↘ Spec (.of k)) t = (d : Cardinal) →
    Nonempty ((pull l hl Ω j).obj omega ≅
      (@sfQbarTwistingCoefficient l _ U (residueInvertibleWithUnit l hl U) Ω _ _ _
        (d : ℤ))⟦(2 : ℤ) * d⟧))

section Properties
variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (B : Datum l hl Ω f)

/-- The two actual functors on either side of the canonical exchange.
Source: Bhatt--Scholze 6.7.19 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def exchangeLeft := (shriek l hl Ω B.factorF).op ⋙ B.dualY l hl Ω

/-- Ordinary adic image composed with the specified internal-Hom dual.
Source: Bhatt--Scholze 6.7.19 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def exchangeRight := B.dualX l hl Ω ⋙ arbitraryFieldDerivedPushWithUnit l hl Ω f

/-- A genuine commutative shift square for the evaluation-defined exchange.
Both sides start at D_Y Rf!(K[n]) and end at Rf*(D_X K[-n]).
Source: Bhatt--Scholze 6.7.19--20
(blueprint: lem-per-qbar-arbitrary-field-duality). -/
def ShiftCompatible : Prop :=
  ∀ (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) (n : ℤ),
    (B.dualY l hl Ω).map
      (((shriekShift l hl Ω B.factorF).commShiftIso n).inv.app K).op ≫
      (dualShift l hl Ω Y B.closedY (B.omegaY l hl Ω)
        ((shriek l hl Ω B.factorF).obj K) n).hom ≫
      (shiftFunctor (generalAlgebraicallyClosedConstructibleCategory l Ω Y) (-n)).map
        (B.exchange l hl Ω K) ≫
      ((pushShift l hl Ω f).commShiftIso (-n)).inv.app
        ((B.dualX l hl Ω).obj (op K)) =
    B.exchange l hl Ω (K⟦n⟧) ≫
      (arbitraryFieldDerivedPushWithUnit l hl Ω f).map
        (dualShift l hl Ω X B.closedX (B.omegaX l hl Ω) K n).hom

/-- The common coefficient unit is the rational coefficient unit at every stage.
The comparison uses the actual normalized unit scalar comparison and transIso.
Source: Bhatt--Scholze 6.8.14 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def unitInclusion (T : Scheme.{u}) [T.Over (Spec (.of k))] (E : Index l Ω) :
    (inclusion E).obj (Rational.unit l hl (Coefficient.{u} l Ω E) T) ≅ unit l hl Ω T :=
  letI := residueInvertibleWithUnit l hl T
  (inclusion E).mapIso
    ((pullbackTensorCommonUnitStage l Ω T E (show
      (pullbackTensorCommonUnit l Ω T).stage ≤ E from
        (show (⊥ : IntermediateField (Padic l) Ω) ≤ E.val from bot_le))).symm) ≪≫
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T).transIso
      (show (Padic.finiteCoefficientBase l Ω) ≤ E from
        (show (⊥ : IntermediateField (Padic l) Ω) ≤ E.val from bot_le))).app _

/-- The Y dualizing-object inclusion is the structure-adjunction transpose of the
finite-stage trace, with the compact-support and coefficient-unit comparisons.
Source: Bhatt--Scholze 6.7.19, 6.8.14
(blueprint: lem-per-qbar-arbitrary-field-duality). -/
def omegaYInclusionArrow (E : Index l Ω)
    (A : Rational.Datum l hl (Coefficient.{u} l Ω E) f B.factorF B.factorY) :
    (inclusion E).obj (A.omegaY l hl (Coefficient.{u} l Ω E)) ⟶ B.omegaY l hl Ω :=
  B.adjY.homEquiv _ _
    ((shriekInclusion l hl Ω E B.factorY _).inv ≫
      (inclusion E).map (A.adjY.counit.app
        (Rational.unit l hl (Coefficient.{u} l Ω E) (Spec (.of k)))) ≫
      (unitInclusion l hl Ω (Spec (.of k)) E).hom)

/-- The X comparison uses the composed structure adjunction and both fixed
compact-support inclusion comparisons, so its trace has the same normalization.
Source: Bhatt--Scholze 6.7.19, 6.8.14
(blueprint: lem-per-qbar-arbitrary-field-duality). -/
def omegaXInclusionArrow (E : Index l Ω)
    (A : Rational.Datum l hl (Coefficient.{u} l Ω E) f B.factorF B.factorY) :
    (inclusion E).obj (A.omegaX l hl (Coefficient.{u} l Ω E)) ⟶ B.omegaX l hl Ω :=
  B.adjX.homEquiv _ _
    ((shriek l hl Ω B.factorY).map (shriekInclusion l hl Ω E B.factorF _).inv ≫
      (shriekInclusion l hl Ω E B.factorY _).inv ≫
      (inclusion E).map (A.adjX.counit.app
        (Rational.unit l hl (Coefficient.{u} l Ω E) (Spec (.of k)))) ≫
      (unitInclusion l hl Ω (Spec (.of k)) E).hom)

/-- Exceptional scalar comparison makes the two trace-normalized maps invertible.
Source: Bhatt--Scholze 6.7.19, 6.8.14
(blueprint: lem-per-qbar-arbitrary-field-duality).
Proof: apply the finite scalar comparison for extraordinary pullback to the base
coefficient unit, preserving its counit. Its adjunction-mate equation identifies
it with the displayed transpose. For X use the composed adjunction and the same
counit equation twice. Rationalization and common-stage descent retain inverses. -/
theorem omegaInclusion_isIso (E : Index l Ω)
    (A : Rational.Datum l hl (Coefficient.{u} l Ω E) f B.factorF B.factorY) :
    IsIso (omegaXInclusionArrow l hl Ω B E A) ∧
      IsIso (omegaYInclusionArrow l hl Ω B E A) := by
  sorry

/-- Inclusion of the X dual is Hom inclusion followed by its trace-normalized
second-argument comparison. Source: Bhatt--Scholze 6.8.14
(blueprint: lem-per-qbar-arbitrary-field-duality). -/
def dualXInclusion (E : Index l Ω)
    (A : Rational.Datum l hl (Coefficient.{u} l Ω E) f B.factorF B.factorY)
    (K : Stage l Ω X E) :
    (inclusion E).obj ((A.dualX l hl (Coefficient.{u} l Ω E)).obj (op K)) ≅
      (B.dualX l hl Ω).obj (op ((inclusion E).obj K)) :=
  homInclusion l hl Ω X B.closedX E K (A.omegaX l hl (Coefficient.{u} l Ω E)) ≪≫
    (hom l Ω X B.closedX.permitted).mapIso
      (Iso.prod (Iso.refl (op ((inclusion E).obj K)))
        (@asIso _ _ _ _ (omegaXInclusionArrow l hl Ω B E A)
          (omegaInclusion_isIso l hl Ω B E A).1))

/-- Inclusion of the Y dual uses the same evaluation and trace normalizations.
Source: Bhatt--Scholze 6.8.14 (blueprint: lem-per-qbar-arbitrary-field-duality). -/
def dualYInclusion (E : Index l Ω)
    (A : Rational.Datum l hl (Coefficient.{u} l Ω E) f B.factorF B.factorY)
    (M : Stage l Ω Y E) :
    (inclusion E).obj ((A.dualY l hl (Coefficient.{u} l Ω E)).obj (op M)) ≅
      (B.dualY l hl Ω).obj (op ((inclusion E).obj M)) :=
  homInclusion l hl Ω Y B.closedY E M (A.omegaY l hl (Coefficient.{u} l Ω E)) ≪≫
    (hom l Ω Y B.closedY.permitted).mapIso
      (Iso.prod (Iso.refl (op ((inclusion E).obj M)))
        (@asIso _ _ _ _ (omegaYInclusionArrow l hl Ω B E A)
          (omegaInclusion_isIso l hl Ω B E A).2))

/-- Finite scalar compatibility compares the defined common-stage exchange with
its rational-stage projection/evaluation/trace transpose through the fixed
inclusion comparisons. This is imposed at every finite field, hence also after
every finite extension and for the identity extension; the inclusion transIso
and scalar mates retain their identity and tower normalizations.
Source: Bhatt--Scholze 6.7.19, 6.8.14--15
(blueprint: lem-per-qbar-arbitrary-field-duality). -/
def ScalarCompatible : Prop :=
  ∃ A : ∀ E : Index l Ω,
      Rational.Datum l hl (Coefficient.{u} l Ω E) f B.factorF B.factorY,
    ∀ (E : Index l Ω) (K : Stage l Ω X E),
      (dualYInclusion l hl Ω B E (A E)
        ((Rational.shriek l hl (Coefficient.{u} l Ω E) B.factorF).obj K)).hom ≫
        (B.dualY l hl Ω).map ((shriekInclusion l hl Ω E B.factorF K).inv).op ≫
        B.exchange l hl Ω ((inclusion E).obj K) =
      (inclusion E).map ((A E).exchange l hl (Coefficient.{u} l Ω E) K) ≫
        (pushInclusion l hl Ω E f
          (((A E).dualX l hl (Coefficient.{u} l Ω E)).obj (op K))).hom ≫
        (arbitraryFieldDerivedPushWithUnit l hl Ω f).map
          (dualXInclusion l hl Ω B E (A E) K).hom

/-- The structure arrow over its base, with the identity base structure explicit.
Source: scheme conventions (blueprint: lem-per-qbar-arbitrary-field-duality). -/
instance structureIsOver (U : Scheme.{u}) [U.Over (Spec (.of k))] :
    (U ↘ Spec (.of k)).IsOver (Spec (.of k)) :=
  inferInstanceAs (IsOverTower U (Spec (.of k)) (Spec (.of k)))

/-- The complete conclusion, with all functors, units and comparison arrows pinned.
The three realization clauses identify the proper/open construction with the
recorded compact-support action on every finite coefficient stage and its arrows.
The X structure operation is their actual composite, not an unrelated left adjoint.
Source: Bhatt--Scholze 6.7.13--20 and 6.8.14--15
(blueprint: lem-per-qbar-arbitrary-field-duality). -/
structure Properties where
  normalizedX : Normalization l hl Ω X (B.omegaX l hl Ω)
  normalizedY : Normalization l hl Ω Y (B.omegaY l hl Ω)
  dualityX : Duality l hl Ω X B.closedX (B.omegaX l hl Ω)
  dualityY : Duality l hl Ω Y B.closedY (B.omegaY l hl Ω)
  compactF : ∃ S : SfCompactSupportCoefficientAction l k hl Ω B.factorF.compactification,
    Nonempty (shriek l hl Ω B.factorF ≅ S.system.functor)
  compactY : ∃ S : SfCompactSupportCoefficientAction l k hl Ω B.factorY.compactification,
    Nonempty (shriek l hl Ω B.factorY ≅ S.system.functor)
  compactX : ∃ c : Compactification (X ↘ Spec (.of k)),
    ∃ S : SfCompactSupportCoefficientAction l k hl Ω c,
    Nonempty (shriek l hl Ω B.factorF ⋙ shriek l hl Ω B.factorY ≅ S.system.functor)
  exchange_isIso (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) :
    IsIso (B.exchange l hl Ω K)
  exchange_natural (K L : generalAlgebraicallyClosedConstructibleCategory l Ω X)
      (a : L ⟶ K) :
    (exchangeLeft l hl Ω B).map a.op ≫ B.exchange l hl Ω L =
      B.exchange l hl Ω K ≫ (exchangeRight l hl Ω B).map a.op
  shift_compatible : ShiftCompatible l hl Ω B
  scalar_compatible : ScalarCompatible l hl Ω B

end Properties
end ArbitraryFieldVerdier

/-- Relative Verdier duality and the canonical direct-image exchange over any field.
Source: Bhatt--Scholze 6.7.13, 6.7.14, 6.7.19--20, 6.8.14 and 6.8.15; BBD 4.0
(blueprint: lem-per-qbar-arbitrary-field-duality).
Proof: (1) Identify the integral stages with the completed constructible categories
by the stratified-perfect characterization. (2) Apply the exceptional adjunction to
the structure maps and their coefficient units; the first finite reduction is the
relative normalized dualizing complex for trdeg_k kappa(t). The smooth-open formula
fixes the Tate sign and shift, and the identity case gives the base coefficient unit.
(3) Reduce the evaluation-defined bidual arrow to finite residue coefficients.
Finite biduality makes its cone reduce to zero; induction through coefficient exact
sequences kills every reduction, and completeness kills the cone. (4) Internal Hom
is contravariantly exact and reverses signed shifts; biduality gives its quasi-inverse.
(5) The open unit and proper counit projection mates give the actual compactification
projection. Compose with evaluation and the structure trace. Its three adjunction
transposes are precisely Datum.exchange. The corresponding natural Hom bijections
supply its inverse, so this arrow, rather than a freely selected comparison, is iso.
(6) Transpose after shifting; signed tensor-Hom comparisons identify the pairings,
which proves ShiftCompatible. (7) Finite scalar extension preserves evaluation,
units, counits and both projection mates. It therefore preserves the three
transposes and the bidual arrow. Rationalize the Hom bijections and their inverses.
(8) Descend along the common-stage coefficient comparisons and their unit and tower
equations. This gives ScalarCompatible, exactness, both adjunctions and the
compact-support realization clauses on the specified category, without imposing
perfectness, separable closedness, or finite Galois cohomological dimension on k. -/
theorem arbitrary_field_verdier_duality
    {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : k))
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ B : ArbitraryFieldVerdier.Datum l hl Ω f,
      Nonempty (ArbitraryFieldVerdier.Properties l hl Ω B) := by
  sorry

end WeilConjectures
