/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.SixFunctors.RationalVerdier
public import Sheaf.SixFunctors.RationalOperations
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.SfBidualityClass
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.CategoryTheory.StageSystemFunctorDescent
import Sheaf.SixFunctors.CoefIntegralFiniteExtension
import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.Paper.SfScalarExtensionComposition

/-! # Verdier biduality at algebraically closed coefficients

Source: blueprint sec-six-functors/sk-prop-sf-biduality-general,
thm-coef-qbar-verdier, statement and proof steps 1–10
(blueprint: thm-coef-qbar-verdier).

The records package conclusions on the published raw finite stages and their actual
pair category. Every comparison is normalized either to an existing coefficient
operation or to its explicit finite-stage evaluation, biduality, unit and counit.
The closure Ω and the schemes have independent universes.
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

/-- The published common-stage tensor with the canonical residue-field units.
Source: blueprint thm-coef-qbar-verdier, tensor–Hom paragraph
(blueprint: thm-coef-qbar-verdier). -/
def CoefQbarTensor
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))] :
    generalAlgebraicallyClosedConstructibleCategory l Ω X ×
      generalAlgebraicallyClosedConstructibleCategory l Ω X ⥤
        generalAlgebraicallyClosedConstructibleCategory l Ω X := by
  letI := RationalVerdier.units D l hl X
  exact commonStageDerivedTensor l Ω X

/-- The published common-stage pullback, with the canonical residue-field units.
Source: blueprint thm-coef-qbar-verdier, exceptional formula
(blueprint: thm-coef-qbar-verdier). -/
def CoefQbarPullback
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [Y.Over (Spec (.of D.k))] (f : X ⟶ Y) :
    generalAlgebraicallyClosedConstructibleCategory l Ω Y ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω X := by
  letI := RationalVerdier.units D l hl X
  letI := RationalVerdier.units D l hl Y
  exact commonStageDerivedPullback l Ω f

namespace CoefQbarVerdier
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition associator unitor)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- An auxiliary small algebraic closure, used only to access the finite-coefficient
part of the existing exceptional-system API. Its closed stage is never used.
The target coefficient category still uses Ω : Type v.
Source: blueprint thm-coef-qbar-verdier, finite-stage passage
(blueprint: thm-coef-qbar-verdier). -/
abbrev AuxiliaryClosure (l : ℕ) [Fact l.Prime] := AlgebraicClosure (ULift.{u} (Padic l))

/-- Package precisely the small model of the specified intermediate field.
Source: blueprint thm-coef-qbar-verdier, finite intermediate extensions
(blueprint: thm-coef-qbar-verdier). -/
abbrev fieldStage (E : Index l Ω) : ConstructibleExceptionalCoefficients.FieldStage.{u} l :=
  ⟨Coefficient.{u} l Ω E⟩

/-- The canonical transition-to-inclusion comparison for arbitrary closure universe.
This is the stage system's transIso conjugated by its recorded transition equality.
Source: blueprint thm-coef-qbar-verdier, common-stage representative calculus
(blueprint: thm-coef-qbar-verdier). -/
def inclusionTransition (X : Scheme.{u}) (E L : Index l Ω) (h : E ≤ L) :
    transition l Ω X E L h ⋙ inclusion L ≅ inclusion E :=
  eqToIso (congrArg (fun F ↦ F ⋙ inclusion L)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω X).exists.choose_spec.1
      E L h).symm) ≪≫
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).transIso h

variable (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Canonical tensor comparison from one finite stage to the common-stage tensor.
It is built from the actual tensor scalar comparison at the compositum, the actual
pair inclusion transition, and the specified object formula for common-stage tensor.
Source: blueprint thm-coef-qbar-verdier, evaluation descent
(blueprint: thm-coef-qbar-verdier). -/
def tensorInclusion (E : Index l Ω) (K M : Stage l Ω X E) :
    (inclusion E).obj ((RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω E)).obj (K, M)) ≅
      (CoefQbarTensor D l hl Ω X).obj ((inclusion E).obj K, (inclusion E).obj M) := by
  letI := RationalVerdier.units D l hl X
  exact
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).transIso
      ((Padic.finiteCoefficientFields_properties l Ω).1 E E).1).symm.app _ ≪≫
    (inclusion (Padic.finiteCoefficientCompositum l Ω E E)).mapIso
      (((operationStageTransitionIso l Ω X E _
          ((Padic.finiteCoefficientFields_properties l Ω).1 E E).1).app _) ≪≫
        (rationalTensorScalarComparison l (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω E E))
          (coefficientInclusion l Ω E _
            ((Padic.finiteCoefficientFields_properties l Ω).1 E E).1) X).app (K, M) ≪≫
        (rationalDerivedTensor l
          (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω E E)) X).mapIso
          (Iso.prod
            ((operationStageTransitionIso l Ω X E _
              ((Padic.finiteCoefficientFields_properties l Ω).1 E E).1).app K).symm
            ((operationStageTransitionIso l Ω X E _
              ((Padic.finiteCoefficientFields_properties l Ω).1 E E).2).app M).symm)) ≪≫
    eqToIso (((commonStageDerivedTensor_existsUnique l Ω X).exists.choose_spec.1
      ((inclusion E).obj K) ((inclusion E).obj M)).symm)

/-- The canonical object comparison for pullback at a specified finite stage.
It is the recorded common-stage pullback's literal object formula.
Source: blueprint thm-coef-qbar-verdier, exceptional formula descent
(blueprint: thm-coef-qbar-verdier). -/
def pullbackInclusion {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))]
    (f : X ⟶ Y) (E : Index l Ω) (M : Stage l Ω Y E) :
    (inclusion E).obj
        ((@rationalDerivedPullback l _ (Coefficient.{u} l Ω E) _ _ _ X Y f
          (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).obj M) ≅
      (CoefQbarPullback D l hl Ω f).obj ((inclusion E).obj M) := by
  letI := RationalVerdier.units D l hl X
  letI := RationalVerdier.units D l hl Y
  exact eqToIso
    (((commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1
      ((inclusion E).obj M)).symm)

/-- Coherent finite-field duality, with the actual rationalized integral maps.
Unit and associator equations concern the same comparisons, including identity fields.
Source: blueprint thm-coef-qbar-verdier, proof steps 1–4
(blueprint: thm-coef-qbar-verdier). -/
structure Finite where
  omega (E : Index l Ω) :
    IntegralFiniteExtension.DualizingDatum l X D hl (Coefficient.{u} l Ω E)
  datum (E : Index l Ω) : RationalVerdier.Datum D l hl X (Coefficient.{u} l Ω E) (omega E)
  hom (E : Index l Ω) :
    RationalOperations.HomIdentification l (Coefficient.{u} l Ω E) X D hl (omega E) (datum E)
  scalar (E L : Index l Ω) (h : E ≤ L) :
    RationalVerdier.Extension D l hl X (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) (omega E) (omega L) (datum E) (datum L)
  normalized (E L : Index l Ω) (h : E ≤ L) :
    RationalVerdier.ExtensionProperties D l hl X (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h)
      (omega E) (omega L) (datum E) (datum L) (scalar E L h)
  beta (E L : Index l Ω) (h : E ≤ L) :
    (datum E).dual ⋙ transition l Ω X E L h ≅
      (transition l Ω X E L h).op ⋙ (datum L).dual
  betaNormalized (E L : Index l Ω) (h : E ≤ L) :
    HEq (beta E L h) (scalar E L h).comparison

/-- Unit and associator equations for the specified finite duality comparisons.
The equations include repeated fields and are imposed on the actual beta maps.
Source: blueprint thm-coef-qbar-verdier, proof steps 1–2
(blueprint: thm-coef-qbar-verdier). -/
def FiniteCoherent (F : Finite D l hl Ω X) : Prop :=
  (∀ (E : Index l Ω) (K : Stage l Ω X E),
    (F.beta E E le_rfl).hom.app (op K) =
      (unitor l Ω X E).hom.app ((F.datum E).dual.obj (op K)) ≫
        (F.datum E).dual.map ((unitor l Ω X E).hom.app K).op) ∧
  ∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) (K : Stage l Ω X E),
    HEq
      ((transition l Ω X L M k).map ((F.beta E L h).hom.app (op K)) ≫
        (F.beta L M k).hom.app (op ((transition l Ω X E L h).obj K)))
      ((associator l Ω X E L M h k).hom.app ((F.datum E).dual.obj (op K)) ≫
        (F.beta E M (h.trans k)).hom.app (op K) ≫
          (F.datum M).dual.map ((associator l Ω X E L M h k).hom.app K).op)


/-- A contravariant common-stage dual tied to every finite stage and its scalar maps.
The linear structure is fixed on finite representatives by the actual coefficient
embedding; it cannot be an unrelated Ω action. Evaluation is fixed by the finite
rational evaluation through the canonical tensor comparison. Biduality is fixed by
SfClassEvaluationCompatible and hence is the descended evaluation-defined arrow.
Source: blueprint thm-coef-qbar-verdier, proof steps 1–5 and 10
(blueprint: thm-coef-qbar-verdier). -/
structure DualityData where
  finite : Finite D l hl Ω X
  duality : SfClassDuality (generalAlgebraicallyClosedConstructibleCategory l Ω X)
  [linearCategory : Linear Ω (generalAlgebraicallyClosedConstructibleCategory l Ω X)]
  comparison (E : Index l Ω) :
    (finite.datum E).dual ⋙ inclusion (Y := X) E ≅ (inclusion (Y := X) E).op ⋙ duality.dual
  omega : generalAlgebraicallyClosedConstructibleCategory l Ω X
  omegaComparison (E : Index l Ω) :
    (inclusion (Y := X) E).obj
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
      (finite.omega E).omega) ≅ omega
  evaluation (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) :
    (CoefQbarTensor D l hl Ω X).obj (K, duality.dual.obj (op K)) ⟶ omega

/-- Equations fixing the scalar action, finite descent, evaluation and biduality,
including restriction of all these maps to retracts. These are conclusions.
Source: blueprint thm-coef-qbar-verdier, proof steps 1–5 and 10
(blueprint: thm-coef-qbar-verdier). -/
def DualityProperties (B : DualityData D l hl Ω X) : Prop :=
  (fun [_linearInst : Linear Ω (generalAlgebraicallyClosedConstructibleCategory l Ω X)] ↦
  (FiniteCoherent D l hl Ω X B.finite) ∧
  B.duality.dual.Additive ∧
  (∀ (E : Index l Ω)
      (K M : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X) (f : K ⟶ M)
      (c : Coefficient.{u} l Ω E),
    (inclusion (Y := X) E).map
      ((sfRationalCoefficientEquiv l (Coefficient.{u} l Ω E)).symm c •
        (f : (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X) ⟶ M)) =
      ((Shrink.algEquiv (Padic l) E.val c : E.val) : Ω) • (inclusion (Y := X) E).map f) ∧
  (∀ (K M : generalAlgebraicallyClosedConstructibleCategory l Ω X)
      (f : K ⟶ M) (c : Ω),
    B.duality.dual.map (c • f).op = c • B.duality.dual.map f.op) ∧
  (∀ (E : Index l Ω) (K : Stage l Ω X E),
    B.duality.dual.obj (op ((inclusion (Y := X) E).obj K)) =
      (inclusion (Y := X) E).obj ((B.finite.datum E).dual.obj (op K))) ∧
  (∀ (E : Index l Ω) (K : Stage l Ω X E),
    HEq ((B.comparison E).hom.app (op K))
      (𝟙 ((inclusion (Y := X) E).obj ((B.finite.datum E).dual.obj (op K))))) ∧
  (∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E),
    (inclusion (Y := X) L).map ((B.finite.beta E L h).hom.app (op K)) ≫
      (B.comparison L).hom.app (op ((transition l Ω X E L h).obj K)) ≫
      B.duality.dual.map ((inclusionTransition l Ω X E L h).inv.app K).op =
    (inclusionTransition l Ω X E L h).hom.app ((B.finite.datum E).dual.obj (op K)) ≫
      (B.comparison E).hom.app (op K)) ∧
  (∀ (E : Index l Ω),
    SfClassEvaluationCompatible (inclusion (Y := X) E) (B.finite.datum E).dual B.duality.dual
      (B.finite.datum E).bidual.hom B.duality.bidual.hom (B.comparison E)) ∧
  (∀ (E L : Index l Ω) (h : E ≤ L),
    (inclusion (Y := X) L).map (B.finite.scalar E L h).omega.hom ≫ (B.omegaComparison L).hom =
      (inclusionTransition l Ω X E L h).hom.app
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
          (B.finite.omega E).omega) ≫ (B.omegaComparison E).hom) ∧
  (∀ (E : Index l Ω) (K : Stage l Ω X E),
    (tensorInclusion D l hl Ω X E K ((B.finite.datum E).dual.obj (op K))).hom ≫
      (CoefQbarTensor D l hl Ω X).map
        (Prod.mkHom (𝟙 ((inclusion (Y := X) E).obj K)) ((B.comparison E).hom.app (op K))) ≫
      B.evaluation ((inclusion (Y := X) E).obj K) =
    (inclusion (Y := X) E).map ((B.finite.datum E).evaluation K) ≫ (B.omegaComparison E).hom) ∧
  (∀ (K M : generalAlgebraicallyClosedConstructibleCategory l Ω X)
      (f : K ⟶ M),
    (CoefQbarTensor D l hl Ω X).map
        (Prod.mkHom f (𝟙 (B.duality.dual.obj (op M)))) ≫ B.evaluation M =
      (CoefQbarTensor D l hl Ω X).map
        (Prod.mkHom (𝟙 K) (B.duality.dual.map f.op)) ≫ B.evaluation K) ∧
  (∀ (P K : generalAlgebraicallyClosedConstructibleCategory l Ω X)
      (i : P ⟶ K) (p : K ⟶ P) (_h : i ≫ p = 𝟙 P),
    (CoefQbarTensor D l hl Ω X).map
      (Prod.mkHom i (B.duality.dual.map p.op)) ≫ B.evaluation K = B.evaluation P) ∧
  (∀ (P K : generalAlgebraicallyClosedConstructibleCategory l Ω X)
      (i : P ⟶ K) (p : K ⟶ P) (_h : i ≫ p = 𝟙 P),
    i ≫ B.duality.bidual.hom.app K ≫
      B.duality.dual.map (B.duality.dual.map p.op).op = B.duality.bidual.hom.app P) ∧
  (∀ (P K : generalAlgebraicallyClosedConstructibleCategory l Ω X)
      (i : P ⟶ K) (p : K ⟶ P) (_h : i ≫ p = 𝟙 P),
    B.duality.dual.map (B.duality.dual.map i.op).op ≫ B.duality.bidual.inv.app K ≫ p =
      B.duality.bidual.inv.app P)) (_linearInst := B.linearCategory)

/-- The specified common-stage duality and its finite-origin equations.
Source: blueprint thm-coef-qbar-verdier, duality and compatibility clauses
(blueprint: thm-coef-qbar-verdier). -/
structure Duality extends DualityData D l hl Ω X where
  properties : DualityProperties D l hl Ω X toDualityData



/-- The actual internal Hom into a fixed object, on its permitted pairs.
The product functor and full-subcategory lift give its real object and arrow maps.
Source: blueprint thm-coef-qbar-verdier, internal-Hom identification
(blueprint: thm-coef-qbar-verdier). -/
def homDual (omega : generalAlgebraicallyClosedConstructibleCategory l Ω X)
    (permitted : ∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω X,
      commonStageHomPairs l Ω X (op K, omega)) :
    (generalAlgebraicallyClosedConstructibleCategory l Ω X)ᵒᵖ ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω X :=
  (commonStageHomPairs l Ω X).lift
    ((𝟭 _).prod' ((Functor.const _).obj omega)) (fun K ↦ permitted K.unop) ⋙
      commonStageDerivedInternalHom l Ω X

/-- Internal Hom into the specified omega, with the universal property of the same
finite-origin evaluation. The displayed bijection is the actual evaluation transpose;
no unspecified Hom-set bijection or arbitrary evaluation family is admitted.
Source: blueprint thm-coef-qbar-verdier, proof step 5
(blueprint: thm-coef-qbar-verdier). -/
structure InternalHom (B : Duality D l hl Ω X) where
  permitted : ∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω X,
    commonStageHomPairs l Ω X (op K, B.omega)
  comparison : B.duality.dual ≅ homDual l Ω X B.omega permitted
  universal (K P : generalAlgebraicallyClosedConstructibleCategory l Ω X) :
    Function.Bijective (fun h : P ⟶ B.duality.dual.obj (op K) ↦
      (CoefQbarTensor D l hl Ω X).map (Prod.mkHom (𝟙 K) h) ≫ B.evaluation K)

section Exceptional
variable {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The existing rational compact-support functor, with its category endpoints cached.
This is exactly the finite rational operation of the recorded exceptional system.
Source: blueprint thm-coef-qbar-verdier, proof steps 6–7
(blueprint: thm-coef-qbar-verdier). -/
def finiteLeft (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f))
    (E : Index l Ω) : Stage l Ω X E ⥤ Stage l Ω Y E :=
  (S.ring.operation c (.rational (fieldStage l Ω E))).F

/-- The existing rational exceptional functor with the same cached finite endpoints.
Source: blueprint thm-coef-qbar-verdier, proof steps 6–7
(blueprint: thm-coef-qbar-verdier). -/
def finiteRight (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f))
    (E : Index l Ω) : Stage l Ω Y E ⥤ Stage l Ω X E :=
  (S.ring.operation c (.rational (fieldStage l Ω E))).G

/-- The actual finite adjunction, including its specified unit and counit.
Source: blueprint thm-coef-qbar-verdier, proof steps 7–8
(blueprint: thm-coef-qbar-verdier). -/
def finiteAdjunction (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f))
    (E : Index l Ω) : finiteLeft D l hl Ω X f c S E ⊣ finiteRight D l hl Ω X f c S E :=
  (S.ring.operation c (.rational (fieldStage l Ω E))).adjunction

/-- The actual compact-support scalar comparison in the recorded finite system.
Source: blueprint thm-coef-qbar-verdier, proof step 6
(blueprint: thm-coef-qbar-verdier). -/
def finiteLeftScalar (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f))
    (E L : Index l Ω) (h : E ≤ L) :
    finiteLeft D l hl Ω X f c S E ⋙ transition l Ω Y E L h ≅
      transition l Ω X E L h ⋙ finiteLeft D l hl Ω X f c S L :=
  (S.fields.rationalComparison c (fieldStage l Ω E) (fieldStage l Ω L)
    (coefficientInclusion l Ω E L h)).q

/-- The actual exceptional scalar comparison, the specified adjunction mate.
Source: blueprint thm-coef-qbar-verdier, proof step 6
(blueprint: thm-coef-qbar-verdier). -/
def finiteRightScalar (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f))
    (E L : Index l Ω) (h : E ≤ L) :
    finiteRight D l hl Ω X f c S E ⋙ transition l Ω X E L h ≅
      transition l Ω Y E L h ⋙ finiteRight D l hl Ω X f c S L :=
  (S.fields.rationalComparison c (fieldStage l Ω E) (fieldStage l Ω L)
    (coefficientInclusion l Ω E L h)).b

/-- Descent of the specified finite-coefficient exceptional system to Ω.
The small auxiliary closure occurs only in that system's finite rational stages.
The displayed inclusion comparisons commute with its scalar comparisons and carry
its actual unit and counit; thus the two functors cannot be unrelated adjoints.
Source: blueprint thm-coef-qbar-verdier, proof steps 6–8
(blueprint: thm-coef-qbar-verdier). -/
structure ExceptionalData (c : Compactification f) where
  system : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f)
  left : generalAlgebraicallyClosedConstructibleCategory l Ω X ⥤
    generalAlgebraicallyClosedConstructibleCategory l Ω Y
  right : generalAlgebraicallyClosedConstructibleCategory l Ω Y ⥤
    generalAlgebraicallyClosedConstructibleCategory l Ω X
  adjunction : left ⊣ right
  leftComparison (E : Index l Ω) :
    (finiteLeft D l hl Ω X f c system E) ⋙ inclusion (Y := Y) E ≅
      inclusion (Y := X) E ⋙ left
  rightComparison (E : Index l Ω) :
    (finiteRight D l hl Ω X f c system E) ⋙ inclusion (Y := X) E ≅
      inclusion (Y := Y) E ⋙ right

/-- Literal pair formulas and the scalar, unit and counit descent equations for
these same specified exceptional operations, including identity scalar extensions.
Source: blueprint thm-coef-qbar-verdier, proof steps 6–8
(blueprint: thm-coef-qbar-verdier). -/
def ExceptionalProperties (c : Compactification f)
    (A : ExceptionalData D l hl Ω X f c) : Prop :=
  (∀ (E : Index l Ω) (K : Stage l Ω X E),
    A.left.obj ((inclusion E).obj K) =
      (inclusion E).obj ((finiteLeft D l hl Ω X f c A.system E).obj K)) ∧
  (∀ (E : Index l Ω) (M : Stage l Ω Y E),
    A.right.obj ((inclusion E).obj M) =
      (inclusion E).obj ((finiteRight D l hl Ω X f c A.system E).obj M)) ∧
  (∀ (E : Index l Ω) (K : Stage l Ω X E),
    HEq ((A.leftComparison E).hom.app K)
      (𝟙 ((inclusion E).obj
        ((finiteLeft D l hl Ω X f c A.system E).obj K)))) ∧
  (∀ (E : Index l Ω) (M : Stage l Ω Y E),
    HEq ((A.rightComparison E).hom.app M)
      (𝟙 ((inclusion E).obj
        ((finiteRight D l hl Ω X f c A.system E).obj M)))) ∧
  (∀ (E : Index l Ω) (K : Stage l Ω X E),
    (inclusion E).map
        ((finiteAdjunction D l hl Ω X f c A.system E).unit.app K) ≫
      (A.rightComparison E).hom.app
        ((finiteLeft D l hl Ω X f c A.system E).obj K) ≫
      A.right.map ((A.leftComparison E).hom.app K) = A.adjunction.unit.app ((inclusion E).obj K)) ∧
  (∀ (E : Index l Ω) (M : Stage l Ω Y E),
    (A.leftComparison E).hom.app
        ((finiteRight D l hl Ω X f c A.system E).obj M) ≫
      A.left.map ((A.rightComparison E).hom.app M) ≫
      A.adjunction.counit.app ((inclusion E).obj M) =
    (inclusion E).map
      ((finiteAdjunction D l hl Ω X f c A.system E).counit.app M)) ∧
  (∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E),
    (inclusion L).map
        ((finiteLeftScalar D l hl Ω X f c A.system E L h).hom.app K) ≫
      (A.leftComparison L).hom.app ((transition l Ω X E L h).obj K) =
    (inclusionTransition l Ω Y E L h).hom.app
        ((finiteLeft D l hl Ω X f c A.system E).obj K) ≫
      (A.leftComparison E).hom.app K ≫
      A.left.map ((inclusionTransition l Ω X E L h).inv.app K)) ∧
  (∀ (E L : Index l Ω) (h : E ≤ L) (M : Stage l Ω Y E),
    (inclusion L).map
        ((finiteRightScalar D l hl Ω X f c A.system E L h).hom.app M) ≫
      (A.rightComparison L).hom.app ((transition l Ω Y E L h).obj M) =
    (inclusionTransition l Ω X E L h).hom.app
        ((finiteRight D l hl Ω X f c A.system E).obj M) ≫
      (A.rightComparison E).hom.app M ≫
      A.right.map ((inclusionTransition l Ω Y E L h).inv.app M))

/-- The finite-origin exceptional functors with their descended adjunction and maps.
Source: blueprint thm-coef-qbar-verdier, exceptional adjunction clause
(blueprint: thm-coef-qbar-verdier). -/
structure Exceptional (c : Compactification f) extends ExceptionalData D l hl Ω X f c where
  properties : ExceptionalProperties D l hl Ω X f c toExceptionalData

/-- The exceptional formula for the same X and Y dualities, normalized at every
finite coefficient field to the rational exceptional comparison. This also records
its compatibility with the actual finite adjunction, not only an abstract formula.
Source: blueprint thm-coef-qbar-verdier, proof step 9
(blueprint: thm-coef-qbar-verdier). -/
structure ExceptionalFormula (BX : Duality D l hl Ω X) (BY : Duality D l hl Ω Y)
    (c : Compactification f) (A : Exceptional D l hl Ω X f c) where
  comparison : A.right ≅ BY.duality.dual.rightOp ⋙
    (CoefQbarPullback D l hl Ω f).op ⋙ BX.duality.dual
  finite (E : Index l Ω) :
    RationalOperations.ExceptionalIdentification l X D hl (AuxiliaryClosure.{u} l) c
      A.system (fieldStage l Ω E) (BX.finite.omega E) (BY.finite.omega E)
      (BX.finite.datum E) (BY.finite.datum E)
  normalized (E : Index l Ω) (M : Stage l Ω Y E) :
    (inclusion E).map ((finite E).comparison.hom.app M) ≫
      (BX.comparison E).hom.app
        (op ((@rationalDerivedPullback l _ (Coefficient.{u} l Ω E) _ _ _ X Y f
          (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).obj
            ((BY.finite.datum E).dual.obj (op M)))) ≫
      BX.duality.dual.map
        ((CoefQbarPullback D l hl Ω f).map ((BY.comparison E).inv.app (op M)) ≫
          (pullbackInclusion D l hl Ω X f E
            ((BY.finite.datum E).dual.obj (op M))).inv).op =
    (A.rightComparison E).hom.app M ≫ comparison.hom.app ((inclusion E).obj M)

end Exceptional

/-- The constant Ω object at the base finite coefficient stage, constructed from
its completed regular module and the published rational localization.
Source: blueprint thm-coef-qbar-verdier, omega = Ra! Ω
(blueprint: thm-coef-qbar-verdier). -/
def coefficientUnit : generalAlgebraicallyClosedConstructibleCategory l Ω X :=
  (inclusion (Padic.finiteCoefficientBase l Ω)).obj
    (RationalOperations.coefficientUnit l
      (Coefficient.{u} l Ω (Padic.finiteCoefficientBase l Ω)) X D hl)

/-- Identification of the same dualizing object with exceptional pullback of the
actual coefficient unit at the structure morphism. This is an isomorphism to a
specified object, not an arbitrary choice of a dualizing object.
Source: blueprint thm-coef-qbar-verdier, proof steps 5 and 9
(blueprint: thm-coef-qbar-verdier). -/
def Dualizing (B : Duality D l hl Ω X) : Prop :=
  ∃ A : Exceptional D l hl Ω X (X ↘ Spec (.of D.k))
      (integralDualizingCompactification D X),
    Nonempty (B.omega ≅ A.right.obj (coefficientUnit D l hl Ω (Spec (.of D.k)))) ∧
      ∀ E : Index l Ω,
        RationalOperations.DualizingIdentification l X D hl (AuxiliaryClosure.{u} l)
          A.system (fieldStage l Ω E) (B.finite.omega E)

end CoefQbarVerdier

/-- The complete common-stage Verdier conclusion: the duality, its actual internal
Hom and dualizing object, and the descended exceptional adjunction for every
separated finite-type k-morphism. All data are conclusions, with no ambient adjoint
assumption and no relation imposed on the scheme and coefficient universes.
Source: blueprint thm-coef-qbar-verdier, all statement clauses
(blueprint: thm-coef-qbar-verdier). -/
def CoefQbarVerdierConclusion
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))] : Prop :=
  ∃ BX : CoefQbarVerdier.Duality D l hl Ω X,
    Nonempty (CoefQbarVerdier.InternalHom D l hl Ω X BX) ∧
    CoefQbarVerdier.Dualizing D l hl Ω X BX ∧
    ∀ {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
      [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f),
      ∃ (BY : CoefQbarVerdier.Duality D l hl Ω Y)
        (A : CoefQbarVerdier.Exceptional D l hl Ω X f c),
        Nonempty (CoefQbarVerdier.InternalHom D l hl Ω Y BY) ∧
        CoefQbarVerdier.Dualizing D l hl Ω Y BY ∧
        Nonempty (CoefQbarVerdier.ExceptionalFormula D l hl Ω X f BX BY c A)

/-- Verdier biduality at algebraically closed coefficients.
Source: blueprint sec-six-functors/sk-prop-sf-biduality-general,
thm-coef-qbar-verdier, statement and proof (blueprint: thm-coef-qbar-verdier).

Proof plan, following the node's ten steps:
1. Use thm-coef-rational-verdier on every finite coefficient field. Send (E,K) to
   (E,D_E K), and a common-stage u to beta_F followed by D_M(u) then beta_E inverse.
2. Expand the scalar associators and beta cocycle. Contravariant naturality cancels
   the middle comparisons, proving invariance under enlargement and eventual equality.
   At one common field the inverse comparisons cancel in compositions and identities.
3. Represent a scalar and an arrow at one finite field. Finite-stage linearity proves
   Ω-linearity without conjugation. Represent a distinguished triangle at a finite
   field and descend the evaluation-normalized shift comparison to prove exactness.
4. Descend finite evaluations and delta. Their scalar squares give naturality on
   representatives; the finite inverse delta descends as well. It supplies the
   quasi-inverse and the evaluation-defined bidual isomorphism.
5. Represent omega at the base finite field. Its scalar comparisons identify it with
   every finite omega. lem-coef-rational-operations identifies duality with internal
   Hom; descend its tensor–Hom adjunction on filtered Hom groups and its evaluation.
6. Normalize self-transitions using the canonical tensor unit and associators.
   lem-sbc-coherent-pair-functor-descent descends the two finite exceptional functors
   and their natural transformations. The left functor is the specified compact support.
7. Index the Hom groups A_M = Hom(Rf_!T K, T L) and B_M = Hom(T K, Rf^!T L) by the
   finite fields M, with transitions from the scalar comparisons of step 6. The finite
   adjunction bijections e_M are additive and compatible with these transitions, since
   coefficient extension preserves units and counits. lem-coef-qbar-adjunction-hom-descent
   gives inverse bijections of the common-stage Hom groups, natural in both variables.
8. Apply lem-weil-pbc-adjunction-of-natural-bijection to these natural bijections to
   obtain the descended unit, counit and both triangle identities, with their original
   finite components. Hence the descended functors form the constructible adjunction.
9. Descend the scalar-compatible finite exceptional formula and its inverse from
   lem-coef-rational-operations. It is D_X f* D_Y with the displayed opposite functors.
   Apply it at a_X to the actual unit to identify omega with Ra_X^! Ω.
10. Put a retract and its split equation at one finite stage. Naturality restricts
   evaluation and delta; their inverses restrict too. The same restriction equations
   apply in each variable of every descended comparison, unit and counit, as in
   lem-coef-rational-retract-evaluation. Thus all the maps respect scalar extension
   and retracts, without tensoring with an infinite topological coefficient field.
-/
theorem coef_qbar_verdier
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] :
    CoefQbarVerdierConclusion D l hl Ω X := by
  sorry

end WeilConjectures
