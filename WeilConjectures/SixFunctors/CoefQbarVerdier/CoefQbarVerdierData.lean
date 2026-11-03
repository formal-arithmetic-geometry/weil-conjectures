/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SixFunctors.Rational.RationalVerdier
public import WeilConjectures.SixFunctors.RationalOperations.RationalOperationsData
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.SixFunctors.Sf.SfBidualityClass
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientComparisons
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

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
set_option Elab.async false
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
def Duality := { B : DualityData D l hl Ω X // DualityProperties D l hl Ω X B }

namespace Duality
variable {D l hl Ω X}
abbrev properties (B : Duality D l hl Ω X) := B.property
abbrev finite (B : Duality D l hl Ω X) := B.val.finite
abbrev duality (B : Duality D l hl Ω X) := B.val.duality
abbrev linearCategory (B : Duality D l hl Ω X) := B.val.linearCategory
abbrev comparison (B : Duality D l hl Ω X) := B.val.comparison
abbrev omega (B : Duality D l hl Ω X) := B.val.omega
abbrev omegaComparison (B : Duality D l hl Ω X) := B.val.omegaComparison
abbrev evaluation (B : Duality D l hl Ω X) := B.val.evaluation
end Duality

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
def Exceptional (c : Compactification f) :=
  { A : ExceptionalData D l hl Ω X f c // ExceptionalProperties D l hl Ω X f c A }

namespace Exceptional
variable {D l hl Ω X f}
abbrev properties {c : Compactification f} (A : Exceptional D l hl Ω X f c) := A.property
abbrev system {c : Compactification f} (A : Exceptional D l hl Ω X f c) := A.val.system
abbrev left {c : Compactification f} (A : Exceptional D l hl Ω X f c) := A.val.left
abbrev right {c : Compactification f} (A : Exceptional D l hl Ω X f c) := A.val.right
abbrev adjunction {c : Compactification f} (A : Exceptional D l hl Ω X f c) := A.val.adjunction
abbrev leftComparison {c : Compactification f} (A : Exceptional D l hl Ω X f c) :=
  A.val.leftComparison
abbrev rightComparison {c : Compactification f} (A : Exceptional D l hl Ω X f c) :=
  A.val.rightComparison
end Exceptional

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

end WeilConjectures

namespace WeilConjectures.CondensedCoefQbarVerdier

/-- Compatibility with the evaluation-defined double-dual arrow under a natural
comparison of contravariant functors. The two comparison factors are forced by
contravariance; this fixes the transported arrow, not merely its source and target.
Source: blueprint thm-sf-biduality-class, coefficient descent
(blueprint: def-sf-common-stage-verdier-data). -/
def EvaluationCompatible
    {C : Type a} [Category.{b} C] {B : Type c} [Category.{e} B]
    (F : C ⥤ B) (D : Cᵒᵖ ⥤ C) (H : Bᵒᵖ ⥤ B)
    (δ : 𝟭 C ⟶ D.rightOp ⋙ D) (ε : 𝟭 B ⟶ H.rightOp ⋙ H)
    (r : D ⋙ F ≅ F.op ⋙ H) : Prop :=
  ∀ K : C,
    F.map (δ.app K) ≫ r.hom.app (op (D.obj (op K))) ≫
      H.map (r.inv.app (op K)).op = ε.app (F.obj K)

/-- Exact anti-equivalence with its specified natural double-dual isomorphism.
Source: prop-functor-package (7) (blueprint: def-sf-common-stage-verdier-data). -/
structure ExactDuality (C : Type a) [Category.{b} C]
    [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] where
  dual : Cᵒᵖ ⥤ C
  exact : ∃ s : dual.CommShift ℤ, ∀ T : Triangle Cᵒᵖ,
    T ∈ distTriang Cᵒᵖ →
      Triangle.mk (dual.map T.mor₁) (dual.map T.mor₂)
        (dual.map T.mor₃ ≫ (s.commShiftIso (1 : ℤ)).hom.app T.obj₁) ∈ distTriang C
  equivalence : dual.IsEquivalence
  bidual : 𝟭 C ≅ dual.rightOp ⋙ dual

/-- The ordinary derived category of modules over the pulled-back condensed ring.
Source: prop-functor-package (7) (blueprint: def-sf-common-stage-verdier-data). -/
abbrev Ambient (X : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

/-- The precise bounded constructible finite-Tor property.
Source: prop-functor-package, proved domains
(blueprint: def-sf-common-stage-verdier-data). -/
abbrev domain (X : Scheme.{u}) : ObjectProperty (Ambient Λ X) :=
  constantModelBoundedConstructible Λ X ⊓ fun K ↦ DerivedCategory.finiteTorAmplitude _ K

/-- Geometric parameters and a supplied constructible exceptional adjunction.
The left adjoint is the actual compactification composite restricted to Dᵇ_ctf;
the adjunction determines the right adjoint up to its unique compatible isomorphism.
The triangulated fields are proofs about the inherited ambient structures.
Source: prop-functor-package (7), with sk-thm-existence
(blueprint: def-sf-common-stage-verdier-data). -/
structure Setting where
  field : FiniteFieldDatum.{u}
  ell : ℕ
  [prime : Fact ell.Prime]
  different : ell ≠ field.p
  admissible : IsLocalizingAdmissibleCoefficient ell Λ
  X : Over (Spec (.of field.k))
  [finiteType : LocallyOfFiniteType X.hom]
  [quasiCompact : QuasiCompact X.hom]
  [separated : IsSeparated X.hom]
  compactification : Compactification X.hom
  [sourceTriangulated : (domain Λ X.left).IsTriangulated]
  [pointTriangulated : (domain Λ (Spec (.of field.k))).IsTriangulated]
  unit_mem : domain Λ (Spec (.of field.k)) (𝟙_ (Ambient Λ (Spec (.of field.k))))
  support_mem : ∀ K : (domain Λ X.left).FullSubcategory,
    domain Λ (Spec (.of field.k))
      ((rightDerivedLowerShriekOfCompactification Λ compactification).obj K.obj)
  exceptional : (domain Λ (Spec (.of field.k))).FullSubcategory ⥤
    (domain Λ X.left).FullSubcategory
  adjunction : (domain Λ (Spec (.of field.k))).lift
    ((domain Λ X.left).ι ⋙ rightDerivedLowerShriekOfCompactification Λ compactification)
      support_mem ⊣ exceptional

/-- The actual coefficient unit in the constructible category.
Source: prop-functor-package (7) (blueprint: def-sf-common-stage-verdier-data). -/
def Setting.unit (s : Setting Λ) : (domain Λ (Spec (.of s.field.k))).FullSubcategory :=
  ⟨𝟙_ (Ambient Λ (Spec (.of s.field.k))), s.unit_mem⟩

/-- The prescribed dualizing object Ra_X^! Λ; no existence witness is selected.
Source: prop-functor-package (7) (blueprint: def-sf-common-stage-verdier-data). -/
def Setting.omega (s : Setting Λ) : (domain Λ s.X.left).FullSubcategory :=
  s.exceptional.obj s.unit

/-- The native internal Hom into the prescribed dualizing object.
Source: prop-functor-package (7) (blueprint: def-sf-common-stage-verdier-data). -/
def Setting.homDual (s : Setting Λ) : (Ambient Λ s.X.left)ᵒᵖ ⥤ Ambient Λ s.X.left :=
  (derivedHom Λ s.X.left).flip.obj s.omega.obj

/-- The evaluation-defined native double-dual arrow, using the derived Koszul braiding.
Source: prop-functor-package (7) (blueprint: def-sf-common-stage-verdier-data).
The named map shares the closed-structure construction across the record projections. -/
def Setting.biduality (s : Setting Λ) :
    𝟭 (Ambient Λ s.X.left) ⟶ s.homDual.rightOp ⋙ s.homDual := by
  letI := DerivedCategory.braidedCategory'
    (Mod (Sheaf (ProEt.topology s.X.left) Ab.{u + 1}) (condensedRingObj Λ s.X.left))
  exact MonoidalClosed.toIhomIhomNatTrans s.omega.obj

/-- Pullback from the condensed point is additive because it is a left adjoint.
Source: native coefficient construction, upperStarFromPoint
(blueprint: def-sf-common-stage-verdier-data).
Proof: the composed inverse-image adjunction preserves finite coproducts and zero;
in a preadditive category these are biproducts and imply additivity. -/
theorem additivePull (X : Scheme.{u}) : (upperStarFromPoint X).Additive := by
  let adj : upperStarFromPoint X ⊣ _ := by
    unfold upperStarFromPoint
    exact pointUpperStarLowerStarAdjunction.comp
      (AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : (upperStarFromPoint X).IsLeftAdjoint := adj.isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  exact Functor.additive_of_preservesBinaryBiproducts (upperStarFromPoint X)

/-- Coordinates for an arbitrary algebraic closure, including one in an independent
universe, in the native algebraic closure used by the condensed ring construction.
Mathlib proves existence of this algebra isomorphism. Its induced coefficient action
retains the specified closure, rather than treating it as an unrelated scalar field.
Source: sk-def-sfb-qlbar-condensed, choice of algebraic closure
(blueprint: def-sf-common-stage-verdier-data). -/
def closureEquiv : Ω ≃ₐ[Padic l] PadicAlgCl l :=
  IsAlgClosure.equiv (Padic l) Ω (PadicAlgCl l)

/-- Canonical scalar multiplication on native algebraically closed coefficients.
The action comes from constant global sections, transported to the scheme and then
through ordinary localization. No linear structure is selected from an existence theorem.
Source: current blueprint prop-functor-package (7)
(blueprint: def-sf-common-stage-verdier-data). -/
@[instance_reducible] def linearCategory : Linear (PadicAlgCl l) (PadicAlgClConstructible X l) := by
  letI : (upperStarFromPoint X).Additive := additivePull X
  letI := Mod.linearOfRingHom
    ((CategoryTheory.MonObj.Γ.mapFunctor (upperStarFromPoint X)).comp
      (Profinite.PadicAlgCl.constRingHom l))
  infer_instance

/-- Canonical linear structure for the independently specified closure. Its action
is constant multiplication after the fixed closure coordinate isomorphism.
Source: sk-def-sfb-qlbar-condensed (blueprint: def-sf-common-stage-verdier-data). -/
@[instance_reducible] def closureLinear : Linear Ω (PadicAlgClConstructible X l) := by
  letI : (upperStarFromPoint X).Additive := additivePull X
  letI := Mod.linearOfRingHom
    (((CategoryTheory.MonObj.Γ.mapFunctor (upperStarFromPoint X)).comp
      (Profinite.PadicAlgCl.constRingHom l)).comp (closureEquiv l Ω).toRingHom)
  infer_instance

/-- The same canonical action at a finite coefficient field.
Source: current blueprint prop-functor-package (7)
(blueprint: def-sf-common-stage-verdier-data). -/
@[instance_reducible] def finiteLinear (E : PadicAlgCl.FiniteIntermediateField l) :
    Linear E (PadicSubfieldConstructible X l E) := by
  letI : (upperStarFromPoint X).Additive := additivePull X
  letI := Mod.linearOfRingHom
    ((CategoryTheory.MonObj.Γ.mapFunctor (upperStarFromPoint X)).comp
      (Profinite.continuousMapConstRingHom E))
  infer_instance

/-- The native triangulated-category hypothesis follows from the standing
finite-type setting; it is not an additional restriction on that setting.
Source: Mathlib AlgebraicGeometry.Noetherian, finite type over a field
(blueprint: def-sf-common-stage-verdier-data).
Proof: the field spectrum is Noetherian. A locally finite-type morphism over it
has locally Noetherian source; quasi-compactness gives a compact source. These two
properties define a Noetherian scheme, whose underlying space is Noetherian. -/
theorem finiteTypeNoetherian (D : FiniteFieldDatum.{u}) (Z : Scheme.{u})
    [Z.Over (Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))] : TopologicalSpace.NoetherianSpace Z := by
  let : IsLocallyNoetherian Z :=
    LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of D.k))
  let : CompactSpace Z :=
    QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of D.k))
  let : IsNoetherian Z := {}
  infer_instance

/-- Native finite-coefficient Verdier data. The comparison and evaluation are in the
ordinary derived module category; its bidual arrow is the evaluation transpose.
Source: current blueprint prop-functor-package (7), finite rational coefficients
(blueprint: def-sf-common-stage-verdier-data). -/
structure FiniteDatum (E : PadicAlgCl.FiniteIntermediateField l) where
  duality : ExactDuality (PadicSubfieldConstructible X l E)
  omega : PadicSubfieldConstructible X l E
  additive : duality.dual.Additive
  comparison : duality.dual ⋙ (boundedConstructible (padicSubfieldRingObj X l E)).ι ≅
    (boundedConstructible (padicSubfieldRingObj X l E)).ι.op ⋙
      (derivedHom (Profinite.continuousMapRingObj E) X).flip.obj omega.obj
  linear : ∀ {K M : PadicSubfieldConstructible X l E} (f : K ⟶ M) (c : E),
    duality.dual.map (c • f).op = c • duality.dual.map f.op
  bidual_normalized :
    letI := DerivedCategory.braidedCategory'
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X l E))
    EvaluationCompatible (boundedConstructible (padicSubfieldRingObj X l E)).ι
      duality.dual ((derivedHom (Profinite.continuousMapRingObj E) X).flip.obj omega.obj)
      duality.bidual.hom (MonoidalClosed.toIhomIhomNatTrans omega.obj) comparison

/-- Finite evaluation is constructed from the actual tensor-Hom counit.
Source: current blueprint prop-functor-package (7), evaluation
(blueprint: def-sf-common-stage-verdier-data). -/
def FiniteDatum.evaluation (E : PadicAlgCl.FiniteIntermediateField l)
    (F : FiniteDatum l X E) (K : PadicSubfieldConstructible X l E) :
    K.obj ⊗ (F.duality.dual.obj (op K)).obj ⟶ F.omega.obj :=
  (𝟙 K.obj ⊗ₘ F.comparison.hom.app (op K)) ≫
    (derivedTensorHomAdjunction (Profinite.continuousMapRingObj E) K.obj).counit.app
      F.omega.obj

/-- The native scalar tensor comparison is the inverse tensorator of the total
left-derived scalar-extension functor. It includes its identity and tower coherences.
Source: current blueprint sk-prop-scalar-six, tensor comparison
(blueprint: def-sf-common-stage-verdier-data). -/
def tensorInclusion (E : PadicAlgCl.FiniteIntermediateField l)
    (K M : Ambient X (Profinite.continuousMapRingObj E)) :
    (derivedExtendScalarsToPadicAlgCl X l E).obj (K ⊗ M) ≅
      (derivedExtendScalarsToPadicAlgCl X l E).obj K ⊗
        (derivedExtendScalarsToPadicAlgCl X l E).obj M := by
  letI := Mod.extendScalarsMonoidal (padicSubfieldRingObjToPadicAlgCl X l E)
  letI := (Mod.extendScalars
    (padicSubfieldRingObjToPadicAlgCl X l E)).leftDerivedFunctorMonoidal
  exact (Functor.Monoidal.μIso (derivedExtendScalarsToPadicAlgCl X l E) K M).symm

/-- The native scalar unit, restricted along the fully faithful inclusion.
Source: sk-prop-scalar-six, unit (blueprint: def-sf-common-stage-verdier-data). -/
def finiteUnit (E : PadicAlgCl.FiniteIntermediateField l) :
    constructibleExtendScalars X l (le_refl E) ≅ 𝟭 (PadicSubfieldConstructible X l E) :=
  Functor.fullyFaithfulCancelRight (boundedConstructible (padicSubfieldRingObj X l E)).ι
    (Functor.isoWhiskerLeft (boundedConstructible (padicSubfieldRingObj X l E)).ι
      (condensedCoefficientUnitIso X l E))

/-- The native multiplication constraint, restricted to constructible objects.
Source: sk-prop-scalar-six, tower (blueprint: def-sf-common-stage-verdier-data). -/
def finiteComp {E F G : PadicAlgCl.FiniteIntermediateField l} (h : E ≤ F) (k : F ≤ G) :
    constructibleExtendScalars X l h ⋙ constructibleExtendScalars X l k ≅
      constructibleExtendScalars X l (h.trans k) :=
  Functor.fullyFaithfulCancelRight (boundedConstructible (padicSubfieldRingObj X l G)).ι
    (Functor.isoWhiskerLeft (boundedConstructible (padicSubfieldRingObj X l E)).ι
      (condensedCoefficientCompIso X l h k))

/-- The finite scalar tensor constraint is the actual derived tensorator.
Source: sk-prop-scalar-six, tensor (blueprint: def-sf-common-stage-verdier-data). -/
def finiteTensor {E F : PadicAlgCl.FiniteIntermediateField l} (h : E ≤ F)
    (K M : Ambient X (Profinite.continuousMapRingObj E)) :
    (derivedExtendScalarsSubfield X l h).obj (K ⊗ M) ≅
      (derivedExtendScalarsSubfield X l h).obj K ⊗
        (derivedExtendScalarsSubfield X l h).obj M := by
  letI := Mod.extendScalarsMonoidal (padicSubfieldRingObjMap X l h)
  letI := (Mod.extendScalars (padicSubfieldRingObjMap X l h)).leftDerivedFunctorMonoidal
  exact (Functor.Monoidal.μIso (derivedExtendScalarsSubfield X l h) K M).symm

/-- The ordinary native integral coefficient category at a finite field.
Source: current blueprint prop-functor-package (7), integral origin
(blueprint: def-sf-common-stage-verdier-data). -/
abbrev IntegralCategory (E : PadicAlgCl.FiniteIntermediateField l) :=
  (boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj l E) X)).FullSubcategory

/-- The same finite dual functor on the raw rationalization, using the canonical
native integral-to-field equivalence. This is a real transport of the supplied
functor; no second duality is chosen.
Source: prop-functor-package (7), finite rationalization
(blueprint: def-sf-common-stage-verdier-data). -/
def FiniteDatum.rawDual (E : PadicAlgCl.FiniteIntermediateField l) (F : FiniteDatum l X E) :
    (Rationalization (Submonoid.powers (l : ℤ)) (IntegralCategory l X E))ᵒᵖ ⥤
      Rationalization (Submonoid.powers (l : ℤ)) (IntegralCategory l X E) :=
  (rationalizationEquivalence X l E).functor.op ⋙ F.duality.dual ⋙
    (rationalizationEquivalence X l E).inverse

/-- Realization of the transported raw rational dual is the specified native dual.
Source: canonical rationalization equivalence
(blueprint: def-sf-common-stage-verdier-data).
Proof: reassociate the composite and cancel inverse followed by functor using the
counit of the actual rationalization equivalence. -/
def FiniteDatum.rawDualComparison (E : PadicAlgCl.FiniteIntermediateField l)
    (F : FiniteDatum l X E) :
    FiniteDatum.rawDual l X E F ⋙ (rationalizationEquivalence X l E).functor ≅
      (rationalizationEquivalence X l E).functor.op ⋙ F.duality.dual :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (rationalizationEquivalence X l E).counitIso ≪≫
      Functor.rightUnitor _)

/-- Derived completeness for the native integral coefficient ring: right orthogonality
to complexes on which the uniformizer is inverted. Since the fraction field is
`O_E[1/l]`, this is the usual derived-adic completeness condition, including all shifts.
Source: blueprint def-weil-derived-complete, Stacks 091S
(blueprint: def-sf-common-stage-verdier-data). -/
def IntegralComplete (E : PadicAlgCl.FiniteIntermediateField l) :
    ObjectProperty (Ambient X (Profinite.padicIntegersRingObj l E)) :=
  fun K ↦ ∀ (M : Ambient X (Profinite.continuousMapRingObj E))
    (f : (Mod.comap (padicIntegersToPadicSubfield X l E)).mapDerivedCategory.obj M ⟶ K),
    f = 0

/-- Completion is specified by its universal property, with the actual inclusion of
derived-complete objects as right adjoint. This fixes the comparison as the adjunction
unit, rather than choosing an arbitrary isomorphism with a completed tensor.
Source: blueprint def-weil-derived-complete and prop-functor-package (7)
(blueprint: def-sf-common-stage-verdier-data). -/
structure IntegralCompletion (E : PadicAlgCl.FiniteIntermediateField l) where
  reflector : Ambient X (Profinite.padicIntegersRingObj l E) ⥤
    (IntegralComplete l X E).FullSubcategory
  adjunction : reflector ⊣ (IntegralComplete l X E).ι

/-- The ordinary-to-completed tensor comparison is the actual completion unit.
Source: blueprint def-sf-rational-verdier-data, normalized completion comparison
(blueprint: def-sf-common-stage-verdier-data). -/
def IntegralCompletion.tensorComparison (E : PadicAlgCl.FiniteIntermediateField l)
    (C : IntegralCompletion l X E)
    (K M : Ambient X (Profinite.padicIntegersRingObj l E)) :
    K ⊗ M ⟶ (C.reflector.obj (K ⊗ M)).obj := C.adjunction.unit.app (K ⊗ M)

/-- The normalized comparison is invertible on a complete ordinary tensor.
Source: reflective derived completion, Mathlib Adjunction.FullyFaithful
(blueprint: def-sf-common-stage-verdier-data).
Proof: a complete tensor lies in the essential image of the fully faithful inclusion;
the unit of its reflection is therefore invertible. -/
theorem IntegralCompletion.tensorComparison_isIso (E : PadicAlgCl.FiniteIntermediateField l)
    (C : IntegralCompletion l X E)
    (K M : Ambient X (Profinite.padicIntegersRingObj l E))
    (h : IntegralComplete l X E (K ⊗ M)) :
    IsIso (IntegralCompletion.tensorComparison l X E C K M) :=
  C.adjunction.isIso_unit_app_of_iso (X := ⟨K ⊗ M, h⟩) (Iso.refl _)

/-- Restriction of the actual integral internal Hom to constructible objects.
Its preservation proof is supplied separately; the functor itself is fixed.
Source: prop-functor-package (7), integral duality
(blueprint: def-sf-common-stage-verdier-data). -/
def integralDual (E : PadicAlgCl.FiniteIntermediateField l) (w : IntegralCategory l X E)
    (h : ∀ K : IntegralCategory l X E,
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj l E) X)
        (((derivedHom (Profinite.padicIntegersRingObj l E) X).flip.obj w.obj).obj (op K.obj))) :
    (IntegralCategory l X E)ᵒᵖ ⥤ IntegralCategory l X E :=
  (boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj l E) X)).lift
    ((boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj l E) X)).ι.op ⋙
      (derivedHom (Profinite.padicIntegersRingObj l E) X).flip.obj w.obj)
    (fun K ↦ h K.unop)

/-- The actual evaluation-transpose arrow of integral duality, restricted through the
fully faithful constructible inclusion. The symmetry is the derived Koszul symmetry.
Source: prop-functor-package (7), integral biduality
(blueprint: def-sf-common-stage-verdier-data). -/
def integralBidual (E : PadicAlgCl.FiniteIntermediateField l) (w : IntegralCategory l X E)
    (h : ∀ K : IntegralCategory l X E,
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj l E) X)
        (((derivedHom (Profinite.padicIntegersRingObj l E) X).flip.obj w.obj).obj (op K.obj))) :
    𝟭 (IntegralCategory l X E) ⟶ (integralDual l X E w h).rightOp ⋙ integralDual l X E w h := by
  letI := DerivedCategory.braidedCategory'
    (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj l E) X))
  exact
    { app := fun K ↦ ObjectProperty.homMk
        ((MonoidalClosed.toIhomIhomNatTrans w.obj).app K.obj)
      naturality := fun K M f ↦ ObjectProperty.hom_ext _
        ((MonoidalClosed.toIhomIhomNatTrans w.obj).naturality f.hom) }

/-- Integral tensor-Hom evaluation in the actual ordinary condensed category.
On integral constructible objects this is the completed evaluation as well, under
the canonical ordinary-to-completed comparison; no unrelated evaluation is supplied.
Source: prop-functor-package (7), integral evaluation
(blueprint: def-sf-common-stage-verdier-data). -/
def integralEvaluation (E : PadicAlgCl.FiniteIntermediateField l)
    (w : IntegralCategory l X E) (K : IntegralCategory l X E) :
    K.obj ⊗ (((derivedHom (Profinite.padicIntegersRingObj l E) X).flip.obj w.obj).obj
      (op K.obj)) ⟶ w.obj :=
  (derivedTensorHomAdjunction (Profinite.padicIntegersRingObj l E) K.obj).counit.app w.obj

/-- Completed integral evaluation uses the inverse of the specified completion unit
followed by the ordinary tensor-Hom counit. This retains the normalization required
of the integral presentation of rational duality.
Source: def-sf-rational-verdier-data, integral evaluation formula
(blueprint: def-sf-common-stage-verdier-data). -/
def IntegralOrigin.completedEvaluation (D : FiniteFieldDatum.{u})
    [X.Over (Spec (.of D.k))] (E : PadicAlgCl.FiniteIntermediateField l)
    (F : FiniteDatum l X E) (I : IntegralOrigin l X D E F) (K : IntegralCategory l X E) :
    (I.completion.reflector.obj
      (K.obj ⊗ ((integralDual l X E I.omega I.preserves).obj (op K)).obj)).obj ⟶ I.omega.obj := by
  letI := IntegralCompletion.tensorComparison_isIso l X E I.completion K.obj
    ((integralDual l X E I.omega I.preserves).obj (op K)).obj
    (I.tensor_complete K ((integralDual l X E I.omega I.preserves).obj (op K)))
  exact inv (IntegralCompletion.tensorComparison l X E I.completion K.obj
    ((integralDual l X E I.omega I.preserves).obj (op K)).obj) ≫
      integralEvaluation l X E I.omega K

/-- The completed evaluation is precisely the ordinary counit after the normalized
comparison; the completion introduces no independently chosen arrow.
Source: def-sf-rational-verdier-data
(blueprint: def-sf-common-stage-verdier-data).
Proof: the comparison is invertible on the complete constructible tensor; cancel
it against its inverse in the definition of completedEvaluation. -/
theorem IntegralOrigin.completedEvaluation_normalized (D : FiniteFieldDatum.{u})
    [X.Over (Spec (.of D.k))] (E : PadicAlgCl.FiniteIntermediateField l)
    (F : FiniteDatum l X E) (I : IntegralOrigin l X D E F) (K : IntegralCategory l X E) :
    IntegralCompletion.tensorComparison l X E I.completion K.obj
        ((integralDual l X E I.omega I.preserves).obj (op K)).obj ≫
      IntegralOrigin.completedEvaluation l X D E F I K = integralEvaluation l X E I.omega K := by
  let := IntegralCompletion.tensorComparison_isIso l X E I.completion K.obj
    ((integralDual l X E I.omega I.preserves).obj (op K)).obj
    (I.tensor_complete K ((integralDual l X E I.omega I.preserves).obj (op K)))
  simp only [IntegralOrigin.completedEvaluation, IsIso.hom_inv_id_assoc]

/-- Coherence and evaluation normalization for the supplied finite comparisons.
Identity and repeated fields are included in the quantified equations. No comparison
is chosen from an existence assertion.
Source: latest blueprint prop-functor-package (7) and sk-prop-scalar-six
(blueprint: def-sf-common-stage-verdier-data). -/
def FiniteCoherent (B : DualityData l Ω X D) : Prop :=
  (∀ (E : PadicAlgCl.FiniteIntermediateField l) (K : PadicSubfieldConstructible X l E),
    (B.beta E E le_rfl).hom.app (op K) =
      (finiteUnit l X E).hom.app ((B.finite E).duality.dual.obj (op K)) ≫
        (B.finite E).duality.dual.map ((finiteUnit l X E).hom.app K).op) ∧
  (∀ (E F G : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ F) (k : F ≤ G)
      (K : PadicSubfieldConstructible X l E),
    (constructibleExtendScalars X l k).map ((B.beta E F h).hom.app (op K)) ≫
      (B.beta F G k).hom.app (op ((constructibleExtendScalars X l h).obj K)) =
    (finiteComp l X h k).hom.app ((B.finite E).duality.dual.obj (op K)) ≫
      (B.beta E G (h.trans k)).hom.app (op K) ≫
        (B.finite G).duality.dual.map ((finiteComp l X h k).hom.app K).op) ∧
  (∀ E : PadicAlgCl.FiniteIntermediateField l,
    (B.omegaScalar E E le_rfl).hom = (finiteUnit l X E).hom.app (B.finite E).omega) ∧
  (∀ (E F G : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ F) (k : F ≤ G),
    (constructibleExtendScalars X l k).map (B.omegaScalar E F h).hom ≫
      (B.omegaScalar F G k).hom =
    (finiteComp l X h k).hom.app (B.finite E).omega ≫
      (B.omegaScalar E G (h.trans k)).hom) ∧
  (∀ (E F : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ F),
    EvaluationCompatible (constructibleExtendScalars X l h)
      (B.finite E).duality.dual (B.finite F).duality.dual
      (B.finite E).duality.bidual.hom (B.finite F).duality.bidual.hom (B.beta E F h)) ∧
  (∀ (E F : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ F)
      (K : PadicSubfieldConstructible X l E),
    (finiteTensor l X h K.obj ((B.finite E).duality.dual.obj (op K)).obj).hom ≫
      (𝟙 _ ⊗ₘ (boundedConstructible (padicSubfieldRingObj X l F)).ι.map
        ((B.beta E F h).hom.app (op K))) ≫
      FiniteDatum.evaluation l X F (B.finite F) ((constructibleExtendScalars X l h).obj K) =
    (derivedExtendScalarsSubfield X l h).map (FiniteDatum.evaluation l X E (B.finite E) K) ≫
      (boundedConstructible (padicSubfieldRingObj X l F)).ι.map (B.omegaScalar E F h).hom)

/-- The finite-origin normalization equations on native data. The scalar square is
required for every inclusion, including identities; its compatibility at a tower is
read with the native scalar compositors. Evaluation and both bidual maps retain their
split-retract formulas, with all arrows interpreted in the ambient derived category.
Source: current blueprint prop-functor-package (7)
(blueprint: def-sf-common-stage-verdier-data). -/
def DualityProperties (B : DualityData l Ω X D) : Prop :=
  (fun [_linearInst : Linear Ω (PadicAlgClConstructible X l)] ↦
  FiniteCoherent l Ω X D B ∧
  B.duality.dual.Additive ∧
  (∀ {K M : PadicAlgClConstructible X l} (f : K ⟶ M) (c : Ω),
    B.duality.dual.map (c • f).op = c • B.duality.dual.map f.op) ∧
  (∀ (E : PadicAlgCl.FiniteIntermediateField l)
      {K M : PadicSubfieldConstructible X l E} (f : K ⟶ M) (c : E),
    (constructibleToPadicAlgCl X l E).map (c • f) =
      (closureEquiv l Ω).symm (c : PadicAlgCl l) •
        (constructibleToPadicAlgCl X l E).map f) ∧
  (∀ (E : PadicAlgCl.FiniteIntermediateField l) (K : PadicSubfieldConstructible X l E),
    B.duality.dual.obj (op ((constructibleToPadicAlgCl X l E).obj K)) =
      (constructibleToPadicAlgCl X l E).obj ((B.finite E).duality.dual.obj (op K))) ∧
  (∀ (E : PadicAlgCl.FiniteIntermediateField l) (K : PadicSubfieldConstructible X l E),
    HEq ((B.comparison E).hom.app (op K))
      (𝟙 ((constructibleToPadicAlgCl X l E).obj ((B.finite E).duality.dual.obj (op K))))) ∧
  (∀ (E F : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ F)
      (K : PadicSubfieldConstructible X l E),
    (constructibleToPadicAlgCl X l F).map ((B.beta E F h).hom.app (op K)) ≫
      (B.comparison F).hom.app (op ((constructibleExtendScalars X l h).obj K)) ≫
      B.duality.dual.map ((constructibleToPadicAlgClCompIso X l h).inv.app K).op =
    (constructibleToPadicAlgClCompIso X l h).hom.app ((B.finite E).duality.dual.obj (op K)) ≫
      (B.comparison E).hom.app (op K)) ∧
  (∀ E : PadicAlgCl.FiniteIntermediateField l,
    EvaluationCompatible (constructibleToPadicAlgCl X l E)
      (B.finite E).duality.dual B.duality.dual
      (B.finite E).duality.bidual.hom B.duality.bidual.hom (B.comparison E)) ∧
  (∀ (E F : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ F),
    (constructibleToPadicAlgCl X l F).map (B.omegaScalar E F h).hom ≫
      (B.omegaComparison F).hom =
    (constructibleToPadicAlgClCompIso X l h).hom.app (B.finite E).omega ≫
      (B.omegaComparison E).hom) ∧
  (∀ (E : PadicAlgCl.FiniteIntermediateField l) (K : PadicSubfieldConstructible X l E),
    (tensorInclusion l X E K.obj ((B.finite E).duality.dual.obj (op K)).obj).hom ≫
      (𝟙 _ ⊗ₘ (boundedConstructible (padicAlgClRingObj X l)).ι.map
        ((B.comparison E).hom.app (op K))) ≫
      B.evaluation ((constructibleToPadicAlgCl X l E).obj K) =
    (derivedExtendScalarsToPadicAlgCl X l E).map (FiniteDatum.evaluation l X E (B.finite E) K) ≫
      (boundedConstructible (padicAlgClRingObj X l)).ι.map (B.omegaComparison E).hom) ∧
  (∀ (K M : PadicAlgClConstructible X l) (f : K ⟶ M),
    ((boundedConstructible (padicAlgClRingObj X l)).ι.map f ⊗ₘ 𝟙 _) ≫ B.evaluation M =
      (𝟙 _ ⊗ₘ (boundedConstructible (padicAlgClRingObj X l)).ι.map
        (B.duality.dual.map f.op)) ≫ B.evaluation K) ∧
  (∀ (P K : PadicAlgClConstructible X l) (i : P ⟶ K) (p : K ⟶ P) (_h : i ≫ p = 𝟙 P),
    ((boundedConstructible (padicAlgClRingObj X l)).ι.map i ⊗ₘ
      (boundedConstructible (padicAlgClRingObj X l)).ι.map (B.duality.dual.map p.op)) ≫
        B.evaluation K = B.evaluation P) ∧
  (∀ (P K : PadicAlgClConstructible X l) (i : P ⟶ K) (p : K ⟶ P) (_h : i ≫ p = 𝟙 P),
    i ≫ B.duality.bidual.hom.app K ≫ B.duality.dual.map (B.duality.dual.map p.op).op =
      B.duality.bidual.hom.app P) ∧
  (∀ (P K : PadicAlgClConstructible X l) (i : P ⟶ K) (p : K ⟶ P) (_h : i ≫ p = 𝟙 P),
    B.duality.dual.map (B.duality.dual.map i.op).op ≫ B.duality.bidual.inv.app K ≫ p =
      B.duality.bidual.inv.app P)) (_linearInst := B.linearCategory)

/-- The datum already includes its normalization equations.
Source: prop-functor-package (7) (blueprint: def-sf-common-stage-verdier-data). -/
abbrev Duality (s : Setting Λ) := DualityData s

/-- Evaluation is the actual tensor-Hom counit through the supplied comparison.
Source: prop-functor-package (7) (blueprint: def-sf-common-stage-verdier-data). -/
def DualityData.evaluation {s : Setting Λ} (B : DualityData s)
    (K : (domain Λ s.X.left).FullSubcategory) :
    K.obj ⊗ (B.duality.dual.obj (op K)).obj ⟶ s.omega.obj :=
  (𝟙 K.obj ⊗ₘ B.comparison.hom.app (op K)) ≫
    (derivedTensorHomAdjunction Λ K.obj).counit.app s.omega.obj

/-- The internal-Hom identification is the specified natural comparison itself.
Source: prop-functor-package (7) (blueprint: def-sf-common-stage-verdier-data). -/
abbrev InternalHom {s : Setting Λ} (B : DualityData s) := B.comparison

/-- The evaluation transpose is the composite of the fully faithful inclusion,
the specified Hom comparison and the native tensor-Hom adjunction.
Source: prop-functor-package (7) (blueprint: def-sf-common-stage-verdier-data).
Construction: each factor is the stated equivalence of Hom sets, so their composite
has exactly the prescribed evaluation as its uncurrying map. -/
def DualityData.evaluationEquiv {s : Setting Λ} (B : DualityData s)
    (K P : (domain Λ s.X.left).FullSubcategory) :
    (P ⟶ B.duality.dual.obj (op K)) ≃ (K.obj ⊗ P.obj ⟶ s.omega.obj) :=
  (ObjectProperty.fullyFaithfulι (domain Λ s.X.left)).homEquiv.trans
    ((Iso.homCongr (Iso.refl P.obj) (B.comparison.app (op K))).trans
      ((derivedTensorHomAdjunction Λ K.obj).homEquiv P.obj s.omega.obj).symm)

/-- The constructed Hom equivalence is the specified evaluation transpose.
Source: prop-functor-package (7) (blueprint: def-sf-common-stage-verdier-data).
Proof: uncurrying is tensoring the arrow with the identity followed by the counit;
expand the composite arrow and use functoriality of left tensoring. -/
theorem DualityData.evaluationEquiv_apply {s : Setting Λ} (B : DualityData s)
    (K P : (domain Λ s.X.left).FullSubcategory) (f : P ⟶ B.duality.dual.obj (op K)) :
    B.evaluationEquiv K P f = (𝟙 K.obj ⊗ₘ f.hom) ≫ B.evaluation K := by
  change ((derivedTensorHomAdjunction Λ K.obj).homEquiv P.obj s.omega.obj).symm
    (𝟙 P.obj ≫ f.hom ≫ B.comparison.hom.app (op K)) = _
  rw [Category.id_comp, Adjunction.homEquiv_counit]
  change (K.obj ◁ (f.hom ≫ B.comparison.hom.app (op K))) ≫ _ = _
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc,
    DualityData.evaluation, MonoidalCategory.id_tensorHom]

/-- Bijectivity is a property of the actual evaluation transpose, rather than
additional independently supplied data.
Source: prop-functor-package (7) (blueprint: def-sf-common-stage-verdier-data).
Proof: the preceding equality identifies the transpose with an equivalence. -/
theorem DualityData.evaluation_transpose_bijective {s : Setting Λ} (B : DualityData s)
    (K P : (domain Λ s.X.left).FullSubcategory) :
    Function.Bijective (fun f : P ⟶ B.duality.dual.obj (op K) ↦
      (𝟙 K.obj ⊗ₘ f.hom) ≫ B.evaluation K) := by
  have h : (fun f ↦ B.evaluationEquiv K P f) =
      (fun f ↦ (𝟙 K.obj ⊗ₘ f.hom) ≫ B.evaluation K) :=
    funext (B.evaluationEquiv_apply K P)
  rw [← h]
  exact (B.evaluationEquiv K P).bijective

/-- Forward biduality on a split retract is forced by naturality.
Source: prop-functor-package (7) (blueprint: def-sf-common-stage-verdier-data).
Proof: apply naturality to the retraction and cancel its composite with the section.
This is the original retract argument, applied to the native coefficient category. -/
theorem DualityData.bidual_retract {s : Setting Λ} (B : DualityData s)
    {P K : (domain Λ s.X.left).FullSubcategory} (i : P ⟶ K) (p : K ⟶ P)
    (h : i ≫ p = 𝟙 P) :
    i ≫ B.duality.bidual.hom.app K ≫
      (B.duality.dual.rightOp ⋙ B.duality.dual).map p = B.duality.bidual.hom.app P := by
  have hp := B.duality.bidual.hom.naturality p
  dsimp only [Functor.id_map] at hp
  rw [← hp, ← Category.assoc, h, Category.id_comp]

/-- Inverse biduality on a split retract is also forced by naturality.
Source: prop-functor-package (7) (blueprint: def-sf-common-stage-verdier-data).
Proof: apply inverse naturality to the section and use the retraction equation.
This reuses the inverse part of the original retract argument. -/
theorem DualityData.bidual_inverse_retract {s : Setting Λ} (B : DualityData s)
    {P K : (domain Λ s.X.left).FullSubcategory} (i : P ⟶ K) (p : K ⟶ P)
    (h : i ≫ p = 𝟙 P) :
    (B.duality.dual.rightOp ⋙ B.duality.dual).map i ≫
      B.duality.bidual.inv.app K ≫ p = B.duality.bidual.inv.app P := by
  have hi := B.duality.bidual.inv.naturality i
  dsimp only [Functor.id_map] at hi
  rw [← Category.assoc, hi, Category.assoc, h]
  exact Category.comp_id (B.duality.bidual.inv.app P)

/-- Restrict actual derived scalar extension, using a supplied preservation proof.
Source: sk-prop-scalar-six (blueprint: def-sf-common-stage-verdier-data). -/
def scalarRestriction (Z : Scheme.{u})
    (h : ∀ K : ConstantModelBoundedConstructible Λ Z,
      constantModelBoundedConstructible Λ' Z
        (((Mod.extendScalars (coefficientMap a Z)).leftDerivedFunctor).obj K.obj)) :
    ConstantModelBoundedConstructible Λ Z ⥤ ConstantModelBoundedConstructible Λ' Z :=
  (constantModelBoundedConstructible Λ' Z).lift
    ((constantModelBoundedConstructible Λ Z).ι ⋙
      (Mod.extendScalars (coefficientMap a Z)).leftDerivedFunctor) h

/-- The actual compactification scalar map: proper pushforward comparison followed
by the open-extension comparison. This definition does not assume it is invertible.
Source: sk-prop-scalar-six, compact support
(blueprint: def-sf-common-stage-verdier-data). -/
def supportScalar {Z Y : Scheme.{u}} {f : Z ⟶ Y} (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification Λ c ⋙
        (Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor ⟶
      (Mod.extendScalars (coefficientMap a Z)).leftDerivedFunctor ⋙
        rightDerivedLowerShriekOfCompactification Λ' c :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((openImmersionLowerShriek Λ c.i).mapDerivedCategory)
      (derivedPushHom a c.g) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (derivedOpenImmersionShriekIso a c.i).hom
      (lowerStar Λ' c.g).rightDerivedFunctor ≫
    (Functor.associator _ _ _).hom

end WeilConjectures.CondensedCoefQbarVerdier
