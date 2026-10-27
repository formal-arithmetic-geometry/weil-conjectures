/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import Sheaf.Paper.NativeAdicRealizationData
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import Sheaf.Algebra.Homology.RingedDerivedTensorNative
import Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction
import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale

/-! # Ambient Hom from the actual evaluation transpose

Source: Bhatt--Scholze, Lemma 3.4.11 and Remark 6.8.15; HRS Theorem 7.7,
Lemma 7.9 and Remark 7.10; the seven-step evaluation comparison in the DAG
(blueprint: lem-sf-adic-ambient-hom-evaluation-comparison).

The tensor input deliberately precedes the Hom-isomorphism assertion in `At`.
The coefficient ring, ordinary presentation, pair category and operations are
all the recorded ones. Finite comparisons below use the rational Hom comparison,
not an arbitrary isomorphism between representing objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme

namespace WeilConjectures.AdicQbarRealization
namespace AmbientHomEvaluation

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- The hypotheses on the symmetric strong tensorator, before asserting any Hom comparison.
This is the tensor portion of the realization hypothesis, with its native K-flat
normalization, coefficient unit and all monoidal equations. In particular its fields
contain no invertibility hypothesis on the map this lemma is to identify.
Source: BS 6.8.15; DAG hypothesis on mu
(blueprint: lem-sf-adic-ambient-hom-evaluation-comparison). -/
structure TensorInput (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] where
  closed : CoefficientClosedStructure (ambientHom l X R)
  models : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R) closed
  symmetry : @SymmetricCategory _ _ closed.monoidal
  coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
    (ProEt.topology X) (ring l X R) closed models symmetry
  tensor : ((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor ≅
    commonStageDerivedTensor l (PadicAlgCl l) X ⋙ ordinary l X R
  unit : closed.monoidal.tensorUnit ≅
    (ordinary l X R).obj (pullbackTensorCommonUnit l (PadicAlgCl l) X)
  associative : ∀ A B C : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    closed.tensor.map (Prod.mkHom (tensor.hom.app (A, B)) (𝟙 _)) ≫
        tensor.hom.app ((commonStageDerivedTensor l (PadicAlgCl l) X).obj (A, B), C) ≫
        (ordinary l X R).map (pullbackTensorCommonAssociator l (PadicAlgCl l) X A B C).hom =
      (closed.monoidal.associator ((ordinary l X R).obj A) ((ordinary l X R).obj B)
        ((ordinary l X R).obj C)).hom ≫
        closed.tensor.map (Prod.mkHom (𝟙 _) (tensor.hom.app (B, C))) ≫
        tensor.hom.app (A, (commonStageDerivedTensor l (PadicAlgCl l) X).obj (B, C))
  left_unit : ∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    closed.tensor.map (Prod.mkHom unit.hom (𝟙 _)) ≫
        tensor.hom.app (pullbackTensorCommonUnit l (PadicAlgCl l) X, A) ≫
        (ordinary l X R).map (pullbackTensorCommonLeftUnitor l (PadicAlgCl l) X A).hom =
      (closed.monoidal.leftUnitor ((ordinary l X R).obj A)).hom
  right_unit : ∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    closed.tensor.map (Prod.mkHom (𝟙 _) unit.hom) ≫
        tensor.hom.app (A, pullbackTensorCommonUnit l (PadicAlgCl l) X) ≫
        (ordinary l X R).map (pullbackTensorCommonRightUnitor l (PadicAlgCl l) X A).hom =
      (closed.monoidal.rightUnitor ((ordinary l X R).obj A)).hom
  symmetric : ∀ A B : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    tensor.hom.app (A, B) ≫
        (ordinary l X R).map (pullbackTensorCommonBraiding l (PadicAlgCl l) X A B).hom =
      (symmetry.braiding ((ordinary l X R).obj A) ((ordinary l X R).obj B)).hom ≫
        tensor.hom.app (B, A)

variable (R : LocallyFiniteAdicRealization.Realization l X)
  [∀ x : X, Invertible (l : X.residueField x)]
  (A : TensorInput l X R)
  (source : PodPartialClosed (commonStageDerivedTensor l (PadicAlgCl l) X)
    (commonStageHomPairs l (PadicAlgCl l) X)
    (commonStageDerivedInternalHom l (PadicAlgCl l) X))

/-- Realized right evaluation, including the specified tensorator.
Source: BS 3.4.11; DAG step 3
(blueprint: lem-sf-adic-ambient-hom-evaluation-comparison). -/
def realizedEvaluation (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory) :
    A.closed.tensor.obj
      ((ordinary l X R).obj ((commonStageDerivedInternalHom l (PadicAlgCl l) X).obj P),
        (ordinary l X R).obj P.obj.1.unop) ⟶ (ordinary l X R).obj P.obj.2 :=
  A.tensor.hom.app ((commonStageDerivedInternalHom l (PadicAlgCl l) X).obj P,
      P.obj.1.unop) ≫ (ordinary l X R).map (source.evaluation P)

/-- The specified c is the ambient transpose of realized right evaluation.
Source: BS 3.4.11; DAG step 3
(blueprint: lem-sf-adic-ambient-hom-evaluation-comparison). -/
def comparison (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory) :
    (ordinary l X R).obj ((commonStageDerivedInternalHom l (PadicAlgCl l) X).obj P) ⟶
      (ambientHom l X R).obj
        (op ((ordinary l X R).obj P.obj.1.unop), (ordinary l X R).obj P.obj.2) :=
  A.closed.transpose _ _ _ (realizedEvaluation l X R A source P)

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory

/-- The realized input at the specified finite stage, using the recorded permitted pair.
Source: DAG step 7 (blueprint: lem-sf-adic-ambient-hom-evaluation-comparison). -/
def finiteM (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
    (F : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (h : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ F) :
    DerivedCategory (modules l X R) :=
  (ordinary l X R).obj ((GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := X) F).obj
      (commonStageHomPairAtStage l (PadicAlgCl l) X P F h).obj.1.unop)

/-- The realized input at the specified finite stage, using the recorded permitted pair.
Source: DAG step 7 (blueprint: lem-sf-adic-ambient-hom-evaluation-comparison). -/
def finiteN (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
    (F : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (h : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ F) :
    DerivedCategory (modules l X R) :=
  (ordinary l X R).obj ((GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := X) F).obj
      (commonStageHomPairAtStage l (PadicAlgCl l) X P F h).obj.2)

/-- The realized rational Hom at the specified finite stage.
Source: DAG step 7 (blueprint: lem-sf-adic-ambient-hom-evaluation-comparison). -/
def finiteH (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
    (F : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (h : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ F) :
    DerivedCategory (modules l X R) :=
  (ordinary l X R).obj ((GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := X) F).obj
      ((rationalDerivedInternalHom l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) F) X).obj
          (commonStageHomPairAtStage l (PadicAlgCl l) X P F h)))

/-- The actual realized finite-stage M comparison, including the scalar associator.
Source: DAG step 7, specified common-stage scalar identifications
(blueprint: lem-sf-adic-ambient-hom-evaluation-comparison). -/
def gammaM (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
    (F : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (h : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ F) :
    (ordinary l X R).obj P.obj.1.unop ≅ finiteM l X R P F h :=
  (ordinary l X R).mapIso
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).isoToStage
      P.obj.1.unop (((Padic.finiteCoefficientFields_properties l (PadicAlgCl l)).1
        P.obj.1.unop.stage P.obj.2.stage).1.trans h))

/-- The actual realized finite-stage N comparison.
Source: DAG step 7, specified common-stage scalar identifications
(blueprint: lem-sf-adic-ambient-hom-evaluation-comparison). -/
def gammaN (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
    (F : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (h : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ F) :
    (ordinary l X R).obj P.obj.2 ≅ finiteN l X R P F h :=
  (ordinary l X R).mapIso
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).isoToStage
      P.obj.2 (((Padic.finiteCoefficientFields_properties l (PadicAlgCl l)).1
        P.obj.1.unop.stage P.obj.2.stage).2.trans h))

/-- The finite-stage H comparison uses exactly the prescribed rational Hom scalar map.
The first equality merely exposes the unchanged literal object of the chosen functor.
Source: DAG step 7; commonStageHomComparison of the recorded operations
(blueprint: lem-sf-adic-ambient-hom-evaluation-comparison). -/
def gammaH (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
    (F : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (h : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ F) :
    (ordinary l X R).obj ((commonStageDerivedInternalHom l (PadicAlgCl l) X).obj P) ≅
      finiteH l X R P F h :=
  (ordinary l X R).mapIso
    (eqToIso ((commonStageDerivedInternalHom_existsUnique l (PadicAlgCl l)
        X).exists.choose_spec.1 P) ≪≫
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).isoToStage
        (commonStageHomObject l (PadicAlgCl l) X P) h ≪≫
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) F).mapIso
          (commonStageHomComparison l (PadicAlgCl l) X P F h))

/-- Realized finite rational evaluation, using the actual inclusion tensorator.
In particular this is not evaluation transported along an arbitrary Hom isomorphism.
Source: BS 3.4.11; DAG step 7 and the finite rational transpose hypothesis
(blueprint: lem-sf-adic-ambient-hom-evaluation-comparison). -/
def finiteEvaluation (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
    (F : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (h : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ F) :
    A.closed.tensor.obj (finiteH l X R P F h, finiteM l X R P F h) ⟶
      finiteN l X R P F h :=
  A.tensor.hom.app
      ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) F).obj
        ((rationalDerivedInternalHom l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) F) X).obj
            (commonStageHomPairAtStage l (PadicAlgCl l) X P F h)),
       (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) F).obj
        (commonStageHomPairAtStage l (PadicAlgCl l) X P F h).obj.1.unop) ≫
    (ordinary l X R).map
      (stageTensor l X (PadicAlgCl l) F
        ((rationalDerivedInternalHom l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) F) X).obj
            (commonStageHomPairAtStage l (PadicAlgCl l) X P F h))
        (commonStageHomPairAtStage l (PadicAlgCl l) X P F h).obj.1.unop).inv ≫
    (ordinary l X R).map
      ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) F).map
          ((podRationalClosed l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) F) X).evaluation
              (commonStageHomPairAtStage l (PadicAlgCl l) X P F h)))

/-- The finite comparison is the transpose of that finite rational evaluation.
Source: DAG step 7 (blueprint: lem-sf-adic-ambient-hom-evaluation-comparison). -/
def finiteComparison (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
    (F : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (h : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ F) :
    finiteH l X R P F h ⟶
      (ambientHom l X R).obj (op (finiteM l X R P F h), finiteN l X R P F h) :=
  A.closed.transpose _ _ _ (finiteEvaluation l X R A P F h)

/-- The actual H transition between two common fields, normalized by gammaH.
Source: DAG step 7 (blueprint: lem-sf-adic-ambient-hom-evaluation-comparison). -/
def homTransition (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
    (F G : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (hF : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ F)
    (hG : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ G) :
    finiteH l X R P F hF ⟶ finiteH l X R P G hG :=
  (gammaH l X R P F hF).inv ≫ (gammaH l X R P G hG).hom

/-- The corresponding ambient Hom transition, contravariant in M and covariant in N.
Source: DAG step 7 (blueprint: lem-sf-adic-ambient-hom-evaluation-comparison). -/
def ambientTransition (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
    (F G : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (hF : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ F)
    (hG : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ G) :
    (ambientHom l X R).obj (op (finiteM l X R P F hF), finiteN l X R P F hF) ⟶
      (ambientHom l X R).obj (op (finiteM l X R P G hG), finiteN l X R P G hG) :=
  (ambientHom l X R).map (Prod.mkHom
    ((gammaM l X R P G hG).inv ≫ (gammaM l X R P F hF).hom).op
    ((gammaN l X R P F hF).inv ≫ (gammaN l X R P G hG).hom))

/-- All conclusions concern the actual evaluation-defined maps, including finite fields.
Source: BS 3.4.11, 6.8.15; DAG steps 1--7
(blueprint: lem-sf-adic-ambient-hom-evaluation-comparison). -/
structure Laws : Prop where
  bounded : ∀ P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory,
    boundedConstructible l X R ((ambientHom l X R).obj
      (op ((ordinary l X R).obj P.obj.1.unop), (ordinary l X R).obj P.obj.2))
  isIso : ∀ P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory,
    IsIso (comparison l X R A source P)
  postcomposition : ∀ (L : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X)
      (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory),
    Function.Bijective (fun a : (ordinary l X R).obj L ⟶
      (ordinary l X R).obj ((commonStageDerivedInternalHom l (PadicAlgCl l) X).obj P) ↦
        a ≫ comparison l X R A source P)
  transpose : ∀ (L : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X)
      (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
      (a : L ⟶ (commonStageDerivedInternalHom l (PadicAlgCl l) X).obj P),
    A.closed.transpose _ _ _
        (A.tensor.hom.app (L, P.obj.1.unop) ≫
          (ordinary l X R).map
            ((commonStageDerivedTensor l (PadicAlgCl l) X).map
              (Prod.mkHom a (𝟙 _)) ≫ source.evaluation P)) =
      (ordinary l X R).map a ≫ comparison l X R A source P
  naturality : ∀ (P Q : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
      (f : P ⟶ Q),
    (ordinary l X R).map ((commonStageDerivedInternalHom l (PadicAlgCl l) X).map f) ≫
        comparison l X R A source Q =
      comparison l X R A source P ≫ (ambientHom l X R).map
        (Prod.mkHom ((ordinary l X R).map f.hom.1.unop).op
          ((ordinary l X R).map f.hom.2))
  evaluation : ∀ P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory,
    A.closed.tensor.map (Prod.mkHom (comparison l X R A source P) (𝟙 _)) ≫
        A.closed.evaluation ((ordinary l X R).obj P.obj.1.unop)
          ((ordinary l X R).obj P.obj.2) = realizedEvaluation l X R A source P
  signed_symmetry : ∀ P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory,
    A.closed.tensor.map (Prod.mkHom (𝟙 _) (comparison l X R A source P)) ≫
        (A.symmetry.braiding ((ordinary l X R).obj P.obj.1.unop)
          ((ambientHom l X R).obj
            (op ((ordinary l X R).obj P.obj.1.unop), (ordinary l X R).obj P.obj.2))).hom ≫
        A.closed.evaluation ((ordinary l X R).obj P.obj.1.unop)
          ((ordinary l X R).obj P.obj.2) =
      A.tensor.hom.app
          (P.obj.1.unop, (commonStageDerivedInternalHom l (PadicAlgCl l) X).obj P) ≫
        (ordinary l X R).map
          ((pullbackTensorCommonBraiding l (PadicAlgCl l) X P.obj.1.unop
            ((commonStageDerivedInternalHom l (PadicAlgCl l) X).obj P)).hom ≫
            source.evaluation P)
  finite_evaluation : ∀ (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
      (F : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
      (h : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ F),
    A.closed.tensor.map
        (Prod.mkHom (gammaH l X R P F h).hom (gammaM l X R P F h).hom) ≫
        finiteEvaluation l X R A P F h =
      realizedEvaluation l X R A source P ≫ (gammaN l X R P F h).hom
  finite_comparison : ∀ (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
      (F : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
      (h : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ F),
    (gammaH l X R P F h).hom ≫ finiteComparison l X R A P F h =
      comparison l X R A source P ≫ (ambientHom l X R).map
        (Prod.mkHom (gammaM l X R P F h).inv.op (gammaN l X R P F h).hom)
  extension : ∀ (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
      (F G : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) (_hFG : F ≤ G)
      (hF : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ F)
      (hG : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ G),
    homTransition l X R P F G hF hG ≫ finiteComparison l X R A P G hG =
      finiteComparison l X R A P F hF ≫ ambientTransition l X R P F G hF hG
  tower : ∀ (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
      (F G K : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
      (_hFG : F ≤ G) (_hGK : G ≤ K)
      (hF : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ F)
      (hG : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ G)
      (hK : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ K),
    homTransition l X R P F G hF hG ≫ homTransition l X R P G K hG hK =
        homTransition l X R P F K hF hK ∧
      ambientTransition l X R P F G hF hG ≫ ambientTransition l X R P G K hG hK =
        ambientTransition l X R P F K hF hK
  identity : ∀ (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
      (F : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
      (h : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ F),
    homTransition l X R P F F h h = 𝟙 _ ∧ ambientTransition l X R P F F h h = 𝟙 _

/-- The ambient part of the seven-step comparison argument.
This is the constructibility, invertibility, transpose, naturality and evaluation
portion; the finite-stage coherence is isolated in `CoherenceLaws` below.
Source: BS Lemma 3.4.11 and Remark 6.8.15
(blueprint: lem-sf-adic-ambient-hom-evaluation-comparison-core). -/
structure CoreLaws : Prop where
  bounded : ∀ P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory,
    boundedConstructible l X R ((ambientHom l X R).obj
      (op ((ordinary l X R).obj P.obj.1.unop), (ordinary l X R).obj P.obj.2))
  isIso : ∀ P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory,
    IsIso (comparison l X R A source P)
  postcomposition : ∀ (L : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X)
      (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory),
    Function.Bijective (fun a : (ordinary l X R).obj L ⟶
      (ordinary l X R).obj ((commonStageDerivedInternalHom l (PadicAlgCl l) X).obj P) ↦
        a ≫ comparison l X R A source P)
  transpose : ∀ (L : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X)
      (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
      (a : L ⟶ (commonStageDerivedInternalHom l (PadicAlgCl l) X).obj P),
    A.closed.transpose _ _ _
        (A.tensor.hom.app (L, P.obj.1.unop) ≫
          (ordinary l X R).map
            ((commonStageDerivedTensor l (PadicAlgCl l) X).map
              (Prod.mkHom a (𝟙 _)) ≫ source.evaluation P)) =
      (ordinary l X R).map a ≫ comparison l X R A source P
  naturality : ∀ (P Q : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
      (f : P ⟶ Q),
    (ordinary l X R).map ((commonStageDerivedInternalHom l (PadicAlgCl l) X).map f) ≫
        comparison l X R A source Q =
      comparison l X R A source P ≫ (ambientHom l X R).map
        (Prod.mkHom ((ordinary l X R).map f.hom.1.unop).op
          ((ordinary l X R).map f.hom.2))
  evaluation : ∀ P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory,
    A.closed.tensor.map (Prod.mkHom (comparison l X R A source P) (𝟙 _)) ≫
        A.closed.evaluation ((ordinary l X R).obj P.obj.1.unop)
          ((ordinary l X R).obj P.obj.2) = realizedEvaluation l X R A source P

/-- The finite-stage and coefficient-tower part of the comparison argument.
It is independent of the constructibility and Hom-bijection fields packaged in
`CoreLaws`, and records the remaining actual evaluation maps and their coherence.
Source: BS Remark 6.8.15 and HRS Lemmas 7.7--7.10
(blueprint: lem-sf-adic-ambient-hom-evaluation-comparison-coherence). -/
structure CoherenceLaws : Prop where
  signed_symmetry : ∀ P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory,
    A.closed.tensor.map (Prod.mkHom (𝟙 _) (comparison l X R A source P)) ≫
        (A.symmetry.braiding ((ordinary l X R).obj P.obj.1.unop)
          ((ambientHom l X R).obj
            (op ((ordinary l X R).obj P.obj.1.unop), (ordinary l X R).obj P.obj.2))).hom ≫
        A.closed.evaluation ((ordinary l X R).obj P.obj.1.unop)
          ((ordinary l X R).obj P.obj.2) =
      A.tensor.hom.app
          (P.obj.1.unop, (commonStageDerivedInternalHom l (PadicAlgCl l) X).obj P) ≫
        (ordinary l X R).map
          ((pullbackTensorCommonBraiding l (PadicAlgCl l) X P.obj.1.unop
            ((commonStageDerivedInternalHom l (PadicAlgCl l) X).obj P)).hom ≫
            source.evaluation P)
  finite_evaluation : ∀ (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
      (F : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
      (h : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ F),
    A.closed.tensor.map
        (Prod.mkHom (gammaH l X R P F h).hom (gammaM l X R P F h).hom) ≫
        finiteEvaluation l X R A P F h =
      realizedEvaluation l X R A source P ≫ (gammaN l X R P F h).hom
  finite_comparison : ∀ (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
      (F : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
      (h : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ F),
    (gammaH l X R P F h).hom ≫ finiteComparison l X R A P F h =
      comparison l X R A source P ≫ (ambientHom l X R).map
        (Prod.mkHom (gammaM l X R P F h).inv.op (gammaN l X R P F h).hom)
  extension : ∀ (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
      (F G : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) (_hFG : F ≤ G)
      (hF : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ F)
      (hG : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ G),
    homTransition l X R P F G hF hG ≫ finiteComparison l X R A P G hG =
      finiteComparison l X R A P F hF ≫ ambientTransition l X R P F G hF hG
  tower : ∀ (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
      (F G K : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
      (_hFG : F ≤ G) (_hGK : G ≤ K)
      (hF : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ F)
      (hG : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ G)
      (hK : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ K),
    homTransition l X R P F G hF hG ≫ homTransition l X R P G K hG hK =
        homTransition l X R P F K hF hK ∧
      ambientTransition l X R P F G hF hG ≫ ambientTransition l X R P G K hG hK =
        ambientTransition l X R P F K hF hK
  identity : ∀ (P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory)
      (F : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
      (h : (commonStageHomObject l (PadicAlgCl l) X P).stage ≤ F),
    homTransition l X R P F F h h = 𝟙 _ ∧ ambientTransition l X R P F F h h = 𝟙 _

/-- Construct the core comparison laws. This is the first, constructibility and
ambient-adjunction half of the proof in the node. -/
theorem adic_ambient_hom_evaluation_comparison_core
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (T : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated T.hom] [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [∀ x : T.left, Invertible (l : T.left.residueField x)]
    (R : LocallyFiniteAdicRealization.Realization l T.left)
    (presentation : (sectionFunctor l T.left R).IsEquivalence)
    (A : TensorInput l T.left R)
    (source : PodPartialClosed (commonStageDerivedTensor l (PadicAlgCl l) T.left)
      (commonStageHomPairs l (PadicAlgCl l) T.left)
      (commonStageDerivedInternalHom l (PadicAlgCl l) T.left))
    (source_normalized : PodCommonTransposeNormalization l (PadicAlgCl l) T.left source) :
    CoreLaws l T.left R A source := by
  sorry

/-- Construct the finite-stage and coefficient tower laws. This is the second half
of the seven-step argument in the node. -/
theorem adic_ambient_hom_evaluation_comparison_coherence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (T : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated T.hom] [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [∀ x : T.left, Invertible (l : T.left.residueField x)]
    (R : LocallyFiniteAdicRealization.Realization l T.left)
    (presentation : (sectionFunctor l T.left R).IsEquivalence)
    (A : TensorInput l T.left R)
    (source : PodPartialClosed (commonStageDerivedTensor l (PadicAlgCl l) T.left)
      (commonStageHomPairs l (PadicAlgCl l) T.left)
      (commonStageDerivedInternalHom l (PadicAlgCl l) T.left))
    (source_normalized : PodCommonTransposeNormalization l (PadicAlgCl l) T.left source) :
    CoherenceLaws l T.left R A source := by
  sorry

/-- Assemble the ambient comparison laws from their strictly smaller core and coherence packages.
(blueprint: lem-sf-adic-ambient-hom-evaluation-comparison). -/
theorem adic_ambient_hom_evaluation_comparison
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (T : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated T.hom] [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [∀ x : T.left, Invertible (l : T.left.residueField x)]
    (R : LocallyFiniteAdicRealization.Realization l T.left)
    (presentation : (sectionFunctor l T.left R).IsEquivalence)
    (A : TensorInput l T.left R)
    (source : PodPartialClosed (commonStageDerivedTensor l (PadicAlgCl l) T.left)
      (commonStageHomPairs l (PadicAlgCl l) T.left)
      (commonStageDerivedInternalHom l (PadicAlgCl l) T.left))
    (source_normalized : PodCommonTransposeNormalization l (PadicAlgCl l) T.left source) :
    Laws l T.left R A source := by
  have hc := adic_ambient_hom_evaluation_comparison_core D l hl T R presentation A source
    source_normalized
  have hh := adic_ambient_hom_evaluation_comparison_coherence D l hl T R presentation A source
    source_normalized
  exact
    { bounded := hc.bounded
      isIso := hc.isIso
      postcomposition := hc.postcomposition
      transpose := hc.transpose
      naturality := hc.naturality
      evaluation := hc.evaluation
      signed_symmetry := hh.signed_symmetry
      finite_evaluation := hh.finite_evaluation
      finite_comparison := hh.finite_comparison
      extension := hh.extension
      tower := hh.tower
      identity := hh.identity }

end AmbientHomEvaluation
end WeilConjectures.AdicQbarRealization
