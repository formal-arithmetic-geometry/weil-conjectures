/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Native.NativeAdicRealizationData
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.SixFunctors.AdicQbarRealization.AmbientHomEvaluation.CoherenceCalculus.CommonStageEvaluationFiniteSquare
import WeilConjectures.SixFunctors.Normalized.NormalizedCommonEvaluationForStructure
import WeilConjectures.SixFunctors.AdicQbarRealization.Native.NativeAdicAmbientHomConstructible
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison

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

attribute [local irreducible] commonStageDerivedInternalHom

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
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
    (eqToIso (commonStageDerivedInternalHom_obj_eq l (PadicAlgCl l) X P) ≪≫
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

open CoherenceCalculus

/-- The constructibility part of the core comparison argument.

The proof follows the first two steps of the retained argument: identify the ordinary
section presentation with the locally finite constructible convention, then apply the
ambient internal-Hom constructibility theorem to the permitted pair. The zero object and
empty schemes are included by the same object-property argument.
Source: BS Lemma 3.4.11 and Remark 6.8.15
(blueprint: lem-sf-adic-ambient-hom-evaluation-comparison-core-bounded). -/
theorem adic_ambient_hom_evaluation_comparison_core_bounded
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
    ∀ P : (commonStageHomPairs l (PadicAlgCl l) T.left).FullSubcategory,
      boundedConstructible l T.left R ((ambientHom l T.left R).obj
        (op ((ordinary l T.left R).obj P.obj.1.unop),
          (ordinary l T.left R).obj P.obj.2)) := by
  have _ := presentation
  have _ := A
  have _ := source_normalized
  intro P
  have hM := (R.image (R.J.obj P.obj.1.unop)).mpr ⟨_, ⟨Iso.refl _⟩⟩
  have hN := (R.image (R.J.obj P.obj.2)).mpr ⟨_, ⟨Iso.refl _⟩⟩
  exact nativeAmbientHom_constructible D l hl T R _ _ hM hN

set_option maxHeartbeats 800000 in
-- the categorical naturality expression needs the larger elaboration budget
private theorem core_adjunction_transpose_field
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (T : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated T.hom] [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [∀ x : T.left, Invertible (l : T.left.residueField x)]
    (R : LocallyFiniteAdicRealization.Realization l T.left)
    (_presentation : (sectionFunctor l T.left R).IsEquivalence)
    (A : TensorInput l T.left R)
    (source : PodPartialClosed (commonStageDerivedTensor l (PadicAlgCl l) T.left)
      (commonStageHomPairs l (PadicAlgCl l) T.left)
      (commonStageDerivedInternalHom l (PadicAlgCl l) T.left))
    (_source_normalized : PodCommonTransposeNormalization l (PadicAlgCl l) T.left source) :
    ∀ (L : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) T.left)
      (P : (commonStageHomPairs l (PadicAlgCl l) T.left).FullSubcategory)
      (a : L ⟶ (commonStageDerivedInternalHom l (PadicAlgCl l) T.left).obj P),
      A.closed.transpose _ _ _
          (A.tensor.hom.app (L, P.obj.1.unop) ≫
            (ordinary l T.left R).map
              ((commonStageDerivedTensor l (PadicAlgCl l) T.left).map
                (Prod.mkHom a (𝟙 _)) ≫ source.evaluation P)) =
        (ordinary l T.left R).map a ≫ comparison l T.left R A source P := by
  intro L P a
  apply (A.closed.transpose _ _ _).symm.injective
  rw [Equiv.symm_apply_apply]
  unfold comparison realizedEvaluation
  rw [uncurry_precomp]
  rw [Functor.map_comp]
  have hn0 := A.tensor.hom.naturality
    (X := (L, P.obj.1.unop))
    (Y := ((commonStageDerivedInternalHom l (PadicAlgCl l) T.left).obj P,
      P.obj.1.unop))
    (Prod.mkHom a (𝟙 P.obj.1.unop))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn0
  have hn := by simpa only [Functor.map_id] using hn0
  rw [← Category.assoc, ← hn, Category.assoc]
  rw [Equiv.symm_apply_apply]
  have hmap := (ordinary l T.left R).map_id P.obj.1.unop
  rw [hmap]

private theorem source_uncurry_local
    {C : Type*} [Category C] [Preadditive C]
    {T : C × C ⥤ C} {J : ObjectProperty (Cᵒᵖ × C)} {H : J.FullSubcategory ⥤ C}
    (S : PodPartialClosed T J H) (L : C) (P : J.FullSubcategory) (a : L ⟶ H.obj P) :
    (S.transpose L P).symm a =
      T.map (Prod.mkHom a (𝟙 _)) ≫ S.evaluation P := by
  apply (S.transpose L P).injective
  rw [AddEquiv.apply_symm_apply, S.parameter_naturality]
  simp only [PodPartialClosed.evaluation, AddEquiv.apply_symm_apply, Category.comp_id]

set_option maxHeartbeats 800000 in
-- The explicit composite of four Hom equivalences requires extra elaboration steps.
private theorem core_postcomposition_field
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
    (source_normalized : PodCommonTransposeNormalization l (PadicAlgCl l) T.left source)
    (hF : ∀ K L, Function.Bijective
      ((ordinary l T.left R).map : (K ⟶ L) → (_ ⟶ _)))
    (L : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) T.left)
    (P : (commonStageHomPairs l (PadicAlgCl l) T.left).FullSubcategory) :
    Function.Bijective (fun a : (ordinary l T.left R).obj L ⟶
      (ordinary l T.left R).obj ((commonStageDerivedInternalHom l (PadicAlgCl l) T.left).obj P)
      ↦ a ≫ comparison l T.left R A source P) := by
  let E := (source.transpose L P).symm.toEquiv |>.trans
    (Equiv.ofBijective (ordinary l T.left R).map (hF _ _)) |>.trans
    (A.tensor.app (L, P.obj.1.unop)).symm.homFromEquiv |>.trans
    (A.closed.transpose _ _ _)
  have he (a : L ⟶ (commonStageDerivedInternalHom l (PadicAlgCl l) T.left).obj P) :
      E a = (ordinary l T.left R).map a ≫ comparison l T.left R A source P := by
    change A.closed.transpose _ _ _ (A.tensor.hom.app (L, P.obj.1.unop) ≫
      (ordinary l T.left R).map ((source.transpose L P).symm a)) = _
    rw [source_uncurry_local]
    exact core_adjunction_transpose_field D l hl T R presentation A source source_normalized
      L P a
  constructor
  · intro a b hab
    obtain ⟨a', rfl⟩ := (hF _ _).surjective a
    obtain ⟨b', rfl⟩ := (hF _ _).surjective b
    congr 1
    apply E.injective
    simpa only [he] using hab
  · intro b
    obtain ⟨a, ha⟩ := E.surjective b
    exact ⟨(ordinary l T.left R).map a, (he a).symm.trans ha⟩

set_option maxHeartbeats 800000 in
-- Elaborating the two-variable tensor naturality identities needs this budget.
/-- The ambient-adjunction part of the core comparison argument.

The proof applies the normalized transpose identity to the specified tensorator. The
ambient adjunction and full faithfulness give the Hom bijection, and injectivity of
transposition gives its transpose, pair naturality, and evaluation equation. The inverse
of the comparison is then constructed from two constructible test objects, so no
unstated detection hypothesis on arbitrary ambient objects is used.
Source: BS Lemma 3.4.11 and Remark 6.8.15
(blueprint: lem-sf-adic-ambient-hom-evaluation-comparison-core-adjunction). -/
theorem adic_ambient_hom_evaluation_comparison_core_adjunction
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
    (∀ P : (commonStageHomPairs l (PadicAlgCl l) T.left).FullSubcategory,
      IsIso (comparison l T.left R A source P)) ∧
    (∀ (L : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) T.left)
      (P : (commonStageHomPairs l (PadicAlgCl l) T.left).FullSubcategory),
      Function.Bijective (fun a : (ordinary l T.left R).obj L ⟶
        (ordinary l T.left R).obj
          ((commonStageDerivedInternalHom l (PadicAlgCl l) T.left).obj P) ↦
          a ≫ comparison l T.left R A source P)) ∧
    (∀ (L : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) T.left)
      (P : (commonStageHomPairs l (PadicAlgCl l) T.left).FullSubcategory)
      (a : L ⟶ (commonStageDerivedInternalHom l (PadicAlgCl l) T.left).obj P),
      A.closed.transpose _ _ _
          (A.tensor.hom.app (L, P.obj.1.unop) ≫
            (ordinary l T.left R).map
              ((commonStageDerivedTensor l (PadicAlgCl l) T.left).map
                (Prod.mkHom a (𝟙 _)) ≫ source.evaluation P)) =
        (ordinary l T.left R).map a ≫ comparison l T.left R A source P) ∧
    (∀ (P Q : (commonStageHomPairs l (PadicAlgCl l) T.left).FullSubcategory)
      (f : P ⟶ Q),
      (ordinary l T.left R).map
          ((commonStageDerivedInternalHom l (PadicAlgCl l) T.left).map f) ≫
          comparison l T.left R A source Q =
        comparison l T.left R A source P ≫ (ambientHom l T.left R).map
          (Prod.mkHom ((ordinary l T.left R).map f.hom.1.unop).op
            ((ordinary l T.left R).map f.hom.2))) ∧
    (∀ P : (commonStageHomPairs l (PadicAlgCl l) T.left).FullSubcategory,
      A.closed.tensor.map (Prod.mkHom (comparison l T.left R A source P) (𝟙 _)) ≫
          A.closed.evaluation ((ordinary l T.left R).obj P.obj.1.unop)
            ((ordinary l T.left R).obj P.obj.2) =
        realizedEvaluation l T.left R A source P) := by
  let := R.commutative
  let := R.sectionsAdditive
  let := R.sectionsLimits
  let := R.sectionsColimits
  have hsections : (LocallyFiniteAdicRealization.sections l T.left).IsEquivalence :=
    presentation
  have : R.J.Full := ⟨fun {K L} ↦ (R.fully_faithful K L).surjective⟩
  have : R.J.Faithful := ⟨fun {K L} ↦ (R.fully_faithful K L).injective⟩
  have hF : ∀ K L, Function.Bijective
      ((ordinary l T.left R).map : (K ⟶ L) → (_ ⟶ _)) := by
    intro K L
    exact (Functor.FullyFaithful.ofFullyFaithful
      (R.J ⋙ (LocallyFiniteAdicRealization.sections l T.left).mapDerivedCategory)).map_bijective
      K L
  have hp := core_postcomposition_field D l hl T R presentation A source source_normalized hF
  have hi (P : (commonStageHomPairs l (PadicAlgCl l) T.left).FullSubcategory) :
      IsIso (comparison l T.left R A source P) := by
    obtain ⟨K, hK, ⟨e⟩⟩ := adic_ambient_hom_evaluation_comparison_core_bounded
      D l hl T R presentation A source source_normalized P
    obtain ⟨L, ⟨t⟩⟩ := (R.image K).mp hK
    let t' : (ordinary l T.left R).obj L ≅ _ :=
      (sectionDerived l T.left R).mapIso t ≪≫ e
    obtain ⟨s, hs⟩ := (hp L P).surjective t'.hom
    dsimp only at hs
    let b := t'.inv ≫ s
    have hbc : b ≫ comparison l T.left R A source P = 𝟙 _ := by
      dsimp only [b]
      rw [Category.assoc, hs, t'.inv_hom_id]
    have hcb : comparison l T.left R A source P ≫ b = 𝟙 _ := by
      apply (hp ((commonStageDerivedInternalHom l (PadicAlgCl l) T.left).obj P) P).injective
      simp only [Category.assoc, hbc, Category.comp_id, Category.id_comp]
    exact ⟨⟨b, hcb, hbc⟩⟩
  refine ⟨hi, hp, core_adjunction_transpose_field D l hl T R presentation A source
    source_normalized, ?_, ?_⟩
  · intro P Q f
    apply (A.closed.transpose _ _ _).symm.injective
    rw [uncurry_precomp, uncurry_postcomp]
    unfold comparison
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    unfold realizedEvaluation
    have hleft := A.tensor.hom.naturality
      (Prod.mkHom ((commonStageDerivedInternalHom l (PadicAlgCl l) T.left).map f)
        (𝟙 Q.obj.1.unop))
    have hright := A.tensor.hom.naturality
      (Prod.mkHom (𝟙 ((commonStageDerivedInternalHom l (PadicAlgCl l) T.left).obj P))
        f.hom.1.unop)
    dsimp only [Functor.comp_map, Functor.prod_map] at hleft hright
    rw [(ordinary l T.left R).map_id Q.obj.1.unop] at hleft
    rw [(ordinary l T.left R).map_id
      ((commonStageDerivedInternalHom l (PadicAlgCl l) T.left).obj P)] at hright
    have hleft' := congrArg (fun k ↦ k ≫
      (ordinary l T.left R).map (source.evaluation Q)) hleft
    have hright' := congrArg (fun k ↦ k ≫
      (ordinary l T.left R).map (source.evaluation P) ≫
        (ordinary l T.left R).map f.hom.2) hright
    simp only [Category.assoc] at hleft' hright'
    have hn := congrArg ((ordinary l T.left R).map)
      (normalizedCommonEvaluationForStructure_naturality l (PadicAlgCl l) T.left
        source source_normalized P Q f)
    simp only [(ordinary l T.left R).map_comp] at hn
    have hn' := congrArg (fun k ↦ A.tensor.hom.app
      (((commonStageDerivedInternalHom l (PadicAlgCl l) T.left).obj P), Q.obj.1.unop) ≫ k)
      hn
    simpa only [Category.assoc] using hleft'.trans (hn'.trans hright'.symm)
  · intro P
    have he := (A.closed.transpose
      ((ordinary l T.left R).obj
        ((commonStageDerivedInternalHom l (PadicAlgCl l) T.left).obj P))
      ((ordinary l T.left R).obj P.obj.1.unop)
      ((ordinary l T.left R).obj P.obj.2)).symm_apply_apply
        (realizedEvaluation l T.left R A source P)
    rw [uncurry] at he
    exact he

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
  have hb := adic_ambient_hom_evaluation_comparison_core_bounded D l hl T R presentation A
    source source_normalized
  have ha := adic_ambient_hom_evaluation_comparison_core_adjunction D l hl T R presentation A
    source source_normalized
  exact
    { bounded := hb
      isIso := ha.1
      postcomposition := ha.2.1
      transpose := ha.2.2.1
      naturality := ha.2.2.2.1
      evaluation := ha.2.2.2.2 }

attribute [local irreducible] ordinary
  commonStageDerivedTensor rationalDerivedInternalHom podRationalClosed

set_option allowUnsafeReducibility true in
attribute [local irreducible] ambientHom

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 1200000 in
-- Comparing the specified finite-stage maps needs additional elaboration heartbeats.
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
  have _hl := hl
  have _presentation := presentation
  have hev (P : (commonStageHomPairs l (PadicAlgCl l) T.left).FullSubcategory) :
      A.closed.tensor.map (Prod.mkHom (comparison l T.left R A source P) (𝟙 _)) ≫
          A.closed.evaluation ((ordinary l T.left R).obj P.obj.1.unop)
            ((ordinary l T.left R).obj P.obj.2) =
        realizedEvaluation l T.left R A source P := by
    have h := (A.closed.transpose _ _ _).symm_apply_apply
      (realizedEvaluation l T.left R A source P)
    rw [uncurry] at h
    exact h
  have he (P : (commonStageHomPairs l (PadicAlgCl l) T.left).FullSubcategory)
      (F : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
      (h : (commonStageHomObject l (PadicAlgCl l) T.left P).stage ≤ F) :
      A.closed.tensor.map
          (Prod.mkHom (gammaH l T.left R P F h).hom (gammaM l T.left R P F h).hom) ≫
          finiteEvaluation l T.left R A P F h =
        realizedEvaluation l T.left R A source P ≫ (gammaN l T.left R P F h).hom := by
    let I := GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := T.left) F
    let Q := commonStageHomPairAtStage l (PadicAlgCl l) T.left P F h
    let gH : (commonStageDerivedInternalHom l (PadicAlgCl l) T.left).obj P ≅
        I.obj ((rationalDerivedInternalHom l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) F) T.left).obj Q) :=
      eqToIso (commonStageDerivedInternalHom_obj_eq l (PadicAlgCl l) T.left P) ≪≫
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) T.left).isoToStage
        (commonStageHomObject l (PadicAlgCl l) T.left P) h ≪≫
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := T.left) F).mapIso
          (commonStageHomComparison l (PadicAlgCl l) T.left P F h)
    let gM : P.obj.1.unop ≅ I.obj Q.obj.1.unop :=
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l)
      T.left).isoToStage P.obj.1.unop
        (((Padic.finiteCoefficientFields_properties l (PadicAlgCl l)).1
          P.obj.1.unop.stage P.obj.2.stage).1.trans h)
    let gN : P.obj.2 ≅ I.obj Q.obj.2 :=
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l)
      T.left).isoToStage P.obj.2
        (((Padic.finiteCoefficientFields_properties l (PadicAlgCl l)).1
          P.obj.1.unop.stage P.obj.2.stage).2.trans h)
    have hs := commonStageEvaluation_finiteSquare l (PadicAlgCl l) T.left
      source source_normalized P F h
    exact realized_evaluation_square (ordinary l T.left R)
      (commonStageDerivedTensor l (PadicAlgCl l) T.left) A.closed.tensor A.tensor
      gH gM gN (source.evaluation P)
      ((stageTensor l T.left (PadicAlgCl l) F
        ((rationalDerivedInternalHom l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) F) T.left).obj
            (commonStageHomPairAtStage l (PadicAlgCl l) T.left P F h))
        (commonStageHomPairAtStage l (PadicAlgCl l) T.left P F h).obj.1.unop).inv)
      ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := T.left) F).map
          ((podRationalClosed l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) F)
              T.left).evaluation
            (commonStageHomPairAtStage l (PadicAlgCl l) T.left P F h))) hs
  have hc (P : (commonStageHomPairs l (PadicAlgCl l) T.left).FullSubcategory)
      (F : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
      (h : (commonStageHomObject l (PadicAlgCl l) T.left P).stage ≤ F) :
      (gammaH l T.left R P F h).hom ≫ finiteComparison l T.left R A P F h =
        comparison l T.left R A source P ≫ (ambientHom l T.left R).map
          (Prod.mkHom (gammaM l T.left R P F h).inv.op (gammaN l T.left R P F h).hom) :=
    comparison_square A.closed _ _ _ _ _ _ _ _
      (gammaH l T.left R P F h) (gammaM l T.left R P F h)
      (gammaN l T.left R P F h) (he P F h)
  refine
    { signed_symmetry := ?_
      finite_evaluation := he
      finite_comparison := hc
      extension := ?_
      tower := ?_
      identity := ?_ }
  · intro P
    calc
      _ = (A.symmetry.braiding ((ordinary l T.left R).obj P.obj.1.unop)
          ((ordinary l T.left R).obj
            ((commonStageDerivedInternalHom l (PadicAlgCl l) T.left).obj P))).hom ≫
          realizedEvaluation l T.left R A source P :=
        braiding_evaluation A.closed A.symmetry _ _ _ _ _ (hev P)
      _ = _ :=
        realized_braiding_evaluation (ordinary l T.left R) _ _ _ _ _
          (A.symmetric P.obj.1.unop
            ((commonStageDerivedInternalHom l (PadicAlgCl l) T.left).obj P)).symm
  · intro P F G _hFG hF hG
    exact comparison_extension (ambientHom l T.left R)
      (gammaH l T.left R P F hF) (gammaM l T.left R P F hF) (gammaN l T.left R P F hF)
      (gammaH l T.left R P G hG) (gammaM l T.left R P G hG) (gammaN l T.left R P G hG)
      (comparison l T.left R A source P) (finiteComparison l T.left R A P F hF)
      (finiteComparison l T.left R A P G hG) (hc P F hF) (hc P G hG)
  · intro P F G K _hFG _hGK hF hG hK
    constructor
    · simp only [homTransition, Category.assoc, Iso.hom_inv_id_assoc]
    · exact ambient_transition_tower (ambientHom l T.left R)
        (gammaM l T.left R P F hF) (gammaN l T.left R P F hF)
        (gammaM l T.left R P G hG) (gammaN l T.left R P G hG)
        (gammaM l T.left R P K hK) (gammaN l T.left R P K hK)
  · intro P F h
    constructor
    · exact (gammaH l T.left R P F h).inv_hom_id
    · simp only [ambientTransition, Iso.inv_hom_id, op_id, ← CategoryTheory.prod_id]
      exact (ambientHom l T.left R).map_id _

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

namespace AlgebraicGeometry.ProEtale.CondensedCoefficientRealization

/-- Evaluation in the native derived category, in the right-tensor convention used
by the ordinary ringed-site Hom. The exchange is the native Koszul braiding.
Source: cor-coef-verdier-weil-equivariance.proof.md, paragraph 2
(blueprint: lem-sf-adic-ambient-hom-evaluation-comparison). -/
def evaluation (K N : DerivedCategory.{u + 1} (Internal Λ X)) :
    ((CondensedRing.derivedTensor Λ X).obj
      (((CondensedRing.derivedHom Λ X).obj (op K)).obj N)).obj K ⟶ N :=
  (@BraidedCategory.braiding _ _ _ (internalBraiding Λ X)
    (((CondensedRing.derivedHom Λ X).obj (op K)).obj N) K).hom ≫
      (CondensedRing.derivedTensorHomAdjunction Λ K).counit.app N

/-- An evaluation-normalized ordinary realization of the actual condensed category.
The tensor is normalized on K-flat representatives, and the Hom comparison is a
natural isomorphism on the entire ambient derived category, not only perfect inputs.
Source: Stacks 08J9--08JB; current cor-coef-verdier-weil-equivariance.proof.md,
paragraph 2 (blueprint: lem-sf-adic-ambient-hom-evaluation-comparison). -/
structure ClosedPresentation where
  closed : CoefficientClosedStructure (hom Λ X)
  models : CoefficientTensorModels.{u, u + 1, u, u + 1}
    (Scheme.ProEt.topology X) (ring Λ X) closed
  tensor : TensorComparison Λ X closed models
  homIso : Functor.uncurry.obj (CondensedRing.derivedHom Λ X) ⋙ forward Λ X ≅
    ((forward Λ X).op.prod (forward Λ X)) ⋙ hom Λ X
  evaluation : ∀ K N : DerivedCategory.{u + 1} (Internal Λ X),
    (forward Λ X).map (CondensedCoefficientRealization.evaluation Λ X K N) =
      tensor.iso.hom.app ((((CondensedRing.derivedHom Λ X).obj (op K)).obj N), K) ≫
        closed.tensor.map
          (X := ((forward Λ X).obj (((CondensedRing.derivedHom Λ X).obj (op K)).obj N),
            (forward Λ X).obj K))
          (Y := ((hom Λ X).obj (op ((forward Λ X).obj K), (forward Λ X).obj N),
            (forward Λ X).obj K))
          (homIso.hom.app (op K, N), 𝟙 ((forward Λ X).obj K)) ≫
            closed.evaluation ((forward Λ X).obj K) ((forward Λ X).obj N)

/-- Uncurrying is tensoring with the identity followed by evaluation. -/
private theorem transpose_symm {C : Type*} [Category C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) (L K N : C) (a : L ⟶ H.obj (op K, N)) :
    (S.transpose L K N).symm a = S.tensor.map (a, 𝟙 K) ≫ S.evaluation K N := by
  change (@MonoidalCategory.tensorRight C _ S.monoidal K).map a ≫ _ = _
  let _ := S.monoidal
  simp [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation]

/-- The evaluation-normalized Hom comparison also identifies every transpose.
Source: cor-coef-verdier-weil-equivariance.proof.md, paragraph 2
(blueprint: lem-sf-adic-ambient-hom-evaluation-comparison).
Proof: use the inverse tensor comparison to express the realized pairing. Tensor
naturality and the evaluation equation identify it with evaluation after the realized
Hom morphism. The inverse of the ordinary tensor--Hom adjunction gives its transpose. -/
theorem ClosedPresentation.transpose_evaluation (S : ClosedPresentation Λ X)
    (L K N : DerivedCategory.{u + 1} (Internal Λ X))
    (a : L ⟶ ((CondensedRing.derivedHom Λ X).obj (op K)).obj N) :
    S.closed.transpose ((forward Λ X).obj L) ((forward Λ X).obj K)
      ((forward Λ X).obj N)
      (S.tensor.iso.inv.app (L, K) ≫ (forward Λ X).map
        ((Functor.uncurry.obj (CondensedRing.derivedTensor Λ X)).map
          (X := (L, K))
          (Y := (((CondensedRing.derivedHom Λ X).obj (op K)).obj N, K))
          (Prod.mkHom a (𝟙 K)) ≫
          CondensedCoefficientRealization.evaluation Λ X K N)) =
      (forward Λ X).map a ≫ S.homIso.hom.app (op K, N) := by
  apply (S.closed.transpose _ _ _).symm.injective
  rw [Equiv.symm_apply_apply, transpose_symm]
  have ht := S.tensor.iso.inv.naturality (Prod.mkHom a (𝟙 K))
  dsimp only [Functor.comp_map, Functor.prod_map] at ht
  rw [CategoryTheory.Functor.map_id] at ht
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc, ← ht]
  rw [Category.assoc, S.evaluation, Iso.inv_hom_id_app_assoc, ← Category.assoc,
    ← S.closed.tensor.map_comp]
  congr 2
  ext <;> simp

/-- Evaluation determines each component of the ordinary internal-Hom comparison.
Source: cor-coef-verdier-weil-equivariance.proof.md, paragraph 2
(blueprint: lem-sf-adic-ambient-hom-evaluation-comparison).
Proof: compare the two evaluation equations and cancel the tensor comparison,
which is an isomorphism. The inverse ordinary tensor--Hom adjunction is injective;
its formula is tensoring with the identity followed by evaluation. -/
theorem ClosedPresentation.hom_component_unique (S : ClosedPresentation Λ X)
    (K N : DerivedCategory.{u + 1} (Internal Λ X))
    (b : (forward Λ X).obj (((CondensedRing.derivedHom Λ X).obj (op K)).obj N) ⟶
      (hom Λ X).obj (op ((forward Λ X).obj K), (forward Λ X).obj N))
    (hb : (forward Λ X).map (CondensedCoefficientRealization.evaluation Λ X K N) =
      S.tensor.iso.hom.app ((((CondensedRing.derivedHom Λ X).obj (op K)).obj N), K) ≫
        S.closed.tensor.map
          (X := ((forward Λ X).obj
            (((CondensedRing.derivedHom Λ X).obj (op K)).obj N), (forward Λ X).obj K))
          (Y := ((hom Λ X).obj (op ((forward Λ X).obj K), (forward Λ X).obj N),
            (forward Λ X).obj K))
          (b, 𝟙 ((forward Λ X).obj K)) ≫
          S.closed.evaluation ((forward Λ X).obj K) ((forward Λ X).obj N)) :
    b = S.homIso.hom.app (op K, N) := by
  apply (S.closed.transpose _ _ _).symm.injective
  rw [transpose_symm, transpose_symm]
  apply (cancel_epi (S.tensor.iso.hom.app
    ((((CondensedRing.derivedHom Λ X).obj (op K)).obj N), K))).1
  exact hb.symm.trans (S.evaluation K N)

/-- The natural Hom comparison is uniquely specified by its evaluation equation.
Source: cor-coef-verdier-weil-equivariance.proof.md, paragraph 2
(blueprint: lem-sf-adic-ambient-hom-evaluation-comparison).
Proof: the preceding component uniqueness applies at every pair of ambient objects.
Natural transformation extensionality and isomorphism extensionality give equality
of the natural isomorphisms. No choice of a coefficient representative is involved. -/
theorem ClosedPresentation.homIso_unique (S : ClosedPresentation Λ X)
    (θ : Functor.uncurry.obj (CondensedRing.derivedHom Λ X) ⋙ forward Λ X ≅
      ((forward Λ X).op.prod (forward Λ X)) ⋙ hom Λ X)
    (he : ∀ K N : DerivedCategory.{u + 1} (Internal Λ X),
      (forward Λ X).map (CondensedCoefficientRealization.evaluation Λ X K N) =
        S.tensor.iso.hom.app ((((CondensedRing.derivedHom Λ X).obj (op K)).obj N), K) ≫
          S.closed.tensor.map
            (X := ((forward Λ X).obj
              (((CondensedRing.derivedHom Λ X).obj (op K)).obj N), (forward Λ X).obj K))
            (Y := ((hom Λ X).obj (op ((forward Λ X).obj K), (forward Λ X).obj N),
              (forward Λ X).obj K))
            (θ.hom.app (op K, N), 𝟙 ((forward Λ X).obj K)) ≫
            S.closed.evaluation ((forward Λ X).obj K) ((forward Λ X).obj N)) :
    θ = S.homIso := by
  apply Iso.ext
  apply NatTrans.ext
  funext P
  exact S.hom_component_unique Λ X P.1.unop P.2 (θ.hom.app P) (he P.1.unop P.2)

/-- The ambient comparison uses the actual pulled-back condensed coefficient ring.
Its natural isomorphism is normalized by evaluation, and the preceding laws identify
its transpose and prove its uniqueness, without a boundedness or perfectness restriction.

Source: cor-coef-verdier-weil-equivariance.proof.md, paragraph 2; Stacks 08J9--08JB.
(blueprint: lem-sf-adic-ambient-hom-evaluation-comparison).

Proof: use the derived section equivalence and its K-flat tensor comparison from the
module-object/ringed-site comparison. Retain the natural internal-Hom isomorphism and
its counit equation, with the native Koszul braiding converting left to right evaluation.
The inverse ordinary tensor-Hom transpose identifies every realized pairing; its
injectivity makes the evaluation-normalized comparison unique. -/
theorem adic_ambient_hom_evaluation_comparison : Nonempty (ClosedPresentation Λ X) := by
  obtain ⟨S, T, t, θ, he, _⟩ := moduleObject_ringedSite_derived_comparison Λ X
  exact ⟨S, T, t, θ, he⟩

end AlgebraicGeometry.ProEtale.CondensedCoefficientRealization
