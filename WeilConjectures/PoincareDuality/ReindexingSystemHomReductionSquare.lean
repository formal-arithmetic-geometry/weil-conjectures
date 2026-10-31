/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluation
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.PoincareDuality.Pod.PodCompletedOrdinaryTensor
import WeilConjectures.PoincareDuality.Pod.PodCompletedKFlatTransport
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearTensorEvaluation
import all WeilConjectures.AlgebraicGeometry.System.SystemOrdinaryTensorReduction
import WeilConjectures.SixFunctors.TensorModelUniqueness.TensorComparisonModelUniqueness

/-! # Reindexing actual coefficient systems and the reduction Hom square

Source: blueprint `prop-pod-dual-tate-data-compatibility`, proof Step 5;
Stacks Project, Tags 0941, 0GMX, 0A8X, 0A95, 08J9, 07A4 and 07A6.
(blueprint: lem-pod-reindexing-system-hom-reduction-square).

## Main definitions

- `podCartesianSystemHomFiber`: evaluation-defined Hom comparison with arbitrary second input.
- `podCartesianSystemHomReduction`: the full scalar-extension/evaluation transpose word.
- `PodSystemHomReindexing`: normalized simultaneous product-Hom representative.
- `PodSystemHomReductionSquare`: actual ambient beta square, before realization.

## Main statements

- `podReindexingSystemHomReductionSquare`: exact equivalences, representatives, cartesian
  evaluations, reduction naturality and reduction/limit adjunction compatibility.

The index n denotes exponent n+1. All systems are modules on the recorded sequence site.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Evaluation's canonical closed transpose, with no condition on either input in its
construction. For a cartesian first input it is the semilinear Hom evaluation isomorphism.
Source: Zheng 4.10; Stacks 08J9, node Step 5
(blueprint: lem-pod-reindexing-system-hom-reduction-square). -/
def podCartesianSystemHomFiber (W : Scheme.{u}) (n : ℕ)
    (M N : coefficientSequenceDerived l E W) :=
  coefficientBaseChangeHom (pullbackTensorCalculus l E W).systemClosed
    ((pullbackTensorCalculus l E W).finiteClosed n)
    (coefficientSequenceDerivedEvaluation l E W n)
    ((pullbackTensorCalculus l E W).evaluationTensor n) M N

/-- The full reduction word: inverse first transition, inverse scalar tensor comparison,
scalar extension of finite evaluation, then the unrestricted second transition, transposed.
Source: Zheng 4.10; Stacks 08J9, node Step 5
(blueprint: lem-pod-reindexing-system-hom-reduction-square). -/
def podCartesianSystemHomReduction (W : Scheme.{u})
    (M N : coefficientSequenceDerived l E W)
    (hM : IsNormalizedCoefficientSequence l E W M) {m n : ℕ} (h : n ≤ m) :=
  ((pullbackTensorCalculus l E W).finiteClosed n).transpose _ _ _
    (((pullbackTensorCalculus l E W).finiteClosed n).tensor.map
        (Prod.mkHom (𝟙 _)
          (coefficientSequenceNormalizationIso l E W
            (pullbackTensorCalculus l E W).toCoefficientDerivedSystemTensors
            (pullbackTensorCalculus l E W).quotientCalculus h M hM).inv) ≫
      ((pullbackTensorCalculus l E W).quotientCalculus.tensor h).inv.app
        ((coefficientFiniteInternalHom l E W m).obj
          (op ((coefficientSequenceDerivedEvaluation l E W m).obj M),
            (coefficientSequenceDerivedEvaluation l E W m).obj N),
          (coefficientSequenceDerivedEvaluation l E W m).obj M) ≫
      (coefficientFiniteQuotientDerived l E W h).map
        (((pullbackTensorCalculus l E W).finiteClosed m).evaluation
          ((coefficientSequenceDerivedEvaluation l E W m).obj M)
          ((coefficientSequenceDerivedEvaluation l E W m).obj N)) ≫
      coefficientSequenceTransitionAdjoint l E W
        (pullbackTensorCalculus l E W).toCoefficientDerivedSystemTensors
        (pullbackTensorCalculus l E W).quotientCalculus h N)

variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]

/-- Product-Hom reindexing on simultaneous system complexes, normalized on slice maps,
product projections and the specified K-injective localization comparison.
Source: Stacks 0GMX, 0A8X and 0A95; node Steps 3--4
(blueprint: lem-pod-reindexing-system-hom-reduction-square). -/
structure PodSystemHomReindexing where
  /-- Ordinary sheaf Hom is reindexed, including all horizontal restrictions. -/
  sheafHom : ∀ M N : coefficientSequenceModules l E Y,
    (pullbackTensorSequenceInverse l E g).obj
        (SheafOfModules.homObj (R := coefficientSequenceCommRingSheaf l E Y) M N) ≅
      SheafOfModules.homObj (R := coefficientSequenceCommRingSheaf l E X)
        ((pullbackTensorSequenceInverse l E g).obj M)
        ((pullbackTensorSequenceInverse l E g).obj N)
  /-- On local slice maps the comparison evaluates the same relabeled homomorphism. -/
  sheafHom_sections : ∀ (M N : coefficientSequenceModules l E Y)
    (U V : ℕ × Y.ProEt) (a : V ⟶ U)
    (f : (SheafOfModules.homObj (R := coefficientSequenceCommRingSheaf l E Y)
      M N).val.obj (op U)) (x : M.val.obj (op V)),
    (((sheafHom M N).hom.val.app (op ((pullbackTensorSequenceBase g).obj U))
      (((pullbackTensorSequenceAdjunction l E g).unit.app
        (SheafOfModules.homObj (R := coefficientSequenceCommRingSheaf l E Y)
          M N)).val.app (op U) f)).app
        (op (Over.mk ((pullbackTensorSequenceBase g).map a)))).hom
          (((pullbackTensorSequenceAdjunction l E g).unit.app M).val.app (op V) x) =
      ((pullbackTensorSequenceAdjunction l E g).unit.app N).val.app (op V)
        ((f.app (op (Over.mk a))).hom x)
  /-- The isomorphism is a chain map for the signed product-Hom differential. -/
  chain : ∀ K I : CochainComplex (coefficientSequenceModules l E Y) ℤ,
    ((pullbackTensorSequenceInverse l E g).mapHomologicalComplex (.up ℤ)).obj
        (homComplex (R := coefficientSequenceCommRingSheaf l E Y) K I) ≅
      homComplex (R := coefficientSequenceCommRingSheaf l E X)
        (((pullbackTensorSequenceInverse l E g).mapHomologicalComplex (.up ℤ)).obj K)
        (((pullbackTensorSequenceInverse l E g).mapHomologicalComplex (.up ℤ)).obj I)
  /-- Every product projection is exactly reindexed, without a boundedness assumption. -/
  chain_projection : ∀ (K I : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (r p : ℤ),
    (chain K I).hom.f r ≫ homComplexπ (R := coefficientSequenceCommRingSheaf l E X)
        (((pullbackTensorSequenceInverse l E g).mapHomologicalComplex (.up ℤ)).obj K)
        (((pullbackTensorSequenceInverse l E g).mapHomologicalComplex (.up ℤ)).obj I)
        r p (p + r) rfl =
      (pullbackTensorSequenceInverse l E g).map
          (homComplexπ (R := coefficientSequenceCommRingSheaf l E Y) K I
            r p (p + r) rfl) ≫ (sheafHom (K.X p) (I.X (p + r))).hom
  /-- The prescribed derived comparison is the localization of this simultaneous model. -/
  derived_model : ∀ (K I : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (hI : I.IsKInjective),
    ∃ hFI : CochainComplex.IsKInjective
      (((pullbackTensorSequenceInverse l E g).mapHomologicalComplex (.up ℤ)).obj I),
      podSystemHomComparison l E g (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj I) =
        (pullbackTensorSequenceDerived l E g).map
          (@podKInjectiveHomModel.{u, u+1, u, u+2} _ _
            (coefficientSequenceTopology (Scheme.ProEt.topology Y)) _ _
            (coefficientSequenceCommRingSheaf l E Y) _ K I hI).hom ≫
        (pullbackTensorSequenceInverse l E g).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map (chain K I).hom ≫
        (@podKInjectiveHomModel.{u, u+1, u, u+2} _ _
          (coefficientSequenceTopology (Scheme.ProEt.topology X)) _ _
          (coefficientSequenceCommRingSheaf l E X) _
          (((pullbackTensorSequenceInverse l E g).mapHomologicalComplex (.up ℤ)).obj K)
          (((pullbackTensorSequenceInverse l E g).mapHomologicalComplex (.up ℤ)).obj I)
          hFI).inv ≫
        (coefficientSequenceInternalHom l E X).map
          (Prod.mkHom
            ((pullbackTensorSequenceInverse l E g).mapDerivedCategoryFactors.hom.app K).op
            ((pullbackTensorSequenceInverse l E g).mapDerivedCategoryFactors.inv.app I))

/-- The ordinary ambient tensor comparison is pinned on local pure tensors; its derived
comparison is fixed on every flat-term K-flat representative by TensorComparisonModel.
Source: Stacks 03EL, 07A4; node Step 6
(blueprint: lem-pod-reindexing-system-hom-reduction-square).
Proof: sectionwise inverse image preserves the sheafified pure tensor and each signed
summand of total tensor. Exact inverse reindexing preserves flat-term K-flat complexes.
Localize that comparison through the K-flat resolving category. Its ordinary generator
formula and the resolving localization give uniqueness. This is the ambient part of
lem-sfb-ringed-derived-monoidal-comparisons and lem-pod-reindexing-hom-resolution-model. -/
theorem podAmbientReindexingTensor_existsUnique :
    ∃! μ : (pullbackTensorCalculus l E Y).integralClosed.tensor ⋙
        podCompletedDerivedInverseImage l E g ≅
      (podCompletedDerivedInverseImage l E g).prod
        (podCompletedDerivedInverseImage l E g) ⋙
          (pullbackTensorCalculus l E X).integralClosed.tensor,
      ∃ T : SemilinearSections.TensorComparisonModel.{u+1, u, u}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l E Y)
        (completedIntegralCommRingSheafUnrestricted l E X)
        (podCompletedModuleInverseImage l E g)
        (pullbackTensorCalculus l E Y).integralClosed
        (pullbackTensorCalculus l E X).integralClosed
        (pullbackTensorCalculus l E Y).integralTensorModel
        (pullbackTensorCalculus l E X).integralTensorModel μ,
        ∀ (M N : integralTowerModules l E Y) (U : X.ProEt)
          (x : M.val.obj (op ((Scheme.proEtaleIsoPostcompose g).obj U)))
          (y : N.val.obj (op ((Scheme.proEtaleIsoPostcompose g).obj U))),
          (T.ordinary M N).hom.val.app (op U)
            (SemilinearSections.tensorSection.{u+1, u, u} (Scheme.ProEt.topology Y)
              (completedIntegralCommRingSheafUnrestricted l E Y) M N
              (op ((Scheme.proEtaleIsoPostcompose g).obj U)) x y) =
            SemilinearSections.tensorSection.{u+1, u, u} (Scheme.ProEt.topology X)
              (completedIntegralCommRingSheafUnrestricted l E X)
              ((podCompletedModuleInverseImage l E g).obj M)
              ((podCompletedModuleInverseImage l E g).obj N) (op U) x y := by
  obtain ⟨e, hn, hp⟩ := podCompletedOrdinaryTensor_exists l E g
  let F := podCompletedModuleInverseImage l E g
  have : F.IsEquivalence := (podCompletedInverseImage_equivalence l E g).1
  obtain ⟨μ, T, hT⟩ := SemilinearSections.modelOfOrdinary.{u + 1, u, u}
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (completedIntegralCommRingSheafUnrestricted l E Y)
    (completedIntegralCommRingSheafUnrestricted l E X)
    F F.inv F.asEquivalence.toAdjunction
    (pullbackTensorCalculus l E Y).integralClosed
    (pullbackTensorCalculus l E X).integralClosed
    (pullbackTensorCalculus l E Y).integralTensorModel
    (pullbackTensorCalculus l E X).integralTensorModel e hn
    (podCompletedKFlatTransport l E g)
  refine ⟨μ, ⟨T, ?_⟩, ?_⟩
  · simpa only [hT] using hp
  · intro ν hν
    obtain ⟨S, hS⟩ := hν
    have ho : S.ordinary = T.ordinary := by
      rw [hT]
      funext M N
      apply Iso.ext
      apply (cancel_epi (e M N).inv).1
      apply SemilinearSections.tensor_hom_ext.{u + 1, u, u}
        (Scheme.ProEt.topology X)
        ((podCompletedModuleInverseImage l E g).obj M)
        ((podCompletedModuleInverseImage l E g).obj N)
      intro U x y
      have he := hp M N U.unop x y
      have hs := hS M N U.unop x y
      have hi := congrArg ((e M N).inv.val.app U) he
      have hei : (e M N).inv.val.app U
          (SemilinearSections.tensorSection.{u + 1, u, u} (Scheme.ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted l E X)
            ((podCompletedModuleInverseImage l E g).obj M)
            ((podCompletedModuleInverseImage l E g).obj N) U x y) =
          SemilinearSections.tensorSection.{u + 1, u, u} (Scheme.ProEt.topology Y)
            (completedIntegralCommRingSheafUnrestricted l E Y) M N
            (op ((Scheme.proEtaleIsoPostcompose g).obj U.unop)) x y := by
        have hc := congrArg (fun f ↦ f.val.app U
          (SemilinearSections.tensorSection.{u + 1, u, u} (Scheme.ProEt.topology Y)
            (completedIntegralCommRingSheafUnrestricted l E Y) M N
            (op ((Scheme.proEtaleIsoPostcompose g).obj U.unop)) x y)) (e M N).hom_inv_id
        exact hi.symm.trans hc
      change (S.ordinary M N).hom.val.app U ((e M N).inv.val.app U _) =
        (e M N).hom.val.app U ((e M N).inv.val.app U _)
      rw [hei]
      exact hs.trans he.symm
    exact (TensorModelUniqueness.tensorComparisonModel_unique.{u + 1, u, u}
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted l E Y)
      (completedIntegralCommRingSheafUnrestricted l E X)
      F (pullbackTensorCalculus l E Y).integralClosed
      (pullbackTensorCalculus l E X).integralClosed
      (pullbackTensorCalculus l E Y).integralTensorModel
      (pullbackTensorCalculus l E X).integralTensorModel ν μ S T ho).1

/-- The unique pure-tensor and K-flat normalized ambient tensor comparison.
Source: Stacks 03EL, 07A4; node Step 6
(blueprint: lem-pod-reindexing-system-hom-reduction-square). -/
def podCompletedAmbientTensor := (podAmbientReindexingTensor_existsUnique l E g).exists.choose

/-- Top followed by right in the unrestricted ambient reduction-Hom square.
Source: Stacks 08J9, 07A6; node Steps 6--7
(blueprint: lem-pod-reindexing-system-hom-reduction-square). -/
def podSystemHomReductionLeft (M N : DerivedCategory (integralTowerModules l E Y)) :=
  (pullbackTensorCalculus l E X).reduction.map
      (coefficientBaseChangeHom (pullbackTensorCalculus l E Y).integralClosed
        (pullbackTensorCalculus l E X).integralClosed
        (podCompletedDerivedInverseImage l E g)
        (podCompletedAmbientTensor l E g) M N) ≫
    coefficientBaseChangeHom (pullbackTensorCalculus l E X).integralClosed
      (pullbackTensorCalculus l E X).systemClosed (pullbackTensorCalculus l E X).reduction
      (pullbackTensorCalculus l E X).reductionTensor
      ((podCompletedDerivedInverseImage l E g).obj M)
      ((podCompletedDerivedInverseImage l E g).obj N)

/-- Left followed by bottom, including the canonical input identifications.
Source: Stacks 08J9, 07A6; node Steps 6--7
(blueprint: lem-pod-reindexing-system-hom-reduction-square). -/
def podSystemHomReductionRight (M N : DerivedCategory (integralTowerModules l E Y)) :=
  (podReductionReindexing l E g
    ((coefficientIntegralInternalHom l E Y).obj (op M, N))).hom ≫
    (pullbackTensorSequenceDerived l E g).map
      (coefficientBaseChangeHom (pullbackTensorCalculus l E Y).integralClosed
        (pullbackTensorCalculus l E Y).systemClosed (pullbackTensorCalculus l E Y).reduction
        (pullbackTensorCalculus l E Y).reductionTensor M N) ≫
    podSystemHomComparison l E g ((pullbackTensorCalculus l E Y).reduction.obj M)
      ((pullbackTensorCalculus l E Y).reduction.obj N) ≫
    (coefficientSequenceInternalHom l E X).map
      (Prod.mkHom (podReductionReindexing l E g M).hom.op
        (podReductionReindexing l E g N).inv)

/-- The ambient beta square for arbitrary completed-ring complexes. Its four sides
are the specified closed comparisons, reduction adjuncts and coefficient identifications.
Source: Stacks 08J9, 07A6; node Steps 6--7
(blueprint: lem-pod-reindexing-system-hom-reduction-square). -/
def PodSystemHomReductionSquare : Prop :=
  ∀ M N : DerivedCategory (integralTowerModules l E Y),
    podSystemHomReductionLeft l E g M N = podSystemHomReductionRight l E g M N

/-- Cartesian first-input evaluation and the unrestricted second-input transition.
Source: Zheng 4.10; Stacks 08J9, 0941; node Step 5
(blueprint: lem-pod-reindexing-system-hom-reduction-square). -/
structure PodCartesianSystemHomCalculus (W : Scheme.{u}) : Prop where
  /-- Only the first input must be cartesian. -/
  fiber_isIso : ∀ (M N : coefficientSequenceDerived l E W),
    IsNormalizedCoefficientSequence l E W M →
      ∀ n : ℕ, IsIso (podCartesianSystemHomFiber l E W n M N)
  /-- The actual system transition is precisely the full displayed transpose word. -/
  reduction : ∀ (M N : coefficientSequenceDerived l E W)
    (hM : IsNormalizedCoefficientSequence l E W M) {m n : ℕ} (h : n ≤ m),
    coefficientSequenceTransitionAdjoint l E W
        (pullbackTensorCalculus l E W).toCoefficientDerivedSystemTensors
        (pullbackTensorCalculus l E W).quotientCalculus h
        ((coefficientSequenceInternalHom l E W).obj (op M, N)) ≫
      podCartesianSystemHomFiber l E W n M N =
    (coefficientFiniteQuotientDerived l E W h).map
        (podCartesianSystemHomFiber l E W m M N) ≫
      podCartesianSystemHomReduction l E W M N hM h
  /-- The evaluation-defined fiber map preserves every transpose. -/
  transpose : ∀ n : ℕ,
    CoefficientEvaluationCompatible (pullbackTensorCalculus l E W).systemClosed
      ((pullbackTensorCalculus l E W).finiteClosed n)
      (coefficientSequenceDerivedEvaluation l E W n)
      ((pullbackTensorCalculus l E W).evaluationTensor n)

variable [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Naturality at cartesian fibers and along every scalar reduction, with arbitrary
second input. All maps are the already specified finite comparisons.
Source: Stacks 08J9, 07A4, 0941; node Step 5
(blueprint: lem-pod-reindexing-system-hom-reduction-square). -/
structure PodCartesianSystemHomReindexing : Prop where
  /-- Reindexing keeps the actual cartesian transition invertible. -/
  normalized : ∀ M : coefficientSequenceDerived l E Y,
    IsNormalizedCoefficientSequence l E Y M →
      IsNormalizedCoefficientSequence l E X ((pullbackTensorSequenceDerived l E g).obj M)
  /-- Finite evaluation gives exactly c^0, without normalizing the second input. -/
  fiber : ∀ (M N : coefficientSequenceDerived l E Y)
    (_hM : IsNormalizedCoefficientSequence l E Y M) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E X n).map (podSystemHomComparison l E g M N) ≫
      podCartesianSystemHomFiber l E X n
        ((pullbackTensorSequenceDerived l E g).obj M)
        ((pullbackTensorSequenceDerived l E g).obj N) =
    (pullbackTensorDerivedEvaluation l E g n).hom.app
        ((coefficientSequenceInternalHom l E Y).obj (op M, N)) ≫
      (finiteDerivedPullback l E n g).map (podCartesianSystemHomFiber l E Y n M N) ≫
      podFiniteHomComparison l E g n
        ((coefficientSequenceDerivedEvaluation l E Y n).obj M)
        ((coefficientSequenceDerivedEvaluation l E Y n).obj N) ≫
      (coefficientFiniteInternalHom l E X n).map
        (Prod.mkHom ((pullbackTensorDerivedEvaluation l E g n).hom.app M).op
          ((pullbackTensorDerivedEvaluation l E g n).inv.app N))
  /-- Scalar extension and both input transitions commute as actual derived maps. -/
  transition : ∀ (N : coefficientSequenceDerived l E Y) {m n : ℕ} (h : n ≤ m),
    (coefficientFiniteQuotientDerived l E X h).map
        ((pullbackTensorDerivedEvaluation l E g m).inv.app N) ≫
      coefficientSequenceTransitionAdjoint l E X
        (pullbackTensorCalculus l E X).toCoefficientDerivedSystemTensors
        (pullbackTensorCalculus l E X).quotientCalculus h
        ((pullbackTensorSequenceDerived l E g).obj N) =
    (pullbackTensorQuotient l E g h).hom.app
        ((coefficientSequenceDerivedEvaluation l E Y m).obj N) ≫
      (finiteDerivedPullback l E n g).map
        (coefficientSequenceTransitionAdjoint l E Y
          (pullbackTensorCalculus l E Y).toCoefficientDerivedSystemTensors
          (pullbackTensorCalculus l E Y).quotientCalculus h N) ≫
      (pullbackTensorDerivedEvaluation l E g n).inv.app N
  /-- The entire scalar-extension/inverse-transition/evaluation word is preserved. -/
  reduction : ∀ (M N : coefficientSequenceDerived l E Y)
    (hM : IsNormalizedCoefficientSequence l E Y M) {m n : ℕ} (h : n ≤ m),
    (coefficientFiniteQuotientDerived l E X h).map
        (podFiniteHomComparison l E g m
          ((coefficientSequenceDerivedEvaluation l E Y m).obj M)
          ((coefficientSequenceDerivedEvaluation l E Y m).obj N) ≫
        (coefficientFiniteInternalHom l E X m).map
          (Prod.mkHom ((pullbackTensorDerivedEvaluation l E g m).hom.app M).op
            ((pullbackTensorDerivedEvaluation l E g m).inv.app N))) ≫
      podCartesianSystemHomReduction l E X
        ((pullbackTensorSequenceDerived l E g).obj M)
        ((pullbackTensorSequenceDerived l E g).obj N) (normalized M hM) h =
    (pullbackTensorQuotient l E g h).hom.app
        ((coefficientFiniteInternalHom l E Y m).obj
          (op ((coefficientSequenceDerivedEvaluation l E Y m).obj M),
            (coefficientSequenceDerivedEvaluation l E Y m).obj N)) ≫
      (finiteDerivedPullback l E n g).map
        (podCartesianSystemHomReduction l E Y M N hM h) ≫
      podFiniteHomComparison l E g n
        ((coefficientSequenceDerivedEvaluation l E Y n).obj M)
        ((coefficientSequenceDerivedEvaluation l E Y n).obj N) ≫
      (coefficientFiniteInternalHom l E X n).map
        (Prod.mkHom ((pullbackTensorDerivedEvaluation l E g n).hom.app M).op
          ((pullbackTensorDerivedEvaluation l E g n).inv.app N))

/-- The specified reduction/limit unit and counit squares before any realization.
Source: Stacks 07A6, 0941; node Step 8
(blueprint: lem-pod-reindexing-system-hom-reduction-square). -/
structure PodSystemAdjunctionReindexing : Prop where
  /-- The two reconstruction-unit maps agree under rho and lambda. -/
  unit : ∀ M : DerivedCategory (integralTowerModules l E Y),
    (podCompletedDerivedInverseImage l E g).map
        ((pullbackTensorCalculus l E Y).adjunction.unit.app M) ≫
      (podLimitReindexing l E g).inv.app ((pullbackTensorCalculus l E Y).reduction.obj M) =
    (pullbackTensorCalculus l E X).adjunction.unit.app
        ((podCompletedDerivedInverseImage l E g).obj M) ≫
      (coefficientSequenceLimit l E X).map (podReductionReindexing l E g M).hom
  /-- The counit equality is an equality of actual system maps. -/
  counit : ∀ N : coefficientSequenceDerived l E Y,
    (podReductionReindexing l E g ((coefficientSequenceLimit l E Y).obj N)).hom ≫
      (pullbackTensorSequenceDerived l E g).map
        ((pullbackTensorCalculus l E Y).adjunction.counit.app N) =
    (pullbackTensorCalculus l E X).reduction.map ((podLimitReindexing l E g).inv.app N) ≫
      (pullbackTensorCalculus l E X).adjunction.counit.app
        ((pullbackTensorSequenceDerived l E g).obj N)

/-- All assertions take place in the actual abelian and unbounded derived system categories.
Every comparison is the evaluation-defined one or has a representative characterization.
Source: blueprint dual-Tate compatibility Step 5; node Steps 1--8
(blueprint: lem-pod-reindexing-system-hom-reduction-square). -/
structure PodSystemReindexingLaws : Prop where
  /-- Exact reindexing with the original horizontal index and coefficient maps. -/
  equivalence : (pullbackTensorSequenceInverse l E g).IsEquivalence
  /-- The induced functor is an equivalence of ordinary unbounded localizations. -/
  derived_equivalence : (pullbackTensorSequenceDerived l E g).IsEquivalence
  /-- K-injectivity is preserved in the system category itself. -/
  kinjective : ∀ I : CochainComplex (coefficientSequenceModules l E Y) ℤ,
    I.IsKInjective → CochainComplex.IsKInjective
      (((pullbackTensorSequenceInverse l E g).mapHomologicalComplex (.up ℤ)).obj I)
  /-- K-flatness is tested by the actual sheafified signed total tensor. -/
  kflat : ∀ K : CochainComplex (coefficientSequenceModules l E Y) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) K →
    CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology X))
      (R := coefficientSequenceCommRingSheaf l E X)
      (((pullbackTensorSequenceInverse l E g).mapHomologicalComplex (.up ℤ)).obj K)
  /-- Actual natural internal-Hom isomorphism, with its specified component maps. -/
  hom : ∃ c : coefficientSequenceInternalHom l E Y ⋙ pullbackTensorSequenceDerived l E g ≅
      (pullbackTensorSequenceDerived l E g).op.prod
        (pullbackTensorSequenceDerived l E g) ⋙ coefficientSequenceInternalHom l E X,
    ∀ M N : coefficientSequenceDerived l E Y,
      c.hom.app (op M, N) = podSystemHomComparison l E g M N
  /-- The product-Hom representative, including the actual signed differential. -/
  representative : Nonempty (PodSystemHomReindexing l E g)
  /-- Naturality, all transposes and composition as actual system identities. -/
  compatible : CoefficientEvaluationCompatible
    (pullbackTensorCalculus l E Y).systemClosed
    (pullbackTensorCalculus l E X).systemClosed (pullbackTensorSequenceDerived l E g)
    (pullbackTensorSystemComparison l E g)
  /-- The specified system evaluation is carried to the specified evaluation. -/
  evaluation : ∀ M N : coefficientSequenceDerived l E Y,
    (pullbackTensorSystemComparison l E g).hom.app
        ((coefficientSequenceInternalHom l E Y).obj (op M, N), M) ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom (podSystemHomComparison l E g M N) (𝟙 _)) ≫
      (pullbackTensorCalculus l E X).systemClosed.evaluation
        ((pullbackTensorSequenceDerived l E g).obj M)
        ((pullbackTensorSequenceDerived l E g).obj N) =
    (pullbackTensorSequenceDerived l E g).map
      ((pullbackTensorCalculus l E Y).systemClosed.evaluation M N)
  /-- Cartesian evaluation and the transition word on Y, with arbitrary second input. -/
  cartesianY : PodCartesianSystemHomCalculus l E Y
  /-- The same actual evaluation and transition word on X. -/
  cartesianX : PodCartesianSystemHomCalculus l E X
  /-- Reindexing commutes with the whole finite reduction word. -/
  cartesian : PodCartesianSystemHomReindexing l E g
  /-- Arbitrary ambient inputs, with no claim that beta is invertible. -/
  beta : PodSystemHomReductionSquare l E g
  /-- Both reduction/limit adjunction squares are actual identities. -/
  adjunction : PodSystemAdjunctionReindexing l E g

/- Reindexing is an exact equivalence on actual coefficient systems; its natural
product-Hom isomorphism has the prescribed cartesian fibers, full reduction word,
arbitrary-input beta square and reduction/limit adjunction compatibilities.
Source: current blueprint prop-pod-dual-tate-data-compatibility, proof Step 5;
Stacks 0941, 0GMX, 0A8X, 0A95, 08J9, 07A4, 07A6
(blueprint: lem-pod-reindexing-system-hom-reduction-square).

Proof, following all nine steps of the node:
1. Apply lem-weil-proetale-isomorphism-inverse-image to the product site, fixing n and
all index arrows. The coefficient map is the same constant-section map at each level;
its completed map is induced by all quotient projections. Reverse relabeling is an
inverse, and componentwise exactness proves exactness.
2. Apply lem-sfb-exact-monoidal-equivalence-total-kflat and
lem-weil-pbc-right-adjoint-preserves-kinjective to the two exact inverse equivalences.
Their termwise unit and counit descend to the ordinary unbounded localizations.
3. Reindex slice-module maps, then every product factor in each Hom degree. The formula
d_I f - (-1)^r f d_K is unchanged. Use def-pur-derived-internal-hom and
lem-pur-rhom-well-defined to descend this simultaneous K-injective representative.
4. By lem-coef-ringed-pullback-hom-evaluation-comparison this is the transpose of the
transported evaluation: both representatives send f tensor x to f(x). The closed
adjunction of lem-sf-ringed-derived-closed-symmetric-monoidal gives uniqueness,
naturality and compatibility with every transpose, before any level evaluation.
5. Apply lem-coef-semilinear-derived-sections to cartesian first input and arbitrary
second input. Finite evaluation is c^0 of lem-pod-reindexing-evaluation-shift-composition.
Transport scalar extension, both input transitions, and the inverse first transition;
uniqueness of transpose gives exactly the full displayed reduction word.
6. Use lem-coef-sequence-projection-derived-adjunction and
lem-sfb-ringed-derived-monoidal-comparisons for rho. On a flat-term K-flat representative
it is the strict quotient-system comparison. The ambient comparison uses the same
ordinary evaluation, without completeness or constructibility hypotheses.
7. Uncurry both beta-square routes by lem-coef-derived-system-evaluation-calculus and
lem-coef-ringed-pullback-hom-evaluation-comparison. Both become reduction of transported
evaluation under the same tensor comparison. Re-curry in the system category itself.
8. Identify limit with the sequence pushforward by
lem-coef-sequence-pushforward-limit-projections. Reindex a whole K-injective system
resolution. By lem-coef-sequence-adjunction-cochain-transposes, the unit sends x to
(x tensor 1)_n and the counit sends x tensor b to b pr_n(q(x)); these strict system
formulas are invariant under reindexing, hence so are both derived adjunction squares.
9. Apply the functorial coefficientSequenceLimit to these already equal system arrows.
No equality detection by evaluations and no inverse of arbitrary beta is used. -/
/-- The actual system-level reindexing laws, isolated from their functorial realization.
Source: blueprint `prop-pod-dual-tate-data-compatibility`, proof Step 5;
Stacks 0941, 0GMX, 0A8X, 0A95, 08J9, 07A4, 07A6
(blueprint: new-e4-pod-system-reindexing-laws).

Proof: relabel the sequence site by the pro-etale equivalence induced by `g`, keeping
its inverse-sequence index and all quotient arrows fixed.  The resulting module functor
and the reverse relabelling are exact inverse equivalences, so their termwise derived
functor is an equivalence and transports K-injective and independent-coefficient
K-flat complexes.  Reindex every factor of the product Hom complex; its signed
differential is unchanged.  The transported evaluation is the same map on pure tensors,
so closedness and transpose uniqueness give the natural Hom comparison and all
compatibility identities.  The finite-level evaluation and scalar-reduction maps are
transported through this comparison, and transpose uniqueness gives the displayed
cartesian reduction word.  The ordinary tensor comparison is the unique pure-tensor
comparison; its K-flat representative identifies the two beta-square paths after
uncurrying.  Finally, the unit and counit formulas for reduction and total limit are
strictly preserved by relabelling, yielding the stated system adjunction squares. -/
theorem podReindexingSystemHomReductionSquare_laws :
    PodSystemReindexingLaws l E g := by
  sorry

end WeilConjectures
