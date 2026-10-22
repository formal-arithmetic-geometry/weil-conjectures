/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q45 and F5
-/
module

public import Sheaf.Paper.CompletedOperationExpressions
public import Sheaf.Paper.IntegralComparisonRealizationModels
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.SemilinearDerivedSections
public import Mathlib.CategoryTheory.Pi.Basic

/-! # Simultaneous primitive models for completed operations

Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.9(4); blueprint
main-20261015, order 2232, coefficient twists; explicit coherent-counit refinement
in original proof steps 1--6 of completed-operation substitution
(blueprint: lem-pur-normalized-completed-operation-models).

All comparisons live in the ordinary derived category of the ringed sequence
site before restriction or total derived limit. The natural-number index n
means positive quotient exponent n+1. Site and coefficient universes are independent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u s i j
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
namespace WeilConjectures.CompletedOperations

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Compatible presentations of the *specified* operations. The tensor structures
are normalized on K-flat total complexes by RingedSiteDualityModel; the reduction
calculus fixes every quotient map and both adjunction projections. Completion's
comparison is pinned by the actual quotient/Roos augmentation. Pullback's
comparison is pinned on every simultaneous quotient presentation, not chosen
separately on evaluated objects.
Source: node proof steps 1, 4--5; Stacks 06YY, 07A4, 0941
(blueprint: lem-pur-completed-operation-tower-substitution). -/
structure Models {S : Type s} (W : S → Scheme.{t}) where
  /-- The recorded reduction/total-limit adjunction. -/
  calculus : ∀ a : S, CoefficientDerivedSystemCalculus l E (W a)
  /-- Canonical total tensor, action unit and signed interchange on whole systems. -/
  system : ∀ a : S, RingedSiteDualityModel.{t + 1, t, u, (max u (t + 1)) + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology (W a)))
    (coefficientSequenceCommRingSheaf l E (W a))
  /-- These are presentations of the same system closed tensor. -/
  system_closed : ∀ a : S, (system a).closed = (calculus a).systemClosed
  /-- The integral tensor is the recorded ordinary tensor used by completion. -/
  integral_closed : ∀ a : S,
    (calculus a).integralClosed = (IntegralOnSlice.duality l E (W a) none).closed
  /-- Completion as the reduction/total-limit composite. -/
  completion : ∀ a : S, IntegralOnSlice.completion l E (W a) none ≅
    (calculus a).reduction ⋙ coefficientSequenceLimit l E (W a)
  /-- Unit normalization determines this comparison, including its maps. -/
  completion_unit : ∀ (a : S) (K : DerivedCategory (scalarReductionSource l E (W a))),
    (IntegralOnSlice.completionUnit l E (W a) none).app K ≫
        (completion a).hom.app K = (calculus a).adjunction.unit.app K
  /-- The actual total-limit/Roos comparison with its K-injective normalization. -/
  roos : ∀ a : S, IntegralComparisonRoosModel l E (W a)
  /-- Pullback is normalized on all K-flat quotient presentations. -/
  pullback : ∀ {a b : S} (f : W a ⟶ W b),
    IntegralComparisonPullbackModel l E f (calculus b) (roos a)

variable {S : Type s} {W : S → Scheme.{t}} (M : Models l E W)

/-- The system tensor in the fixed canonical total-complex presentation.
Source: node proof steps 1--2 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def tensor (a : S) := (M.system a).closed.tensor

/-- The coefficient unit system B_n[0], including its actual quotient transitions.
Source: node proof steps 3 and 7 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def unit (a : S) : coefficientSequenceDerived l E (W a) :=
  ringedSiteDualityUnit.{t + 1, t, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology (W a)))
    (coefficientSequenceCommRingSheaf l E (W a))

/-- The defining quotient-limit tensor realization. Each factor is fixed by the
reduction tensor model, closed-tensor presentation, or completion augmentation.
Source: node proof step 5 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def tensorRealization (a : S) : IntegralOnSlice.completedTensor l E (W a) none ≅
    ((M.calculus a).reduction.prod (M.calculus a).reduction) ⋙
      tensor l E M a ⋙ coefficientSequenceLimit l E (W a) :=
  isoWhiskerLeft (IntegralOnSlice.duality l E (W a) none).closed.tensor (M.completion a) ≪≫
    isoWhiskerRight
      (isoWhiskerRight
        (eqToIso (congrArg CoefficientClosedStructure.tensor (M.integral_closed a).symm))
          (M.calculus a).reduction ≪≫
        (M.calculus a).reductionTensor ≪≫
        isoWhiskerLeft ((M.calculus a).reduction.prod (M.calculus a).reduction)
          (eqToIso (congrArg CoefficientClosedStructure.tensor (M.system_closed a).symm)))
      (coefficientSequenceLimit l E (W a))

/-- The primitive tensor comparison is L(T(e_A,e_N)), after its defining realization.
This is a formula using the coherent counit, before any invertibility assertion.
Source: node proof step 6 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def tensorComparison (a : S) (A N : coefficientSequenceDerived l E (W a)) :
    (IntegralOnSlice.completedTensor l E (W a) none).obj
        ((coefficientSequenceLimit l E (W a)).obj A,
         (coefficientSequenceLimit l E (W a)).obj N) ⟶
      (coefficientSequenceLimit l E (W a)).obj ((tensor l E M a).obj (A, N)) :=
  (tensorRealization l E M a).hom.app _ ≫
    (coefficientSequenceLimit l E (W a)).map
      ((tensor l E M a).map (Prod.mkHom
        ((M.calculus a).adjunction.counit.app A) ((M.calculus a).adjunction.counit.app N)))

/-- The primitive pullback comparison is L(F(e_C)), after quotient-model realization.
Source: node proof step 6 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def pullbackComparison {a b : S} (f : W a ⟶ W b)
    (C : coefficientSequenceDerived l E (W b)) :
    (integralDerivedPullback l E f).obj ((coefficientSequenceLimit l E (W b)).obj C) ⟶
      (coefficientSequenceLimit l E (W a)).obj
        ((integralComparisonDerivedSequencePullback l E f).obj C) :=
  (M.pullback f).realization.hom.app _ ≫
    (coefficientSequenceLimit l E (W a)).map
      ((integralComparisonDerivedSequencePullback l E f).map
        ((M.calculus b).adjunction.counit.app C))

/-- Normalization for the three primitive operations and effectivity of the
specified coherent counit. These assertions involve individual systems only.
Source: original proof steps 1--6 of completed-operation substitution; Stacks
07A4, 07A6 and 0941 (blueprint: lem-pur-normalized-completed-operation-models). -/
structure PrimitiveLaws : Prop where
  counit : ∀ (a : S) (N : coefficientSequenceDerived l E (W a)),
    IsNormalizedCoefficientSequence l E (W a) N →
      IsIso ((M.calculus a).adjunction.counit.app N)
  unit : ∀ a : S, IsNormalizedCoefficientSequence l E (W a) (unit l E (W := W) a)
  tensor : ∀ (a : S) (A N : coefficientSequenceDerived l E (W a)),
    IsNormalizedCoefficientSequence l E (W a) A →
    IsNormalizedCoefficientSequence l E (W a) N →
      IsNormalizedCoefficientSequence l E (W a) ((tensor l E M a).obj (A, N))
  pullback : ∀ {a b : S} (f : W a ⟶ W b) (N : coefficientSequenceDerived l E (W b)),
    IsNormalizedCoefficientSequence l E (W b) N →
      IsNormalizedCoefficientSequence l E (W a)
        ((integralComparisonDerivedSequencePullback l E f).obj N)

/-- Simultaneous quotient and Roos models with primitive normalization.
This is the construction part of completed-operation substitution; it makes no
assertion about finite expressions, naturality of their recursive comparisons,
simultaneous substitution, or transport of structural maps.

Source: Bhatt--Scholze Definition 3.4.10 and Lemma 6.5.9(4), with the
representative-normalized refinement in the original substitution proof steps
1--6; Stacks 07A4, 07A6, 0941
(blueprint: lem-pur-normalized-completed-operation-models).

Proof: choose the canonical closed total-tensor models on the integral and
sequence sites. Construct the reduction/total-limit adjunction by deriving the
ordinary quotient-system tensor adjunction, computing both sides on simultaneous
flat-term K-flat and K-injective resolutions. Use the normalized representative
comparisons to present the calculus with integral closed structure equal to the
specified IntegralOnSlice.duality, and the sequence closed structure equal to the
chosen system duality. Derive the strict quotient tower and apply the natural
Roos/total-limit comparison. On K-injectives this is the ordinary limit tuple
with zero shifted coordinate. This gives completion; the strict augmentation
identifies completionUnit with the adjunction unit. The finite inverse images of
one whole reduction diagram give the pullback realizations with exactly their
simultaneous quotient-presentation normalization. These constructions use one
Roos comparison at each scheme, hence work simultaneously for all morphisms.
The unit's transition adjunct is scalar multiplication with inverse insertion
of 1. Tensor transition adjuncts are monoidal scalar extension followed by the
tensor of the two input adjuncts. Pullback transition adjuncts are inverse scalar
association followed by inverse image of the input adjunct. Their quotient
cocycles hold before localization by scalar associativity. Thus these three
operations preserve normalization. Finally normalized-DVR effectivity applied to
the coherent reduction adjunction makes its actual counit invertible; its
finite components are the adjoints of the total-limit projections, so this is
the specified coherent counit, not independently chosen finite isomorphisms.
Empty families require no choices, and none of these computations assumes
boundedness, constructibility, or flatness of a quotient map. -/
theorem normalizedCompletedOperationModels {S : Type s} (W : S → Scheme.{t})
    (_hl : ∀ (a : S) (x : W a), IsUnit (l : (W a).residueField x)) :
    ∃ M : Models l E W, PrimitiveLaws l E M := by
  sorry

end WeilConjectures.CompletedOperations
