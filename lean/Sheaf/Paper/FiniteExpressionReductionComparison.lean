/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.Paper.IntegralReductionTowerCanonical
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.CompletedOperationExpressions
public import Sheaf.Paper.CompletedPrimitiveCounitComparison

/-! # Finite expression comparison and coherent reduction

Source: blueprint main-20261015, order 2232, coefficient twists, and the
agent-extracted finite-expression argument in steps 7--8 of
lem-pur-completed-operation-tower-substitution
(blueprint: lem-pur-finite-expression-reduction-comparison).

The realizations and primitive isomorphism hypotheses are supplied as the recorded
PrimitiveCounit.Comparisons, including their quotient-complex/Roos normalizations.
No structural constraints or substitution laws from the parent theorem are used.
A natural-number index n denotes the positive coefficient exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u s i
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.FiniteExpressionReduction
open CompletedOperations

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {S : Type s} (W : S → Scheme.{t})
  (D : ∀ a : S, CoefficientDerivedSystemReduction l E (W a))
  (ρ : ∀ a : S, PrimitiveCounit.RoosRealization l E (W a))
  (C : ∀ {a b : S} (f : W a ⟶ W b),
    PrimitiveCounit.Comparisons l E f (W a) (D a) (D b) (ρ a) (ρ a))

variable {I : Type i} {location : I → S}

/-- Evaluation in the actual whole-system tensor, geometric inverse image and unit.
This recursion preserves the expression's parentheses, output and repeated inputs.
Source: node paragraphs 1 and 3, proof steps 1--4; blueprint order 2232
(blueprint: lem-pur-finite-expression-reduction-comparison). -/
def systemValue {a : S} (N : ∀ k : I, coefficientSequenceDerived l E (W (location k))) :
    Expression W location a → coefficientSequenceDerived l E (W a)
  | .input k => N k
  | .unit a => ringedSiteDualityUnit.{t + 1, t, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology (W a)))
        (coefficientSequenceCommRingSheaf l E (W a))
  | .tensor P Q => (D a).systemClosed.tensor.obj (systemValue N P, systemValue N Q)
  | .pullback f P => (PrimitiveCounit.pull l E f).obj (systemValue N P)

/-- Evaluation on limits using the actual quotient-complex/Roos completed operations.
Source: node paragraph 3, proof steps 1--4; blueprint order 2232
(blueprint: lem-pur-finite-expression-reduction-comparison). -/
def completedValue {a : S}
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k))) :
    Expression W location a → DerivedCategory (scalarReductionSource l E (W a))
  | .input k => (coefficientSequenceLimit l E _).obj (N k)
  | .unit a => (coefficientSequenceLimit l E (W a)).obj (ringedSiteDualityUnit.{t + 1, t, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology (W a)))
        (coefficientSequenceCommRingSheaf l E (W a)))
  | .tensor P Q => (integralCompletedTensor l E (W a)).obj
      (completedValue N P, completedValue N Q)
  | .pullback f P => (integralDerivedPullback l E f).obj (completedValue N P)

/-- The prescribed beta: identities at leaves, functor images followed by the primitive
realization and counit comparison at each internal vertex. In particular the tensor
primitive is PrimitiveCounit.tensorBeta, not an arbitrary map between the same objects.
Source: node paragraph 3 and proof steps 2--4; blueprint order 2232
(blueprint: lem-pur-finite-expression-reduction-comparison). -/
def beta {a : S} (P : Expression W location a)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k))) :
    completedValue l E W N P ⟶
      (coefficientSequenceLimit l E (W a)).obj (systemValue l E W D N P) :=
  match P with
  | .input _ => 𝟙 _
  | .unit _ => 𝟙 _
  | .tensor P Q =>
      (integralCompletedTensor l E (W a)).map
        (Prod.mkHom (beta P N) (beta Q N)) ≫
      PrimitiveCounit.tensorBeta l E (W a) (D a) (C (𝟙 (W a))).tensor
        (systemValue l E W D N P) (systemValue l E W D N Q)
  | .pullback f P => (integralDerivedPullback l E f).map (beta P N) ≫
      PrimitiveCounit.pullBeta l E f (D _) (C f).geometric (systemValue l E W D N P)

/-- The whole-system gamma is R(beta) followed by the actual coherent adjunction counit.
It is constructed before evaluation, so its transition equation is genuine naturality.
Source: node paragraphs 3 and 5 and proof steps 5--6; blueprint order 2232
(blueprint: lem-pur-finite-expression-reduction-comparison). -/
def gamma {a : S} (P : Expression W location a)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k))) :
    (D a).reduction.obj (completedValue l E W N P) ⟶ systemValue l E W D N P :=
  (D a).reduction.map (beta l E W D ρ C P N) ≫
    (D a).adjunction.counit.app (systemValue l E W D N P)

/-- Finite typed expression induction with the prescribed recursive comparisons.
The primitive natural-isomorphism assumptions, and the canonical effective counits,
are the fields tensor_iso, geometric_iso and counit_effective of the recorded C.
The remaining three hypotheses say exactly that unit, tensor and pullback preserve
normalization; the input hypothesis applies to each input, with no distinctness condition.

Source: agent-extracted argument, blueprint main-20261015, order 2232,
finite reduction of coefficient twists
(blueprint: lem-pur-finite-expression-reduction-comparison).

Proof plan (the seven proof steps of the node):
1. Induct simultaneously over output locations on the number of operation symbols.
Inputs have size zero, units size one, tensors one plus both child sizes, and
pullbacks one plus the child size. Thus both tensor children are smaller.
2. At an input normalization is the input hypothesis and beta is the identity.
At a unit normalization is hUnit and beta is again the identity.
3. At a tensor, hTensor gives normalization from the two induction hypotheses.
The completed bifunctor sends the pair of child isomorphisms to an isomorphism;
its inverse is the image of their inverse pair. Compose with the specified
primitive tensorBeta, invertible by C.tensor_iso on the normalized children.
The inverse composite has the two factors in reverse order. No reassociation occurs.
4. At a pullback use hPull and the child hypothesis. Apply the completed functor
to the child comparison and its inverse, then compose with pullBeta, invertible
by C.geometric_iso. This proves normalization and beta invertibility in every case.
5. The adjunction in lem-coef-derived-system-evaluation-calculus gives the actual
system counit. By lem-coef-normalized-dvr-effectivity it is invertible on normalized
systems, as recorded in C.counit_effective (using the identity scheme map).
Reduction preserves the beta isomorphism, hence gamma is a whole-system isomorphism.
Its inverse is the inverse counit followed by reduction of the inverse beta.
6. Transitions are natural transformations on the ordinary derived system category
by lem-coef-semilinear-derived-sections. Compose the transition square of R(beta)
with that of the counit. Functoriality of restriction gives the displayed square
for their composite gamma, including identity quotients m=n. Equality is never
deduced from equality of evaluations.
7. No enumeration of scheme or input indices is used. Empty input contexts retain
unit expressions; an empty scheme context has no output-typed expressions.
Repeated inputs are independent occurrences. Parentheses remain fixed, and neither
faithfulness of reduction nor interchange of tensor with inverse limit is required. -/
theorem finiteExpressionReductionComparison
    (_hInvertible : ∀ (a : S) (x : W a), IsUnit (l : (W a).presheaf.stalk x))
    (hUnit : ∀ a : S, IsNormalizedCoefficientSequence l E (W a) (ringedSiteDualityUnit.{t + 1, t, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology (W a)))
        (coefficientSequenceCommRingSheaf l E (W a))))
    (hTensor : ∀ (a : S) (A B : coefficientSequenceDerived l E (W a)),
      IsNormalizedCoefficientSequence l E (W a) A →
      IsNormalizedCoefficientSequence l E (W a) B →
      IsNormalizedCoefficientSequence l E (W a) ((D a).systemClosed.tensor.obj (A, B)))
    (hPull : ∀ {a b : S} (f : W a ⟶ W b) (A : coefficientSequenceDerived l E (W b)),
      IsNormalizedCoefficientSequence l E (W b) A →
      IsNormalizedCoefficientSequence l E (W a) ((PrimitiveCounit.pull l E f).obj A))
    {a : S} (P : Expression W location a)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (hN : ∀ k : I, IsNormalizedCoefficientSequence l E (W (location k)) (N k)) :
    IsNormalizedCoefficientSequence l E (W a) (systemValue l E W D N P) ∧
      IsIso (beta l E W D ρ C P N) ∧ IsIso (gamma l E W D ρ C P N) ∧
      (∀ {m n : ℕ} (h : n ≤ m),
        (coefficientSequenceDerivedEvaluation l E (W a) m).map (gamma l E W D ρ C P N) ≫
            (coefficientSequenceDerivedTransition l E (W a) h).app (systemValue l E W D N P) =
          (coefficientSequenceDerivedTransition l E (W a) h).app
              ((D a).reduction.obj (completedValue l E W N P)) ≫
            (normalizedDVRRes l E (W a) h).map
              ((coefficientSequenceDerivedEvaluation l E (W a) n).map
                (gamma l E W D ρ C P N))) := by
  have h : IsNormalizedCoefficientSequence l E (W a) (systemValue l E W D N P) ∧
      IsIso (beta l E W D ρ C P N) := by
    induction P with
    | input k =>
        refine ⟨hN k, ?_⟩
        dsimp only [beta]
        infer_instance
    | unit a =>
        refine ⟨hUnit a, ?_⟩
        dsimp only [beta]
        infer_instance
    | @tensor a P Q hP hQ =>
        have := hP.2
        have := hQ.2
        have := (C (𝟙 (W a))).tensor_iso
          (systemValue l E W D N P) (systemValue l E W D N Q) hP.1 hQ.1
        have : IsIso (Prod.mkHom (beta l E W D ρ C P N) (beta l E W D ρ C Q N)) :=
          (isIso_prod_iff (f := _)).mpr ⟨hP.2, hQ.2⟩
        refine ⟨hTensor a _ _ hP.1 hQ.1, ?_⟩
        dsimp only [beta]
        infer_instance
    | @pullback a b f P hP =>
        have := hP.2
        have := (C f).geometric_iso (systemValue l E W D N P) hP.1
        refine ⟨hPull f _ hP.1, ?_⟩
        dsimp only [beta]
        infer_instance
  have := h.2
  have := (C (𝟙 (W a))).counit_effective (systemValue l E W D N P) h.1
  refine ⟨h.1, h.2, ?_, ?_⟩
  · dsimp only [gamma]
    infer_instance
  · intro m n hmn
    exact (coefficientSequenceDerivedTransition l E (W a) hmn).naturality
      (gamma l E W D ρ C P N)

end WeilConjectures.FiniteExpressionReduction
