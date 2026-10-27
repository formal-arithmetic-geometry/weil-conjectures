/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import Sheaf.Paper.CompletedCoefficientTransportExpressions

/-!
# Whole-system normalization of iterated coefficient transport

Source: blueprint main-20261015, lem-fix-operation-reduction.proof.md, final paragraph;
the dispatched transport item's proof steps 6--7 and 11
(blueprint: def-pur-completed-coefficient-system-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u s i j k m
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
namespace WeilConjectures.CompletedCoefficientTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {S : Type s} {W : S → Scheme.{t}} (T : Transport.{t, u, s, i, j} l E W)
  {I : Type k} {location : I → S}

/-- The actual reflector Hom inverse into a complete target. This is a construction
from the recorded bijection, so its augmentation determines it uniquely.
Source: Stacks 099I
(blueprint: def-pur-completed-coefficient-system-transport). -/
def reflectConstant {a : S} (K : DA l E (W a)) (N : DR l E (W a))
    (hN : completeR l E (W a) N)
    (f : K ⟶ (T.site a).U.functor.obj N) :
    (T.site a).completion.completion.obj K ⟶ (T.site a).U.functor.obj N :=
  (Equiv.ofBijective _ ((T.site a).a_reflect K ((T.site a).U.functor.obj N)
    ((T.site a).restrict_complete N |>.mp hN))).symm f

/-- Constant-side whole-expression comparison, built before using a or b. At a tensor
vertex, reflect the ordinary balancing map followed by the actual R completion unit
and the coherent-counit tensorComparison. At a pullback vertex, reflect the scalar-unit
mate tau, the actual completion unit, normalized Arrow.pullback and pullbackComparison.
Thus the finite change-of-rings and scalar-unit maps are applied to whole systems,
with every transition retained. No finite evaluation is used to detect equality.
Source: node proof steps 3--7
(blueprint: def-pur-completed-coefficient-system-transport). -/
def constantSystemComparison {I : Type i} {location : I → S} {a : S}
    (P : CompletedOperations.Expression W location a)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (hN : ∀ k, IsNormalizedCoefficientSequence l E _ (N k)) :
    ((valueA l E T P).obj (fun k ↦ ((T.site (location k)).restriction l E).obj
      ⟨_, T.system_complete _ (N k) (hN k)⟩)).obj ⟶
    (T.site a).U.functor.obj ((coefficientSequenceLimit l E (W a)).obj
      ((CompletedOperations.systemValue l E T.systems P).obj N)) :=
  match P with
  | .input _ => 𝟙 _
  | .unit a =>
      ((expressionTransport l E T (.unit a)
        (fun k ↦ ⟨_, T.system_complete _ (N k) (hN k)⟩)).hom).hom ≫
          (T.site a).U.functor.map ((T.site a).r_tensor.unit.hom ≫
            (T.system_unit a).hom)
  | .tensor P Q =>
      (T.site a).a_tensor.tensor.hom.app _ ≫
      reflectConstant l E T _ _
        (T.system_complete a _
          (T.system_comparison.normalized (.tensor P Q) N hN))
        ((T.site a).closed.closed.tensor.map
          (Prod.mkHom (constantSystemComparison P N hN) (constantSystemComparison Q N hN)) ≫
        (T.tensor a).balancing.app
          ((coefficientSequenceLimit l E (W a)).obj
              ((CompletedOperations.systemValue l E T.systems P).obj N),
            (coefficientSequenceLimit l E (W a)).obj
              ((CompletedOperations.systemValue l E T.systems Q).obj N)) ≫
        (T.site a).U.functor.map
          ((IntegralOnSlice.completionUnit l E (W a) none).app _ ≫
            CompletedOperations.tensorComparison l E T.systems a
              ((CompletedOperations.systemValue l E T.systems P).obj N)
              ((CompletedOperations.systemValue l E T.systems Q).obj N)))
  | .pullback f P =>
      reflectConstant l E T _ _
        (T.system_complete a _
          (T.system_comparison.normalized (.pullback f P) N hN))
        ((T.arrow f).a.left.map (constantSystemComparison P N hN) ≫
          (T.arrow f).tau l E _ ≫ (T.site a).U.functor.map
            ((IntegralOnSlice.completionUnit l E (W a) none).app _ ≫
              (T.arrow f).pullback.hom.app _ ≫
                CompletedOperations.pullbackComparison l E T.systems f
                  ((CompletedOperations.systemValue l E T.systems P).obj N)))

/-- The iterated a/b comparison is the comparison induced on the entire system
expression, using the actual coherent counit comparison beta_P. This links the
recursion to the quotient construction, rather than merely asserting abstract
monoidal substitution. The accompanying system structural law records the coherent reduction square
using reductionComparison, including every quotient transition.
Source: node statement, iterated versions clause; proof steps 6--7
(blueprint: def-pur-completed-coefficient-system-transport). -/
def ExpressionSystemLaw : Prop :=
  ∀ {I : Type i} {location : I → S} {a : S}
    (P : CompletedOperations.Expression W location a)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (hN : ∀ k, IsNormalizedCoefficientSequence l E _ (N k)),
    ((expressionTransport l E T P
        (fun k ↦ ⟨_, T.system_complete _ (N k) (hN k)⟩)).hom).hom ≫
        (T.site a).U.functor.map
          ((valueRIdentification l E T P
            (fun k ↦ ⟨_, T.system_complete _ (N k) (hN k)⟩)).hom ≫
              CompletedOperations.comparison l E T.systems P N) =
      constantSystemComparison l E T P N hN

/-- The actual complete R structural maps, after recursive identification, satisfy
both the total-limit and whole-system reduction squares of the substitution theorem.
Source: node proof steps 6--7
(blueprint: def-pur-completed-coefficient-system-transport). -/
def ExpressionSystemStructuralLaw : Prop :=
  ∀ {I : Type i} {location : I → S} {a : S}
    {P Q : CompletedOperations.Expression W location a}
    (α : CompletedOperations.StructuralMap P Q)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (hN : ∀ k, IsNormalizedCoefficientSequence l E _ (N k)),
    (structureR l E T α (fun k ↦ ⟨_, T.system_complete _ (N k) (hN k)⟩)).hom.hom ≫
        (valueRIdentification l E T Q
          (fun k ↦ ⟨_, T.system_complete _ (N k) (hN k)⟩)).hom ≫
        CompletedOperations.comparison l E T.systems Q N =
      (valueRIdentification l E T P
        (fun k ↦ ⟨_, T.system_complete _ (N k) (hN k)⟩)).hom ≫
        CompletedOperations.comparison l E T.systems P N ≫
          (coefficientSequenceLimit l E (W a)).map
            (CompletedOperations.structuralValue l E T.systems α N).hom ∧
    (T.systems.calculus a).reduction.map
        ((valueRIdentification l E T P
          (fun k ↦ ⟨_, T.system_complete _ (N k) (hN k)⟩)).inv ≫
        (structureR l E T α (fun k ↦ ⟨_, T.system_complete _ (N k) (hN k)⟩)).hom.hom ≫
        (valueRIdentification l E T Q
          (fun k ↦ ⟨_, T.system_complete _ (N k) (hN k)⟩)).hom) ≫
        CompletedOperations.reductionComparison l E T.systems Q N =
      CompletedOperations.reductionComparison l E T.systems P N ≫
        (CompletedOperations.structuralValue l E T.systems α N).hom

end WeilConjectures.CompletedCoefficientTransport
