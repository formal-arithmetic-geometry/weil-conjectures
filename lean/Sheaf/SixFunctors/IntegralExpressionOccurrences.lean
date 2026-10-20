/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.SixFunctors.IntegralSystemExpressionDomain

/-! # Independent leaf occurrences in an integral-system expression

Source: blueprint, adic transport in sk-thm-purity-transport, Step 2; independent
occurrence-slot convention of lem-pur-integral-realization-shift-coherence
(blueprint: def-pur-integral-expression-occurrences).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

/-- Rename the variables of the existing expression, preserving every operation.
Source: blueprint, adic expression trees
(blueprint: def-pur-integral-expression-occurrences). -/
def Expression.reindexInputs {B : Scheme.{u}} {I J : Type u} {Y : J → Over B}
    (f : I → J) : {W : Over B} → Expression B I (Y ∘ f) W → Expression B J Y W
  | _, .var i => .var (f i)
  | _, .pull g e => .pull g (e.reindexInputs f)
  | _, .push g hp e => .push g hp (e.reindexInputs f)
  | _, .shriek j hj hq e => .shriek j hj hq (e.reindexInputs f)
  | _, .compactSupport g c e => .compactSupport g c (e.reindexInputs f)
  | _, .tensor e t => .tensor (e.reindexInputs f) (t.reindexInputs f)

/-- Each leaf contributes its own singleton, and a tensor contributes a disjoint
sum. In particular two occurrences of the same variable give different elements.
Source: blueprint, independent occurrence slots
(blueprint: def-pur-integral-expression-occurrences). -/
def Expression.Occurrences {B : Scheme.{u}} {I : Type u} {X : I → Over B} :
    {W : Over B} → Expression B I X W → Type u
  | _, .var _ => PUnit.{u + 1}
  | _, .pull _ e => e.Occurrences
  | _, .push _ _ e => e.Occurrences
  | _, .shriek _ _ _ e => e.Occurrences
  | _, .compactSupport _ _ e => e.Occurrences
  | _, .tensor e t => e.Occurrences ⊕ t.Occurrences

/-- Finite trees have finitely many independent leaf occurrences, regardless of
unused labels in the original index type.
Source: blueprint, finite expressions
(blueprint: def-pur-integral-expression-occurrences). -/
instance Expression.finiteOccurrences {B : Scheme.{u}} {I : Type u} {X : I → Over B} :
    {W : Over B} → (e : Expression B I X W) → Finite e.Occurrences
  | _, .var _ => inferInstanceAs (Finite PUnit.{u + 1})
  | _, .pull _ e => e.finiteOccurrences
  | _, .push _ _ e => e.finiteOccurrences
  | _, .shriek _ _ _ e => e.finiteOccurrences
  | _, .compactSupport _ _ e => e.finiteOccurrences
  | _, .tensor e t =>
    letI := e.finiteOccurrences
    letI := t.finiteOccurrences
    inferInstanceAs (Finite (e.Occurrences ⊕ t.Occurrences))

/-- The scheme belonging to a leaf occurrence, retaining the original base map.
Source: blueprint, well-typed expression trees
(blueprint: def-pur-integral-expression-occurrences). -/
def Expression.occurrenceScheme {B : Scheme.{u}} {I : Type u} {X : I → Over B} :
    {W : Over B} → (e : Expression B I X W) → e.Occurrences → Over B
  | _, .var i => fun _ ↦ X i
  | _, .pull _ e => e.occurrenceScheme
  | _, .push _ _ e => e.occurrenceScheme
  | _, .shriek _ _ _ e => e.occurrenceScheme
  | _, .compactSupport _ _ e => e.occurrenceScheme
  | _, .tensor e t => Sum.elim e.occurrenceScheme t.occurrenceScheme

/-- Original input label at a leaf occurrence. This retains labels independently
of equality of the supplied objects.
Source: blueprint, each leaf occurrence is an independent slot
(blueprint: def-pur-integral-expression-occurrences). -/
def Expression.occurrenceLabel {B : Scheme.{u}} {I : Type u} {X : I → Over B} :
    {W : Over B} → (e : Expression B I X W) → e.Occurrences → I
  | _, .var i => fun _ ↦ i
  | _, .pull _ e => e.occurrenceLabel
  | _, .push _ _ e => e.occurrenceLabel
  | _, .shriek _ _ _ e => e.occurrenceLabel
  | _, .compactSupport _ _ e => e.occurrenceLabel
  | _, .tensor e t => Sum.elim e.occurrenceLabel t.occurrenceLabel

/-- The same expression with every individual occurrence used as its own variable.
All proper/open hypotheses and the chosen compactifications are retained verbatim.
Source: blueprint, independent occurrence-slot convention
(blueprint: def-pur-integral-expression-occurrences). -/
def Expression.independentInputs {B : Scheme.{u}} {I : Type u} {X : I → Over B} :
    {W : Over B} → (e : Expression B I X W) →
      Expression B e.Occurrences e.occurrenceScheme W
  | _, .var _ => .var PUnit.unit
  | _, .pull f e => .pull f e.independentInputs
  | _, .push f hp e => .push f hp e.independentInputs
  | _, .shriek j hj hq e => .shriek j hj hq e.independentInputs
  | _, .compactSupport f c e => .compactSupport f c e.independentInputs
  | _, .tensor e t => .tensor
    (e.independentInputs.reindexInputs Sum.inl)
    (t.independentInputs.reindexInputs Sum.inr)

/-- Repeat an original input at each of its occurrences. The new variable labels
remain distinct even if two supplied objects are equal.
Source: blueprint, independent occurrence-slot convention
(blueprint: def-pur-integral-expression-occurrences). -/
def Expression.occurrenceInputs {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {C : Scheme.{u} → Type v} (K : ∀ i, C (X i).left) :
    {W : Over B} → (e : Expression B I X W) → ∀ i, C (e.occurrenceScheme i).left
  | _, .var i => fun _ ↦ K i
  | _, .pull _ e => e.occurrenceInputs K
  | _, .push _ _ e => e.occurrenceInputs K
  | _, .shriek _ _ _ e => e.occurrenceInputs K
  | _, .compactSupport _ _ e => e.occurrenceInputs K
  | _, .tensor e t => fun j ↦ match j with
    | Sum.inl i => e.occurrenceInputs K i
    | Sum.inr i => t.occurrenceInputs K i

/-- The occurrence-family construction on objects and morphisms, using the existing
product-category and disjoint-family functors.
Source: blueprint, naturality in all independent inputs
(blueprint: def-pur-integral-expression-occurrences). -/
def Expression.occurrenceInputsFunctor {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)] :
    {W : Over B} → (e : Expression B I X W) →
      (∀ i, C (X i).left) ⥤ ∀ i, C (e.occurrenceScheme i).left
  | _, .var i => Functor.pi' (fun _ : PUnit.{u + 1} ↦ Pi.eval _ i)
  | _, .pull _ e => e.occurrenceInputsFunctor
  | _, .push _ _ e => e.occurrenceInputsFunctor
  | _, .shriek _ _ _ e => e.occurrenceInputsFunctor
  | _, .compactSupport _ _ e => e.occurrenceInputsFunctor
  | _, .tensor e t =>
    Functor.pi' (fun j : e.Occurrences ⊕ t.Occurrences ↦ match j with
      | Sum.inl i => e.occurrenceInputsFunctor ⋙ Pi.eval _ i
      | Sum.inr i => t.occurrenceInputsFunctor ⋙ Pi.eval _ i)

open Classical in
/-- Shift exactly one occurrence; all other occurrences, including repetitions of
its original object, retain their supplied values.
Source: blueprint, designated independent input slot
(blueprint: def-pur-integral-expression-occurrences). -/
def Expression.shiftOccurrence {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)] [∀ W, HasShift (C W) ℤ]
    {W : Over B} (e : Expression B I X W)
    (K : ∀ i, C (e.occurrenceScheme i).left) (i : e.Occurrences) (r : ℤ) :
    ∀ j, C (e.occurrenceScheme j).left :=
  Function.update K i ((K i)⟦r⟧)

open Classical in
/-- Shift one factor of a product input category; all other factors retain their maps.
Source: blueprint Step 2 (blueprint: def-pur-integral-expression-occurrences). -/
def inputShift {I : Type u} (C : I → Type v) [∀ i, Category.{w} (C i)]
    [∀ i, HasShift (C i) ℤ] (i : I) (r : ℤ) : (∀ j, C j) ⥤ ∀ j, C j :=
  Functor.pi' (fun j ↦ Pi.eval C j ⋙ if i = j then shiftFunctor (C j) r else 𝟭 (C j))

open Classical in
/-- The input endofunctor has exactly the dependent-update object family.
Source: blueprint Step 2 (blueprint: def-pur-integral-expression-occurrences).
Proof: apply dependent function extensionality at j and split on i = j. After
substitution the selected component is (K i)[r]; every other component is K j. -/
theorem inputShift_obj {I : Type u} (C : I → Type v) [∀ i, Category.{w} (C i)]
    [∀ i, HasShift (C i) ℤ] (K : ∀ j, C j) (i : I) (r : ℤ) :
    (inputShift C i r).obj K = Function.update K i ((K i)⟦r⟧) := by
  sorry

open Classical in
/-- Shift just the designated occurrence as an endofunctor of all input families.
The selected component is evaluation followed by shift and equality transport;
every other component is evaluation. Hence all input morphisms are retained.
Source: blueprint, naturality in every independent slot
(blueprint: def-pur-integral-expression-occurrences). -/
def Expression.shiftOccurrenceFunctor {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)] [∀ W, HasShift (C W) ℤ]
    {W : Over B} (e : Expression B I X W) (i : e.Occurrences) (r : ℤ) :
    (∀ j, C (e.occurrenceScheme j).left) ⥤ ∀ j, C (e.occurrenceScheme j).left :=
  inputShift (fun j ↦ C (e.occurrenceScheme j).left) i r

open Classical in
/-- The functorial construction shifts precisely the dependent-update family.
Source: blueprint, independent input slots
(blueprint: def-pur-integral-expression-occurrences).

Proof: apply dependent function extensionality and split on i = j. In the equal
case substitute j = i; the equality transport is the identity and evaluation
followed by shift gives (K i)[r]. In the unequal case both the product functor
and Function.update give K j. -/
theorem Expression.shiftOccurrenceFunctor_obj {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)]
    [∀ W, HasShift (C W) ℤ] {W : Over B} (e : Expression B I X W)
    (K : ∀ j, C (e.occurrenceScheme j).left) (i : e.Occurrences) (r : ℤ) :
    (e.shiftOccurrenceFunctor i r).obj K = e.shiftOccurrence K i r := by
  sorry

/-- A single designated input, with every other operand held at its actual value.
Unary vertices retain their original maps and witnesses, and tensor vertices retain
which of the two inputs contains the designated occurrence.
Source: blueprint, independent slotwise comparisons
(blueprint: def-pur-integral-expression-occurrences). -/
inductive Expression.SlotContext {B : Scheme.{u}} {C : Scheme.{u} → Type v}
    [∀ W, Category.{w} (C W)] (d : Interpretation C) (A : Over B) :
    Over B → Type (max (u + 1) v) where
  | input : SlotContext d A A
  | pull {U V : Over B} (f : U ⟶ V) (e : SlotContext d A V) : SlotContext d A U
  | push {U V : Over B} (f : U ⟶ V) (hp : IsProper f.left)
      (e : SlotContext d A U) : SlotContext d A V
  | shriek {U V : Over B} (j : U ⟶ V) (hj : IsOpenImmersion j.left)
      (hq : QuasiCompact j.left) (e : SlotContext d A U) : SlotContext d A V
  | compactSupport {U V : Over B} (f : U ⟶ V) (c : Compactification f.left)
      (e : SlotContext d A U) : SlotContext d A V
  | tensorLeft {W : Over B} (e : SlotContext d A W) (N : C W.left) : SlotContext d A W
  | tensorRight {W : Over B} (M : C W.left) (e : SlotContext d A W) : SlotContext d A W

/-- A context is the actual unary composite, using the appropriate curried tensor
functor at a tensor vertex. No functor or map is chosen by an existence theorem.
Source: blueprint, expression contexts and slotwise comparisons
(blueprint: def-pur-integral-expression-occurrences). -/
def Expression.SlotContext.evaluate {B : Scheme.{u}} {C : Scheme.{u} → Type v}
    [∀ W, Category.{w} (C W)] {d : Interpretation C} {A : Over B} :
    {W : Over B} → SlotContext d A W → (C A.left ⥤ C W.left)
  | _, .input => 𝟭 _
  | _, .pull f e => e.evaluate ⋙ d.pull f.left
  | _, .push f _ e => e.evaluate ⋙ d.push f.left
  | _, .shriek j hj _ e =>
    letI := hj
    e.evaluate ⋙ d.shriek j.left
  | _, .compactSupport f c e => e.evaluate ⋙ d.compactSupport f.left c
  | W, .tensorLeft e N => e.evaluate ⋙ (Functor.curry.obj (d.tensor W.left)).flip.obj N
  | W, .tensorRight M e => e.evaluate ⋙ (Functor.curry.obj (d.tensor W.left)).obj M

/-- Extract the context at an individual leaf, evaluating every subtree away from
that leaf at the supplied independent occurrence family.
Source: blueprint, fixing the other input in a tensor context
(blueprint: def-pur-integral-expression-occurrences). -/
def Expression.slotContext {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)] (d : Interpretation C) :
    {W : Over B} → (e : Expression B I X W) →
      (K : ∀ i, C (e.occurrenceScheme i).left) → (i : e.Occurrences) →
        Expression.SlotContext d (e.occurrenceScheme i) W
  | _, .var _, _ => fun _ ↦ .input
  | _, .pull f e, K => fun i ↦ .pull f (e.slotContext d K i)
  | _, .push f hp e, K => fun i ↦ .push f hp (e.slotContext d K i)
  | _, .shriek j hj hq e, K => fun i ↦ .shriek j hj hq (e.slotContext d K i)
  | _, .compactSupport f c e, K => fun i ↦ .compactSupport f c (e.slotContext d K i)
  | _, .tensor e t, K => fun i ↦ match i with
    | Sum.inl j =>
      .tensorLeft (e.slotContext d (fun k ↦ K (Sum.inl k)) j)
        ((t.independentInputs.evaluate d).obj (fun k ↦ K (Sum.inr k)))
    | Sum.inr j =>
      .tensorRight ((e.independentInputs.evaluate d).obj (fun k ↦ K (Sum.inl k)))
        (t.slotContext d (fun k ↦ K (Sum.inr k)) j)

open Classical in
/-- Evaluating the selected-slot context is evaluating the existing expression with
only that occurrence replaced. This equality fixes the comparison without choosing
an unrelated object or isomorphism.
Source: blueprint, the designated independent slot
(blueprint: def-pur-integral-expression-occurrences).

Proof: induct on the expression. For a variable the occurrence set is a singleton,
so its updated family has the prescribed value. Every unary case is the induction
identity followed by its unchanged operation. At a tensor vertex use the disjoint
sum of the two occurrence sets. In the selected summand apply the induction identity;
in the other summand the update leaves the family unchanged. Variable renaming in
independentInputs simply precomposes the family with the relevant sum inclusion,
as is checked recursively using Expression.evaluate. Thus the curried tensor
functor gives exactly the tensor of these two values, in either selected slot. -/
theorem Expression.slotContext_evaluate {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)] (d : Interpretation C)
    {W : Over B} (e : Expression B I X W)
    (K : ∀ i, C (e.occurrenceScheme i).left) (i : e.Occurrences)
    (P : C (e.occurrenceScheme i).left) :
    ((e.slotContext d K i).evaluate).obj P =
      (e.independentInputs.evaluate d).obj (Function.update K i P) := by
  sorry

/-- Relabelling by occurrences gives precisely one leaf for each input label.
Source: blueprint, the independent-occurrence convention
(blueprint: def-pur-integral-expression-occurrences).

Proof: use induction on the expression. The variable case is the bijection of
singletons. Unary operations preserve the occurrence and label maps. At a tensor,
reindexing by the left and right sum inclusions preserves all occurrences in the
respective subtree. Their label maps are the corresponding inclusions after the
inductive bijections. Their disjoint union is a bijection onto the sum. -/
theorem Expression.independentInputs_bijectiveLabel {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {W : Over B} (e : Expression B I X W) :
    Function.Bijective e.independentInputs.occurrenceLabel := by
  sorry

/-- Independently labelled finite expressions. This is only a presentation of
independent occurrences: independentInputs provides it for every existing expression.
Source: blueprint, independent input slots
(blueprint: def-pur-integral-expression-occurrences). -/
abbrev IndependentExpression (B : Scheme.{u}) (I : Type u) (X : I → Over B) (W : Over B) :=
  {e : Expression B I X W // Function.Bijective e.occurrenceLabel}

open Classical in
/-- Search the expression for a designated input label. At a tensor the actual
other subtree is held fixed. For independent labels there is exactly one hit.
Source: blueprint, individual occurrence slots
(blueprint: def-pur-integral-expression-occurrences). -/
def Expression.variableContext {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)] (d : Interpretation C)
    (K : ∀ i, C (X i).left) (i : I) :
    {W : Over B} → Expression B I X W → Option (Expression.SlotContext d (X i) W)
  | _, .var j => if h : i = j then h ▸ some .input else none
  | _, .pull f e => (e.variableContext d K i).map (.pull f)
  | _, .push f hp e => (e.variableContext d K i).map (.push f hp)
  | _, .shriek j hj hq e => (e.variableContext d K i).map (.shriek j hj hq)
  | _, .compactSupport f c e => (e.variableContext d K i).map (.compactSupport f c)
  | _, .tensor e t => match e.variableContext d K i with
    | some c => some (.tensorLeft c ((t.evaluate d).obj K))
    | none => (t.variableContext d K i).map
      (fun c ↦ .tensorRight ((e.evaluate d).obj K) c)

/-- Every independently labelled input has a context in the explicit search.
Source: blueprint, independent leaf indexing
(blueprint: def-pur-integral-expression-occurrences).

Proof: surjectivity of the label map gives a leaf with label i. Follow its path
through the tree. Unary vertices preserve successful searches. At a tensor the
leaf is in one of the two disjoint occurrence sets. Injectivity excludes an
occurrence of i in the other subtree, so the search reaches precisely that branch.
A variable labelled i returns the input context. Thus the resulting Option is some. -/
theorem IndependentExpression.variableContext_isSome {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)]
    (d : Interpretation C) {W : Over B} (e : IndependentExpression B I X W)
    (K : ∀ i, C (X i).left) (i : I) : (e.val.variableContext d K i).isSome := by
  sorry

/-- Extract the context from the successful explicit tree search. The proof only
certifies Option.get; it does not choose a context from an existence theorem.
Source: blueprint, independent input slots
(blueprint: def-pur-integral-expression-occurrences). -/
def IndependentExpression.variableContext {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)]
    (d : Interpretation C) {W : Over B} (e : IndependentExpression B I X W)
    (K : ∀ i, C (X i).left) (i : I) : Expression.SlotContext d (X i) W :=
  (e.val.variableContext d K i).get (e.variableContext_isSome d K i)

open Classical in
/-- Replacing the sole occurrence of a label is evaluation of its actual context.
Source: blueprint, slotwise comparison
(blueprint: def-pur-integral-expression-occurrences).

Proof: induct along the successful search. At a variable, bijectivity identifies
its label with i and the context is identity. Unary functor evaluation preserves
the equality. At a tensor the nonselected subtree has no occurrence of i, by
injectivity of the global leaf-label map. Its evaluation therefore ignores the
update. The selected subtree satisfies the inductive identity, so the respective
curried tensor gives the stated equality. The same induction with P = K i gives
the second equality, since update at the current value is the original family. -/
theorem IndependentExpression.variableContext_evaluate {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)]
    (d : Interpretation C) {W : Over B} (e : IndependentExpression B I X W)
    (K : ∀ i, C (X i).left) (i : I) (P : C (X i).left) :
    ((e.variableContext d K i).evaluate).obj P =
      (e.val.evaluate d).obj (Function.update K i P) ∧
    ((e.variableContext d K i).evaluate).obj (K i) = (e.val.evaluate d).obj K := by
  sorry

end WeilConjectures.IntegralSystemRealization

