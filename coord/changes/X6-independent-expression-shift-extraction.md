# InterpretationShifts, Expression.SlotContext.shift and IndependentExpression.shift

## Reason

The generic recursive naturality lemma must be below the integral source's
naturality theorem. Move these three definitions byte-verbatim to
Sheaf.SixFunctors.IndependentExpressionShiftNaturality and publicly import it
from IntegralOperationShiftData. Names, universes, signatures, constructions and
public visibility are identical. The new public import preserves every original
consumer. This is an interface extraction, not a change of mathematical meaning.
The source's reduction/limit naturality is proved by composition from the generic
expression lemma and the separate pointwise component equation.

## Old

In lean/Sheaf/SixFunctors/IntegralOperationShiftData.lean:

```lean
/-- Shift comparisons for each primitive operation; tensor slots remain separate.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
structure InterpretationShifts {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)]
    [∀ W, HasShift (C W) ℤ] (d : Interpretation C) where
  pull {U V : Scheme.{u}} (f : U ⟶ V) : (d.pull f).CommShift ℤ
  push {U V : Scheme.{u}} (f : U ⟶ V) : (d.push f).CommShift ℤ
  shriek {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] : (d.shriek j).CommShift ℤ
  compactSupport {U V : Scheme.{u}} (f : U ⟶ V) (c : Compactification f) :
    (d.compactSupport f c).CommShift ℤ
  tensorLeft (W : Scheme.{u}) (r : ℤ) :
    tensorShiftFirst (C W) r ⋙ d.tensor W ≅ d.tensor W ⋙ shiftFunctor (C W) r
  tensorRight (W : Scheme.{u}) (r : ℤ) :
    completedTensorShiftSecond (C W) r ⋙ d.tensor W ≅
      d.tensor W ⋙ shiftFunctor (C W) r

/-- Reindex shifts through the actual single-slot context, with the designated
left or right tensor comparison at every tensor vertex.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
def Expression.SlotContext.shift {B : Scheme.{u}} {C : Scheme.{u} → Type v}
    [∀ W, Category.{w} (C W)] [∀ W, HasShift (C W) ℤ] {d : Interpretation C}
    (a : InterpretationShifts d) {A : Over B} (r : ℤ) :
    {W : Over B} → (e : Expression.SlotContext d A W) → (P : C A.left) →
      e.evaluate.obj (P⟦r⟧) ≅ (e.evaluate.obj P)⟦r⟧
  | _, .input, _ => Iso.refl _
  | _, .pull f e, P => (d.pull f.left).mapIso (e.shift a r P) ≪≫
    (Functor.commShiftIso (d.pull f.left) (self := a.pull f.left) r).app (e.evaluate.obj P)
  | _, .push f _ e, P => (d.push f.left).mapIso (e.shift a r P) ≪≫
    (Functor.commShiftIso (d.push f.left) (self := a.push f.left) r).app (e.evaluate.obj P)
  | _, .shriek j hj _ e, P =>
    letI := hj
    (d.shriek j.left).mapIso (e.shift a r P) ≪≫
      (Functor.commShiftIso (d.shriek j.left) (self := a.shriek j.left) r).app
        (e.evaluate.obj P)
  | _, .compactSupport f c e, P => (d.compactSupport f.left c).mapIso (e.shift a r P) ≪≫
    (Functor.commShiftIso (d.compactSupport f.left c)
      (self := a.compactSupport f.left c) r).app (e.evaluate.obj P)
  | W, .tensorLeft e N, P =>
    ((Functor.curry.obj (d.tensor W.left)).flip.obj N).mapIso (e.shift a r P) ≪≫
      (a.tensorLeft W.left r).app (e.evaluate.obj P, N)
  | W, .tensorRight M e, P =>
    ((Functor.curry.obj (d.tensor W.left)).obj M).mapIso (e.shift a r P) ≪≫
      (a.tensorRight W.left r).app (M, e.evaluate.obj P)

open Classical in
/-- The actual comparison for a single independently labelled input.
Its endpoint identifications are equalities of explicit evaluations, not chosen isos.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
def IndependentExpression.shift {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)] [∀ W, HasShift (C W) ℤ]
    (d : Interpretation C) (a : InterpretationShifts d) {W : Over B}
    (e : IndependentExpression B I X W) (K : ∀ i, C (X i).left) (i : I) (r : ℤ) :
    (e.val.evaluate d).obj (Function.update K i ((K i)⟦r⟧)) ≅
      ((e.val.evaluate d).obj K)⟦r⟧ :=
  (eqToIso (e.variableContext_evaluate d K i ((K i)⟦r⟧)).1).symm ≪≫
    (e.variableContext d K i).shift a r (K i) ≪≫
    (shiftFunctor (C W.left) r).mapIso
      (eqToIso (e.variableContext_evaluate d K i (K i)).2)
```

## New

In lean/Sheaf/SixFunctors/IndependentExpressionShiftNaturality.lean:

```lean
/-- Shift comparisons for each primitive operation; tensor slots remain separate.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
structure InterpretationShifts {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)]
    [∀ W, HasShift (C W) ℤ] (d : Interpretation C) where
  pull {U V : Scheme.{u}} (f : U ⟶ V) : (d.pull f).CommShift ℤ
  push {U V : Scheme.{u}} (f : U ⟶ V) : (d.push f).CommShift ℤ
  shriek {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] : (d.shriek j).CommShift ℤ
  compactSupport {U V : Scheme.{u}} (f : U ⟶ V) (c : Compactification f) :
    (d.compactSupport f c).CommShift ℤ
  tensorLeft (W : Scheme.{u}) (r : ℤ) :
    tensorShiftFirst (C W) r ⋙ d.tensor W ≅ d.tensor W ⋙ shiftFunctor (C W) r
  tensorRight (W : Scheme.{u}) (r : ℤ) :
    completedTensorShiftSecond (C W) r ⋙ d.tensor W ≅
      d.tensor W ⋙ shiftFunctor (C W) r

/-- Reindex shifts through the actual single-slot context, with the designated
left or right tensor comparison at every tensor vertex.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
def Expression.SlotContext.shift {B : Scheme.{u}} {C : Scheme.{u} → Type v}
    [∀ W, Category.{w} (C W)] [∀ W, HasShift (C W) ℤ] {d : Interpretation C}
    (a : InterpretationShifts d) {A : Over B} (r : ℤ) :
    {W : Over B} → (e : Expression.SlotContext d A W) → (P : C A.left) →
      e.evaluate.obj (P⟦r⟧) ≅ (e.evaluate.obj P)⟦r⟧
  | _, .input, _ => Iso.refl _
  | _, .pull f e, P => (d.pull f.left).mapIso (e.shift a r P) ≪≫
    (Functor.commShiftIso (d.pull f.left) (self := a.pull f.left) r).app (e.evaluate.obj P)
  | _, .push f _ e, P => (d.push f.left).mapIso (e.shift a r P) ≪≫
    (Functor.commShiftIso (d.push f.left) (self := a.push f.left) r).app (e.evaluate.obj P)
  | _, .shriek j hj _ e, P =>
    letI := hj
    (d.shriek j.left).mapIso (e.shift a r P) ≪≫
      (Functor.commShiftIso (d.shriek j.left) (self := a.shriek j.left) r).app
        (e.evaluate.obj P)
  | _, .compactSupport f c e, P => (d.compactSupport f.left c).mapIso (e.shift a r P) ≪≫
    (Functor.commShiftIso (d.compactSupport f.left c)
      (self := a.compactSupport f.left c) r).app (e.evaluate.obj P)
  | W, .tensorLeft e N, P =>
    ((Functor.curry.obj (d.tensor W.left)).flip.obj N).mapIso (e.shift a r P) ≪≫
      (a.tensorLeft W.left r).app (e.evaluate.obj P, N)
  | W, .tensorRight M e, P =>
    ((Functor.curry.obj (d.tensor W.left)).obj M).mapIso (e.shift a r P) ≪≫
      (a.tensorRight W.left r).app (M, e.evaluate.obj P)

open Classical in
/-- The actual comparison for a single independently labelled input.
Its endpoint identifications are equalities of explicit evaluations, not chosen isos.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
def IndependentExpression.shift {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)] [∀ W, HasShift (C W) ℤ]
    (d : Interpretation C) (a : InterpretationShifts d) {W : Over B}
    (e : IndependentExpression B I X W) (K : ∀ i, C (X i).left) (i : I) (r : ℤ) :
    (e.val.evaluate d).obj (Function.update K i ((K i)⟦r⟧)) ≅
      ((e.val.evaluate d).obj K)⟦r⟧ :=
  (eqToIso (e.variableContext_evaluate d K i ((K i)⟦r⟧)).1).symm ≪≫
    (e.variableContext d K i).shift a r (K i) ≪≫
    (shiftFunctor (C W.left) r).mapIso
      (eqToIso (e.variableContext_evaluate d K i (K i)).2)
```

IntegralOperationShiftData publicly imports that module. The existing declarations
are available to all original importers with unchanged bodies. The local
irreducibility attributes on HasDerivedCategory.standard and the operation shift
data affect elaboration only. They prevent expensive expansion of reconstruction
calculus data while checking the naturality proof.
The four new intermediate theorem statements are recorded in their new nodes and do not alter
existing statements. No Challenge declaration changes meaning; no target semantic
review is reopened by this verbatim extraction.

## Users

The direct-importer list comes from tools/downstream.py. A name search for
InterpretationShifts, shift_naturality and limitShift_roos found only the item
itself. The original named data remain publicly reexported to all consumers.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.IntegralOperationShiftData | X6 | Publicly imports the extracted data; new naturality proof. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed | Identical public data through reexport; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Identical public data through reexport; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Identical public data through reexport; no adaptation. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | claimed | Identical public data through reexport; no adaptation. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed | Identical public data through reexport; no adaptation. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed | Identical public data through reexport; no adaptation. |
| Sheaf.SixFunctors.CompletedTensorSlotShiftLaws | unclaimed | Identical public data through reexport; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed | Identical public data through reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | claimed | Identical public data through reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Identical public data through reexport; no adaptation. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | Identical public data through reexport; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | Identical public data through reexport; no adaptation. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed | Identical public data through reexport; no adaptation. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed | Identical public data through reexport; no adaptation. |
| Sheaf.SixFunctors.SystemTensorShiftCoherence | unclaimed | Identical public data through reexport; no adaptation. |
| Sheaf.SixFunctors.SystemTensorShiftRepresentativeModels | unclaimed | Identical public data through reexport; no adaptation. |

The unit route is retained. No source-library declaration is changed or removed.
The delivery's independent reader should compile the direct consumers against
the extraction, as required for public import changes.

## Status

landed 20261026T003221-L-153828 2026-10-26 (merge of deliver/X6/Sheaf.SixFunctors.IntegralOperationShiftData)
