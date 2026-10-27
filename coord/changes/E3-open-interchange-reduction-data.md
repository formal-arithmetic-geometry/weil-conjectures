# OpenInterchangeReduction data declarations

## Reason

The four specialized forward-square proofs need the same predicates and input actions as the item theorem. Keeping those definitions in the theorem module would close an import cycle. Extract the eight existing definitions into a data module, and publicly re-export it from the original module. Every definition is preserved verbatim; every public import is preserved except that the parent `GeneratorReductionStatement` is replaced by its data module `GeneratorReductionData` (all that the definitions and the item statement use), so that the parent can import this item without a cycle. Only the item module is adapted; the parent GeneratorReductionStatement is untouched.

## Old

In lean/Sheaf/SixFunctors/OpenInterchangeReductionSquares.lean:

```lean
def Structural {S : Type s} {W : S → Scheme.{u}} {I : Type i} {location : I → S}
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C) : Prop :=
  match g with
  | .tensorAssociator .. | .tensorLeftUnit .. | .tensorRightUnit ..
  | .pullComposition .. | .pushComposition ..
  | .pullPushUnit .. | .pullPushCounit .. | .openUnit .. | .openCounit .. => True
  | .openBaseChange .. | .openTensor ..
  | .properOpenInterchange .. | .properOpenLambda .. => False

/-- Precisely beta, gamma, lambda_Q and Gamma_Q, with their prescribed canonical
normalizations. Source: blueprint fix-prop-coherence, open-adjunction/clopen expansion
(blueprint: lem-sf-open-interchange-reduction-squares). -/
def OpenGenerator {S : Type s} {W : S → Scheme.{u}} {I : Type i} {location : I → S}
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C) : Prop :=
  match g with
  | .openBaseChange .. | .openTensor ..
  | .properOpenInterchange .. | .properOpenLambda .. => True
  | _ => False

/-- The invertible open comparisons. Gamma_Q is a morphism, and is deliberately
excluded. Source: blueprint fix-prop-coherence, open-adjunction/clopen expansion
(blueprint: lem-sf-open-interchange-reduction-squares). -/
def OpenIsomorphism {S : Type s} {W : S → Scheme.{u}} {I : Type i}
    {location : I → S} {a : S} {B C : Word W location a}
    (g : GeneratorKind W location B C) : Prop :=
  match g with
  | .openBaseChange .. | .openTensor .. | .properOpenLambda .. => True
  | _ => False

/-- The square for the inverse of a specified isomorphism, using exactly the same
recursive comparisons at its endpoints. The ambient inverse is only used on the
admissible domain where the canonical maps are invertible.
Source: blueprint fix-prop-coherence, proof step 1, inversion of squares
(blueprint: lem-sf-open-interchange-reduction-squares). -/
def InverseAssertion {S : Type s} (W : S → Scheme.{u}) {I : Type i}
    (location : I → S) (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C) : Prop :=
  C.r l E W location o K ≫
    inverseOrZero (g.systemMap l E W location o (inputReduction l E W location K)) =
  (IntegralSystemRealization.calculus l E (W a)).reduction.map
    (inverseOrZero (g.integralMap l E W location o K)) ≫ B.r l E W location o K

/-- Action on input morphisms in the already defined system evaluation. This is
structural functoriality of the finite word, in both tensor slots.
Source: blueprint fix-prop-coherence, naturality clause
(blueprint: lem-sf-open-interchange-reduction-squares). -/
def systemInputMap {S : Type s} (W : S → Scheme.{u}) {I : Type i}
    (location : I → S) (o : Operations l E)
    {M N : ∀ k : I, coefficientSequenceDerived l E (W (location k))}
    (f : ∀ k : I, M k ⟶ N k) : {a : S} → (B : Word W location a) →
      B.systemValue l E W location o M ⟶ B.systemValue l E W location o N
  | _, .input k => f k
  | _, .unit _ => 𝟙 _
  | a, .tensor B C => (IntegralSystemRealization.calculus l E (W a)).systemClosed.tensor.map
      (Prod.mkHom (systemInputMap W location o f B) (systemInputMap W location o f C))
  | _, .pull v _ _ _ B => (IntegralSystemRealization.pull l E v).map
      (systemInputMap W location o f B)
  | _, .push v _ _ _ _ B => (IntegralSystemRealization.Operations.push l E o.system v).map
      (systemInputMap W location o f B)
  | _, .open j hj _ B => letI := hj
      (IntegralSystemRealization.Operations.shriek l E o.system j).map
        (systemInputMap W location o f B)

/-- Action on input morphisms of the specified completed integral evaluation.
Source: blueprint fix-prop-coherence, naturality clause
(blueprint: lem-sf-open-interchange-reduction-squares). -/
def integralInputMap {S : Type s} (W : S → Scheme.{u}) {I : Type i}
    (location : I → S) (o : Operations l E)
    {K L : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))}
    (f : ∀ k : I, K k ⟶ L k) : {a : S} → (B : Word W location a) →
      B.integralValue l E W location o K ⟶ B.integralValue l E W location o L
  | _, .input k => f k
  | _, .unit _ => 𝟙 _
  | a, .tensor B C => (integralCompletedTensor l E (W a)).map
      (Prod.mkHom (integralInputMap W location o f B) (integralInputMap W location o f C))
  | _, .pull v _ _ _ B => (integralDerivedPullback l E v).map
      (integralInputMap W location o f B)
  | _, .push v _ _ _ _ B => (integralPush l E o v).map
      (integralInputMap W location o f B)
  | _, .open j hj _ B => letI := hj
      (IntegralSystemRealization.ringedOpen l E j).map
        (integralInputMap W location o f B)

/-- Naturality of both vertical comparisons and both horizontal arrows of the square.
This is equality of actual whole-system morphisms and of actual integral morphisms.
Source: blueprint fix-prop-coherence, final naturality clause
(blueprint: lem-sf-open-interchange-reduction-squares). -/
def SquareNaturality {S : Type s} (W : S → Scheme.{u}) {I : Type i}
    (location : I → S) (o : Operations l E)
    {K L : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))}
    (f : ∀ k : I, K k ⟶ L k)
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C) : Prop :=
  (∀ V : Word W location a,
    V = B ∨ V = C →
    (IntegralSystemRealization.calculus l E (W a)).reduction.map
      (integralInputMap l E W location o f V) ≫ V.r l E W location o L =
    V.r l E W location o K ≫ systemInputMap l E W location o
      (fun k ↦ (IntegralSystemRealization.calculus l E (W (location k))).reduction.map (f k))
      V) ∧
  integralInputMap l E W location o f B ≫ g.integralMap l E W location o L =
    g.integralMap l E W location o K ≫ integralInputMap l E W location o f C ∧
  systemInputMap l E W location o
      (fun k ↦ (IntegralSystemRealization.calculus l E (W (location k))).reduction.map (f k))
      B ≫ g.systemMap l E W location o (inputReduction l E W location L) =
    g.systemMap l E W location o (inputReduction l E W location K) ≫
      systemInputMap l E W location o
        (fun k ↦ (IntegralSystemRealization.calculus l E (W (location k))).reduction.map (f k)) C

/-- Structural-square hypothesis as a family on the stipulated intermediate domain.
There is no length-three bound here: in particular it applies to the length-four
intermediates in the clopen factorization. Each instance is a square of the actual
whole-system maps, not a choice of a lift of an evaluated square.
Source: blueprint fix-prop-coherence, structural-square hypothesis
(blueprint: lem-sf-open-interchange-reduction-squares). -/
def StructuralSquares (D : FiniteFieldDatum.{u}) (o : Operations l E) : Prop :=
  ∀ {S : Type s} (W : S → Scheme.{u}) (_hW : FiniteTypeFamily W D.k)
    {I : Type i} (location : I → S)
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C),
    Structural g →
    ∀ (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
      (lo hi torLo torHi : ℤ),
      (∀ k : I, Admissible l E
        (IntegralSystemRealization.calculus l E (W (location k))) (K k)
        lo hi torLo torHi) →
      Word.admissible l E W location o K lo hi torLo torHi B →
      Word.admissible l E W location o K lo hi torLo torHi C →
      Assertion l E W location o K g
```

## New

Exactly the same declarations and bodies in lean/Sheaf/SixFunctors/OpenInterchangeReductionData.lean:

```lean
def Structural {S : Type s} {W : S → Scheme.{u}} {I : Type i} {location : I → S}
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C) : Prop :=
  match g with
  | .tensorAssociator .. | .tensorLeftUnit .. | .tensorRightUnit ..
  | .pullComposition .. | .pushComposition ..
  | .pullPushUnit .. | .pullPushCounit .. | .openUnit .. | .openCounit .. => True
  | .openBaseChange .. | .openTensor ..
  | .properOpenInterchange .. | .properOpenLambda .. => False

/-- Precisely beta, gamma, lambda_Q and Gamma_Q, with their prescribed canonical
normalizations. Source: blueprint fix-prop-coherence, open-adjunction/clopen expansion
(blueprint: lem-sf-open-interchange-reduction-squares). -/
def OpenGenerator {S : Type s} {W : S → Scheme.{u}} {I : Type i} {location : I → S}
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C) : Prop :=
  match g with
  | .openBaseChange .. | .openTensor ..
  | .properOpenInterchange .. | .properOpenLambda .. => True
  | _ => False

/-- The invertible open comparisons. Gamma_Q is a morphism, and is deliberately
excluded. Source: blueprint fix-prop-coherence, open-adjunction/clopen expansion
(blueprint: lem-sf-open-interchange-reduction-squares). -/
def OpenIsomorphism {S : Type s} {W : S → Scheme.{u}} {I : Type i}
    {location : I → S} {a : S} {B C : Word W location a}
    (g : GeneratorKind W location B C) : Prop :=
  match g with
  | .openBaseChange .. | .openTensor .. | .properOpenLambda .. => True
  | _ => False

/-- The square for the inverse of a specified isomorphism, using exactly the same
recursive comparisons at its endpoints. The ambient inverse is only used on the
admissible domain where the canonical maps are invertible.
Source: blueprint fix-prop-coherence, proof step 1, inversion of squares
(blueprint: lem-sf-open-interchange-reduction-squares). -/
def InverseAssertion {S : Type s} (W : S → Scheme.{u}) {I : Type i}
    (location : I → S) (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C) : Prop :=
  C.r l E W location o K ≫
    inverseOrZero (g.systemMap l E W location o (inputReduction l E W location K)) =
  (IntegralSystemRealization.calculus l E (W a)).reduction.map
    (inverseOrZero (g.integralMap l E W location o K)) ≫ B.r l E W location o K

/-- Action on input morphisms in the already defined system evaluation. This is
structural functoriality of the finite word, in both tensor slots.
Source: blueprint fix-prop-coherence, naturality clause
(blueprint: lem-sf-open-interchange-reduction-squares). -/
def systemInputMap {S : Type s} (W : S → Scheme.{u}) {I : Type i}
    (location : I → S) (o : Operations l E)
    {M N : ∀ k : I, coefficientSequenceDerived l E (W (location k))}
    (f : ∀ k : I, M k ⟶ N k) : {a : S} → (B : Word W location a) →
      B.systemValue l E W location o M ⟶ B.systemValue l E W location o N
  | _, .input k => f k
  | _, .unit _ => 𝟙 _
  | a, .tensor B C => (IntegralSystemRealization.calculus l E (W a)).systemClosed.tensor.map
      (Prod.mkHom (systemInputMap W location o f B) (systemInputMap W location o f C))
  | _, .pull v _ _ _ B => (IntegralSystemRealization.pull l E v).map
      (systemInputMap W location o f B)
  | _, .push v _ _ _ _ B => (IntegralSystemRealization.Operations.push l E o.system v).map
      (systemInputMap W location o f B)
  | _, .open j hj _ B => letI := hj
      (IntegralSystemRealization.Operations.shriek l E o.system j).map
        (systemInputMap W location o f B)

/-- Action on input morphisms of the specified completed integral evaluation.
Source: blueprint fix-prop-coherence, naturality clause
(blueprint: lem-sf-open-interchange-reduction-squares). -/
def integralInputMap {S : Type s} (W : S → Scheme.{u}) {I : Type i}
    (location : I → S) (o : Operations l E)
    {K L : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))}
    (f : ∀ k : I, K k ⟶ L k) : {a : S} → (B : Word W location a) →
      B.integralValue l E W location o K ⟶ B.integralValue l E W location o L
  | _, .input k => f k
  | _, .unit _ => 𝟙 _
  | a, .tensor B C => (integralCompletedTensor l E (W a)).map
      (Prod.mkHom (integralInputMap W location o f B) (integralInputMap W location o f C))
  | _, .pull v _ _ _ B => (integralDerivedPullback l E v).map
      (integralInputMap W location o f B)
  | _, .push v _ _ _ _ B => (integralPush l E o v).map
      (integralInputMap W location o f B)
  | _, .open j hj _ B => letI := hj
      (IntegralSystemRealization.ringedOpen l E j).map
        (integralInputMap W location o f B)

/-- Naturality of both vertical comparisons and both horizontal arrows of the square.
This is equality of actual whole-system morphisms and of actual integral morphisms.
Source: blueprint fix-prop-coherence, final naturality clause
(blueprint: lem-sf-open-interchange-reduction-squares). -/
def SquareNaturality {S : Type s} (W : S → Scheme.{u}) {I : Type i}
    (location : I → S) (o : Operations l E)
    {K L : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))}
    (f : ∀ k : I, K k ⟶ L k)
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C) : Prop :=
  (∀ V : Word W location a,
    V = B ∨ V = C →
    (IntegralSystemRealization.calculus l E (W a)).reduction.map
      (integralInputMap l E W location o f V) ≫ V.r l E W location o L =
    V.r l E W location o K ≫ systemInputMap l E W location o
      (fun k ↦ (IntegralSystemRealization.calculus l E (W (location k))).reduction.map (f k))
      V) ∧
  integralInputMap l E W location o f B ≫ g.integralMap l E W location o L =
    g.integralMap l E W location o K ≫ integralInputMap l E W location o f C ∧
  systemInputMap l E W location o
      (fun k ↦ (IntegralSystemRealization.calculus l E (W (location k))).reduction.map (f k))
      B ≫ g.systemMap l E W location o (inputReduction l E W location L) =
    g.systemMap l E W location o (inputReduction l E W location K) ≫
      systemInputMap l E W location o
        (fun k ↦ (IntegralSystemRealization.calculus l E (W (location k))).reduction.map (f k)) C

/-- Structural-square hypothesis as a family on the stipulated intermediate domain.
There is no length-three bound here: in particular it applies to the length-four
intermediates in the clopen factorization. Each instance is a square of the actual
whole-system maps, not a choice of a lift of an evaluated square.
Source: blueprint fix-prop-coherence, structural-square hypothesis
(blueprint: lem-sf-open-interchange-reduction-squares). -/
def StructuralSquares (D : FiniteFieldDatum.{u}) (o : Operations l E) : Prop :=
  ∀ {S : Type s} (W : S → Scheme.{u}) (_hW : FiniteTypeFamily W D.k)
    {I : Type i} (location : I → S)
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C),
    Structural g →
    ∀ (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
      (lo hi torLo torHi : ℤ),
      (∀ k : I, Admissible l E
        (IntegralSystemRealization.calculus l E (W (location k))) (K k)
        lo hi torLo torHi) →
      Word.admissible l E W location o K lo hi torLo torHi B →
      Word.admissible l E W location o K lo hi torLo torHi C →
      Assertion l E W location o K g
```

The original item begins with `public import Sheaf.SixFunctors.OpenInterchangeReductionData`. Its original public imports are all preserved in that data module, except `GeneratorReductionStatement`, replaced by `GeneratorReductionData`.

## Users

`tools/downstream.py Sheaf.SixFunctors.OpenInterchangeReductionSquares --uses Structural OpenGenerator OpenIsomorphism InverseAssertion systemInputMap integralInputMap SquareNaturality StructuralSquares` reports zero current downstream modules, and the item itself as the only textual user of each name. Unfinished DAG parents still need the item theorem; this extraction withdraws no declaration or module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.OpenInterchangeReductionSquares | E3 | Same definitions and main theorem signature; public import environment the same except GeneratorReductionStatement → GeneratorReductionData; definitions supplied by public reexport. |
| Sheaf.SixFunctors.GeneratorReductionStatement | K4 (landing dc9dd96b188 dropped by 5b5f112c922) | Unchanged. No longer re-exported by the item (no module imports the item). K4's proof imports this item through StructuralReductionWordSubstitution; the data-only import keeps that direction acyclic. |

## Status

landed 20261025T201726-L-2608118 2026-10-25 (merge of deliver/E3/Sheaf.SixFunctors.OpenInterchangeReductionSquares)
