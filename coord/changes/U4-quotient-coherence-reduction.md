# IntegralQuotientMixedCoherence and canonical bracketing API


## Reason

Repair expensive elaboration of the twelve-field coherence structure by sharing
its field types through named proposition definitions. Make structural recursion
explicit in the two bracketing interpretations. Move the existing scalar-comparison
and bracketing data API into a shared module to allow independent component lemmas
without an import cycle. The item publicly imports that module, preserving every
original name and its public availability. This is also a proof decomposition:
five independent component lemmas are added with holes and their own DAG nodes.

The original structure base required 53.2 seconds; literal clause factoring reduced
the base diagnostic to 27.5 seconds. The shared API separation is for independent
components, after that definition repair, rather than dividing a slow proof.
No declaration under lean/WeilConjectures is changed. No Challenge target changes.

## Old

Original path and bracketing definitions (verbatim from the shared source):

```lean
def IntegralQuotientPathInvertible (l : ℕ) {X : Scheme.{t}} :
    ∀ {Y : Scheme.{t}}, Quiver.Path X Y → Prop
  | _, .nil => ∀ x : X, Nonempty (Invertible (l : X.residueField x))
  | Y, .cons p _ => IntegralQuotientPathInvertible l p ∧
      ∀ y : Y, Nonempty (Invertible (l : Y.residueField y))

/-- Binary parenthesizations of a fixed finite string, with empty pieces permitted.
Source: the finite-string assertion of the node, Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
inductive IntegralQuotientBracketing :
    {X Y : Scheme.{t}} → Quiver.Path X Y → Type (t + 1)
  | nil (X : Scheme.{t}) : IntegralQuotientBracketing (Quiver.Path.nil : Quiver.Path X X)
  | single {X Y : Scheme.{t}} (f : X ⟶ Y) : IntegralQuotientBracketing f.toPath
  | comp {X Y Z : Scheme.{t}} {p : Quiver.Path X Y} {q : Quiver.Path Y Z}
      (a : IntegralQuotientBracketing p) (b : IntegralQuotientBracketing q) :
      IntegralQuotientBracketing (p.comp q)

/-- Interpret the parenthesized string by iterated pullback, retaining its entire diagram.
Source: finite-string clause, Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
def integralQuotientBracketFunctor
    (D : Scheme.{t} → Type a) [∀ X : Scheme.{t}, Category.{v} (D X)]
    (U : ∀ {X Y : Scheme.{t}}, (X ⟶ Y) → (D Y ⥤ D X)) :
    ∀ {X Y : Scheme.{t}} {p : Quiver.Path X Y},
      IntegralQuotientBracketing p → (D Y ⥤ D X)
  | _, _, _, .nil _ => 𝟭 _
  | _, _, _, .single f => U f
  | _, _, _, .comp a b =>
      integralQuotientBracketFunctor D U b ⋙ integralQuotientBracketFunctor D U a

/-- The comparison associated to a parenthesization, recursively using only the given
canonical compositor and inverse-image unitor. Equal composites use equality transport.
Source: finite-string clause, Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
def integralQuotientBracketComparison
    (D : Scheme.{t} → Type a) [∀ X : Scheme.{t}, Category.{v} (D X)]
    (U : ∀ {X Y : Scheme.{t}}, (X ⟶ Y) → (D Y ⥤ D X))
    (c : ∀ {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z), U (f ≫ g) ≅ U g ⋙ U f)
    (e : ∀ X : Scheme.{t}, U (𝟙 X) ≅ 𝟭 (D X)) :
    ∀ {X Y : Scheme.{t}} {p : Quiver.Path X Y} (b : IntegralQuotientBracketing p),
      U (CategoryTheory.composePath p) ≅ integralQuotientBracketFunctor D U b
  | _, _, _, .nil X => e X
  | _, _, _, .single f =>
      eqToIso (congrArg (fun g ↦ U g) (CategoryTheory.composePath_toPath f))
  | _, _, _, .comp (p := p) (q := q) a b =>
      eqToIso (congrArg (fun g ↦ U g) (CategoryTheory.composePath_comp p q)) ≪≫
        c (CategoryTheory.composePath p) (CategoryTheory.composePath q) ≪≫
        Functor.isoWhiskerLeft (U (CategoryTheory.composePath q))
          (integralQuotientBracketComparison D U c e a) ≪≫
        Functor.isoWhiskerRight (integralQuotientBracketComparison D U c e b)
          (integralQuotientBracketFunctor D U a)

/-- Clause-by-clause packaging of mixed coherence; every field is an equality of the
specified transformations, rather than an assumption supplying arbitrary comparisons.
Source: Stacks 0D6D, with the node's mixed tensor-generator calculations
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
```

Original structure (verbatim):

```lean
structure IntegralQuotientMixedCoherence (l : ℕ) [Fact l.Prime] : Prop where
  /-- The geometric/scalar square, as transformations of whole diagrams. -/
  ordinary_mixed : ∀
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    {V W Z : Scheme.{t}}
    [∀ x : V, Invertible (l : V.residueField x)]
    [∀ x : W, Invertible (l : W.residueField x)]
    [∀ x : Z, Invertible (l : Z.residueField x)]
    (h : Z ⟶ W) (k : W ⟶ V),
    Functor.whiskerRight (integralComparisonSequenceComposition l E h k).hom
      ((integralComparisonSequenceScalarModel l E L ι Z).E) ≫
        Functor.whiskerLeft (integralComparisonSequencePullback l E k)
          (integralComparisonSequenceScalarPullback l E L ι h).hom ≫
        Functor.whiskerRight (integralComparisonSequenceScalarPullback l E L ι k).hom
          (integralComparisonSequencePullback l L h) =
      (integralComparisonSequenceScalarPullback l E L ι (h ≫ k)).hom ≫
        Functor.whiskerLeft ((integralComparisonSequenceScalarModel l E L ι V).E)
          (integralComparisonSequenceComposition l L h k).hom
  /-- Multiplication is compatible with the scalar/pullback comparison. -/
  ordinary_scalar_unit : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)] (f : X ⟶ Y),
    (integralComparisonSequenceScalarPullback l E E (AlgHom.id ℚ_[l] E) f).hom ≫
        Functor.whiskerRight (integralComparisonSequenceScalarUnit l E Y).hom
          (integralComparisonSequencePullback l E f) =
      Functor.whiskerLeft (integralComparisonSequencePullback l E f)
        (integralComparisonSequenceScalarUnit l E X).hom
  /-- The associator multiplies successive coefficient factors, including equal fields. -/
  ordinary_scalar_tower : ∀
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (j : L →ₐ[ℚ_[l]] M) {X Y : Scheme.{t}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)] (f : X ⟶ Y),
    Functor.whiskerRight (integralComparisonSequenceScalarPullback l E L ι f).hom
      ((integralComparisonSequenceScalarModel l L M j X).E) ≫
        Functor.whiskerLeft ((integralComparisonSequenceScalarModel l E L ι Y).E)
          (integralComparisonSequenceScalarPullback l L M j f).hom ≫
        Functor.whiskerRight (integralComparisonSequenceScalarComposition l E L ι M j Y).hom
          (integralComparisonSequencePullback l M f) =
      Functor.whiskerLeft (integralComparisonSequencePullback l E f)
          (integralComparisonSequenceScalarComposition l E L ι M j X).hom ≫
        (integralComparisonSequenceScalarPullback l E M (j.comp ι) f).hom
  /-- Three-arrow associativity, with the canonical identification of equal composites. -/
  ordinary_associative : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {T V W Z : Scheme.{t}}
    [∀ x : T, Invertible (l : T.residueField x)]
    [∀ x : V, Invertible (l : V.residueField x)]
    [∀ x : W, Invertible (l : W.residueField x)]
    [∀ x : Z, Invertible (l : Z.residueField x)]
    (f : Z ⟶ W) (g : W ⟶ V) (h : V ⟶ T),
    (integralComparisonSequenceComposition l E (f ≫ g) h).hom ≫
        Functor.whiskerLeft (integralComparisonSequencePullback l E h)
          (integralComparisonSequenceComposition l E f g).hom =
      eqToHom (congrArg (fun k ↦ integralComparisonSequencePullback l E k) (Category.assoc f g h)) ≫
        (integralComparisonSequenceComposition l E f (g ≫ h)).hom ≫
        Functor.whiskerRight (integralComparisonSequenceComposition l E g h).hom
          (integralComparisonSequencePullback l E f)
  /-- Both geometric unit laws, with their scheme-morphism equality identifications. -/
  ordinary_unital : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)] (f : X ⟶ Y),
    ((integralComparisonSequenceComposition l E (𝟙 X) f).hom ≫
        Functor.whiskerLeft (integralComparisonSequencePullback l E f)
          (integralComparisonSequenceUnit l E X).hom =
      eqToHom (congrArg (fun k ↦ integralComparisonSequencePullback l E k) (Category.id_comp f))) ∧
    ((integralComparisonSequenceComposition l E f (𝟙 Y)).hom ≫
        Functor.whiskerRight (integralComparisonSequenceUnit l E Y).hom
          (integralComparisonSequencePullback l E f) =
      eqToHom (congrArg (fun k ↦ integralComparisonSequencePullback l E k) (Category.comp_id f)))
  /-- All parenthesizations of every finite string give the same comparison. -/
  ordinary_finite : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (p : Quiver.Path X Y) (_hp : IntegralQuotientPathInvertible l p)
    (a b : IntegralQuotientBracketing p),
    ∃ h : integralQuotientBracketFunctor (fun W ↦ coefficientSequenceModules.{t, u} l E W)
        (integralComparisonSequencePullback.{t, u} l E) a =
      integralQuotientBracketFunctor (fun W ↦ coefficientSequenceModules.{t, u} l E W)
        (integralComparisonSequencePullback.{t, u} l E) b,
    integralQuotientBracketComparison (fun W ↦ coefficientSequenceModules.{t, u} l E W)
        (integralComparisonSequencePullback.{t, u} l E)
        (integralComparisonSequenceComposition.{t, u} l E)
        (integralComparisonSequenceUnit.{t, u} l E) a ≪≫ eqToIso h =
      integralQuotientBracketComparison (fun W ↦ coefficientSequenceModules.{t, u} l E W)
        (integralComparisonSequencePullback.{t, u} l E)
        (integralComparisonSequenceComposition.{t, u} l E)
        (integralComparisonSequenceUnit.{t, u} l E) b
  /-- The geometric/scalar square, as transformations of whole diagrams. -/
  derived_mixed : ∀
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    {V W Z : Scheme.{t}}
    [∀ x : V, Invertible (l : V.residueField x)]
    [∀ x : W, Invertible (l : W.residueField x)]
    [∀ x : Z, Invertible (l : Z.residueField x)]
    (h : Z ⟶ W) (k : W ⟶ V),
    Functor.whiskerRight (integralComparisonSystemComposition l E h k).hom
      (integralComparisonDerivedSequenceScalar l E L ι Z) ≫
        Functor.whiskerLeft (integralComparisonDerivedSequencePullback l E k)
          (integralComparisonSystemScalarPullback l E L ι h).hom ≫
        Functor.whiskerRight (integralComparisonSystemScalarPullback l E L ι k).hom
          (integralComparisonDerivedSequencePullback l L h) =
      (integralComparisonSystemScalarPullback l E L ι (h ≫ k)).hom ≫
        Functor.whiskerLeft (integralComparisonDerivedSequenceScalar l E L ι V)
          (integralComparisonSystemComposition l L h k).hom
  /-- Multiplication is compatible with the scalar/pullback comparison. -/
  derived_scalar_unit : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)] (f : X ⟶ Y),
    (integralComparisonSystemScalarPullback l E E (AlgHom.id ℚ_[l] E) f).hom ≫
        Functor.whiskerRight (integralComparisonSystemScalarUnit l E Y).hom
          (integralComparisonDerivedSequencePullback l E f) =
      Functor.whiskerLeft (integralComparisonDerivedSequencePullback l E f)
        (integralComparisonSystemScalarUnit l E X).hom
  /-- The associator multiplies successive coefficient factors, including equal fields. -/
  derived_scalar_tower : ∀
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (j : L →ₐ[ℚ_[l]] M) {X Y : Scheme.{t}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)] (f : X ⟶ Y),
    Functor.whiskerRight (integralComparisonSystemScalarPullback l E L ι f).hom
      (integralComparisonDerivedSequenceScalar l L M j X) ≫
        Functor.whiskerLeft (integralComparisonDerivedSequenceScalar l E L ι Y)
          (integralComparisonSystemScalarPullback l L M j f).hom ≫
        Functor.whiskerRight (integralComparisonSystemScalarComposition l E L M ι j Y).hom
          (integralComparisonDerivedSequencePullback l M f) =
      Functor.whiskerLeft (integralComparisonDerivedSequencePullback l E f)
          (integralComparisonSystemScalarComposition l E L M ι j X).hom ≫
        (integralComparisonSystemScalarPullback l E M (j.comp ι) f).hom
  /-- Three-arrow associativity, with the canonical identification of equal composites. -/
  derived_associative : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {T V W Z : Scheme.{t}}
    [∀ x : T, Invertible (l : T.residueField x)]
    [∀ x : V, Invertible (l : V.residueField x)]
    [∀ x : W, Invertible (l : W.residueField x)]
    [∀ x : Z, Invertible (l : Z.residueField x)]
    (f : Z ⟶ W) (g : W ⟶ V) (h : V ⟶ T),
    (integralComparisonSystemComposition l E (f ≫ g) h).hom ≫
        Functor.whiskerLeft (integralComparisonDerivedSequencePullback l E h)
          (integralComparisonSystemComposition l E f g).hom =
      eqToHom (congrArg (fun k ↦ integralComparisonDerivedSequencePullback l E k) (Category.assoc f
        g h)) ≫
        (integralComparisonSystemComposition l E f (g ≫ h)).hom ≫
        Functor.whiskerRight (integralComparisonSystemComposition l E g h).hom
          (integralComparisonDerivedSequencePullback l E f)
  /-- Both geometric unit laws, with their scheme-morphism equality identifications. -/
  derived_unital : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)] (f : X ⟶ Y),
    ((integralComparisonSystemComposition l E (𝟙 X) f).hom ≫
        Functor.whiskerLeft (integralComparisonDerivedSequencePullback l E f)
          (integralComparisonSystemUnit l E X).hom =
      eqToHom (congrArg (fun k ↦ integralComparisonDerivedSequencePullback l E k) (Category.id_comp
        f))) ∧
    ((integralComparisonSystemComposition l E f (𝟙 Y)).hom ≫
        Functor.whiskerRight (integralComparisonSystemUnit l E Y).hom
          (integralComparisonDerivedSequencePullback l E f) =
      eqToHom (congrArg (fun k ↦ integralComparisonDerivedSequencePullback l E k) (Category.comp_id
        f)))
  /-- All parenthesizations of every finite string give the same comparison. -/
  derived_finite : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (p : Quiver.Path X Y) (_hp : IntegralQuotientPathInvertible l p)
    (a b : IntegralQuotientBracketing p),
    ∃ h : integralQuotientBracketFunctor (fun W ↦ coefficientSequenceDerived.{t, u} l E W)
        (integralComparisonDerivedSequencePullback.{t, u} l E) a =
      integralQuotientBracketFunctor (fun W ↦ coefficientSequenceDerived.{t, u} l E W)
        (integralComparisonDerivedSequencePullback.{t, u} l E) b,
    integralQuotientBracketComparison (fun W ↦ coefficientSequenceDerived.{t, u} l E W)
        (integralComparisonDerivedSequencePullback.{t, u} l E)
          (integralComparisonSystemComposition.{t, u} l E) (integralComparisonSystemUnit.{t, u} l E)
          a ≪≫ eqToIso h =
      integralQuotientBracketComparison (fun W ↦ coefficientSequenceDerived.{t, u} l E W)
        (integralComparisonDerivedSequencePullback.{t, u} l E)
          (integralComparisonSystemComposition.{t, u} l E) (integralComparisonSystemUnit.{t, u} l E)
          b

```

## New

The path and bracketing API now lives in
`Sheaf.Paper.QuotientSystemMixedCoherenceData`, publicly re-exported by the item:

```lean
def IntegralQuotientPathInvertible (l : ℕ) {X : Scheme.{t}} :
    ∀ {Y : Scheme.{t}}, Quiver.Path X Y → Prop
  | _, .nil => ∀ x : X, Nonempty (Invertible (l : X.residueField x))
  | Y, .cons p _ => IntegralQuotientPathInvertible l p ∧
      ∀ y : Y, Nonempty (Invertible (l : Y.residueField y))

/-- Binary parenthesizations of a fixed finite string, with empty pieces permitted.
Source: the finite-string assertion of the node, Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
inductive IntegralQuotientBracketing :
    {X Y : Scheme.{t}} → Quiver.Path X Y → Type (t + 1)
  | nil (X : Scheme.{t}) : IntegralQuotientBracketing (Quiver.Path.nil : Quiver.Path X X)
  | single {X Y : Scheme.{t}} (f : X ⟶ Y) : IntegralQuotientBracketing f.toPath
  | comp {X Y Z : Scheme.{t}} {p : Quiver.Path X Y} {q : Quiver.Path Y Z}
      (a : IntegralQuotientBracketing p) (b : IntegralQuotientBracketing q) :
      IntegralQuotientBracketing (p.comp q)

/-- Interpret the parenthesized string by iterated pullback, retaining its entire diagram.
Source: finite-string clause, Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
@[reducible]
def integralQuotientBracketFunctor
    (D : Scheme.{t} → Type a) [∀ X : Scheme.{t}, Category.{v} (D X)]
    (U : ∀ {X Y : Scheme.{t}}, (X ⟶ Y) → (D Y ⥤ D X))
    {X Y : Scheme.{t}} {p : Quiver.Path X Y} (b : IntegralQuotientBracketing p) :
    D Y ⥤ D X :=
  match b with
  | .nil _ => 𝟭 _
  | .single f => U f
  | .comp a b =>
      integralQuotientBracketFunctor D U b ⋙ integralQuotientBracketFunctor D U a
termination_by structural b

/-- The comparison associated to a parenthesization, recursively using only the given
canonical compositor and inverse-image unitor. Equal composites use equality transport.
Source: finite-string clause, Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
@[reducible]
def integralQuotientBracketComparison
    (D : Scheme.{t} → Type a) [∀ X : Scheme.{t}, Category.{v} (D X)]
    (U : ∀ {X Y : Scheme.{t}}, (X ⟶ Y) → (D Y ⥤ D X))
    (c : ∀ {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z), U (f ≫ g) ≅ U g ⋙ U f)
    (e : ∀ X : Scheme.{t}, U (𝟙 X) ≅ 𝟭 (D X))
    {X Y : Scheme.{t}} {p : Quiver.Path X Y} (b : IntegralQuotientBracketing p) :
    U (CategoryTheory.composePath p) ≅ integralQuotientBracketFunctor D U b :=
  match b with
  | .nil X => e X
  | .single f =>
      eqToIso (congrArg (fun g ↦ U g) (CategoryTheory.composePath_toPath f))
  | .comp (p := p) (q := q) a b =>
      eqToIso (congrArg (fun g ↦ U g) (CategoryTheory.composePath_comp p q)) ≪≫
        c (CategoryTheory.composePath p) (CategoryTheory.composePath q) ≪≫
        Functor.isoWhiskerLeft (U (CategoryTheory.composePath q))
          (integralQuotientBracketComparison D U c e a) ≪≫
        Functor.isoWhiskerRight (integralQuotientBracketComparison D U c e b)
          (integralQuotientBracketFunctor D U a)
termination_by structural b


```

The twelve original field propositions are copied literally into the public
`integralQuotientClause...` definitions of the item. No binder, universe, equality
transport, assumption or conclusion changes. The structure uses those definitions:

```lean
structure IntegralQuotientMixedCoherence (l : ℕ) [Fact l.Prime] : Prop where
  /-- The geometric/scalar square, as transformations of whole diagrams. -/
  ordinary_mixed : integralQuotientClauseOrdinaryMixed.{t, u} l
  /-- Multiplication is compatible with the scalar/pullback comparison. -/
  ordinary_scalar_unit : integralQuotientClauseOrdinaryScalarUnit.{t, u} l
  /-- The associator multiplies successive coefficient factors, including equal fields. -/
  ordinary_scalar_tower : integralQuotientClauseOrdinaryScalarTower.{t, u} l
  /-- Three-arrow associativity, with the canonical identification of equal composites. -/
  ordinary_associative : integralQuotientClauseOrdinaryAssociative.{t, u} l
  /-- Both geometric unit laws, with their scheme-morphism equality identifications. -/
  ordinary_unital : integralQuotientClauseOrdinaryUnital.{t, u} l
  /-- All parenthesizations of every finite string give the same comparison. -/
  ordinary_finite : integralQuotientClauseOrdinaryFinite.{t, u} l
  /-- The geometric/scalar square, as transformations of whole diagrams. -/
  derived_mixed : integralQuotientClauseDerivedMixed.{t, u} l
  /-- Multiplication is compatible with the scalar/pullback comparison. -/
  derived_scalar_unit : integralQuotientClauseDerivedScalarUnit.{t, u} l
  /-- The associator multiplies successive coefficient factors, including equal fields. -/
  derived_scalar_tower : integralQuotientClauseDerivedScalarTower.{t, u} l
  /-- Three-arrow associativity, with the canonical identification of equal composites. -/
  derived_associative : integralQuotientClauseDerivedAssociative.{t, u} l
  /-- Both geometric unit laws, with their scheme-morphism equality identifications. -/
  derived_unital : integralQuotientClauseDerivedUnital.{t, u} l
  /-- All parenthesizations of every finite string give the same comparison. -/
  derived_finite : integralQuotientClauseDerivedFinite.{t, u} l

```

The existing scalar comparison definitions retain their inferred result types,
now written explicitly; their existence/uniqueness proofs and definitions are moved
to the shared data module. No arbitrary witness of mere existence is used.

## Users

The downstream textual-use audit found four external users; the other transitive
importers do not mention the changed definitions. The bracketing definitions have
no external textual user. Public re-export preserves source compatibility.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.CounitRealizationSubstitution | no current claim found | Uses relocated scalar comparisons through unchanged public re-export; no adaptation. |
| Sheaf.TraceFormula.ScalarModelAssociativity | no current claim found | Uses relocated scalar associator through unchanged public re-export; no adaptation. |
| Sheaf.TraceFormula.ScalarModelUnit | no current claim found | Uses relocated scalar unitor through unchanged public re-export; no adaptation. |
| Sheaf.Paper.QuotientSystemMixedCoherence | U4 | Original twelve fields assembled from smaller lemmas. |
| Sheaf.Paper.FdPullbackSignedShiftWordTransport | no current claim found | Stores unchanged IntegralQuotientMixedCoherence proposition in Transport.mixed; no adaptation. |
| Sheaf.Paper.PullbackIdentitiesScalarExtension | no current claim found | Applies the projection `(integralQuotientMixedCoherence l).derived_mixed E L ι h k`, whose field type is now `integralQuotientClauseDerivedMixed l` (definitionally the original); uses relocated scalar comparisons through re-export; compiles unchanged (reviewer, 2026-10-25). |
| Sheaf.Paper.WholeTowerIntegralPullbackComparison | no current claim found | Direct importer; mentions no changed name; compiles unchanged (reviewer, 2026-10-25). |
| Sheaf.Paper.QuotientSystemMixedCoherenceData | new in this delivery | Relocates data declarations with the same public names. |
| Sheaf.Paper.SequenceDerivedAssociativity | new in this delivery | Uses only the shared canonical comparison API. |
| Sheaf.Paper.SequenceFiniteBracketingCoherence | new in this delivery | Uses unchanged bracketing constructors and interpretation. |
| Sheaf.Paper.SequenceDerivedMixedSquare | new in this delivery | Uses shared canonical comparison API. |
| Sheaf.Paper.SequenceDerivedScalarUnit | new in this delivery | Uses shared canonical comparison API. |
| Sheaf.Paper.SequenceDerivedScalarTower | new in this delivery | Uses shared canonical comparison API. |

The independent reader should compare the clause bodies and original field types
modulo whitespace, and check the constructor equations and the stored proposition.
Targets using the factored definition require the normal statement review.

## Status

landed 20261025T164455-L-1022707 2026-10-25 (merge of deliver/U4/Sheaf.Paper.QuotientSystemMixedCoherence)
