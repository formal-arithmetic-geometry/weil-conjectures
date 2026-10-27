# WeilConjectures.CompletedQuotient.completedComparisonQuotientRealization

## Reason

The single theorem includes recursive normalization, canonical representative
identification, coherent transport, strict coherence and scalar realization. Separate
three genuine proof steps into independent public theorem modules so they can be
proved separately. Their statements require the existing definitions, so those
constructions move into CompletedComparisonQuotientRealizationDefs, re-exported by
public import from the original module. All existing names and signatures remain.
The theorem's complete statement is unchanged. This extraction was made to avoid
an import cycle between the original theorem and its split steps, before a timeout
was observed; it is not a division of a slow proof to evade the compile limit.

Profiling the definitions after removing unused proof imports found typeclass
search timing out on the tensor constructor of strictMap. Its tensor action now
supplies the complex category and all four objects to tensorHom explicitly,
with local irreducibility of the sheaf monoidal structure.
This is the same action on the same complexes and arrows; it changes no mathematical
definition. No target changes meaning.

## Old

```lean
def GoodExpressions {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y) {r : ℕ}
    (P : Fin r → (integralOperationsGoodComplex l E Y).FullSubcategory) : Prop :=
  ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f r W),
    StrictQuotient.SystemGood l E (strictValue l E (fun i ↦ quotient l E (P i).obj) A)
```

The data declarations quotient through ScalarAssociation, including the proved
sequencePullback_eq, are defined in
Sheaf.Paper.CompletedComparisonQuotientRealization.

The tensor branch of strictMap is:

```lean
  | _, .tensor A B => (strictMap a A) ⊗ₘ (strictMap a B)
```

## New

```lean
abbrev GoodExpressions {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y) {r : ℕ}
    (P : Fin r → (integralOperationsGoodComplex l E Y).FullSubcategory) : Prop :=
  ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f r W),
    StrictQuotient.SystemGood l E (strictValue l E (fun i ↦ quotient l E (P i).obj) A)
```

The same data declarations, with the same names and signatures, are defined in
Sheaf.Paper.CompletedComparisonQuotientRealizationDefs and re-exported through:

```lean
public import Sheaf.Paper.CompletedComparisonQuotientRealizationDefs
```

The tensor branch of strictMap is:

```lean
  | W, .tensor A B =>
      @MonoidalCategory.tensorHom (StrictQuotient.Complex l E W) _ _
        (strictValue l E N A) (strictValue l E N' A)
        (strictValue l E N B) (strictValue l E N' B)
        (strictMap a A) (strictMap a B)
```

GoodExpressions is now an abbrev of its identical predicate, so importing proof
modules can use its witness as the function expected by substitution. This changes
only transparency, not the predicate or its parameters. No other existing
construction body changes. The original theorem is reduced to
three smaller theorem obligations. Its assembly proves the counit reduction,
inverse comparison and unique structural transport equations directly, and uses
the existing scalar tower laws.

## Users

`python3 tools/downstream.py Sheaf.Paper.CompletedComparisonQuotientRealization`
reported zero current Lean downstream modules. The item is nevertheless retained:
its DAG parents still need it. Existing DAG parent statements remain unchanged,
and receive the exact same theorem and definition meanings. No forced adaptation
of another group's module is included.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedComparisonQuotientRealization | Y3 | Same signature and data, new proof assembly and public re-export |
| Sheaf.Paper.CompletedComparisonQuotientRealizationDefs | new in this packet | Owns the relocated unchanged data and explicit tensor action |
| Sheaf.Paper.CompletedComparisonQuotientNormalization | new in this packet | Uses those exact definitions for normalization and recursive substitution |
| Sheaf.Paper.CompletedComparisonCanonicalIdentification | new in this packet | Uses those exact definitions for canonical comparison identification |
| Sheaf.Paper.CompletedComparisonScalarLimitImage | new in this packet | Uses those exact definitions for scalar closure and limit realization |

## Status

landed 20261025T101942-L-3760431 2026-10-25 (merge of deliver/Y3/Sheaf.Paper.CompletedComparisonQuotientRealization)
