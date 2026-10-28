# AlgebraicGeometry.ProEtale.RationalP1.ScalarTraceWitness.exchange_eq

## Reason

The native exchange has expanded derived-functor endpoints, while the rest of
this calculation uses fixed module-object endpoints. Normalizing that conversion
at the specialized rational Tate line times out in the kernel. The profiled
attempt with an arbitrary coefficient ring and complex also exceeds 120 seconds.
The existing `secondPretraceExchangeMap` was introduced precisely to cache this
fixed-endpoint native component. Use it in the witness field too, so the proof
compares the same literal maps without repeating the conversion.

Separately, the node lem-sfb-scalar-trace-equation described composition of
unshifted Tate-line comparisons, while its Lean declaration and both parents
use ScalarTraceWitness. Correct its prose to the interface it actually carries.
The stale title and original source fields are maintainer-owned; their mismatch
is reported for the maintainer to reconcile.

## Old

```lean
structure ScalarTraceWitness
    (l : ℕ) [Fact l.Prime]
    (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hpl : p ≠ l) (Y : Scheme.{u}) [Y.Over (Spec (.of k))] : Prop where
  exchange_eq : secondTraceExchange l c k p hpl Y =
      (condensedAmbientExchange (coefficient l c).X (square Y)).app
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y))
          0).obj (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≫
      (moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).map
        (firstLineComparisonForTrace l c k p hpl Y).hom
```

The old node statement, verbatim:

For a prime l, a finite rational coefficient index c or the algebraic-closure index, and composable scheme arrows f:X→Y and g:Y→Z with l invertible in every residue field of X,Y,Z, let Λ=(coefficient l c).X and L_A=line l c A as in [def-sfb-rational-tate-pullback-comparison]. Then the canonical underived internal-module compositor c_f,g:(f≫g)*≅g*⋙f*, followed by f* of lineComparison(g) and lineComparison(f), equals lineComparison(f≫g). This is an equality of unshifted module maps, before taking degree-zero complexes, derived functors, shifts, exchange mates or adjunction units.

## New

```lean
structure ScalarTraceWitness
    (l : ℕ) [Fact l.Prime]
    (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hpl : p ≠ l) (Y : Scheme.{u}) [Y.Over (Spec (.of k))] : Prop where
  exchange_eq : secondTraceExchange l c k p hpl Y =
      secondPretraceExchangeMap (coefficient l c).X Y
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y))
          0).obj (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≫
      (moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).map
        (firstLineComparisonForTrace l c k p hpl Y).hom
```

`secondPretraceExchangeMap Λ Y M` is defined in
`Sheaf.Paper.RationalP1SecondPretraceData` by unfolding the fixed derived
pullback/pushforward aliases and applying exactly
`(condensedAmbientExchange Λ (square Y)).app M`. Thus the changed field is
definitionally equal to the old field: its mathematical content, arguments,
endpoints, and direction stay identical. No data is chosen, and no trace law
or new hypothesis is inserted. The theorem `scalar_trace_equation` keeps its
signature verbatim and now constructs the field by unfolding
`secondTraceExchange` and reflexivity. Local irreducibility attributes are
confined to this file and do not change imported interfaces.

The corrected node statement is the literal forward exchange on the shifted
Tate line, as recorded in statement_change with its old statement and both
citers. The schema requires the `by` field's stage-2 spelling even for this
stage-3 prose correction.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ScalarTraceEquation | F7 | Fold the field through the existing native wrapper; close its one proof hole. |
| Sheaf.Paper.ScalarComponentFromTrace | F6 | The existing witness hypothesis and its meaning are preserved; compile original against the change. |
| Sheaf.Paper.ScalarP1UnitMateComponent | unclaimed | The application of scalar_trace_equation keeps exactly the same signature; compile original against the change. |

These are the direct importers. The repository search finds no other user of
ScalarTraceWitness or its accessor. Both parent DAG nodes use this witness,
not the unshifted composition claim erroneously copied into the old prose.
No consumer source adaptation is needed.

## Status

landed 20261028T034746-L-3541393 2026-10-28 (merge of deliver/F7/Sheaf.Paper.ScalarTraceEquation)
