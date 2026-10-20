# AlgebraicGeometry.Scheme.exists_stalk_cardinality_bound_of_constructible

## Reason

Retire the duplicate `Sheaf.AlgebraicGeometry.ConstructibleStalkCardinalityBound`
in favour of `WeilConjectures.AlgebraicGeometry.ConstructibleStalkCardinalityBound`,
as requested by its depth-zero row in `coord/retire-items.tsv` and the human's
2026-10-20 retirement instruction. The public theorem signatures and complete import
lists agree verbatim. The upstream module has additional results and generalizes
its private constant-chart bounds from algebraically closed to separably closed
fields; no consumer uses those private helpers.

## Old

The duplicate module declares:

```lean
theorem exists_stalk_cardinality_bound_of_constructible
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F)) :
    ∃ N : ℕ, ∀ x : X,
      Finite (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj F) ∧
      Nat.card (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj F) ≤ N
```

Its sole direct consumer, `Sheaf.AlgebraicGeometry.ConstructibleCurveAnnihilator`,
contains this proof-only import:

```lean
import Sheaf.AlgebraicGeometry.ConstructibleStalkCardinalityBound
```

## New

Withdraw the duplicate module through `deleted.txt`; preserve the existing node
`lem-weil-pbc-constructible-stalk-cardinality-bound` and attach it to the unchanged
upstream theorem with the signature above. The consumer instead contains:

```lean
import WeilConjectures.AlgebraicGeometry.ConstructibleStalkCardinalityBound
```

No declaration, definition, proof body, or target statement changes. Both modules
import exactly the same dependencies, so the substitution introduces no additional
pair of duplicate dependency modules into the consumer's import environment.
The upstream theorem has only the axioms `propext`, `Classical.choice`, `Quot.sound`.
The adapted direct consumer compiles without warnings in 2.0 seconds.

## Users

`tools/downstream.py` reports the following six downstream modules. Only the direct
consumer imports the duplicate or mentions the theorem; its only edit is the
proof-only import replacement. All six currently have no claim holder.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ConstructibleCurveAnnihilator | unclaimed | Replace one proof-only import; unchanged proof and signatures compile. |
| Sheaf.AlgebraicGeometry.ConstructibleCurveSubPart | unclaimed | Indirect consumer; no change. |
| Sheaf.AlgebraicGeometry.ConstructibleCurveSubQuotient | unclaimed | Indirect consumer; no change. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardAssertions | unclaimed | Indirect consumer; no change. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardCoefficientControl | unclaimed | Indirect consumer; no change. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardConstructibleDescent | unclaimed | Indirect consumer; no change. |

The only DAG parent is `lem-weil-pbc-curve-constructible-annihilator`; its dependency
on the same cardinality-bound node remains valid. No node is deleted and the unit
`sk-thm-p1` route is preserved. The theorem's definitions do not change, so this
retirement does not reopen target-statement review.

## Status

landed 20261020T221134-L-4148411 2026-10-20 (merge of deliver/E6/Sheaf.AlgebraicGeometry.ConstructibleStalkCardinalityBound)
