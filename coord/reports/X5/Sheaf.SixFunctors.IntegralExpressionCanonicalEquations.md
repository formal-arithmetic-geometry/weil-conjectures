## What changed

Proved `WeilConjectures.IntegralSystemRealization.ExpressionRecursion.canonicalComparisons_equations`
by induction on the actual expression tree. A private categorical transport lemma identifies
inverse comparisons by the injectivity of the actual adjunction hom-set equivalence.
Private unary and tensor steps provide the required domain witnesses and invertibility;
the compact-support case applies the unary step first to the open expression and then to
the proper arrow. Both tensor children are retained, without a distinct-variable assumption.

The private Good-invariance lemmas transport normalization, the same common bounds, and
origins across isomorphisms. These follow the existing private calculations in
`Sheaf.SixFunctors.IntegralSupportCounitProjection`. The proof adds one private import,
`Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`, to obtain the closed-under-isomorphism
property of finite-level constructibility. Its node `lem-weil-proetale-dbc-triangulated`
is an auxiliary domain tool, not a replacement of the unit's route. The item's DAG proof
and proof dependencies now describe these calculations. There are no public interface,
statement, definition, instance, attribute, or source-library changes.

## Proved and sorry left

Closed the single original hole:
`WeilConjectures.IntegralSystemRealization.ExpressionRecursion.canonicalComparisons_equations`
(node `lem-sf-integral-expression-canonical-equations`). Proved 1 of 1 item sorries;
0 remain in the item, 0 added, and 0 split off. All new private helpers are completely proved.
The proof uses the existing invertibility theorem `transposeComparison_isIso` through
`canonicalComparisons`; its pre-existing hole is outside this delivery.

The complete item proof compiled alone in 17.0 seconds. A subsequent compile of the
current dependency chain and both direct consumers passed, one file at a time in import
order: `IntegralExpressionRecursionData` (58.6 s), `IntegralExpressionTransposeIsIso`
(5.0 s), the proved equations (23.2 s), `IntegralExpressionCanonicalSupport` (31.6 s),
and `IntegralExpressionRecursion` (4.6 s). The four unchanged dependency/consumer
copies were then removed from the delivery sandbox. No warnings or errors were reported.

## No longer needed

None. No imports, nodes, or modules are pruned. The three previously declared proof
dependencies remain used; the constructibility domain tool is additionally needed.
No new statement modules or new DAG nodes were created.

## Where the brief, the DAG or earlier work was wrong

The recorded red build reported a bad import of `IntegralExpressionTransposeIsIso`,
and the rework row traces this to `CoefficientChangeOpenImmersion`. The shared snapshot
now contains the restored item and its dependency modules. The original item compiles
against the published artifacts, so no declaration rename or interface repair was
justified by the current sources. This delivery supplies a real proof rather than
claiming that the successful unchanged compile repaired the old build.

The existing induction plan is correct. Its Good-transport step needs explicit
isomorphism-invariance calculations and finite-level constructibility's invariance;
these are now proved locally and the additional dependency is recorded in the DAG.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralExpressionCanonicalEquations": "1e62d0238f8ec32f50d87508f580fb89932ee3f4"}, "results": {"Sheaf.SixFunctors.IntegralExpressionCanonicalSupport": {"hash": "c3a5a705c900269711ee1bf7a48fb343daed9723", "status": "OK"}, "Sheaf.SixFunctors.IntegralExpressionRecursion": {"hash": "20f8680941bf19a94eabc365d8ff61b643885436", "status": "OK"}}, "seconds": 63, "time": "2026-10-28T01:03:06+0800", "transitive": 0, "version": 1}
```

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
