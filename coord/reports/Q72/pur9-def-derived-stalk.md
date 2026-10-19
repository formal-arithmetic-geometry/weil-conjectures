# Stage-1 report: pur9-def-derived-stalk

## Files written

- `dag/nodes/sec-smooth-purity/pur9-def-derived-stalk.json`: definition; no new Mathlib leaf.
- `citations.json`: empty, because this definition has no proof steps.

## Attachments

None. The source and slopmaster2 searches found no declaration tagged `(blueprint: pur9-def-derived-stalk)` and no sorry-free declaration stating this definition.

## WANTED

None.

## What was wrong or changed

The imported statement's blueprint references `pur713-def-derived-pull` and `pur713-def-data`, but neither identifier exists in the current main-20261015 blueprint or DAG. The current DAG already has `def-weil-derived-pullback-tensor-hom`, whose finite-level clause defines exactly the required $D(X_{\Proet},\mathcal O_E/\varpi^n)$ and $L\bar x^*_{\mathcal O_E/\varpi^n}$, and `pur7710-def-derived-sections`, which defines the displayed $R\Gamma$. I replaced those stale references with these existing definitions and cited `def-kun-separably-closed` for the field condition. This keeps the source's construction and its allowance that $\operatorname{Spec}\Omega$ need not be finite type over $k$.

## Review by Q72

I read the item node, the unit `sk-prop-sf-trace-perfectness`, the chapter `sec-smooth-purity`, and the exact blueprint source `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sf-trace-perfectness/pur9-def-derived-stalk.md`. I also opened each statement used as a dependency: `def-pc-scheme` supplies the scheme notion, `def-kun-separably-closed` supplies the meaning of separably closed, `def-weil-derived-pullback-tensor-hom` supplies the finite-coefficient pro-etale derived category and derived pullback, and `pur7710-def-derived-sections` supplies the derived-sections functor on arbitrary schemes, including test schemes that need not be finite type. The revised statement uses each dependency for exactly the clause it states. There are no proof steps, so no citation quotes are required. I checked the edge cases $n\geq1$, $X=\varnothing$, and an arbitrary separably closed $\Omega$; the construction remains a formal definition in each case. The source's two stale identifiers were corrected explicitly rather than silently treated as existing nodes.

## What could not be finished

Nothing; the item is a definition and has no proof obligations.

## Second reading by Q72

- Item statement: checked against the exact main-20261015 blueprint node `pur9-def-derived-stalk` (order 2171); the derived-stalk formula, arbitrary scheme test point, and non-finite-type allowance agree, with the finite coefficient datum and standing invertibility convention now stated explicitly.
- Statement dependencies: read `sk-def-purity-conv`, `def-pc-scheme`, `def-kun-separably-closed`, `def-weil-derived-pullback-tensor-hom`, and `pur7710-def-derived-sections`; each supplies the coefficient datum, scheme, separably closed field, finite-level derived category/pullback, or derived sections used by the formula.
- Proof steps and citations: there are no proof steps for this definition, so `citations.json` correctly remains empty and no uncited argument is hidden in the node.
- Edge cases: checked (n=1), the n=0 boundary (excluded by the standing coefficient convention), (X=\varnothing), (K=0), and (X=\operatorname{Spec}\Omega); the definition is well-formed in each allowed case, including the empty scheme and zero complex.
- New nodes: none; the item is the imported blueprint definition, and no duplicate or Mathlib leaf is created.
- Changes made: added the standing coefficient/invertibility convention to the statement and added `sk-def-purity-conv` to `stmt_deps`, because the original split used (E), (\varpi), (n), and (\ell)-invertibility without a self-contained definition dependency.
