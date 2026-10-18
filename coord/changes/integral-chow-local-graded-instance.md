# AlgebraicGeometry.exists_integral_chow_relatively_ample

## Reason

The proof mentions the polynomial Proj twisting module.
Its grading instance `MvPolynomial.gradedAlgebra` must be enabled locally to elaborate these
expressions. The stage-3 static gate classifies any added attribute command as an environment
change and requests this record. The annotation is local: it adds no global instance and
changes no declaration signature, definition, public import, visibility, or target meaning.
The proof imports the existing private helpers with `import all`; no helper is redeclared.

## Old

```lean
namespace AlgebraicGeometry
```

## New

```lean
namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.IntegralChowRelativelyAmple
--uses exists_integral_chow_relatively_ample` reports one downstream module, the parent
below. Its textual uses list includes only the assigned module’s declaration itself.
The parent’s source is unchanged: its theorem still has the same statement and uses no
new helper. There is no interface change that forces a consumer adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.IntegralChowRelativelyAmple | R4 | Proof uses existing imported helpers; original public signature unchanged. |
| Sheaf.AlgebraicGeometry.TopCoherentCohomologyFinite | unclaimed | No signature, visibility, definition or target-meaning change; no adaptation needed. |

## Status

landed 20261018T071218-L-1676227 2026-10-18 (merge of deliver/R4/Sheaf.AlgebraicGeometry.IntegralChowRelativelyAmple)
