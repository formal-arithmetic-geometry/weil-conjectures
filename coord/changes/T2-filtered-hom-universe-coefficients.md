# CochainComplex.FiniteFiltered.FilteredTruncationData

## Reason

This is a DAG citation correction, not a Lean definition change. The existing
`FilteredDerivedHomCalculus` module contains the concrete finite-filtered
localizations, truncations, and canonical-coefficient Hom calculus. Its original
DAG node was subsequently attached to the independent coefficient-universe
interface in `FilteredDerivedHomCalculusUniverse`. The new proof of that interface
uses exact coefficient transport and the existing universal truncation Hom
bijection. Leaving the infrastructure citation attached to the enlarged Hom
interface would introduce a spurious cycle.

Record the already-existing base theorem and its unchanged seven-step proof plan
as `lem-trf-filtered-derived-hom-calculus-base`. Redirect the infrastructure
citation in `def-trf-filtered-truncation-data` to this base node. No Lean file
other than the assigned item and the new coefficient-change module is changed.
No existing declaration is renamed, removed, weakened, or given a new hole.

## Old

Lean signature, unchanged:

```lean
structure FilteredTruncationData where
```

The definition node cites `[lem-trf-filtered-derived-hom-calculus]` for the concrete
localization infrastructure, and its first statement dependency is
`lem-trf-filtered-derived-hom-calculus`.

## New

Lean signature, unchanged:

```lean
structure FilteredTruncationData where
```

The same sentence cites `[lem-trf-filtered-derived-hom-calculus-base]`, and its
first statement dependency is `lem-trf-filtered-derived-hom-calculus-base`.
All mathematical clauses and all fields of the Lean structure stay verbatim.
The complete old node statement and dependencies are retained in its
`statement_change` record, with its sole DAG citer audited.

## Users

The read-only `tools/downstream.py` audit reports three downstream modules and
two modules with textual uses of the declaration. None needs adaptation because
no Lean declaration, body, or import changes in this definition module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.FilteredTruncationData | unclaimed; unchanged | Defining module; citation only changes in its DAG node. |
| Sheaf.Algebra.Homology.FilteredTruncationTriangle | unclaimed; unchanged | Same structure and theorem; its DAG use still holds. |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | unclaimed; unchanged | Same imported interface. |
| Sheaf.CategoryTheory.FilteredFunctorGradedComparison | unclaimed; unchanged | Same imported interface. |

The new coefficient-change theorem imports and uses the unchanged truncation
triangle theorem. The assigned item's existing public structures, public import,
and theorem signature have been compared verbatim against the shared source.
No target declaration or definition used by a target changes meaning, so the
statement-equivalence review is not reopened by this citation correction.

## Status

landed 20261021T011038-L-2032412 2026-10-21 (merge of deliver/T2/Sheaf.Algebra.Homology.FilteredDerivedHomCalculusUniverse)
