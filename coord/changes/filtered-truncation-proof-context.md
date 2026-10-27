# CochainComplex.FiniteFiltered.filteredTruncationTriangle

## Reason

Preflight classifies the proof-context commands added while proving this item as
changes visible to other modules, and requires this record. Namespace openings
provide the category composition and zero-object triangle API to private helpers;
the three backward elaboration options allow the definitionally equal full
subcategory and localization presentations to elaborate. These are elaboration
commands, with no change to an existing declaration's type, attributes, public
imports, or body of a public definition. The only new instance is explicitly
`private` and expresses the localization property of a private functor.

## Old

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
```

The existing theorem signature was:

```lean
theorem filteredTruncationTriangle : Nonempty (FilteredTruncationData A)
```

## New

```lean
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Pretriangulated
open ZeroObject

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
```

The theorem signature remains verbatim:

```lean
theorem filteredTruncationTriangle : Nonempty (FilteredTruncationData A)
```

## Users

`tools/downstream.py` lists the following five downstream modules, and `--uses`
finds a direct use of the theorem only in `ExactFilteredCoefficientChange` and the
item's own declaration. No consumer adaptation is necessary: each existing public
signature and the public import of `FilteredTruncationData` remain unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.FilteredTruncationTriangle | M8 | Proof and private helpers added; signature unchanged |
| Sheaf.Algebra.Homology.ExactFilteredCoefficientChange | unclaimed | Existing theorem application retains its type |
| Sheaf.Algebra.Homology.FilteredDerivedHomCalculusUniverse | unclaimed | No public interface change |
| Sheaf.Algebra.Homology.FilteredGlobalHomExactAdjunction | unclaimed | No public interface change |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | unclaimed | No public interface change |
| Sheaf.CategoryTheory.FilteredFunctorGradedComparison | Y9 | No public interface change; no edits |

The new module `FilteredTruncationConstruction` exposes only the explicit core
structure and its matching construction theorem, documented by the new DAG node.
No target statement or definition used by a target changes meaning.

## Status

landed 20261023T135043-L-2829779 2026-10-23 (merge of deliver/M8/Sheaf.Algebra.Homology.FilteredTruncationTriangle)
