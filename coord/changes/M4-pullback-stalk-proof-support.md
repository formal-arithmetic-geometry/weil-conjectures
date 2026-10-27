# CategoryTheory.RingedToposMorphism.pullback_stalk

## Reason

Private proof support and scoped elaboration options implement the original
statement. All existing public signatures, definitions, attributes and public
imports are preserved. No target meaning changes and no consumer needs adaptation.

## Old

The original proof-only imports were:

```lean
import Sheaf.SecSmoothPurity.CochainInverseComparison
import Sheaf.CategoryTheory.GeometricModuleConstruction
```

The original theorem proof was:

```lean
by
  sorry
```

There were no private `compositePoint` or `stalkPresentation` helpers, and no
scoped elaboration options preceding the helper or theorem.

## New

The proof-only imports are:

```lean
import all Sheaf.SecSmoothPurity.CochainCompositeAlgebraic
import Sheaf.CategoryTheory.RingedSitePointScalarExtension
```

Both new helpers are private and completely proved. The theorem has a complete
assembly proof from the scalar-extension comparison at one point, whose
remaining proof is a separate public theorem and DAG node. The scoped options
preceding the private composite-point helper are:

```lean
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
```

They restrict elaboration to respect transparency while checking this private
construction. A scoped `set_option maxHeartbeats 800000 in` on the assembly
allows its dependent tensor expressions to elaborate; the compile-time limit
remains 60 seconds. No shared definition or its reduction behavior changes for
clients.

## Users

`tools/downstream.py Sheaf.CategoryTheory.RingedToposPullbackStalk --uses
pullback_stalk` reports zero downstream modules and only the item's own use.
Unfinished DAG parents remain represented by the unchanged original statement
and attachment. No caller, quarantined parent or source-library declaration is
removed or weakened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.RingedToposPullbackStalk | M4 | Original interface preserved; private proof support and theorem proof added. |

## Status

landed 20261027T094446-L-230316 2026-10-27 (merge of deliver/M4/Sheaf.CategoryTheory.RingedToposPullbackStalk)
