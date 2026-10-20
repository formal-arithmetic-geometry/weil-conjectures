# CategoryTheory.cartanEilenberg_comparison_independence

## Reason

Restore the quarantined item listed in coord/rework.tsv without withdrawing its
statement, its completed proof, or its DAG attachment. The archived proof fails to
import: both DoubleComplexTotal providers declare the same constant names. The
presentations and two-column-image dependencies already use the adopted provider;
three unclaimed homotopy modules still use the Sheaf provider. Align those three
imports with the adopted provider. After resolving that collision, the item fails
at the removed HomPreservingSteps.hom accessor; use the current morphism projection.

The reproduced errors are:

```
import Sheaf.CategoryTheory.DoubleComplexTotal failed, environment already contains
'HomologicalComplex₂.secondFiltration_graded' from
WeilConjectures.CategoryTheory.DoubleComplexTotal
```

```
Unknown constant `CategoryTheory.FilteredObject.HomPreservingSteps.hom`
```

## Old

In CartanEilenbergDoubleComplexHomotopy,
CartanEilenbergDoubleComplexHomotopyComponents, and
CartanEilenbergDoubleComplexHomotopyFiltration:

```lean
public import Sheaf.CategoryTheory.DoubleComplexTotal
```

Additionally in CartanEilenbergDoubleComplexHomotopyFiltration:

```lean
import all Sheaf.CategoryTheory.DoubleComplexTotal
```

In the archived item's identity-comparison proof:

```lean
FilteredObject.HomPreservingSteps.hom (𝟙 (T P))
```

## New

In the same three modules:

```lean
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
```

Additionally in the filtration-factorization module:

```lean
import all WeilConjectures.CategoryTheory.DoubleComplexTotal
```

The proof expression becomes:

```lean
(𝟙 (T P) : T P ⟶ T P).hom
```

All public declaration signatures and all dependency proof bodies remain verbatim.
Only the item's one proof expression changes; its complete archived proof is restored.
The chosen import supplies the same finite supremum of diagonal inclusion images
at every filtration step. Its ambient PBC filtration structure differs from the
Sheaf structure, but these three theorem signatures expose only its step subobjects
and arrows, whose formulas agree. Their hypotheses, conclusions, and meaning stay
the same, including empty diagonal intervals and negative degrees. The factorization
module reuses the corresponding existing private helpers through import all.
No target statement, definition body, visibility, or adopted source file changes.

## Users

The source-only downstream.py checks for each of the three dependency modules list
CartanEilenbergComparisonHomotopy and the main homotopy module as the active
consumers. The quarantined assigned module is restored in this delivery. A direct
import scan through both lean/ and quarantine/ finds no other consumer.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CartanEilenbergComparisonIndependence | V3 | Restored; current identity-map hom projection; unchanged theorem signature. |
| Sheaf.CategoryTheory.CartanEilenbergDoubleComplexHomotopy | unclaimed | Adopted public total-complex import; unchanged theorem and proof. |
| Sheaf.CategoryTheory.CartanEilenbergDoubleComplexHomotopyComponents | unclaimed | Adopted public total-complex import; unchanged theorem and its existing hole. |
| Sheaf.CategoryTheory.CartanEilenbergDoubleComplexHomotopyFiltration | unclaimed | Adopted public and private-helper imports; unchanged theorem and proof. |
| Sheaf.CategoryTheory.CartanEilenbergComparisonHomotopy | unclaimed | Original source compiles unchanged against all three repaired dependencies. |

The restored item currently has no direct Lean importers in either tree. Its
DAG parents and unit records are retained. The consumer compile was performed
with an exact temporary copy in the sandbox, removed from the delivery afterward.
Each of the four delivery modules and this unchanged consumer compiled alone
through lcompile.py --all in dependency order, without errors or warnings.
No mathematical meaning of a target changes; no target statement review is reopened.

## Status

landed 20261020T235631-L-1198937 2026-10-20 (merge of deliver/V3/Sheaf.CategoryTheory.CartanEilenbergComparisonIndependence)
