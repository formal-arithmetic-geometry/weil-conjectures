# CategoryTheory.CoefficientStageDescent.texact_coefficient_stage_descent

## Reason

Prove the existing theorem with private proved helpers and a private proof import of
CohomologyComparisonPasting. Scoped elaboration options and local irreducibility
attributes prevent expansion of the coefficient-ring construction during the
coefficient-family proof. The stage-system argument is proved generically in a private
helper so specializing it does not repeatedly compare tensor-category instances. They do not change the
underlying constructions, signatures or exported instance behavior. The original
written theorem signature and the public import list were compared byte-for-byte
and are unchanged. The command
scanner may conservatively classify these proof-context commands as interface edits.
No consumer adaptation is required and no target statement changes its meaning.

## Old

```lean
import Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Colimit.Module
```

The theorem body was `by sorry`, with no local proof helpers or coefficient-family
unfolding controls.

## New

```lean
import Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison
import Sheaf.CategoryTheory.Triangulated.CohomologyComparisonPasting
```

The theorem has a complete proof. All existing public definitions, public imports
and theorem signatures are unchanged. Private helpers and theorem-scoped elaboration
options are implementation details. Local irreducibility is used for the existing
coefficient ring, absolute value and uniformizer definitions; their original bodies
are unchanged and importers retain the original reducibility attributes.

## Users

`tools/downstream.py Sheaf.CategoryTheory.Triangulated.CoefficientStageDescent`
finds exactly one transitive importer. The `--uses texact_coefficient_stage_descent`
check finds no occurrence in that importer.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Triangulated.CoefficientStageDescent | C6 | Proof and private helpers. |
| Sheaf.Paper.ZlOpenExtensionTExact | unclaimed | Existing public interface unchanged. |

## Status

landed 20261025T094951-L-3278416 2026-10-25 (merge of deliver/C6/Sheaf.CategoryTheory.Triangulated.CoefficientStageDescent)
