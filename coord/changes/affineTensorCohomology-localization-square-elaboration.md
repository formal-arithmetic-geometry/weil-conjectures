# RingTensorCohomology.affineTensorCohomology_localization_square

## Reason

The completed proof needs monoidal tensor notation, explicit change-of-rings
tensor notation, and the right tensor-factor algebra instance. The stage-3
static checker treats changes to `open` and `attribute` commands conservatively
as interface changes and requires this record. No existing declaration's
signature, visibility, definition or statement is changed. The item signature
is byte-for-byte identical to its DAG Lean record. These commands affect proof
elaboration inside this file and do not weaken any statement.

## Old

```lean
open CategoryTheory
open scoped TensorProduct

namespace RingTensorCohomology
```

## New

```lean
open CategoryTheory MonoidalCategory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology
```

The three new private helpers are proved and serve only the theorem's proof.
The theorem additionally uses the per-declaration elaboration option
`set_option backward.isDefEq.respectTransparency false in`; it changes no
elaborated signature. New proof imports are nonpublic. No target definition or
target statement changes, and no target semantic review is reopened.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.AffineTensorCohomologyLocalizationSquare | G2 | Same public statement; complete reduction proof and private helpers. |
| Sheaf.Algebra.Homology.AffineTensorCohomologyLocalizationIsos | unclaimed | Existing invocation and elaborated type unchanged; no adaptation required. |
| Sheaf.Algebra.Homology.AffineDerivedBaseChangeComparison | unclaimed | Transitive importer; no exposed statement or definition changes and no adaptation required. |

The downstream list is from `tools/downstream.py`; no downstream module is
edited by this delivery. There is no forced adaptation.

## Status

landed 20261013T145119-L-695927 2026-10-13 (merge of deliver/G2/Sheaf.Algebra.Homology.AffineTensorCohomologyLocalizationSquare)
