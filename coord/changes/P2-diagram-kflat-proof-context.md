# CochainComplex.exists_diagram_isKFlatResolution and CochainComplex.diagram_pullback_quasiIso

## Reason

The static stage-3 gate detects the extra `open` commands and scoped zero-object
notation used in the complete proofs and private helpers. These commands only resolve
names and notation inside this module. Every existing public signature and public import
is unchanged. No definition is changed; the two new private definitions transpose a
diagram and its morphism, and no public signature or definition uses them. No target
statement or target definition changes, and no forced adaptation is needed.

## Old

```lean
open CategoryTheory
```

The two public theorem signatures are unchanged from the repository version. Only their
proofs were `by sorry`.

## New

```lean
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ZeroObject
```

Both theorems now have complete proofs. The added scope gives `0` its usual zero-object
meaning in the tensor argument. The added opens resolve the biproduct, evaluation,
colimit and tensor names. These commands do not export new instances or notation.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.DiagramKFlatReplacements --uses
exists_diagram_isKFlatResolution` and the same command for `diagram_pullback_quasiIso`
both report zero downstream modules and the item's own occurrence only.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.DiagramKFlatReplacements | P2 | Proof-local context; signatures identical. |

The item can be needed by a parent's unproved argument before that parent imports it;
no source consumer currently requires an adaptation. All original public imports remain.

## Status

landed 20261018T062843-L-667801 2026-10-18 (merge of deliver/P2/Sheaf.Algebra.Homology.DiagramKFlatReplacements)
