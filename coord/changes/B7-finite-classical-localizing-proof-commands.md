# AlgebraicGeometry.ProEtale.finite_classical_localizing

## Reason

The completed proof adds two elaborator transparency options and opens the
`ZeroObject` notation scope. The static delivery checker classifies these module
commands as an interface change and requires this record. They support inference
through the recorded coefficient functors and notation for the zero module.
All six original public imports and the entire theorem signature are verbatim
unchanged. Existing definitions and their meanings are unchanged. Every new helper
is private and proved; there are no new public declarations or instances.

## Old

The original module-command block, verbatim:

```lean
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
```

## New

The delivered module-command block, verbatim:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject
```

These options control proof elaboration in this file; the kernel checks the resulting
terms. The scope supplies notation in the private helpers and theorem proof. Neither
introduces a hypothesis, changes a conclusion, nor changes a coefficient construction.
Proof-only imports supply the existing comparison, exactness, and constructibility APIs.
The updated DAG and report list their uses and the obsolete dependencies removed.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing --uses
AlgebraicGeometry.ProEtale.finite_classical_localizing` reports zero downstream
modules and only the item's own occurrence of the theorem name. No external module
needs adaptation. Parents that still cite the node in their unfinished argument keep
the same statement and six-clause unit route.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | B7 | Completed proof; unchanged signature. |

## Status

landed 20261021T203426-L-3739310 2026-10-21 (merge of deliver/B7/Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing)
