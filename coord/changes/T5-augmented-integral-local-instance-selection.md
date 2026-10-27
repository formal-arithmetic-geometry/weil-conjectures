# Local instance selection in augmented integral descent proofs

## Reason

The new proof imports expose generic abelian and derived-category instances with
maximum universes. Exclude the two overlapping instances while elaborating the
private gluing helper and the Roos theorem, so the fixed integral module instances
determine the universes. Each command ends in `in` and restores the instance table.
No public signature, definition, attribute or public import changes.

## Old

The module had no such local instance-selection commands.

## New

```lean
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenRoos.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived in
```

This command scopes each of `integralRoosCalculus` and
`augmentedIntegralRoosDescent`. Existing public declarations retain their exact
signatures. Only the finite exactness and Roos theorem proofs are filled.

## Users

`tools/downstream.py Sheaf.Paper.AugmentedIntegralDescent --uses
augmentedIntegralRoosDescent` reports zero downstream modules. The DAG parent
still requires this module; its statements and route are retained.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AugmentedIntegralDescent | T5 | Local proof elaboration only. |

No consumer adaptation is required. The local commands affect only selection of
existing structures during proof elaboration, so target meanings stay identical.

## Status

landed 20261025T101452-L-3698313 2026-10-25 (merge of deliver/T5/Sheaf.Paper.AugmentedIntegralDescent)
