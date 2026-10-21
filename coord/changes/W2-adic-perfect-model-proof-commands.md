## Reason

Prove `AlgebraicGeometry.Scheme.adicPerfectModel_complete_reduction` without
unfolding the large chosen completion cone in the final theorem assembly.
The preflight conservatively classifies added command-level proof setup as an
interface change, so this record documents its scope.

## Old

The item had its existing public definitions and theorem statement, with the
one theorem proof left `sorry`. It opened the category-theory namespaces and
used `backward.isDefEq.respectTransparency false`.

## New

The existing public definitions, theorem signature, and public imports are
verbatim. All 45 added helper declarations are private and proved. Add
`open scoped ChangeOfRings TensorProduct` for tensor notation and
`set_option backward.isDefEq.respectTransparency.types false` for elaboration
of the existing coefficient presentations. Immediately before the final
public theorem, add
`attribute [local irreducible] ConstantCompletion.completed` to prevent its
large inverse-limit definition from unfolding during proof assembly.
This attribute is local to the namespace and has no effect on importers.
No new instance, global attribute, public notation, definition, or assumption
is exported. This is proof setup, with no mathematical interface change.

## Users

`Sheaf.Paper.CompletedPerfectScalarPullback` is the sole current direct Lean
importer. Its existing proof imports the same item with the same public
signatures and definitions; no adaptation is needed. All downstream modules
likewise see the unchanged public API. The DAG parent remains supported by
this item, whose proof now has no holes.

## Status

landed 20261021T144023-L-37685 2026-10-21 (merge of deliver/W2/Sheaf.Paper.AdicPerfectModelCompleteReduction)
axiom probe passed. Independent review checks the local scope of the commands
and the unchanged public API.
