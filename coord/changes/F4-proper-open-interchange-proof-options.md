# Proper/open interchange proof options

## Reason

The complete proof needs the backward elaboration options for the large
functor expressions. Scoped lint suppression preserves the original unused
public binder names. These commands trigger the static visibility check.

## Old

`Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`, held by F4, had the
original public theorem with a sorry and no local backward elaboration options.

## New

The public theorem signature and all existing definitions remain unchanged.
The implementation adds `backward.isDefEq.respectTransparency false`,
`backward.isDefEq.respectTransparency.types false`, and
`backward.defeqAttrib.useBackward true` before private proved helpers.
A scoped `set_option linter.unusedVariables false in` preserves the two
original unused binder names in the public statement without style warnings.
No imported declaration receives a reducibility attribute.
Three new modules expose named subargument theorems with matching DAG nodes.
Base change is proved; composition and refinement normalization are the
two remaining obligations listed in the report.

## Users

All existing importers retain exactly the original public theorem signature
and definitions. No consumer requires adaptation: these options support
elaboration and linting of this proof, with no new mathematical assumption.
The new subargument modules are proof-only imports of the item.

## Status

landed 20261018T071150-L-1667247 2026-10-18 (merge of deliver/F4/Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence)
and axiom probes compiled successfully. Final preflight is rerun with this
record and complete search records. No existing signature or definition changes.
