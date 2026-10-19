# proEtaleRingModuleAdjunction (local transparency in ProEtaleIntrinsicClosedAmbient)

## Reason

The preflight flags a new local attribute as a command-interface change and requires this
record. During the support-kernel comparison, unfolding the concrete coefficient adjunction
caused excessive elaboration. A local irreducibility registration keeps the constructed
adjunction abstract. The kernel comparison is proved generically for abelian categories and
then specialized. All new helper definitions are private and fully constructed.

No existing definition, theorem signature, visibility, or public import changes. In particular,
this registration is local to this file; an importer does not inherit it. No target statement
or definition used by a target changes its meaning. No consumer adaptation is required.

## Old

There was no local transparency registration for `proEtaleRingModuleAdjunction` in this module.
The declaration itself is defined in the existing canonical-adjunction module and is unchanged.

## New

```lean
attribute [local irreducible] proEtaleRingModuleAdjunction
```

The existing declaration itself is unchanged. This command affects elaboration only inside
the current module.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient | F7 | Local elaboration only; the existing public theorem keeps its exact signature and is now proved. |

The required `downstream.py --uses sfIntrinsicClosedAmbientAdjunction` search found only the
item module (one occurrence). The import graph has 335 downstream modules, but this local
registration and the private helpers do not change any of their statements or elaboration
attributes. The imported `proEtaleRingModuleAdjunction` declaration is not modified.

## Status

landed 20261019T002547-L-2153334 2026-10-19 (merge of deliver/F7/Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient)
