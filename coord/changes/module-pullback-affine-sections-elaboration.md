# exists_tensorPullback_affine_sections (local elaboration options)

## Reason

The theorem signature is unchanged. The proof uses the existing section-module instances
through semireducible scheme definitions, so backward elaboration transparency is set
locally in the module. The original signature's lambda `fun G ↦ Module.compHom _ ...`
uses G through the inferred type; the unused-function-argument linter otherwise emits
a false positive once the theorem has a proof. Only that linter's function-argument
check is disabled around this theorem. The stage-3 interface checker conservatively
classifies any changed option commands as an interface change, hence this record.

## Old

No option commands between `namespace AlgebraicGeometry.Scheme.Modules` and the theorem.
The theorem signature is exactly the repository's original signature.

## New

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The existing theorem is also enclosed by:

```lean
set_option linter.unusedVariables.funArgs false in
```

No statement, definition, instance, notation, public import, or target changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| All importers of Sheaf.AlgebraicGeometry.ModulePullbackAffineSections | unchanged | None: options govern compilation of this file; its public signature and public imports are unchanged. |

There are no declaration-name users of the option commands and no modules to adapt.
No target statement is reopened.

## Status

landed 20261012T060755-L-2916227 2026-10-12 (merge of deliver/T2/Sheaf.AlgebraicGeometry.ModulePullbackAffineSections)
