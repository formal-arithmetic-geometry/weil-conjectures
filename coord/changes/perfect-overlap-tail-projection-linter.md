# perfectOverlapTailProjectionComponent

## Reason

The original statement binds unused gluing data and apex comparisons. Proving the theorem activates Lean's unused-variable warnings for those pre-existing signature lets. Disable that linter in this module so the unchanged public statement compiles without warnings. This setting changes no mathematical definition, theorem signature, visibility, instance or exported notation.

## Old

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
```

## New

```lean
set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionComponent | R1 | Local lint setting only; the declaration statement is identical. |

No consumer adaptation is needed: set_option is local to the file and changes neither an exported declaration nor its meaning. Every downstream consumer sees the identical interface.

## Status

landed 20261017T013051-L-4174255 2026-10-17 (merge of deliver/R1/Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionComponent)
