# formalFunctions_finite_open_factorization elaboration options

## Reason

The completed proof needs the backward elaborator to respect reducibility for
scheme-module morphism types. The module commands change only these two options;
the checker conservatively classifies any changed module commands as an interface
change. This record documents that finding. No definition, theorem signature,
visibility, notation or instance changes. The new coefficient theorem has its own
node and module.

## Old

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

## New

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
```

These options control elaboration in the current module and are not inherited
by importers. The elaborated existing theorem type is unchanged. The new module
uses the same options.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteOpenFactorization | X2 | Its proof elaborates with reducibility respected; signature unchanged. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientMaps | unclaimed | Direct theorem user; unchanged signature and no inherited option change. No adaptation. |

The downstream command lists 230 transitive importers. The declaration search
finds only the module itself and FormalFunctionsFiniteQuotientMaps. All importers
receive the identical theorem signature and no elaboration options. No target's
statement or the definitions it uses change meaning. No forced adaptation occurs.

## Status

landed 20261013T100218-L-2502377 2026-10-13 (merge of deliver/X2/Sheaf.AlgebraicGeometry.FormalFunctionsFiniteOpenFactorization)
