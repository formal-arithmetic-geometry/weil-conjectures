# LocalizedModule.gradedModuleAwayMaps

## Reason

The proof adds a module-local elaboration option to handle the localization instance
transparency and a theorem-local linter option for unused binders in the original signature.
The static interface checker treats these commands as visible changes. No declaration
signature or definition changes.

## Old

No additional option commands after `namespace LocalizedModule` or before the theorem.

## New

```lean
set_option backward.isDefEq.respectTransparency false
```

and, immediately before the existing theorem docstring:

```lean
set_option linter.unusedVariables false in
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Module.GradedModuleAwayRestriction | not checked | None; same theorem signature |

The options control only elaboration and linting of this module. No target statement
changes meaning and no downstream module needs adaptation.

## Status

landed 20261012T135336-L-1701158 2026-10-12 (merge of deliver/X3/Sheaf.Algebra.Module.GradedModuleAwayMaps)
