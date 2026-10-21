# Sheaf.Paper.CompletedPerfectScalarPullback proof environment

## Reason

The stage-3 preflight conservatively treats added universe and attribute commands as
changes to what importers see. These commands support proved private helpers and prevent
elaboration from expanding large chosen coefficient constructions. This record covers
that command-level change; no existing signature or definition changes.

## Old

The universe command was, verbatim:

```lean
universe t u
```

There were no local irreducibility commands for `coefficientProEtaleDirectRingMap`,
`scalarChange`, `finiteChange`, `constant`, `completedIntegralCoefficientSheafUnrestricted`,
or `unrestrictedIntegralReductionExistence` in this item module. Its existing command
`attribute [local irreducible] HasDerivedCategory.standard` is retained unchanged.
All 53 original non-theorem declaration bodies and all public imports are retained verbatim.

## New

```lean
universe t u v w
```

The two extra universe names are used only in the proved private theorem
`product_unit_condition`; existing declarations acquire no extra universe parameters.
The following commands are added inside the module's existing public section:

```lean
attribute [local irreducible] coefficientProEtaleDirectRingMap
attribute [local irreducible] scalarChange finiteChange constant
  completedIntegralCoefficientSheafUnrestricted unrestrictedIntegralReductionExistence
```

The first command follows the proved private coefficient-naturality helper. The second
follows `quotientProduct`, before the proved private quotient-unit and abstract product
helpers. They affect only elaboration in this file and do not export irreducibility.
Every helper is private and fully proved; none occurs in a public signature or definition.
Only proof imports are added or removed. The existing DAG node's proof route is updated
without changing its statement, Lean attachment, unit or chapter.

## Users

`tools/downstream.py Sheaf.Paper.CompletedPerfectScalarPullback --direct` and its
`--uses` check for all six names in the local attribute commands found zero downstream
modules. Unfinished mathematical parents remain in the DAG; no withdrawal is requested.
No consumer needs adaptation, and the definitions used by targets are unchanged.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompletedPerfectScalarPullback | B4 | Eight theorem proofs, proved private helpers, private proof imports, local elaboration attributes, two private-helper universe names |

## Status

landed 20261021T170713-L-2751451 2026-10-21 (merge of deliver/B4/Sheaf.Paper.CompletedPerfectScalarPullback)
