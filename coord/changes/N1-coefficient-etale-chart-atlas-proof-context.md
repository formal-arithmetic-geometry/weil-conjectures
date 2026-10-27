# Sheaf.Paper.CoefficientEtaleDerivedChartAtlas proof context

## Reason

The proof needs the coefficient-sized sheafification instances rather than the generic
essentially-small instance. It also uses a private generic helper in universe w. The static
checker flags these command changes conservatively as an interface change. No existing
signature, definition or public import is changed. The instance commands are listed below.

## Old

The original context, verbatim:

```lean
set_option synthInstance.maxSize 2048
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

universe u v
```

## New

```lean
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

universe u v w
```

The two private generic helpers additionally suppress
`HasDerivedCategory.ofIsGrothendieckAbelian` with `attribute [-instance] ... in` for their
own declaration, to fix the standard derived localization explicitly. The original public
theorem signature, including universes, is unchanged verbatim. Its original public imports
are unchanged; all proof imports are private. The three new support modules have their own
nodes and do not replace or modify an existing definition. No target statement changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientConnectedLocalStalkModels | unclaimed; stage 3 done | Unchanged direct importer; compile checked against the proof context. |

The importer is copied only for validation and is removed from the sandbox after compiling;
it is not delivered or adapted. No forced adaptation is needed.

## Status

landed 20261026T130546-L-3475843 2026-10-26 (merge of deliver/N1/Sheaf.Paper.CoefficientEtaleDerivedChartAtlas)
