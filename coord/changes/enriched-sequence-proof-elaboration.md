# SheafOfModules.EnrichedSequenceProjection proof elaboration

## Reason

Proving the presentation comparisons and the projection formula requires local control
of unfolding. The full file reached the fixed 60-second limit when Lean expanded the
chosen derived-functor and comparison definitions. Generic proved helpers and local
irreducibility attributes keep these conversions explicit. Preflight classifies the
changed section commands as an interface edit, so this record documents them.

## Old

The original module has these options (verbatim):

```lean
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

It has no local irreducibility commands at the proof-helper location.
All existing declaration signatures, definitions, attributes attached to declarations,
and public imports are preserved verbatim.

## New

The original options remain. The section additionally has:

```lean
set_option linter.unusedSectionVars false
```

The following commands occur after the original definitions and before the private
proof helpers:

```lean
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors

attribute [local irreducible] ordinarySectionsIso sectionsH0Comparison
  toStrictEvaluation homIdentification
  CategoryTheory.Functor.rightDerivedFunctorObjQIso
  CategoryTheory.Functor.rightDerivedFunctorUnitQ
```

These attributes apply only within the section. The public definitions and their
reducibility for importing modules do not change. Private proved helpers supply the
required normalization equations. No statement or data construction changes.
The complete item compiles without warnings in 58.5 seconds with the unchanged limit.

## Users

`tools/downstream.py Sheaf.CategoryTheory.EnrichedSequenceProjectionFormula --uses
sectionsH0Comparison` reports zero downstream modules and only the defining module as
a textual user. A source import search also finds no current importing module. DAG
parents with unfinished proofs retain their dependencies and will use the identical API.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.EnrichedSequenceProjectionFormula | K3 | Local proof elaboration; signatures and public definitions unchanged. |

## Status

landed 20261021T203641-L-3849496 2026-10-21 (merge of deliver/K3/Sheaf.CategoryTheory.EnrichedSequenceProjectionFormula)
