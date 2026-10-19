# openComparison_unit_normalization

## Reason

The proof introduces a private categorical helper namespace, opens `Opposite`, and uses
three elaboration options scoped to each of two private lemmas. The static interface
scanner records changes to these commands, so this record documents the proof context.
All existing signatures, both public definitions, and all public imports are unchanged.

## Old

The file used the following namespace-opening command:

```lean
open CategoryTheory
```

It had no `CategoryTheory` helper namespace and no scoped elaboration options before
private helper lemmas. The theorem `AlgebraicGeometry.ProEtale.openComparison_unit_normalization`
had the existing signature and proof `:= by sorry`.

## New

The namespace-opening command is:

```lean
open CategoryTheory Opposite
```

A closed `namespace CategoryTheory` contains only the proved private lemma
`homEquiv_conjugate`. Before each of the two new private lemmas
`openComparisonRestrictionIso_conjugate` and `openComparisonRestriction_directImage_mate`,
the following options apply only to that declaration:

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
```

The existing theorem is proved with its signature unchanged. The existing definitions
`openComparisonRestrictionIso` and `openComparisonHomEquiv` are unchanged. The sole added
import is proof-only; redundant or unused proof-only imports are removed as listed in
report.md. No public import is removed, and no target or definition changes meaning.

## Users

The required source-only query was run:
`python3 tools/downstream.py Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization --uses openComparison_unit_normalization`.
It found 493 downstream modules and only the item itself mentioning the theorem name.
The downstream modules receive exactly the same public signatures and definitions.
No consumer needs adaptation because all additions are proved private helpers or commands
that affect only elaboration within this file. No other module is delivered.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization | J7 | Existing theorem proved; signatures and definitions unchanged. |

## Status

landed 20261019T005306-L-2749150 2026-10-19 (merge of deliver/J7/Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization)
