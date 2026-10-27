# AlgebraicGeometry.ProEtale.SpTowerCalculus.geometric_calculus

## Reason

Restore the assigned rework item from
`quarantine/Sheaf/Paper/CoefficientTowerGeometricComposition.lean` to its original
library path. Its rework row records the failed cluster restore of 2026-10-20.
The archived theorem now compiles against the restored dependencies. Preserve its
complete signature, original proof hole, docstring, imports and DAG attachment.

The archive also removes an instance globally and re-registers it at high priority
after the theorem. Scope this proof-environment change with a section instead.
Leaving that section restores the inherited registration, so restoring this module
does not export a new instance-priority command. No mathematical definition changes.

## Old

The full archived module is the baseline. Its commands around the unchanged
mathematical declaration block are:

```lean
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
```

and, after the namespace closes:

```lean
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
```

## New

```lean
section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
```

The explicit final re-registration is replaced by `end`, closing that section.
All other source text is byte-for-byte identical to the archive. In particular,
`geometric_calculus` retains its one original `sorry`, not a new split or theorem.
No data is chosen from an unproved existence theorem. No definition, target type,
normalization equation, public import or universe parameter changes.

## Users

`tools/downstream.py Sheaf.Paper.CoefficientTowerGeometricComposition --allow-missing`
reports zero current Lean consumers. An import search including `quarantine/`
finds the single archived consumer below. No consumer needs a signature adaptation.
The corresponding node and its parent dependency remain attached unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientTowerGeometricComposition | E3 | Restore archived theorem; scope instance removal. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | not queried; not edited | Archived consumer; theorem signature and all imports unchanged. |

The restored item compiles through `lcompile.py` in 3.4 seconds. A separate compile
of the unchanged archived consumer was attempted, but its dependency closure asks
for a missing `Mathlib.olean`; it failed before elaborating the consumer. This is
not evidence of a consumer source incompatibility, and no consumer edit is included.
The maintainer's global build remains the consumer verification.

## Status

landed 20261023T041828-L-1701654 2026-10-23 (merge of deliver/E3/Sheaf.Paper.CoefficientTowerGeometricComposition)
