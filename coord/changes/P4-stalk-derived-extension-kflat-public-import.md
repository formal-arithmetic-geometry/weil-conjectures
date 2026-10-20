# AlgebraicGeometry.SingleComplexBaseChange.exists_stalkDerivedExtensionComparison

## Reason

Restore the quarantined module assigned in `coord/rework.tsv`, preserving its
Lean attachment and proof dependencies. Compiling the unmodified archive through
`lcompile.py` reproduces `Invalid field IsAcyclicTensorKFlat` at line 102 in the
public theorem's `hP` hypothesis, followed by a cascading unsolved goal. Its
upstream public imports expose the differently named `IsKFlatTensor`; its private
proof imports do not make `IsAcyclicTensorKFlat` available in a public signature.
Add the existing defining module as a direct public import.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorLocalizedNaturality
import all Mathlib.Algebra.Homology.Localization
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorLocalizedNaturality
public import Sheaf.Algebra.Homology.KFlat
import all Mathlib.Algebra.Homology.Localization
```

All other lines, including the theorem signature, docstring, private helper and
complete proof, are verbatim from the quarantine archive. No definition or
statement changes meaning. The repaired module compiles without diagnostics
through `lcompile.py` in 7.2 seconds. The archive itself is retained.
An isolated scratch importer also compiles with only a public import of the
restored module, exposing the K-flat predicate and the existing theorem.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparison | P4 | Restored with the public dependency required by its existing signature. |
| Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality | quarantined; no current claim found | Its existing theorem application and signature are unchanged; no adaptation required. |

A search of `lean/Sheaf` and `quarantine/Sheaf` finds the second row as the only
direct importer or external user. The archived consumer obtains the same
`L`, counit, universal property, comparison isomorphism and computation at line
112; it then applies the computation twice, with exactly the original arguments.
No consumer is weakened or withdrawn. Its separate quarantine/rework assignment
is preserved. The parallel upstream `WeilConjectures` module uses its upstream
predicate and comparison declarations and is untouched.

`tools/downstream.py --allow-missing --uses` reports zero live downstream modules
and zero live uses of this quarantined module's theorem.

The existing node `lem-pc-stalk-derived-extension-comparison` already records
this exact statement, proof and all proof dependencies. None changes. No target,
unit route, or target-used definition changes.

## Status

landed 20261020T162317-L-3588922 2026-10-20 (merge of deliver/P4/Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparison)
