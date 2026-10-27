# AlgebraicGeometry.ConstantComplexBaseChange.siteSmall

## Reason

Restore `Sheaf.Paper.ConstantComplexQuotientModel` from its preserved quarantine
source, as assigned in `coord/rework.tsv`. The reported error occurs when
`constantModules` synthesizes coefficient sheaf operations: the imported
`WeilConjectures.scalarReductionSiteSmall` leaves an unconstrained universe in
`EssentiallySmall.{max ?v (u + 1)} W.ProEt`. An expected functor type alone does
not resolve it. A higher-priority instance fixes the smallness universe
at `u + 1` using Mathlib's proved `essentiallySmallSelf.{0, u, u + 1}`.

The instance is exported alongside the existing fixed-size abelian sheafification
instances. A local-only version compiled this module but left the same universe
error in the archived direct importer `ConstantComplexStrictBaseChangeData`.
No imported instance registration changes, no mathematical construction changes,
and no existing signature changes. All quotient, tensor, reduction, normalization
and tower definitions remain verbatim
from the quarantine source. The existing DAG attachment and dependencies remain.
This changes no target statement or mathematical definition used by a target.

## Old

No `AlgebraicGeometry.ConstantComplexBaseChange.siteSmall` declaration. The affected
constant realization was, and remains:

```lean
abbrev constantModules (W : Scheme.{u}) (R : Type u) [CommRing R] :=
  commutativeSiteConstantModuleFunctor.{u + 1, u} (ProEt.topology W) (ULift.{u + 1} R)
```

## New

Immediately after opening `AlgebraicGeometry.ConstantComplexBaseChange`, add:

```lean
/-- Fix the smallness universe before synthesizing the coefficient sheaf operations.
Source: the small-site size convention
(blueprint: def-a1-constant-complex-quotient-model). -/
instance (priority := 4000) siteSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} W.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _
```

The `constantModules` declaration and every existing declaration are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantComplexQuotientModel | G1 (assigned repair) | Restored; smallness inference fixed at the coefficient size. |
| Sheaf.Paper.ConstantComplexNormalizedReductions | unclaimed in shared snapshot | Archived direct importer; existing signatures preserved. |
| Sheaf.Paper.ConstantComplexStrictBaseChangeData | unclaimed in shared snapshot | Archived direct importer; existing signatures preserved. |
| Sheaf.Paper.ConstantComplexFinitePullback | unclaimed in shared snapshot | Archived indirect consumer; no construction changes. |
| Sheaf.Paper.ConstantComplexCompletedPullback | unclaimed in shared snapshot | Archived indirect consumer; no construction changes. |
| Sheaf.Paper.ConstantComplexStrictBaseChange | unclaimed in shared snapshot | Archived indirect consumer; no construction changes. |

`tools/downstream.py --allow-missing --uses constantModules` reports zero live
importers because the dependent files are quarantined too. Searching `quarantine/`
finds the two direct importers listed above. Their unchanged archived sources are
checked against the repaired module: the item compiles in 37.3 seconds,
`ConstantComplexNormalizedReductions` in 5.2 seconds, and
`ConstantComplexStrictBaseChangeData` in 21.3 seconds. Temporary validation copies
are removed before delivery. Also checked the unchanged indirect consumers:
`ConstantComplexCompletedPullback` (2.8 seconds), `ConstantComplexFinitePullback`
(2.9 seconds), and `ConstantComplexStrictBaseChange` (30.9 seconds).
All five copies were checked byte-identical to their archives before removal.
The exported instance is the reason this consumer check matters:
the local-only attempt failed in the data module at line 134 with the same
`max ?v (u + 1)` constraint. Restoration of those separately quarantined items is outside
this repair.

## Status

landed 20261026T111839-L-1751617 2026-10-26 (merge of deliver/G1/Sheaf.Paper.ConstantComplexQuotientModel)
