# AlgebraicGeometry.coherent_zero_support_finite_scheme

## Reason

Restore the quarantined module named in coord/rework.tsv. Its public theorem mentions
RingedSpace.IsCoherent, whose source had only a private import. Make that existing
import public. Retain the archived theorem signature verbatim and complete its proof.
There is no change to a statement or definition, including the targets' definitions.

## Old

```lean
import WeilConjectures.AlgebraicGeometry.Coherent
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.Coherent
```

## Users

The source-only downstream query with --allow-missing reports no current Lean importers.
A search of quarantine finds the following two archived direct importers. Neither calls
the declaration in its unfinished proof. Their theorem signatures and meanings are
unchanged. The extra public coherence import restores the interface needed by this
module's own statement. No consumer edit or forced adaptation is needed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport | unclaimed | Quarantined direct importer; same statement and interface; no adaptation. |
| Sheaf.TraceFormula.PointedGenusZeroProjectiveLine | unclaimed | Quarantined direct importer; same statement and interface; no adaptation. |

## Status

landed 20261020T152950-L-2856212 2026-10-20 (merge of deliver/D2/Sheaf.AlgebraicGeometry.ZeroSupportFiniteScheme)
