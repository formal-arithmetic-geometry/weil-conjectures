# AlgebraicGeometry.affineSpectrum_counit_compatibility

## Reason

Restore the quarantined module and repair the failure recorded in
`coord/rework.tsv`. The current unmodified quarantine source fails at line 28:
Lean rejects setting local irreducibility when `derivedPullback` is already
irreducible. The upstream definition uses `noncomputable irreducible_def`.

For the return of ef25e9fc64, re-read the current shared checkout and the current
project-server tree. The live item is absent in both. The current rework row
still names the quarantine source; both current copies have SHA-256
`55d5b4c17e05b800bff4902a7b17637fa9f509e72c1ba7f71db45c37ed109912`.
The restored source is that current file with the invalid command removed.
The unmodified source fails in 11.6 seconds; the repaired source compiles
without warnings in 9.5 seconds through `lcompile.py`.

## Old

The current quarantined module contains the following command immediately
inside `namespace AlgebraicGeometry`:

```lean
attribute [local irreducible] derivedPullback
```

## New

Remove that command and its following blank line. Preserve every other line
of the current quarantine source. The theorem signature, complete proof,
public imports and docstrings are unchanged. No definition or target meaning
changes, and the existing DAG attachment and proof route are retained.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineSpectrumCounitCompatibility | M8 | Restore compilation with the same public interface and complete proof. |

No current live or quarantined module imports this Sheaf module. The adopted
upstream counterpart and its upstream consumer are preserved unchanged.
Removing a local attribute does not affect an importer's elaboration context;
there are no consumer adaptations in this delivery.

## Status

landed 20261020T145530-L-2407971 2026-10-20 (merge of deliver/M8/Sheaf.AlgebraicGeometry.AffineSpectrumCounitCompatibility)
