# ModuleCat.BaseDerivedTensorCohomologyModel.counit_isIso_of_termwise_tor_acyclic

## Reason

Repair of the stale-base return for delivery 8650353c78 (base e0d550965). Rechecked the current
shared checkout and the server: the item is absent from lean/ and its current
quarantined version still has the signature below and one sorry. This packet
reconstructs that current version with the canonical import and a complete
proof. The final naturality-square cancellation has also been simplified and
compiled in this repair. No concurrently landed proof is overwritten.

Restore the quarantined module and prove its theorem. The sync diagnostic in
coord/rework.tsv reports a duplicate BaseDerivedTensorCohomologyModel declaration:
the old Sheaf definition and the adopted upstream definition were both imported.
The K-flat counit module already uses the upstream definition, so this module's
public model import must use that same definition.

## Old

```lean
public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
```

The original theorem is the one in
quarantine/Sheaf/Algebra/Homology/TermwiseTorAcyclicBaseComparison.lean, with its
whole proof `by sorry`.

## New

```lean
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
```

The theorem's written signature is retained verbatim, now elaborated against the
canonical upstream model. Its proof is complete. The only added declarations are
proved private helpers for the common-universe calculation and scalar-extension
transport. The source library itself is unchanged.

## Users

The downstream.py query with --allow-missing reports zero live downstream modules;
the item is absent from lean/ because it was quarantined. Searching quarantine/
finds one direct consumer. Its signature is compatible with the theorem once it
uses the same canonical model; it has its own pre-existing obsolete model import
and remains a separate rework item.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.TermwiseTorAcyclicBaseComparison | G7 | Restored, canonical model import, theorem proved. |
| Sheaf.Algebra.Homology.TorIndependentProjectiveComplexTensor | unclaimed; quarantined | Existing application at line 115 retains the same arguments. Its obsolete public model import requires its separate rework repair; no file changed here. |

The interface repair preserves the mathematical model and statement. No target
statement or definition used by a target is edited.

## Status

landed 20261020T145514-L-2404120 2026-10-20 (merge of deliver/G7/Sheaf.Algebra.Homology.TermwiseTorAcyclicBaseComparison)
