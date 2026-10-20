# RingTensorCohomology.prescribedTensorCohomology_model_realization

## Reason

Restore the quarantined item and complete its proof. Its public Sheaf model import
collides with the adopted upstream model imported by its proof dependencies,
producing the duplicate BaseDerivedTensorCohomologyModel._sizeOf_inst error recorded
in coord/rework.tsv. Use the upstream model provider consistently, as in the
already landed DerivedTensorLocalizationCohomology repair. The theorem signature,
all hypotheses, and all three conclusions are preserved verbatim.

## Old

```lean
public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
```

## New

```lean
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
```

The original Sheaf provider has since been withdrawn as an empty module; the
adopted upstream structure is the current authoritative provider of the same
qualified model declaration. No model definition, source-library declaration,
or target statement is edited.
Proof-only imports and fully proved private helpers support the new complete
proof. No public helper declaration or new module is introduced.

## Users

The live source tree has no importer because this module and its parent were
quarantined. Search of lean/Sheaf, lean/WeilConjectures, and quarantine/Sheaf finds
the following direct consumer; its two calls use the unchanged theorem signature.
An unchanged copy of this quarantined consumer compiles successfully against the
restored item (11.8 seconds). Its unchanged restored dependencies were compiled
for this test; none of these temporary consumer/dependency copies is delivered.
No adaptation is forced by the provider repair. Running tools/downstream.py
with --allow-missing --uses prescribedTensorCohomology_model_realization reports
zero live downstream modules and zero live uses; quarantined uses are listed below.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.PrescribedTensorCohomologyModelRealization | N1 | Restored; upstream provider selected and the existing proof hole closed. |
| Sheaf.Algebra.Homology.AffineTensorCohomologyLocalizationSquare | unclaimed, quarantined (D5 rework cluster) | Calls at lines 223 and 249 keep the exact signature; no source change. |

## Status

landed 20261020T153012-L-2862762 2026-10-20 (merge of deliver/N1/Sheaf.Algebra.Homology.PrescribedTensorCohomologyModelRealization)
