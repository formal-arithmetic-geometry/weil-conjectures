# residue-tor-instance-path

## Reason

Kernel checking the specialization of the generic categorical residue criterion unfolded
competing quotient-ring `Ring` instances and exceeded the single-file timeout. The local
priority annotation selects the canonical `CommRing.toRing` path used by the criterion and
made the retained proof compile in 11.3 seconds in the earlier attempt. The local braiding
priorities likewise match the existing étale derived tensor construction. Neither annotation
exports an instance change or changes a mathematical construction or public theorem type.

## Old

No local instance-priority annotations were present in
`Sheaf.AlgebraicGeometry.ResidueTorAmplitudeTest`.

## New

```lean
attribute [local instance 20000] CommRing.toRing
```

Within `AlgebraicGeometry.Etale`, before the proof helpers:

```lean
attribute [local instance 20000] SymmetricCategory.toBraidedCategory sheafBraidedCategory
```

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.ResidueTorAmplitudeTest` | X9 | The proof elaborates and kernel-checks through the canonical quotient-ring instance path. |

## Status

landed 20261019T112622-L-3962395 2026-10-19 (merge of deliver/X9/Sheaf.AlgebraicGeometry.ResidueTorAmplitudeTest)
