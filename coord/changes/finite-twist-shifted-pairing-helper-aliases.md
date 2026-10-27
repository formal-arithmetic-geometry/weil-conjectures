# Private finite-twist shift helper uses the recorded functor aliases

## Reason

The unchanged direct consumer
`Sheaf.AlgebraicGeometry.FiniteTwistShiftedPairingPullback` failed against this packet:
`NOT ACCEPTED: this compile took 72 s > 60 s`. A controlled compile against the
original item passed in 55.0 s. Profiling the consumer against the packet reports
48.7 s of kernel checking for the public theorem's concrete instantiation of the
private helper. Directly invoking the general shift theorem did not improve this.

The private helper is adapted to accept the recorded `ordinaryFinitePullback` and
`ordinaryFiniteTensor` aliases already used by the degree-zero evaluation theorem.
Conversions to the underlying derived functors now occur when the objects are
abstract in the helper, rather than after inserting the concrete finite-twist
objects in the public proof. These aliases have exactly the same definitions.

## Old

The helper `module_pairing_shifts` used the expanded derived inverse image in the
parameter `u`, the expanded derived tensors in `q` and `q'`, and expanded derived
inverse image/tensor in the premise `hq`.

## New

Only those private helper parameter types use the existing recorded aliases.
The conclusion, proof body, all public declaration signatures and visibility,
attributes, public imports, and the public proof body are unchanged. There are
no new statements or holes. No definition is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteTwistShiftedPairingPullback | unclaimed in local claim record | Private helper parameter aliases; public theorem unchanged. |

The private helper is used only in this module. Its public interface stays
identical, so no importer adaptation is required.

The final sandbox-wide `lcompile.py --all` check accepted the adapted module
against all delivered dependencies, within the tool's per-file limit.

## Status

landed 20261026T222639-L-677900 2026-10-26 (merge of deliver/F2/Sheaf.AlgebraicGeometry.EtaleSingleFunctorMonoidalCompatibility)
