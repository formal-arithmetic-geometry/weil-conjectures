# FiniteBaseChangeRestrictionMateTransport: exact Kernel site

**Declaration:** `finite_base_change_restriction_mate_transport`, origin
`0676f555de6`.

## Measurements and bisect

The declared type alone is 3.80 s. The 400,000-heartbeat Before probe is
88.46 s and times out; its Kernel-skipped control is 4.60 s. The canonical
4,000,000-heartbeat Before is 577.08 s, while After is 4.10 s.

`probes/ApplicationOnly.lean` binds the direct `transport_from_unit` result
and then uses `sorry`: 577.57 s on / 4.60 s skipped. Replacing only the
`hb` argument (the supplied right-square identity) with a typed `sorry` in
`probes/NoHB.lean` reduces the 400,000-budget run to 4.70 s. Replacing the
`hγ` mate proof instead (`probes/NoHGamma.lean`) still times out at 90.56 s.
Thus the exact first expensive component is checking `hb` as an argument to
`transport_from_unit`; `hγ` is not needed to reproduce the cost.

## Expressions and diagnostics

The direct application supplies four concrete equivalence records and a
concrete `ordinaryTheta.inv`; the expected `hb` binder is a square over the
abstract categories `A`, `B`, `C`, and `D`. The concrete argument expands
`Functor.obj`, `PresheafOfModules.obj`, and additive/module instance paths
before it can be compared with that binder. Diagnostics on `NoHGamma.lean`
show 2,226 Kernel unfolds of `Functor.obj`, 1,168 of `PresheafOfModules.obj`,
and 812 of `ModuleCat.isAddCommGroup`; the `NoHB` control removes this chain.

## Classification

Primary mechanism: **A**. Contributing mechanisms: **C** and **E**.
Evidence: **confirmed** for the `hb` argument check and **strongly supported**
for the mechanism. The fixed proof abstracts the four functors and
equivalences before applying the concrete theorem, so the expected binder and
the supplied square share the same representation.
