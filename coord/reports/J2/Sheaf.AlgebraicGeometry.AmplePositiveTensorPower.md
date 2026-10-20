## What changed

The assigned module is already retired on the current sheaf-dag base. Its Sheaf file is the
empty withdrawn module, and the public theorem is retained and proved in
`WeilConjectures.AlgebraicGeometry.AmplePositiveTensorPower`. This packet preserves that
retirement and records the completed zero-hole state.

## Proved and sorry left

There are zero declarations and zero `sorry`s in the assigned Sheaf module. The upstream twin
contains the complete proof of `AlgebraicGeometry.Scheme.Modules.isAmple_positive_tensorPow`.
No new sorry is introduced and no theorem is split off.

## No longer needed

No imports or proof dependencies are needed by the withdrawn Sheaf module. The old Sheaf
private helper and duplicate proof were removed by the already landed retirement; downstream
consumers use the upstream twin.

## Where the brief, the DAG or earlier work was wrong

The assignment arrived after the retirement had already landed in
`coord/changes/retire-ample-positive-tensor-power-S4.md`. The live module therefore has no
remaining proof hole to close. The DAG node is attached to the proved upstream declaration.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
