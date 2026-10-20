## What changed

Restored the quarantined module with its complete existing proof. Replaced the withdrawn
`Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations` public import by the adopted
source module `WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`.
This supplies the public `externalCupCoefficients` and `RingedSpace.moduleCohomology`
declarations required by the unchanged theorem statement and proof.

The change record is
`coord/changes/picard-external-coefficients-acyclic-upstream-import.md`.
A search across both library roots and quarantine finds one caller,
`Sheaf.AlgebraicGeometry.PicardExternalCupAcyclic`; its theorem invocation keeps the
same name and full type, so no consumer adaptation is forced.

The module compiles with `python3 /home/ubuntu/weil-launcher/lcompile.py`.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Modules.picardExternalCupCoefficients_acyclic` is proved; it
contains no `sorry`. Actual hole count: zero before, zero after; holes closed: zero;
holes added: zero; split off: zero. This is the assigned import restoration, not a new
proof claim. No new declarations or holes were added.

## No longer needed

Removed the public import of the empty withdrawn module
`Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`, replacing it with
its canonical adopted source module. No mathematical nodes or modules are pruned.
The DAG node and its proof dependencies are unchanged.

## Where the brief, the DAG or earlier work was wrong

The quarantined source retained a public import of a withdrawn Sheaf module. That import
made the public cohomology and external-coefficient declarations unavailable, producing the
reported unknown-identifier errors. The canonical adopted `WeilConjectures` module is the
correct public source and restores the original interface without changing any declaration.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
