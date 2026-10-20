## What changed

Restored `lean/Sheaf/Paper/IntegralConstructibleSerre.lean` from the quarantine path in
`coord/rework.tsv`. Added public imports of
`Mathlib.CategoryTheory.ObjectProperty.Kernels` and
`Mathlib.CategoryTheory.ObjectProperty.Extensions`, which define the three predicates in
its public theorem type. All archived declarations, signatures, docstrings, proof bodies,
and existing imports are preserved verbatim. This is the assigned zero-hole repair,
not a new decomposition.

Change record: `coord/changes/A3-integral-constructible-serre-public-imports.md`.
The live and quarantined consumer closure was checked; no consumer needs adaptation.
The module compiles through `lcompile.py`. A separate public consumer imports only this
module, opens the same `CategoryTheory.Obj` and `CategoryTheory.Functor` scopes, and checks
all three closure predicates by applying the exported theorem. The check file is scratch
material and is not part of the delivery.

## Proved and sorry left

`AlgebraicGeometry.ProEtale.CondensedRing.integralConstructible_serre` retains its complete
proof: apply `constructible_cokernels_extensions` to the actual integral coefficient ring
and combine its two factors with `integralConstructible_kernels`.

Baseline: zero local holes. Closed: 0 of 0. Added: zero. Split off: zero.
No declaration in this delivery contains `sorry`. The axiom check still reports inherited
`sorryAx` through existing dependencies; this repair does not claim to close that transitive
proof chain. The theorem and DAG attachment are unchanged.

## No longer needed

None. No imports, declarations, nodes or modules are removed. Both declared proof
dependencies remain needed: `lem-weil-pbc-integral-constructible-kernels` supplies kernel
closure, and `lem-weil-pbc-constructible-cokernels-extensions` supplies the other two factors.
The unit route and the node's existing proof, proof dependencies and attachment stay intact.

## Where the brief, the DAG or earlier work was wrong

The quarantine error was a public-import visibility defect, not a remaining hole in this
module. The archived signature names closure predicates available only through private
proof imports. Explicit public imports of their defining Mathlib modules repair it.
No mathematical statement or definition changes. The dependency nodes' historical notes
about unfinished kernel work do not change this item's actual zero-hole count.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
