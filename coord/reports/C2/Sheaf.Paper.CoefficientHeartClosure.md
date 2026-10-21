## What changed

Restored `lean/Sheaf/Paper/CoefficientHeartClosure.lean` from the archive identified
by its current `coord/rework.tsv` entry. The live module was absent following the
cluster restore; its archive already contains a complete proof. The restoration
is byte-for-byte faithful to that archive, including all public imports, the
signature of `AlgebraicGeometry.ProEtale.coefficientHeart_closure`, and its private
helpers. No quarantined file is deleted and no Lean attachment is removed.

The existing proof identifies lisse modules with locally finitely presented
modules using the finite-field and bounded-image algebraic-closure criteria,
transfers the generic local and stratified Serre closure results, and constructs
the abelian full subcategory and exact inclusion using Mathlib. The finite
stratification comparison includes rank zero, empty strata and the empty scheme.

Validation: `lcompile.py` compiled the restored module against the current server
library with exit code 0, no diagnostics, in 11.5 seconds. The restored source has
no `sorry`. No mathematical or interface change is necessary against the current
dependencies. This is a missing-module restoration, not a newly proved theorem.

## Proved and sorry left

The archived module has zero holes. Its existing complete proof of
`AlgebraicGeometry.ProEtale.coefficientHeart_closure` is restored
(node `det-lem-coefficient-heart-closure`). Holes closed in this repair: zero.
Holes added: zero. Holes remaining in the item: zero. No statements are split off.
Dependencies retain their own proof status; this report makes no claim that all
dependencies are axiom-free.

## No longer needed

None newly pruned. All archived imports and the current node's dependencies are
retained. No node, module, source declaration or quarantined parent is withdrawn.
The existing DAG proof already describes the restored Lean proof, so no node
update is needed.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantined restoration with zero existing holes, as recorded in
`coord/rework.tsv`, rather than an unproved theorem. Its archived implementation
now compiles against the current server dependencies without adaptation. The
missing live module, rather than its archived mathematical proof, was repaired.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
