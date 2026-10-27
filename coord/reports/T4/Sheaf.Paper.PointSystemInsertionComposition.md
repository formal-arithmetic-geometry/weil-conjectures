## What changed

Filled the proofs of `WeilConjectures.PointSystemInsertion.coefficient_existsUnique`
and `WeilConjectures.PointSystemInsertion.G_exact` in the assigned module.
The first assembles the inverses of the normalized finite coefficient comparisons,
using their naturality for quotient reductions and the actual sequence-site maps.
A local transparency adjustment exposes constant sheafification only within these
private coefficient calculations, restoring the existing setting afterward.
The second transports the site equivalence to abelian sheaves and reflects finite
limits and colimits through the module-to-abelian-sheaf forgetful functor. All
existing declaration signatures and all data constructions are unchanged.

## Proved and sorry left

Closed two of the three original holes:

- `WeilConjectures.PointSystemInsertion.coefficient_existsUnique`.
- `WeilConjectures.PointSystemInsertion.G_exact`.

One original hole remains:
`WeilConjectures.PointSystemInsertion.pointSystemInsertionComposition`
(node `lem-trf-point-system-insertion-composition`). Its statement and proof sketch
are unchanged. No holes were added or split off. The earlier proved declarations
remain proved.

## No longer needed

No mathematical dependency nodes or modules are withdrawn: the main composition
proof still remains open, so its planned dependency route remains applicable.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction. Mathlib already supplies the sheafification
comparison, its normalization and naturality, and reflection of finite limits and
colimits; these suffice for the two auxiliary holes. The existing finite-field
specialization in `PointRestrictionSystemChainMap` supplied a checked template for
the sequence-ring component and naturality calculations; its finite-field datum
is not used in those calculations. The present proof works for the arbitrary
field and automorphism in the assigned signatures. The identity automorphism,
all positive powers, and the first quotient level are included without extra
conditions on system transitions.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
