## What changed

In `Sheaf.Paper.IntegralPointTransportComparisons`, proved
`WeilConjectures.IntegralPointTransportTower.restrictionComparison_existsUnique`
by specializing the existing proved
`WeilConjectures.integralTowerInverseImageUnit_existsUnique` to
`((pointFrobeniusAut D)^r).hom`. Added a private proof import of
`Sheaf.Paper.IntegralTowerInverseImageUnit`. The theorem statement, every definition,
and all preexisting proofs and public imports are unchanged. Updated the item's
node proof and proof dependencies to record this specialization.

Validation: `lcompile.py` compiled the complete delivered module successfully
(exit 0, 45.9 seconds, within the 60-second limit). The import-direction check
accepted the new proof import without a cycle.

The existing theorem applies to every scheme isomorphism, every quotient system,
every index and every site object. Its section normalization is exactly the
item's formula, including the actual sequence generator and comma arrow. In
particular, the identity power and zero sections require no separate assumptions.
The cited theorem's module contains no `sorry`. Its node belongs to the same
unit `sk-thm-trace-transport`, and no unit statement or proof step is bypassed.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.IntegralPointTransportTower.restrictionComparison_existsUnique`
(node `lem-trf-integral-point-restriction-comparison`).

Holes closed: 1. Holes added: 0. Sorries left in the delivered module: 0.
No split-off statements or other modules are added.

## No longer needed

The item's direct proof dependencies
`lem-weil-proetale-isomorphism-inverse-image`,
`lem-weil-isomorphism-scalar-quotient-chain-squares`, and
`lem-trf-ordinary-quotient-pullback-tower-comparison` are replaced by
`def-trf-integral-tower-inverse-image-unit`. The general unit theorem already
constructs the normalized whole-tower comparison, so repeating the finite-level
construction and its assembly is unnecessary. These nodes and modules are not
withdrawn: their other consumers and the general theorem's dependencies remain.
In particular, the existing private scalar-quotient import is still needed by
the already proved inverse-limit comparison in this module.

No preexisting imports were removed, and no modules are claimed globally pruned.
The new proof import is used by the single specialization above.

## Where the brief, the DAG or earlier work was wrong

The old proof plan missed the existing general theorem
`integralTowerInverseImageUnit_existsUnique`, which has the identical normalization
for arbitrary scheme isomorphisms. The specialization avoids duplicating its
completed-linear construction and transition compatibility argument. The item
statement itself needs no correction.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
