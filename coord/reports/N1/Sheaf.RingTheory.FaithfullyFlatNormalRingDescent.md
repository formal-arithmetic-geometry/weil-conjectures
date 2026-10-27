## What changed

Completed `Algebra.normal_ring_of_faithfullyFlat` in
`Sheaf.RingTheory.FaithfullyFlatNormalRingDescent`, without changing its signature,
docstring, or imports. Added a proved private helper
`Algebra.integrallyClosed_of_faithfullyFlat` in the same module.

The proof follows Stacks, Algebra, Tag 033G and the node's six steps. Lift each
prime to the faithfully flat algebra, equip the induced map of prime localizations
with its algebra structure, and use flatness and locality to obtain faithful
flatness. Injectivity descends domainhood. For integral closedness, embed the base
fraction field in the target fraction field, transport integrality, and use the
target's integral closedness. Contract the principal ideal of the denominator to
recover the fraction in the base ring. All ingredients are already in Mathlib.

The single-file server compile passed without warnings (7.8 seconds). No data is
chosen from an unproved theorem. No assumption of Noetherianity or domainhood of
the unlocalized rings is introduced. The zero ring is handled by the absence of
prime ideals, as in the unchanged statement.

## Proved and sorry left

Closed the sole original hole:
`Algebra.normal_ring_of_faithfullyFlat`
(`lem-sfb-faithfully-flat-normal-ring-descent`).

The private helper `Algebra.integrallyClosed_of_faithfullyFlat` is proved.
Holes closed: 1. Holes added: 0. Sorries left: none. Split off: none.

## No longer needed

None. Every existing import is used by the statement or proof. All six declared
proof dependencies remain used, through their recorded Mathlib declarations or
the inline normal-ring predicate. No node or module is withdrawn, and the DAG
proof plan and unit route remain unchanged.

## Where the brief, the DAG or earlier work was wrong

None. The existing proof plan suffices directly using the recorded Mathlib APIs.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
