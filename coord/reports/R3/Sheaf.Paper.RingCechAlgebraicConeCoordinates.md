## What changed

Proved `CategoryTheory.ringCechAlgebraicCone_coordinates` with its entire signature
unchanged. The supplied tail differential is identified with the canonical one using
its hypotheses and uniqueness of algebra maps out of localization.

Added two completely proved supporting modules:
`Sheaf.Paper.RingCechConeLinearEquiv` constructs the subset partition, canonical face
maps, localization tensor equivalences, the degreewise coordinate equivalence, and
its evaluation formulas. `Sheaf.Paper.RingCechConeDifferential` proves the alternating
differential identity on the first block and on pure tensors in the second block,
then extends by tensor induction and adds the two identities. The augmented term is
checked separately. Both proofs follow Stacks `more-algebra.tex`,
`section-alternating-cech`, with localization base change from Mathlib.

Moved `ringCechTailTerm` verbatim into the first supporting module to avoid an import
cycle; it remains publicly available from the original module. The change record is
`coord/changes/R3-ring-cech-tail-term-relocation.md`. No other existing Lean module is
changed. The direct consumer `Sheaf.Paper.RingCechCoordinateTensorStep` compiled from
its unchanged source against the delivery in 43.9 s; its temporary copy was removed.
The supporting modules compiled in 7.9 s and 17.2 s, and the item in 2.6 s.
`#print axioms CategoryTheory.ringCechAlgebraicCone_coordinates` and the explicit
coordinate equivalence each report only `propext`, `Classical.choice`, `Quot.sound`.

## Proved and sorry left

Closed the original module's sole hole:
`CategoryTheory.ringCechAlgebraicCone_coordinates`
(node `lem-weil-pbc-ring-cech-algebraic-cone-coordinates`).

Holes closed: 1. Holes added: 0. Holes remaining in all three delivered Lean modules: 0.
No statements were split off with `sorry`. All definitions are actual constructions.
The main new results are `CategoryTheory.ringCechConeEquiv`,
`CategoryTheory.ringCechConeEquiv_d` and `CategoryTheory.ringCechConeEquiv_d_zero`.

## No longer needed

No DAG dependency, library module or unit step is pruned. The localization-base-change
leaf remains needed by the explicit construction. The original six direct public
Mathlib imports are replaced by the public import of the construction module; their
public APIs remain available through that module and its public imports. The
canonical differential module is a private proof import of the item. No unused
project proof dependency was imported.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The planned partition and sign argument
works without any assumption that a generator or the ring is nonzero. Empty ordered
coordinate types are handled by finite-product tensor distribution, while the
unique empty embedding handles the augmented term; thus r=0, zero generators,
repeated generators, the zero ring and degrees above the number of generators remain
included. The unit route is unchanged. Mathlib already supplies successive
localization and localization uniqueness, so no separate fraction-level inverse
construction or additional unproved lemma is necessary.

## New nodes

`lem-weil-pbc-ring-cech-cone-linear-equiv` records the explicitly constructed
coordinate equivalence and its pure-tensor evaluation formulas, including the
relocated augmented tail terms. Its module contains no holes.

`lem-weil-pbc-ring-cech-cone-differential` records the canonical alternating
differential compatibility and the degree-zero identity. Its module contains no
holes. Neither node creates a new proof obligation. The parent proof and dependency
list now agree with the Lean implementation. The relocation change record is
`coord/changes/R3-ring-cech-tail-term-relocation.md`.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
