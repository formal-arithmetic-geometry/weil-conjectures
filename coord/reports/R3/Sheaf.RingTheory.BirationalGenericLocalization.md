## What changed

Filled the proof of `Localization.bijective_map_of_unique_minimalPrimes` in
`Sheaf.RingTheory.BirationalGenericLocalization`, preserving its statement and imports.
The proof follows the seven-step Stacks 0BAB argument already recorded on
`lem-sfb-birational-generic-localization`: define the canonical localization maps,
use the surjective residue-field map to obtain a maximal kernel, identify its
contraction and extension, show every prime contains it, and invert all elements
outside the original minimal prime. Localization uniqueness identifies the resulting
isomorphism with the specified ring map.

The localization prime correspondence is used through
`IsLocalization.prime_localRing_residueField_iso`; minimal-prime existence and
maximal-ideal existence are used through their recorded Mathlib declarations.
There is no change to definitions, public interfaces, consumers, or the unit route.
The module compiles through `lcompile.py` (4.1 seconds of Lean compilation).
The final delivery preflight also checks compilation and declaration axioms.

## Proved and sorry left

Closed the sole hole: `Localization.bijective_map_of_unique_minimalPrimes`
(node `lem-sfb-birational-generic-localization`). One original hole closed,
zero holes added, zero holes remaining, and zero statements split off.

## No longer needed

None. Every original import is retained. All four recorded proof dependencies
remain used. No node, declaration, or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The earlier dropped per-chapter node
`lem-per-birational-generic-localization` is not used; this proves the live
six-functors node directly. The original assumptions and conclusion are unchanged.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
