## What changed

Replaced the proof of `WeilConjectures.PowerTorsionLimit.unit_condition` in
`Sheaf.Paper.PowerTorsionSheafLimitComplete` by a proof from
`koszulRepresentativeAugmentation_naturality`. Projection from the product reduces
the one-minus-shift equation to that existing adjacent-level identity. Explicit
site and sheaf-composition instances fix the independent coefficient universe.
No statement, definition, visibility, or import changed.

## Proved and sorry left

Closed one of the two existing holes:
`WeilConjectures.PowerTorsionLimit.unit_condition`.

One existing hole remains:
`WeilConjectures.PowerTorsionLimit.power_torsion_sheaf_limit_complete`
(node `lem-sp-power-torsion-sheaf-limit-complete`). Its existing full proof plan
is retained. The signed double-Roos interchange, nilpotent Koszul-unit calculation,
and projection-normalized quotient comparison are not proved by this packet.
No holes were added or split off.

## No longer needed

None. The main theorem remains unfinished, so its planned dependencies and imports
are retained; proving the elementary unit condition does not justify pruning them.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The existing Koszul augmentation naturality
lemma suffices for the first hole; no additional intermediate statement is needed.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
