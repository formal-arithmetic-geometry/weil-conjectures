## What changed

Repaired `sectionRingVeroneseFractionCanonicalMap` so it is explicitly the quotient
of the constructed numerator-to-fraction map by the section-fraction relations.
The theorem retains the repaired full statement: bijectivity plus the generator
formula `[n, ξ] ↦ ξ / s^n`. Its proof uses the kernel equality and surjectivity of
the explicit map, then computes the quotient lift on each summand generator.
Added the forced definition change record and updated the item's node proof route.

## Proved and sorry left

Verified the proof of `sectionRing_veronese_fraction_core` (one theorem of one)
with no `sorry` left and no split-off statements. Holes closed: none; holes added:
none. The current repository baseline already proves this theorem, so the net
hole change is zero; this delivery repairs the construction and proof route.
The definition is concrete and uses no witness from a bare existence theorem.

## No longer needed

Removed import `Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsFormula`.
The old proof dependency `lem-sc-section-ring-veronese-fractions-formula` is no
longer used by this module. The replacement route uses
`lem-sc-section-ring-veronese-fraction-kernel` and
`def-sc-section-ring-veronese-fraction-map` directly. No module becomes unreachable
from targets: the parent `SectionRingVeroneseFractions` still imports and uses the
formula module. No unit-level realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous repair exposed bijectivity but still defined the advertised canonical
map as an inverse equivalence. That obscured the requested map `[n, ξ] ↦ ξ / s^n`.
The definition is now the explicit quotient descent, while the theorem certifies its
bijectivity and generator value. The existing theorem statement is unchanged.

## New nodes

None. The existing kernel and explicit numerator-map nodes supply all dependencies.

## Earlier second reading (a previous round; superseded)

Read the repaired node, the explicit numerator map, and the kernel theorem. The
canonical map's definition now directly descends the fixed map whose value is the
homogeneous fraction with denominator `s^n`; its kernel equality and surjectivity
strictly supply injectivity and surjectivity. The generator computation is checked
by the summand formula and numerator cancellation. The theorem signature is unchanged
and all edge cases remain included. The change record
`coord/changes/sectionRing_veronese_fraction_canonical_map.md` records the forced
definition change.

## Second reading by K2

1. Compared the delivered module against the repository with `diff` and checked
   both declaration signatures byte for byte: identical. The sole definition-body
   change is declared in `coord/changes/sectionRing_veronese_fraction_canonical_map.md`.
   A scratch `example ... := by rfl` identifies the new map with the old map, so
   the theorem's meaning is preserved. Downstream-use search found no external
   textual user of the map; the direct importer retains its own formula import.
2. Compiled the delivered file locally with `lcompile.py`, cleanly. No `sorry`,
   forbidden declaration mechanisms, or hollow definitions occur. The scratch
   axiom checks for both declarations show only `propext`, `Classical.choice`,
   and `Quot.sound` (no `sorryAx`). Data are the concrete quotient descent of the
   constructed numerator map, with no witness from a bare existence theorem.
3. No new statements or split-off holes exist. Read the existing numerator-map,
   cancellation, surjectivity, and kernel proofs. The general quotient criteria
   apply without additional hypotheses, including `d=0`, `n=0`, and zero or
   nilpotent `s`; there is no denominator cancellation assumption.
4. Checked the shortest route against Mathlib's quotient lift, injectivity, and
   surjectivity lemmas and the existing library constructions. These are used
   directly. The kernel import is public because the exposed definition uses
   its theorem; the formula import is removed. Corrected the pruning report to
   name the old formula dependency while distinguishing local pruning from
   target-closure pruning. Inspected `dag/units/sk-thm-curveestimate.json`:
   its `realized` statement and steps remain intact.
5. Parsed the old and new node JSON: only `proof`, `proof_deps`, and
   `proof_origin` differ. Those fields match the two proof steps and imported
   kernel/map declarations. No new nodes or statement changes were made.

Second-reading changes: corrected the report's baseline hole accounting and
pruning list; expanded the change record to include both full definitions,
downstream findings, and meaning preservation; normalized JSON Unicode to avoid
unrelated textual changes. The compiled Lean proof needed no repair.
