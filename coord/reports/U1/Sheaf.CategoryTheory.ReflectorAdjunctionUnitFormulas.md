## What changed

Proved `CategoryTheory.exists_reflector_restricted_adjunction` in
`Sheaf.CategoryTheory.ReflectorAdjunctionUnitFormulas`. Applied the retained complete
proof to the current shared source, preserving its signature, public imports,
visibility, and existing docstrings verbatim.

The proof follows all seven DAG steps: establish the restricted functors' linearity,
compose the reflection Hom bijection with the ordinary adjunction, prove linearity
and naturality of the composite, construct the adjunction with
`Adjunction.mkOfHomEquiv`, and calculate the specified unit and counit.
The reflection bijection uses `hκB` with complete target `N`; it does not require
`L.obj M.obj` to be complete. `Equiv.ofBijective` takes its inverse from the actual
bijectivity hypothesis, so no construction rests on an unproved existence theorem.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.exists_reflector_restricted_adjunction`
(blueprint: `lem-sbc-reflector-adjunction-unit-formulas`).

Holes closed: 1. Holes added: 0. Holes left: 0. Split off: 0.
No other modules are changed. The repair compiled cleanly through `lcompile.py`
in 2.8 seconds (exit code 0). Delivery preflight checks the declaration axioms.

## No longer needed

None. All three original public imports are needed by the unchanged statement.
All stated proof dependencies are used through their recorded Mathlib declarations:
`def-weil-linear-category`, `def-weil-linear-functor`, and
`lem-weil-pbc-adjunction-of-natural-bijection`. No nodes or modules are withdrawn.
The existing seven-step DAG proof agrees with the Lean proof and needs no update.

Removed the obsolete sandbox change record
`coord/changes/U1-reflector-adjunction-source-publication.md` from the packet:
this is now a proof change to an existing module, with no interface publication.

## Where the brief, the DAG or earlier work was wrong

Repaired the return at delivery head `6f019ae165a`: its base `ca371c7a0` predated
publication of the assigned source by `45eba2ae8c4`, so the landing tools correctly
refused the earlier packet as a conflicting file creation. Read the current shared
source and compared it with the retained version. Their statements, imports, and
docstrings are identical; the sole mathematical difference is replacement of the
current theorem's `sorry` by the complete proof. Reapplied that proof to the current
source and recompiled it for this repair. The new delivery uses the current base.
The earlier publication change record and its historical report claims no longer
apply and have been removed from this packet.

No mathematical discrepancy or quarantine/rework entry was found. The retained
semantic and direct library searches found no theorem covering the entire normalized
linear restriction statement; the proof uses the recorded Mathlib constructor.
The unit `sk-rem-rest` has no realized statement or proof steps to bypass.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
