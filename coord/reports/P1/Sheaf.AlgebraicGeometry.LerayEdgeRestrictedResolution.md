## What changed

Replaced the proof hole in
`AlgebraicGeometry.Scheme.Modules.lerayEdge_restrictedResolution`, preserving its exact
statement. The item now proves the restriction calculation locally from
`restrictedResolution_cohomology`, naturality of the homology/evaluation comparison,
and naturality of theta, then applies the whole-open identity and naturality of the
inverse derived resolution comparison.

Added the proved helper modules `Sheaf.AlgebraicGeometry.SectionCohomologyCycleFormula`
and `Sheaf.AlgebraicGeometry.LerayWholeOpenClass`:
`whole_open_leray_edge` identifies the whole-open section-class map with the chosen
cocycle-pinned Leray edge. Its proof explicitly calculates the sheafification adjunction
on cycles and uses the monic cycle inclusion to identify the cycle section, followed
by surjectivity of the cycle quotient. The calculation follows proved private helpers
in `FlatUnitRawSections`; the restriction calculation follows proved private helpers in
`TargetSectionClassRestriction`. Those adopted source modules remain unchanged.

Added private imports of `RestrictedResolutionCohomology` and `LerayWholeOpenClass`.
Updated the item's node proof and added a node for the proved whole-open identity.
Kept the large constructed maps and homology/resolution comparisons locally irreducible
during comparisons to avoid unnecessary unfolding. No transparency override is used. No shared definition, existing signature, or public import changed.

Validation: `lcompile.py --all` compiled all three final files without errors or warnings:
`SectionCohomologyCycleFormula` 21.5 s, `LerayWholeOpenClass` 49.5 s, and the item 40.1 s.
Every file is below the unchanged 60-second wall-clock limit.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.Scheme.Modules.lerayEdge_restrictedResolution`
(node `lem-weil-pbc-leray-edge-restricted-resolution`).

Also proved the new helper `AlgebraicGeometry.Scheme.Modules.whole_open_leray_edge`
(node `lem-weil-pbc-leray-edge-whole-open-class`). All private helpers are proved.
Also proved `AlgebraicGeometry.Scheme.Modules.section_comparison_cycles`
(node `lem-weil-pbc-section-cohomology-cycle-formula`).
Added 0 holes; split off 0 unproved statements. No `sorry` remains in delivered files.

## No longer needed

No imports or modules removed. Both original public imports are needed by the statement.
The direct dependency on `lem-weil-pbc-derived-functor-map-via-lift` in the cycle argument
now passes through the proved whole-open helper. No nodes are withdrawn; the unit route
and the original three mathematical steps are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error was found. The formerly split obligation closes by
combining the existing restriction calculation with the explicit cocycle characterization
of the chosen Leray edge. No additional unproved theory is required.

## New nodes

`lem-weil-pbc-leray-edge-whole-open-class` records the proved whole-open part of the
argument, in `Sheaf.AlgebraicGeometry.LerayWholeOpenClass`. Its source is Stacks 01E4 and
01F4. LeanFinder, Loogle, and Mathlib grep found no existing comparison with this chosen
edge. The lemma removes the arbitrary open and restricted-resolution data; the parent
adds the restriction/naturality argument in real Lean. There are no change records
because no existing interface is changed.


`lem-weil-pbc-section-cohomology-cycle-formula` records the proved theta-on-cycles
calculation, in `Sheaf.AlgebraicGeometry.SectionCohomologyCycleFormula`, from Stacks 01E4.
The formula is stated at an arbitrary open and degree and makes no injective-resolution
or Leray choice. Search found the proved private calculation in `FlatUnitRawSections`,
which is reproduced through its Mathlib API without modifying the adopted source tree.
After local folding of constructed maps, the combined helper still exceeded 60 seconds;
this self-contained calculation was therefore factored into its own proved module.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
