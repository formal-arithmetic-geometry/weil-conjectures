## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Scheme.Modules.graded_line_homogeneous_fraction_atlas` by an explicit
construction from two smaller geometric comparison lemmas. The original theorem statement,
public imports, definitions, and downstream API are unchanged.

Added proved private scalar-coefficient and localized scalar formulas. The proof explicitly
indexes localization spectra by every affine free frame and positive-degree denominator.
It proves that their ranges are the corresponding coefficient basic opens. Generation gives
a covering: a nonunit coefficient would put the given homogeneous-image germ in the
maximal-ideal multiple, contradicting the generation hypothesis. The proof then constructs
an open cover, glues its prescribed maps using overlap compatibility, proves the structural
equation over the base from the scalar formulas, applies the trivialized-test comparison,
and supplies every requested fraction formula and factorization by the gluing equations.

New modules: `GradedLineFractionChart` (concrete chart indices and maps, no holes),
`GradedLineFractionOverlap` (pairwise overlap equality), and `GradedLineFractionTest`
(comparison on one trivialized open test). All are under `Sheaf.TraceFormula`.
Only proof imports were added to the item. No existing shared module was changed.

Validation: `lcompile.py --all` compiled all four modules without diagnostics.
Timings: chart data 13.6 s, overlap 11.0 s, test comparison 13.0 s, item 33.7 s.
After restoring the original namespace opening, the final item recompiled in 30.7 s.
The three new node signatures also match the preflight parser exactly.
A signature comparison confirms the original theorem type is byte-for-byte unchanged.
Every dependency reference resolves and no delivery node belongs to a dependency cycle.

## Proved and sorry left

Closed the existing hole in
`AlgebraicGeometry.Scheme.Modules.graded_line_homogeneous_fraction_atlas`
(node `lem-trf-graded-line-homogeneous-fraction-atlas`). Its proof is complete from the
imported statements, with no local `sorry`.

Added exactly two named theorem holes:

- `AlgebraicGeometry.Scheme.Modules.gradedLineFraction_overlap`
  (`lem-trf-graded-line-fraction-overlap`). It compares two already constructed maps
  on their pullback and has no generation or global existence conclusion.
- `AlgebraicGeometry.Scheme.Modules.gradedLineFraction_test`
  (`lem-trf-graded-line-fraction-test`). It compares an already supplied morphism
  with `Proj.fromOfGlobalSections` on one trivialized open test; it does not construct
  the morphism or assert its structural equation.

This is a decomposition: one old hole closed, two smaller holes added, net minus one.
The chart data module has zero holes; all definitions are explicit constructions.
The scalar, cover, gluing, structural-map, and existential-witness assembly arguments
are proved in Lean rather than postponed in either new statement.

## No longer needed

Removed `lem-weil-pbc-nonvanishing-section-trivializes` from this node's proof dependencies:
the generation cover follows directly by taking germs of the coefficient equation and
using membership in the maximal ideal, without a nonvanishing-open trivialization theorem.
Its module is not withdrawn; the original public imports are retained.

No original imports were removed. The sheaf-input atlas modules
`Sheaf.TraceFormula.LineProjAffineChartAtlas`,
`Sheaf.TraceFormula.LineProjFractionChartData`,
`Sheaf.TraceFormula.LineProjFractionCoefficientHom`,
`Sheaf.TraceFormula.LineProjGenerationLocus`, and
`Sheaf.TraceFormula.LineProjFractionCompatibility` were inspected but not imported:
their input requires homogeneous sheaves and their decomposition, whereas the present
statement only supplies affine-basis graded algebra data. Their algebraic construction
is supplied directly by the item's existing coefficient and localization helpers.
The new overlap and test lemmas retain the two affine-basis geometric arguments.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The original plan's claim that the generic gluing
and nonvanishing lemmas alone supply all remaining geometry omits two substantial
comparisons: arbitrary affine-base/frame overlaps, and compatibility with tensor-pullback
trivializations in `IsCanonicalMap`. These are now separate sourced Lean statements.
The stronger sheaf-input atlas interface is not immediately applicable to affine-basis
`GradedAlgebraData`. No unsupported decomposition or arbitrary choice from a sorried
existence theorem was introduced.

Edge cases checked mathematically: empty source or test, zero/nilpotent denominator,
zero divisors, exponent zero, distinct positive degrees, base intersections that are
not affine, arbitrary degree-zero algebra, and a line module only locally framed on
the opens used by the comparison lemmas. The two lemmas need neither global generation
nor invertibility away from those framed opens.

## New nodes

`def-trf-graded-line-fraction-chart` records the explicit framed chart indexing,
coefficient family, localization domain, source open immersion, target map, and fraction
formula. Its supporting Lean definitions are concrete and have no `sorry`.

`lem-trf-graded-line-fraction-overlap` isolates the original proof's second step,
agreement of two fraction-chart maps after arbitrary affine-base and frame refinements.

`lem-trf-graded-line-fraction-test` isolates the original proof's fourth step,
identification on a trivialized open test with Mathlib's global-section Proj morphism.

All three nodes inherit the item's chapter, unit, blueprint ancestor, and source.
No change record is needed because no existing signature or definition changed.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
