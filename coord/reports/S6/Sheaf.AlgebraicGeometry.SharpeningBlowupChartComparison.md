## What changed

Completed `AlgebraicGeometry.Monoscheme.sharpening_blowup_chart_comparison` and
`AlgebraicGeometry.Monoscheme.sharpening_blowup_overlap_comparison` in the assigned module.
The chart proof includes the product ideal, ordinary and saturated product charts, existence
and uniqueness of the intrinsic sharp equivalence, and the all-ideal fraction presentation.
The overlap proof includes ordinary, saturated, and triple-overlap equalities.

Added only proved private helpers: ideal-generator fraction membership; the positive-root
membership description; clearing denominators in a localized root saturation; the splitting
map's bijectivity and numerator formula; transport and product formulas for saturation;
and the sharp quotient equivalence for a product with a group. No definition or public
signature changed. All original public imports remain. Updated proof steps 4--7 and the
proof-origin record of the existing node to describe the completed Lean proofs.

The final single-file compile completed cleanly in 10.0 seconds through `lcompile.py`.
Both closed theorems follow directly from concrete definitions and Mathlib, without using
any of the remaining theorem holes in this module or the project's monoid lemma holes.

## Proved and sorry left

Closed 2 of the 6 original holes:

- `AlgebraicGeometry.Monoscheme.sharpening_blowup_chart_comparison`.
- `AlgebraicGeometry.Monoscheme.sharpening_blowup_overlap_comparison`.

Added 0 holes; split off 0 statements. The following 4 named theorem holes remain,
all attached to `lem-trf-sharpening-blowup-chart-comparison`, with their existing
source and complete natural-language proof docstrings:

- `AlgebraicGeometry.Monoscheme.sharpening_blowup_ideal_comparison`.
- `AlgebraicGeometry.Monoscheme.sharpening_saturated_blowup_exists`.
- `AlgebraicGeometry.Monoscheme.sharpening_saturated_blowup_comparison`.
- `AlgebraicGeometry.Monoscheme.sharpening_saturated_tower_comparison`.

Preserved the earlier complete proofs of `sharpening_blowup_chart_substitution` and
`sharpening_saturated_tower_pullback`. This is a partial proof delivery, with net two
holes closed, rather than a decomposition into new obligations.

## No longer needed

No imports or modules are removed, and no DAG node is withdrawn. All three existing
public imports supply statement-level interfaces. The completed algebraic chart and
overlap clauses do not need the planned fine-monoid unit-splitting, finite-saturation,
fs face-sharpening, integral-sharpening exactness, or affine-fan section lemmas: the
splitting is already an argument, and saturation and localization are computed directly.
Those dependency nodes remain needed by the four unfinished global geometric clauses,
so the node's overall proof-dependency list is retained. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found and no signature repair was needed. The displayed
algebraic clauses hold more generally than their retained fine/torsion-free hypotheses.
In particular the saturation formulas and overlap identities do not require the
finite-saturation theorem. Their proofs cover an empty generator set whenever its
stated hypotheses allow it, arbitrary chart denominators, trivial unit groups, and
coincident overlap indices. The global sheaf, gluing, torsion-free, and tower obligations
are not discharged by these algebraic calculations; their existing holes are left intact.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
