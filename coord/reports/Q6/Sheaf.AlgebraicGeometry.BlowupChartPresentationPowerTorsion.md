## What changed

Proved `AlgebraicGeometry.blowupChartPresentationPowerTorsion` without changing
its statement or any public definition. Evaluation sends the quotient variables
to the specified chart fractions. Ideal-span induction shows its image contains
the generators of the chart subalgebra. The proved private helper
`presentation_constant_multiple` uses polynomial induction to turn every
quotient class into a constant after multiplication by some power of `a 0`.
The localization zero criterion then proves both directions of the kernel
characterization. Updated the item node to describe these two inductions.

Searches: Lean Finder for the quotient-to-chart power-torsion kernel found only
general algebra-presentation kernels and the presentation of the full
localization. Loogle for `"IsLocalization", "eq_zero"` found
`IsLocalization.map_eq_zero_iff`, which is used. Mathlib grep for
`chartRing|ker_localizationAway`, and repository searches for power torsion,
found no existing theorem with this chart-presentation statement. The source
strict-transform kernel argument was useful as a model, but its tensor-product
source differs and its module is not imported.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.blowupChartPresentationPowerTorsion`
(node `lem-trf-blowup-chart-presentation-power-torsion`).

Holes closed: 1. Holes added: 0. Sorries left in the delivery: 0.
No intermediate statements were split off. The final source compiled cleanly
through `lcompile.py` in 22.4 seconds (exit code 0).

## No longer needed

None. All original statement imports and all four declared dependencies remain
needed. No existing module or DAG node is withdrawn. The proof does not import
`WeilConjectures.Blowup.Affine.StrictTransformChart`.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The degree-bound calculation of the planned proof
is implemented by polynomial induction: sums use the sum of the two exponent
bounds, and multiplication by a variable increases the exponent by one. This
needs neither regularity nor cancellation in R. The one-generator case s=0,
the zero ring, nilpotent a, and unit a all remain covered. The unit route and
the source-library boundary are unchanged.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
