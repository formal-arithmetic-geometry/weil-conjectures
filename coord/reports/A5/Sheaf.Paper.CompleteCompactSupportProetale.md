## What changed

Filled three proofs in `lean/Sheaf/Paper/CompleteCompactSupportProetale.lean`.
Finite constant-section normalizations give the coefficient unit and counit identities;
limit projections give their completed versions. The resulting module adjunction proves
the section-normalized restriction unit and identifies its transpose with the unique
isomorphism between left adjoints. The derived open unit follows from the existing
Cartesian open comparison on the self-pullback square of the open immersion.

All added helpers are private, fully proved theorems. Existing declaration signatures,
definitions and imports are unchanged. The DAG's first proof step and proof origin now
record these arguments. No new nodes or change records are needed.

Validation: the complete module compiled through `lcompile.py`, with no warnings.
The proofs impose no quasi-compactness, nonemptiness or nonzero-coefficient assumptions;
the empty open and zero coefficient cases use the same formulas.

## Proved and sorry left

Closed 3 of the original 13 holes, with no holes added or split off:

- `AlgebraicGeometry.Scheme.cbcRestrictionUnit_existsUnique`
- `AlgebraicGeometry.Scheme.cbcPullToRestriction_isIso`
- `AlgebraicGeometry.Scheme.cbcOpenUnit_isIso`

The last proof uses the existing, still-holed `cbcBetaInv_isIso` declaration.
All ten remaining holes belong to `thm-cbc-complete-proetale`:

- `AlgebraicGeometry.Scheme.cbcBetaInv_isIso`
- `AlgebraicGeometry.Scheme.cbcOpenToPush_isIso`
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_isIso`
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_identity`
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_horizontal`
- `AlgebraicGeometry.Scheme.cbcRefinementMap_isIso`
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_compactifications`
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_refinement`
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_vertical`
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_composition_refinement`

## No longer needed

None. The existing imports and planned dependencies remain relevant to the unfinished
clauses; no module or node is withdrawn. The open-unit proof avoids a separate direct
calculation with extension-by-zero summands by using the already stated self-base-change
comparison.

## Where the brief, the DAG or earlier work was wrong

The step-6 dependency `Sheaf.Paper.CompleteProetaleStrictTowerRealization` imports this
item module. Importing it directly here would therefore create a cycle; its shared
interface requires extraction before the remaining strict-tower route can use it.

Explicit coefficient universes and an abstract ring-module helper prevent expensive
unfolding during the section-unit proof. Consolidating both finite coefficient identities
into one proof avoids repeating their constant-section calculation.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
