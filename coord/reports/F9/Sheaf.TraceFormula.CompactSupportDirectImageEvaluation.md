## What changed

The parent direct-image evaluation theorem is now a real assembly of two strictly smaller
component theorems.  The ordinary component records the sectionwise identity comparison;
the derived component records the derived comparisons, arbitrary-resolution normalization,
and the unit and counit equations.  The parent packages their conclusions without adding
any further assumptions or changing its statement.  Two DAG nodes were added for these
component theorems, and the parent node proof dependencies were updated accordingly.

## Proved and sorry left

- Closed `WeilConjectures.compactSupportDirectImageEvaluation` (the original module hole).
- Added one `sorry` in `WeilConjectures.compactSupportDirectImageOrdinaryEvaluation`.
- Added one `sorry` in `WeilConjectures.compactSupportDirectImageDerivedEvaluation`.

The two remaining declarations are strictly smaller parts of the argument: the first is
only the ordinary comparison and its section normalization; the second takes that ordinary
comparison as input and concludes only the derived square and its two mate equations.

## No longer needed

The parent proof uses only the two component declarations and
`def-trf-compact-support-system-evaluation-diagram`.  The former direct proof-plan
dependencies `def-coef-ringed-sequence-site`, `prop-weil-pbc-proetale-constant-ring-map`,
`def-weil-proetale-inverse-image`, and `lem-coef-semilinear-derived-sections` are delegated
to the component statements and are not imported or used directly by this delivery.
No existing module was withdrawn.

## Where the brief, the DAG or earlier work was wrong

The imported three-step proof plan combines the ordinary section comparison, the derived
arbitrary-resolution comparison, and the mate equations into one declaration.  Those
pieces have independent interfaces and were therefore split into two proper substatements;
the parent proof is now a complete tuple assembly.  No target statement was changed.

## New nodes

- `lem-trf-compact-support-direct-image-ordinary-evaluation`
- `lem-trf-compact-support-direct-image-derived-evaluation`

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
