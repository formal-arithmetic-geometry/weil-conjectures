## What changed

Proved `AlgebraicGeometry.Etale.etaleAmbientLeftComparison_baseChange` in
`Sheaf.AlgebraicGeometry.EtaleAmbientLeftComparisonBaseChange`, preserving its statement
and public imports. Private proved helpers identify arbitrary normalization with the
canonical graph comparison, compute the normalized inverse exchange mate, transport
exact pullback to left-derived pullback, and combine it with compact-support composition.
The node proof and proof dependencies now record this route.

Added private proof imports for normalized-mate pasting, open-extension proper-support
range, and the support-exchange right-mate identity. The normalized-mate module publicly
provides the unbounded compact-support comparisons and compactification refinements.
No existing module other than the assigned item was changed, and no public declaration
was added.

Validation: the complete module compiled cleanly through `lcompile.py` in 29.6 seconds;
the main signature is byte-for-byte unchanged and all Lean lines are at most 100 characters.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.etaleAmbientLeftComparison_baseChange`
(node `lem-amb-etale-left-comparison-base-change`).

Original holes: 1. Closed: 1. Added: 0. Remaining in the delivery: 0.
No split-off statements. Existing imported statements with pending proofs are used as
permitted by stage 3; their holes are not moved or duplicated in this delivery.

## No longer needed

No module is withdrawn and no existing public import is removed.
The former direct proof dependencies
`def-weil-pbc-etale-shriek-base-change-map`,
`def-weil-pbc-underived-exchange`,
`lem-weil-pbc-etale-restriction-injectives`, and
`lem-weil-pbc-etale-shriek-base-change-modules` are not used directly: existing normalized
support right-mate and pasting results replace a new sheaf-level exchange calculation.
They may still be needed transitively or by other consumers; this delivery does not
claim their global removal. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No statement repair was required. The existing plan's sheaf exchange calculation need
not be repeated: the declared normalized support right-mate theorem, open-restriction
normalization and normalization-pasting theorem give the exact square on arbitrary
Cartesian squares. The proof explicitly transports this identity to the left-derived
adjunctions in the unchanged statement.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
