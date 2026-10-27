## What changed

Proved five of the eight existing theorem holes. Naturality uses native scalar-Hom
naturality, and restriction normalization follows from a proved generic adjunction-mate
identity. The field tail is filtered and final, with finite freeness supplied by Cartesian
coefficients. The bimodule right unitor identifies scalar extension of the regular
module with the regular target module; its multiplication equation and the actual
mixed-scalar transition formula preserve all transition maps and closure legs.
Finality restricts the existing ring-object colimit to the prescribed field tail.

All original public declaration signatures, definition bodies and public imports are
preserved. New helpers are private and proved. A proof-only import supplies native
scalar-Hom naturality; The existing dependency imports supply filtered finality. The DAG
copy records these auxiliary arguments while retaining the unfinished comparison route.

Focused compilation of this complete packet passed in 52.5 seconds with local monoidal transparency boundaries. The delivery tool
performs the final compile and preflight. Work on all eight proof bodies is preserved
in scratchpad/full-proof-before-partial-packet.lean.txt, outside the delivery. That larger
candidate exceeded the 60-second compile limit despite substantial profiling and
conversion simplifications, so its unvalidated definition changes are not included.

## Proved and sorry left

Original holes: 8. Closed 5:

- AlgebraicGeometry.ProEtale.QlbarInternalHom.evaluationComparison_naturality
- AlgebraicGeometry.ProEtale.QlbarInternalHom.evaluationComparison_restriction
- AlgebraicGeometry.ProEtale.QlbarInternalHom.fieldDiagram
- AlgebraicGeometry.ProEtale.QlbarInternalHom.coefficientModules
- AlgebraicGeometry.ProEtale.QlbarInternalHom.coefficientRingColimit

The following 3 original holes remain unchanged, all attached to
lem-sfb-qlbar-internal-hom-coefficient-comparison:

- AlgebraicGeometry.ProEtale.QlbarInternalHom.coefficient_colimit_formula
- AlgebraicGeometry.ProEtale.QlbarInternalHom.coefficient_comparison_roof
- AlgebraicGeometry.ProEtale.QlbarInternalHom.qlbar_internalHom_coefficient_comparison

Holes added: 0. Split off: 0. No private helper or definition contains sorry.

## No longer needed

Imports removed: none. No node or module is withdrawn. The aggregate finite-free tail
presentation is unnecessary for the five proved auxiliary clauses: direct filteredness,
Cartesian finite freeness, the regular-module unitor and finality suffice. It remains
in the DAG for the three original unproved comparison clauses. No dependency of that
unfinished argument is declared obsolete or pruned.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed or weakened. The generic native evaluation-roof argument and
finite-free transport compiled in focused diagnostic files, but the full eight-proof
candidate did not pass whole-file compilation. Large existential eliminations caused
avoidable unfolding: explicit witness projections fixed the finite-free diagnostic.
Further section-module and monoidal-instance conversions remain expensive in the full
candidate. No compiler limit was raised and no module was split to evade it.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
