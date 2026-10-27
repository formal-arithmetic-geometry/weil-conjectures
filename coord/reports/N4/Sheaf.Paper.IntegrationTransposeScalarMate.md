## What changed

Proved `AlgebraicGeometry.Etale.IntegrationScalar.integrationTransposeScalarMate` in
`Sheaf.Paper.IntegrationTransposeScalarMate`, preserving its statement and all five
constructions. Added a proved private projection-naturality helper. The proof follows
all six existing DAG steps: the scalar projection square, naturality along the
orientation isomorphism, the trace equation and normalized right unitor, naturality
of the inverse scalar comparison, adjunction transposition, and conjugation by the
invertible gamma components.

Added the private proof import `Sheaf.Paper.ExceptionalCoefficientUnitCoherence`.
Updated the item's proof record to name its existing right-unit theorem explicitly.
No public definition or signature changes.

Validation: `lcompile.py` compiled the complete module cleanly in 23.5 seconds,
with no compiler warnings. The public theorem statement is byte-identical to the
original; every Lean line fits the 100-character limit.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.IntegrationScalar.integrationTransposeScalarMate`
(blueprint `lem-pur-integration-transpose-scalar-mate`).
No holes remain in the delivered module. No holes were added or split off.
The proof uses the existing `etaleCompactScalarCoherence` theorem, whose remaining
proof obligations stay in its own module.

## No longer needed

None. No imports, declarations, modules, or nodes were withdrawn. The tensor/pullback
comparison remains the one specified by the original statement. The unit route is
unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The normalization node supplies the chosen
comparisons, while their right-unitor law has already been proved separately as
`ExceptionalCoefficients.tensorIso_right_unit`, node `lem-pur-scalar-right-unit`.
The proof record now cites that existing theorem for step 3. It is used only as a
general normalization tool; it does not replace a step of the vector-bundle route.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
