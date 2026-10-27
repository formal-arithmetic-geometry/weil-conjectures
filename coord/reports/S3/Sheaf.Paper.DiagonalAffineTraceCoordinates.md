## What changed

Filled three auxiliary theorem proofs in `Sheaf.Paper.DiagonalAffineTraceCoordinates`.
`projectionSmooth` inducts on the affine-line tower and composes relative dimensions.
`coefficientPlus` obtains flatness of the degree-one Tate line from its signed tensor
inverse, then inducts using the tensor lower-bound theorem and the shift by two.
`powerUnit` uses the cast-of-power identity and `IsUnit.pow`.

Added two proof-only imports: `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`
and `WeilConjectures.SixFunctors.Etale.Derived.Shift`. Updated the existing node's proof,
proof dependencies and proof origin. All existing signatures and public imports are
unchanged. Only proposition-valued
local instance proofs in `MapPair` and `transportCoordinates` are made explicit to
avoid expensive finite-type instance search. Their data are unchanged by proof
irrelevance. See `coord/changes/S3-diagonal-affine-coordinate-instance-proofs.md`.
No other module is adapted.

The optimized full module compiled cleanly through `lcompile.py` in 28.3 seconds.
Profiling after a delivery timeout identified slow local finite-type instance search
and motivated the explicit instance proofs above. An unchanged copy of the sole
downstream consumer `DiagonalAffineTraceSiteComparison` also compiled against the
sandbox module; that temporary copy is excluded from delivery. The smoothness induction includes dimension zero. The boundedness argument uses no finiteness of the
coefficient ring; its tensor-inverse argument also covers the zero ring, exponent one,
and the empty base.

## Proved and sorry left

Closed 3 of the 4 original holes; added 0 holes and split off 0 statements.
The following names are in namespace
`WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace`:

- Proved: `projectionSmooth`.
- Proved: `coefficientPlus`.
- Proved: `powerUnit`.
- Original hole retained unchanged: `projectionIso_existsUnique`
  (node `def-pur-diagonal-affine-trace-coordinates`).

This is a partial proof delivery, not a claim to have proved the projection formula.

## No longer needed

None. No original imports, nodes or modules are removed. The original node had no
proof steps or proof dependencies to prune. All original public imports remain needed
by its coordinate constructions.

## Where the brief, the DAG or earlier work was wrong

The node had an empty proof plan despite the four theorem holes in its module; the
updated proof plan records the three auxiliary arguments actually completed.

`projectionIso_existsUnique` does not retain the ambient invertibility assumption
`hS` in its elaborated signature, since its statement does not mention it. Its
projection-isomorphism assertion therefore needs an argument for that full signature.
The invertible-Tate-line boundedness argument completed here does not supply that
remaining argument. No statement is changed or asserted false.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
