## What changed

Closed five original holes in `Sheaf.Paper.RationalRealizationScalarCoherence`.
The mixed comparison is assembled from the declared unit-cancellation record,
including the strict completion-unit equation and the actual raw component transports.
The pentagon and coefficient mixed tower follow from the declared coherence equations
by cancellation and naturality. The pullback-composition construction inverts the
normalized ordinary, ambient, completed and raw comparisons. Identity mixed coherence
uses uniqueness of the tensor-unit-normalized ordinary unitor and its derived computation.

Added private proof imports of `Sheaf.Paper.RationalScalarMixedUnitCancellation` and
`Sheaf.AlgebraicGeometry.ProEtaleCanonicalAdjunctionUnit`, plus proved private helpers.
The existing public signatures, definitions and public imports are unchanged.
The node proof and proof dependencies now describe these arguments.

Validation: the complete assigned module compiled cleanly through `lcompile.py`
in 52.0 seconds. A source comparison found all 22 existing public signatures and
both public imports unchanged. No other library module is edited.

## Proved and sorry left

Closed 5 of the 6 original holes:

- `AlgebraicGeometry.Scheme.rationalRealizationScalarMixed`.
- `AlgebraicGeometry.Scheme.rationalRealizationScalarPentagon`.
- `AlgebraicGeometry.Scheme.rationalRealizationScalarMixedTower`.
- `AlgebraicGeometry.Scheme.rationalScalarPullComposition`.
- `AlgebraicGeometry.Scheme.rationalRealizationScalarMixedIdentity`.

One original hole remains:
`AlgebraicGeometry.Scheme.rationalRealizationScalarMixedComp`, attached to
`lem-per-rational-realization-scalar-coherence`. Its original statement, source,
complete proof docstring and `:= by sorry` body are retained.

Added holes: none. Split off: none. Actual hole count in the delivered module: 1.
These are proofs from the existing declared dependencies; those dependencies still
contain their own separately tracked holes.

## No longer needed

None. The original imports and all four original proof dependencies remain needed.
No module, node, declaration or unit route is withdrawn. The added canonical-unit
lemma is needed to identify arbitrary normalized identity records with the canonical
unitor used by the dependency's geometric identity theorem.

## Where the brief, the DAG or earlier work was wrong

The dependency's geometric coherence equations use its canonical normalized
compositors and unitors, whereas the parent accepts arbitrary records satisfying
normalization. Applying those equations to the parent needs uniqueness arguments;
the records do not match by definitional equality alone. The identity case is
proved here using the ordinary composite adjunction and cochain computation.

For the remaining geometric mixed-composition clause, the ordinary compositor is
similarly determined by its tensor-unit sections. The additional derived uniqueness
step is to use flat-term K-flat representatives, preservation under inverse image
and scalar extension, and cancellation of the two invertible computation counits;
then extend along a K-flat resolution by naturality. The final equation is the inverse
of `rationalMixedGeometricComposition` after identifying those compositors. Exploratory
scratch proofs are outside the delivery; no unverified helper is imported or delivered.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
