## What changed

Only Sheaf.Paper.PointWeilPairingRealization is changed. Proved the point-category
shift stability, unique normalized rational shift, unique normalized small unit,
fullness and faithfulness, point-Hom realization bijectivity, coefficient-scalar
bijectivity, and compact/ordinary specialization. Statements and definition bodies
are unchanged. Full and faithful are moved before realize_bijective so that its
proof can use them. The existing private, fully proved pointRationalFibre_equivalence
and rawLocalization helpers are accessed with proof-only `import all`; no dependency
module or public visibility is changed. The DAG Step 1 now records the actual proof.

## Proved and sorry left

Closed 8 of the original 11 holes, with no new holes or split statements:

- WeilConjectures.PointWeilPairing.fdShift
- WeilConjectures.PointWeilPairing.fShift_existsUnique
- WeilConjectures.PointWeilPairing.unit_existsUnique
- WeilConjectures.PointWeilPairing.full
- WeilConjectures.PointWeilPairing.faithful
- WeilConjectures.PointWeilPairing.realize_bijective
- WeilConjectures.PointWeilPairing.scalar_bijective
- WeilConjectures.PointWeilPairing.compact_ordinary_specialization

Three original holes remain, all attached to
lem-pod-point-weil-pairing-realization with their original source and proof docstrings:

- WeilConjectures.PointWeilPairing.tensor_existsUnique
- WeilConjectures.PointWeilPairing.point_weil_pairing_realization
- WeilConjectures.PointWeilPairing.exchange_isIso

The large tensor normalization and pairing/coherence arguments are unchanged.
No arbitrary existence witness is used to construct new data: the two existence
proofs closed here retain their existing uniqueness conditions and definitions.

## No longer needed

Removed the following unused private proof imports:
Sheaf.SixFunctors.PointRingedEvaluationModel,
Sheaf.Algebra.Homology.FieldComplexCohomologySplitting,
Sheaf.Paper.ConstantWeilStructure,
Sheaf.Paper.InverseImagePullbackComparisonDerived,
Sheaf.Paper.CanonicalCoefficientPullbackReduction,
Sheaf.Algebra.Homology.TotalTensorSignedCoherence, and
Sheaf.SixFunctors.CompletedTensorShiftRight.

The projective-single Hom equivalence replaces field splitting in the proved Hom
calculations. The Step 1 dependency lem-trf-field-complex-cohomology-splitting is no longer
needed for the point-Hom and scalar calculations, which use homSingleEquivOfProjective.
The other six nodes remain in the plan of the untouched main pairing hole; their
modules should be imported when that proof uses them. No module is withdrawn and
the unit route is unchanged.
All original public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The public point_fibre_equivalence wrapper is stated
for finite fields embedded in a chosen algebraic closure, but its existing proved
private rational helper already handles the arbitrary finite extension used here.
`import all` avoids changing that dependency's interface. The DAG Hom step can use
the proved projective-single API directly, without constructing a complex splitting.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
