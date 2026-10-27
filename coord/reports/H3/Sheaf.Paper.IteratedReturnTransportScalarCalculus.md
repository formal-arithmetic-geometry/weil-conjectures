## What changed

Replaced the assigned theorem's one hole with naturality, scalar-iteration and point-iteration
arguments plus three strictly lower coherence statements. Generic private lemmas prove
iteration naturality, return-comparison naturality, point scalar induction, and scalar unit
and tower induction. Finite constructibility uses the existing arbitrary-finite-ring
pullback argument. Integral comparison naturality uses the named realization laws;
rational composition naturality extends the integral equation by tensor-product induction.

Moved the original 35 definitions verbatim to IteratedReturnTransportData and publicly
reexported them, to let lower statements refer to them without an import cycle. No target or definition body changed. The inferred endpoint type of finiteComposition
is now written explicitly (definitionally identical), to avoid expanding its large
presentation-comparison expression during naturality elaboration. The new definition node owns their
attachments. See coord/changes/iterated-return-transport-data-module.md.

## Proved and sorry left

The closed original hole is WeilConjectures.iteratedReturnTransportScalarCalculus
(1 of 1 original holes closed; zero holes remain in the assigned module). Its body is reduced to the three strictly simpler statements listed below; this is a
decomposition, not a claim of a net hole reduction. Holes added (3):

- WeilConjectures.returnScalarSquares — lem-trf-return-scalar-squares.
- WeilConjectures.pointScalarSingleStepCoherence — lem-trf-point-scalar-single-step-coherence.
- WeilConjectures.rationalScalarSingleStepNormalization —
  lem-trf-rational-scalar-single-step-normalization.

Each is a public theorem in a separate new module, with its source and full proof in words.
Edge cases checked in the statements and prose arguments: finite exponent n+1 is positive
also at n=0; return length r+1 starts at one; scalar iteration length zero is identity;
zero objects give zero morphism equalities; identity coefficients reduce to the
multiplication unit; repeated coefficients in a tower reduce to the same unit. The
return-square argument uses only w and does not assume an extra periodicity hypothesis.
The data module has zero holes, and no data are chosen from a new existence theorem.

## No longer needed

The upper proof no longer directly imports Sheaf.Paper.PointAutomorphismTransportScalarExtension;
its one-step comparison is needed in the lower point coherence proof, so that module and its
node remain needed. Original public imports are preserved through the definition module.
The proved canonical finite pullback coordinate comparison is used as a change of
coordinates, with its definition node recorded in the proof dependencies.
No original dependency module is asserted pruned: each remains used by the naturality
argument, the data, or one of the lower coherence statements. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old DAG proof suppressed presentation-conversion glue: the rational point pullback is
identified by a specified equality, and raw rational composition requires tensor induction.
The proof now accounts for these identifications explicitly. The original finite-ring
pullback preservation needed for the finite transport square is available as a proved
argument in IsomorphismDerivedPullback, although its public theorem specializes to
isomorphisms; the private general finite-ring argument is reused here.

The source path in the old node names a historical blueprint snapshot. The current latest
trace-transport unit no longer has that exact local-normalization file. This delivery
implements the assigned six-step local-normalization argument and does not alter a unit
or chapter route. The lower nodes record the existing node proof steps as their sources.

## New nodes

- def-trf-iterated-return-transport-data: ownership of the unchanged definitions.
- lem-trf-return-scalar-squares: Step 3, cancellation of the two scalar-compositor words;
  contains no point naturality or point scalar assertion.
- lem-trf-point-scalar-single-step-coherence: Step 4 and the point unit/tower part of Step 6;
  only the length-one point scalar square, without any induction.
- lem-trf-rational-scalar-single-step-normalization: the length-one rational unit and tower
  equations from Step 6, without the higher iteration laws.

Change record: coord/changes/iterated-return-transport-data-module.md.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
