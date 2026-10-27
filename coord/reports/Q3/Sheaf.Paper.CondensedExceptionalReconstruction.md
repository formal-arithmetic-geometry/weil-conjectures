## What changed

Replaced the sole sorry of `Sheaf.Paper.CondensedExceptionalReconstruction` by an
explicit assembly from four strictly partial proof obligations. The assembly proves
invertibility from a representing Hom bijection and naturality by transposition, then
combines these with refinement compatibility and the independent normalized
coefficient-unit and shift obligation. The theorem's statement, universe and hypotheses stay unchanged.

Moved the original data declarations unchanged (updating blueprint ownership tags) to
`Sheaf.Paper.CondensedExceptionalReconstructionData`, publicly reexported by the item.
Added `SystemIdentification` (the Brown identification before condensed invertibility)
and `SystemRecognition` (those identifications with same-degree uniqueness). No original
definition body or signature changes. Change record:
`coord/changes/Q3-condensed-exceptional-data.md`.

The four proof-only imports are `CondensedExceptionalSystemRecognition`,
`CondensedExceptionalCounitRepresentation`, `CondensedExceptionalRealizationProperties`, and
`CondensedExceptionalRefinementCounits`. Their statements refer to actual existing
counits, limits, coefficient inclusions and normalization maps. In the refinement lemma,
both support comparisons are explicitly taken from the same supplied `ComparisonFamily`.

## Proved and sorry left

Closed the body of
`WeilConjectures.CondensedExceptionalReconstruction.condensed_exceptional_reconstruction`.
This is a decomposition, not a proof free of new assumptions: one original hole is closed
and four are added. The item's module and the data module have zero sorry.

Every remaining new hole is listed here (all in namespace
`WeilConjectures.CondensedExceptionalReconstruction`):

- `condensed_exceptional_system_recognition`, node
  `lem-pur-condensed-exceptional-system-recognition`: bounded Brown-system recognition,
  reconstruction/origin units and same-degree system-map recognition.
- `condensed_exceptional_counit_representation`, node
  `lem-pur-condensed-exceptional-counit-representation`: raw extended-counit Hom bijectivity
  and its actual supplied-system naturality square.
- `condensed_exceptional_realization_properties`, node
  `lem-pur-condensed-exceptional-realization-properties`: regular coefficient membership,
  normalized scalar unit and canonical natural shift comparisons.
- `condensed_exceptional_refinement_counits`, node
  `lem-pur-condensed-exceptional-refinement-counits`: sequence counit and specified condensed
  transpose refinement squares for the coherent specified family.

Each has its own module, named public theorem, source, complete proof in words and DAG
node. None asserts the original Family theorem or constructs its exceptional comparisons. All new
sorries are exactly named theorem bodies; there is no hole in data or private helpers.

## No longer needed

Removed the item's direct private imports of
`Sheaf.Paper.FilteredCondensedRepresentingPair`,
`Sheaf.Paper.PurIntegralReductionUniformTor`,
`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`, and
`Sheaf.Paper.CondensedFlatCoefficientCalculus`. These are used by the lower obligations'
plans rather than by the explicit assembly. They remain dependencies through those
obligations and/or existing public data dependencies; no module is withdrawn or claimed
pruned.

All original direct proof dependencies remain mathematically needed below the four
new nodes: uniform reduction, etale Brown adjunction, finite/site comparison, integral
representing pairs, finite scalar extension, filtered condensed representing pairs,
refinement coherence, realization, derived change of rings and flat coefficient calculus.
No blueprint unit statement or proof route is bypassed. No source-library declaration
is removed or altered.

## Where the brief, the DAG or earlier work was wrong

The declarations in the original plan live in canonical quotient/sequence coordinates;
the assigned statement uses supplied strict-system presentations and specified
normalization comparisons. Their interfaces do not identify themselves by a one-line
application. The remaining recognition, raw-counit transport and coefficient-normalization obligations record that
glue explicitly, without inferring general derived-system equality from evaluations.

The first draft of the refinement obligation allowed independent support comparisons.
That would not ensure their relative normalization. Before delivery it was restricted
to the two specified members of the original supplied coherent ComparisonFamily.
No discrepancy in the original theorem statement is asserted.

Edge cases checked in the new statements: empty schemes and zero objects cause no
extra nonvanishing premise; all integer shifts and common degrees are quantified; towers
retain their original n+1 coefficient convention and actual quotient maps; the supplied
theta is retained; no faithfulness of arbitrary derived evaluation is assumed; finite
scalar extension includes ramification; the exact original condensed adjunction is used.

## New nodes

`def-pur-condensed-exceptional-reconstruction-data` owns the unchanged extracted data
and the two intermediate system records. It imports no assembly theorem and makes no
arbitrary existential data choice.

`lem-pur-condensed-exceptional-system-recognition` records parent Steps 1--3 before
passing to condensed coefficients; it has no condensed adjoint in its conclusion.

`lem-pur-condensed-exceptional-counit-representation` records the integral-to-finite-to-
closure Hom argument of Steps 3--5, before transposing its counit.

`lem-pur-condensed-exceptional-realization-properties` records the regular coefficient,
normalized scalar unit and canonical shift part of Step 7. It contains no exceptional
adjoint comparison or compactification data. The parent combines it with the geometric
comparison and refinement branches.

`lem-pur-condensed-exceptional-refinement-counits` records Step 6, including the mate
calculation. This obligation includes transposition of its raw condensed square under the specified
adjunctions; the parent applies it to the constructed compactification comparisons.

The existing node now records precisely the four obligations and the explicit categorical
assembly. Search records include LeanSearch, LeanFinder/Loogle and Mathlib grep, and the
current blueprint was searched for overlapping recognition/coefficient/refinement facts.
The change record is `coord/changes/Q3-condensed-exceptional-data.md`.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
