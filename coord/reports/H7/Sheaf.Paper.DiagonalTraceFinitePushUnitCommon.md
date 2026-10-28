## What changed

Replaced the proof of `diagonalTrace_finitePush_unit_common` without changing its statement.
The ordinary coefficient cone square is proved from normalization at one, generation of
finite constant coefficients by one, and the actual completed ring-limit projections.

The derived argument extends the supplied varying normalization from K-injective
representatives to every complex, evaluates the completed, varying and limit squares on
single objects, and uses the canonical derived adjunction unit. A generic cone calculation
combines these identities. Its application is the proof in the assigned module.

The five new modules separate the ordinary coefficient calculation, the generic categorical
lemmas, and the coefficient adjunction and varying single-object comparisons. Four named
propositions record the exact single-object and map-definition equalities. Their generic proofs unfold them
once, keeping concrete system-category specialization within the compile limit. No existing
dependency interface is changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finitePush_unit_common`.
Original holes closed: 1 of 1; holes added: 0. No `sorry` remains in the delivered Lean files.

These new public theorems and every private helper have complete proofs:

- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_coefficient_cone_push`
- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_full_normalization_of_kInjective`
- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_coefficient_single_adjunct`
- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_varying_single_square`
- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_varying_single_adjunct`

A clean compile of all six delivered modules passed without warnings. The slowest module
was the ordinary coefficient calculation at 34.4 seconds; the assigned module took
21.6 seconds. A temporary audit printed only `propext`, `Classical.choice`, and `Quot.sound`
for the assigned theorem and all five new public theorems. The audit source was removed.
The unchanged direct consumer `Sheaf.Paper.DiagonalTraceFinitePushUnitSeed` also compiled
against the delivered proof in 6.2 seconds; its temporary sandbox copy was removed.

## No longer needed

The assigned node's planned dependency
`lem-sfb-diagonal-trace-exact-cone-projection`
(`Sheaf.Paper.DiagonalTraceCoefficientProjection`) is unused: the ordinary cone square and
common-unit normalizations establish the equality before finite projection. Removed that
edge from this node's proof route. No existing module is withdrawn.

The original public import of `Sheaf.Paper.DiagonalTraceFiniteEvaluation` is preserved.
Every added proof import is used. No source-library declaration or import is changed.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The ordinary coefficient square can be proved directly
from the recorded normalizations. The supplied varying normalization is only recorded
on K-injective complexes, so using it on a coefficient single complex requires an extension
argument. Acyclicity constructs the fully normalized square, and naturality on K-injective
representatives identifies it with the supplied comparison. This extension is proved here.

## New nodes

`lem-sfb-diagonal-trace-coefficient-cone-push` records the ordinary cone square in
`lean/Sheaf/Paper/DiagonalTraceCoefficientConePush.lean`.

`lem-sfb-diagonal-trace-varying-full-normalization` records the generic extension from
K-injective normalization in `lean/Sheaf/Paper/DiagonalTraceSingleNormalization.lean`.
Its supporting definitions `DiagonalSingleSquare`, `DiagonalSingleUnitCompatible`,
`DiagonalFinitePushUnitFormula`, and `DiagonalExactConeFormula` each contain an explicit
equality formula and no missing data.

`lem-sfb-diagonal-trace-coefficient-single-adjunct` records the canonical coefficient
adjunct formula in `lean/Sheaf/Paper/DiagonalTraceCoefficientSingleAdjunct.lean`.

`lem-sfb-diagonal-trace-varying-single-square` records the normalized varying square on a
system object in degree zero in `lean/Sheaf/Paper/DiagonalTraceVaryingSingleSquare.lean`.

`lem-sfb-diagonal-trace-varying-single-adjunct` combines the last two identities in
`lean/Sheaf/Paper/DiagonalTraceVaryingSingleAdjunct.lean`.

`coord/changes/H7-diagonal-trace-common-unit-proof-settings.md` records the file-local
proof settings and its unchanged direct consumer. The only existing module and existing
node edited are the assigned item's own module and node.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.DiagonalTraceCoefficientConePush": "3f450597a61f64b17af869624c45b5b2fec01e6b", "Sheaf.Paper.DiagonalTraceCoefficientSingleAdjunct": "7ecca0263dad0adc9da2db24108b137158ff0cde", "Sheaf.Paper.DiagonalTraceFinitePushUnitCommon": "d56edc5f2c23c09066a0065a617f170851daaf0e", "Sheaf.Paper.DiagonalTraceSingleNormalization": "bf5bf1556608a9ec410facdb008dcc16f529f148", "Sheaf.Paper.DiagonalTraceVaryingSingleAdjunct": "0ec0888db437aadf17f2731fff84cf4e8df38659", "Sheaf.Paper.DiagonalTraceVaryingSingleSquare": "93ae5087221eec2779c2744cca64b5af3ee556db"}, "results": {"Sheaf.Paper.DiagonalTraceFinitePushUnitSeed": {"hash": "141713c36107b03a2bfc155b4e8395329541a928", "status": "OK"}}, "seconds": 203, "time": "2026-10-28T12:39:20+0800", "transitive": 0, "version": 1}
```

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
