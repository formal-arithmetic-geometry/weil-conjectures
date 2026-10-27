## What changed

Replaced the hole in `diagonalUniformizer_traceChernDegree` by a proof from a
trace-independent comparison of Chern arrows. The existing statement and both
public imports are unchanged. The added proof imports supply Chern normalization,
twisted-splitting components, and degree-zero faithfulness.

The proof first lifts the system Chern adjunct to completed coefficients. It
proves the Chern/trace identity in the entire system category from the existing
positive twisted-splitting component, then transports that identity to completed
coefficients using the lift and trace normalizations and degree-zero faithfulness.

The formal coefficient calculation is proved as `fourStepChernDegree` for four
abstract coefficient functors and eight endpoint maps. It composes their trace
squares, substitutes the Chern comparison, and cancels the composite unit
isomorphism. `ChernCoefficientDiagram.traceDegree` supplies these functors and
maps over abstract coefficient rings, from the actual scalar compatibility
records and finite presentation. `UniformizerChernNormalizationData.diagram`
specializes that proved calculation to the supplied uniformizer quotient.
The formal calculation thus does not unfold the quotient-ring construction.

`UniformizerChernNormalizationData` packages the supplied inputs and the proved
completed lift with its original system normalization. Its `ChernNormalized`
predicate states the equality of Chern arrows before composing any trace. The
remaining theorem has no `q_trace` hypothesis and contains neither a realized
trace nor a degree predicate. No coefficient-transport equation or trace-degree
assertion is a field of the data record. Definitions construct all maps explicitly.

Each of the four modules compiled through `lcompile.py` within the per-file limit.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalUniformizer_traceChernDegree`
(node `lem-diagonal-uniformizer-trace-chern-degree`), 1 of 1.

Additional proved theorems:
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_completedChern_lift`
(node `lem-diagonal-completed-chern-lift`), and
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.fourStepChernDegree` and
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.ChernCoefficientDiagram.traceDegree`
(node `def-diagonal-uniformizer-chern-transport`), with no sorry.

New hole:
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalUniformizer_chernNormalization`
(node `lem-diagonal-uniformizer-chern-normalization`), exactly one sorry.
There are no other sorries in the packet. This is a decomposition: one original
hole closed and one strictly smaller Chern-normalization hole added. It is not a
net reduction in the target closure's hole count.

## No longer needed

No existing public import or module is removed. The generic K-injective
derivability argument is proved privately in the new lift module, so it needs no
`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition` import.
The original direct citations to `sk-lem-geo-cartier`, `sk-lem-geo-p1-cohomology`,
and `def-sfb-diagonal-coefficient-quotient-line` are localized to the Chern
normalization node; their mathematics remains needed there. No module is claimed
pruned. The main proof uses the whole-system splitting identity, without trying
to detect equality of arbitrary derived arrows from finite levels.

## Where the brief, the DAG or earlier work was wrong

No statement correction or shared definition repair is required. Existing finite
P1 Kummer naturality results start with finite coefficients; they do not supply
the completed-root-to-uniformizer-quotient comparison. The original plan left
this comparison and formal trace transport together in prose. The latter is now
proved, along with the completed Chern lift and whole-system Chern/trace identity.
The remaining comparison concerns only the positive Chern arrow, independently
of completed trace compatibility; it is a genuine step of the argument, not a
renamed degree equation.

Checked the positive exponent n+1 at n=0, ramified finite quotients using exactly
hA, and the empty scheme. The completed-lift argument uses completeness and
adjunction and includes the empty scheme. The unit's section-class, coefficient
extension, and trace route are retained.

## New nodes

`lem-diagonal-completed-chern-lift`: the explicit system Chern arrow and the
proved existence of its completed lift with the actual sourceMap/unitMap
normalization. Fullness is used in the opposite Hom direction from the trace;
no data is chosen from an undetermined existence assertion.

`def-diagonal-uniformizer-chern-transport`: the explicit four-step Chern comparison
predicate, the proved formal transport theorem, the abstract coefficient-diagram
API and its proved trace calculation, the input-data record, and its specialization
to the actual coefficient maps. The data contains no geometric
comparison assertion; the predicate is defined by the explicit arrow equation.

`lem-diagonal-uniformizer-chern-normalization`: comparison of the completed Chern
arrow with the finite positive Kummer Chern adjunct under the prescribed endpoint
and pushforward maps. It is the sole new hole. Its docstring gives the source,
root and coefficient normalization argument, K-flat boundary calculation, and
adjunction/universal-unit comparison.

No shared interfaces were changed and no change record is needed.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
