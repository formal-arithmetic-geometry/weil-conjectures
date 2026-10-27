## What changed

The item keeps its original statement and public import. Its proof now factors
through the explicit coefficient-unit direct-image arrow and composes four arrow
squares. Naturality transports a local derived arrow once the unit square is
known. The two scalar squares use the same scalar-unit lemma, including for the
nonflat quotient. The final calculation identifies the prescribed unit inverses,
shifted line endpoints and finite adjunction exactly. The concrete endpoint
lemma constructs an application of ordinary category associativity from the
arguments already in the goal; this avoids expensive re-elaboration of the
coefficient record, and its proof term is checked by the kernel. The final definitional conversion
likewise supplies the already constructed hypothesis directly to the kernel.

New modules provide the coefficient-unit construction, its proved naturality and
single-object comparison, the scalar-unit calculation, proved scalar-prefix, finite-arrow and generic
assembly modules, and two smaller remaining comparison statements. No existing module other than the item is changed, and no
existing signature, definition, instance, global attribute or public import changes.

Validation: `lcompile.py --all` compiled all eight delivered Lean modules in
import order after removing profiling options. Every file finished within 60
seconds (maximum 56.7 seconds); the item itself took 32.6 seconds. The original
theorem signature is unchanged. The direct importer
`Sheaf.Paper.DiagonalUniformizerChernNormalization` also compiled unchanged against
the delivery (51 seconds). Static checks found exactly the two named holes,
valid node JSON, no missing dependency IDs, and no Lean line over 100 characters.

## Proved and sorry left

Original hole closed in the item:
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalUniformizer_adjunctTransport`.
Its body is a complete combination of the comparison statements. This is a
decomposition, not a completed proof of the original mathematical obligation.

Proved support statements:
`coefficientOrdinaryUnit_underlying`, `singlePushComparison_naturality`,
`singlePushComparison_square`, and
`scalar_unit_push`, `finiteUnitAdjunct_naturality`, and
`scalar_adjunct_transport`, `FiniteRealization.unitIsoDerived_hom`,
`finite_unit_arrow_transport`, and `coefficient_adjunct_transport`, in namespace
`AlgebraicGeometry.ProEtale.DiagonalCoefficients`. The constructions
`coefficientOrdinaryUnit`, `coefficientUnitPush`, `finiteUnitAdjunct`, `finiteAdjunct`, and
`ChernCoefficientDiagram.localAdjunctArrow`,
`ChernCoefficientDiagram.scalarLocalArrow`, and
`ChernCoefficientDiagram.ScalarTransportTo`, and
`FiniteRealization.unitIsoDerived` are explicit and contain no
hole. The ordinary arrow is kept irreducible, with its underlying-map lemma, to
avoid repeatedly reducing the ordinary monoidal-adjunction construction. The private mate,
naturality and composition helpers are proved.

Two holes added, both whole public theorem bodies in separate modules:

- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.completed_adjunct_square`
  (`lem-diagonal-completed-adjunct-square`): only the first completed-realization
  square, before either scalar change or finite realization.
- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.finite_unit_push`
  (`lem-diagonal-finite-unit-push`): only the finite coefficient-unit square,
  without a local Chern arrow, positive line, trace or completed coefficients.

Thus the item has zero remaining holes, and the delivery adds two strictly
smaller holes. Neither repeats the original four-step equation.

## No longer needed

No original import is removed. No module is withdrawn. The new scalar module uses
DiagonalCoefficientScalars directly, instead of the larger Reference import;
the new finite-unit module uses DiagonalCoefficientFiniteRealization directly,
instead of DiagonalFiniteTraceChernCriterion. No proof needs those larger imports.
The item no longer directly needs the planned completion/full-faithfulness
lemmas: `lem-sfb-diagonal-complete-scalar-restriction` and
`lem-sfb-diagonal-completed-line-complete`, nor the direct proof uses of
`def-sfb-diagonal-trace-presentation`, `def-sfb-diagonal-trace-coefficients`,
`def-sfb-diagonal-coefficient-reference`,
`def-sfb-diagonal-coefficient-scalars`, and
`def-sfb-diagonal-coefficient-finite-realization`.
Their relevant uses are recorded on the smaller comparison nodes; none is
claimed globally pruned. The original local-endpoint and finite-comparison nodes
remain directly needed. No blueprint unit or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan's scalar step needs only the coefficient-unit square:
naturality then handles every derived local arrow and every shifted-line map.
Endpoint normalization at a positive line is unnecessary for this step. The
same observation removes all line and Chern data from the finite residual
obligation. The full universal-unit normalization, rather than an unspecified
natural isomorphism, is essential in the proved single-object calculation.

The current queue and build-error records were checked. The original item
compiled against the available dependencies; no currently reproducible import
collision required adapting another module.

The proved scalar prefix, finite-arrow calculation, and final assembly are
separate modules, and all are kept separate from specialization to the concrete uniformizer
coefficients. Named irreducible unit arrows with proved naturality
avoid repeated reduction of large ordinary and derived adjunction constructions.

## New nodes

`def-diagonal-coefficient-unit-push` records the explicit ordinary-adjunction and
universal-derived-unit construction and its proved single-object API.

`lem-diagonal-scalar-adjunct-transport` records the proved scalar prefix, its
local-arrow construction, and the explicit three-square predicate.

`lem-diagonal-finite-unit-arrow-transport` records the proved finite arrow
calculation and its explicit finite derived-unit isomorphism.

`lem-diagonal-coefficient-adjunct-assembly` records the generic assembly and
its explicit local-arrow construction. It has no remaining hole.

`lem-diagonal-scalar-unit-push` records the proved scalar-unit mate calculation.
It uses extension/restriction adjunctions, the ordinary coefficient-unit square,
and the normalized single-object square, without flatness.

`lem-diagonal-completed-adjunct-square` records only the first square of the
original plan. Its statement stops before integral extension and quotient.

`lem-diagonal-finite-unit-push` records only the finite-unit comparison, with the
supplied canonical-derived-unit normalization retained explicitly. It is
independent of the completed Chern arrow and the positive-line endpoints.

All new nodes retain the original blueprint source and unit. The change record
`coord/changes/H4-diagonal-uniformizer-adjunct-transport.md` documents the new APIs
and the local elaboration attributes. The only existing module and node edited
belong to this item.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.DiagonalCoefficientAdjunctAssembly": "bff5aaeb656b8f592197f32b7a4bacd234abaad3", "Sheaf.Paper.DiagonalCoefficientUnitPush": "99b85e1f4fe574f08b5f5b9643041ad481d6e6a3", "Sheaf.Paper.DiagonalCompletedAdjunctSquare": "bd4d50f9a1d2f4e37fc603d72e7d3a54b783d9ec", "Sheaf.Paper.DiagonalFiniteUnitArrowTransport": "94032623b24d7319d6c7735ceffeeb6d969e2b23", "Sheaf.Paper.DiagonalFiniteUnitPush": "4e54433c46977300d0fe070e906e32fed68fa3e8", "Sheaf.Paper.DiagonalScalarAdjunctTransport": "7f0439f7aa9c59b49fb005888546bdfde91cc4e0", "Sheaf.Paper.DiagonalScalarUnitPush": "954f898b1f99a51cd703d5d75a8aa3b5905b13c7", "Sheaf.Paper.DiagonalUniformizerAdjunctTransport": "df41cc3ceaff2fb7b9fa22d1f055037911592030"}, "results": {"Sheaf.Paper.DiagonalUniformizerChernNormalization": {"hash": "74a6da2680308db8816d6b112ebf6f8c04350cb2", "status": "OK"}}, "seconds": 39, "time": "2026-10-28T05:34:42+0800", "transitive": 0, "version": 1}
```

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
