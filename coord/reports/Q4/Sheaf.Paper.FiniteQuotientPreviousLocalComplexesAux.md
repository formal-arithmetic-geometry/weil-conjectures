## What changed

`finiteQuotient_previous_local_complexes_chart` now constructs the successor-level
complex by restricting scalars along `Ideal.Quotient.factorPowSucc`. The strict lower
and upper support bounds are transported by the homological-complex restriction lemmas,
and term finiteness follows from the finite quotient datum and
`Module.finite_iff_finite`. The remaining exact slice-homology transport is isolated in
`Sheaf.Paper.FiniteQuotientPreviousLocalComplexesChartHomology` and imported as a proof-only
module.

## Proved and sorry left

The parent declaration `finiteQuotient_previous_local_complexes_chart` is reduced to a
constructive complex together with proved support and finiteness properties; those three
parts are closed. One strictly simpler named obligation remains:

- `AlgebraicGeometry.Scheme.finiteQuotient_previous_local_complexes_chart_homology`
  (`lem-weil-pbc-finite-quotient-previous-local-complexes-chart-homology`) retains one
  `sorry` for transporting the supplied chart comparison to every slice homology object.

The original parent hole is therefore closed by decomposition into the algebraic
construction and this strictly smaller transport statement; one split-off hole remains.

## No longer needed

No declared proof dependency was removed. The proof uses only the quotient datum,
finite perfect model data, finite coefficient local homology data, ringed-site derived
restriction, and the new chart-homology transport node. No coefficient-layer tensor
calculation or residue-model module is needed for this chart step.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan combines the algebraic restriction-of-scalars construction with a
substantial exact slice-homology comparison but supplied no Lean declaration for that
comparison. The comparison is now recorded as a separate, strictly simpler node while
the algebraic part is proved directly.

## New nodes

`lem-weil-pbc-finite-quotient-previous-local-complexes-chart-homology` is stated in
`lean/Sheaf/Paper/FiniteQuotientPreviousLocalComplexesChartHomology.lean`; its DAG record is
in the corresponding `dag/nodes/sec-proper-base-change/` path.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteQuotientPreviousLocalComplexesAux": "6743e61a20945dfac2347156c748aa7f39728e30", "Sheaf.Paper.FiniteQuotientPreviousLocalComplexesChartHomology": "690c7eb78c6f6fa92deec4db264d754b27736f67"}, "results": {}, "time": "2026-10-28T04:30:20+0800", "transitive": 0, "version": 1}
```

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
