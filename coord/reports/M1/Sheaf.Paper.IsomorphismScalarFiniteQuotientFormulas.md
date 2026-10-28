## What changed

The combined quotient-formula theorem now packages two independently stated component
obligations.  Its Lean proof applies the left and right existence theorems and combines
their witnesses.  The two component modules record the concrete unit-insertion and finite-
projection calculations separately.

## Proved and sorry left

The original `quotient_formulas_exists` hole is decomposed into the strictly smaller
`left_quotient_formula_exists` and `right_quotient_formula_exists` holes.  The combination
proof is complete; no definition contains `sorry`.

## No longer needed

No imported mathematical dependency was removed.  Exploratory scratch modules were
removed before delivery.

## Where the brief, the DAG or earlier work was wrong

The one-step route in the original proof plan treated the generic quotient-chain
construction as if its canonical scalar-extension presentation were definitionally the
selected completed and finite presentations used by this paper.  The source exposes those
compatibilities only through a substantial concrete transport argument.  Splitting the
left and right unit/projection constructions isolates two genuinely independent parts of
that argument; neither component statement is the original conjunction under another name.

## New nodes

- `lem-weil-isomorphism-scalar-finite-left-quotient-formula`, implemented by
  `Sheaf.Paper.IsomorphismScalarFiniteLeftQuotientFormula`.
- `lem-weil-isomorphism-scalar-finite-right-quotient-formula`, implemented by
  `Sheaf.Paper.IsomorphismScalarFiniteRightQuotientFormula`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IsomorphismScalarFiniteLeftQuotientFormula": "75b5ec5dd371852e154e1a6a9491d85b4cebd530", "Sheaf.Paper.IsomorphismScalarFiniteQuotientFormulas": "5d472b18ecab7595a9627d061838d21729270910", "Sheaf.Paper.IsomorphismScalarFiniteRightQuotientFormula": "3a6340de97a328601f05c9b051e68d304cabcac2"}, "results": {}, "time": "2026-10-28T08:17:41+0800", "transitive": 0, "version": 1}
```

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
