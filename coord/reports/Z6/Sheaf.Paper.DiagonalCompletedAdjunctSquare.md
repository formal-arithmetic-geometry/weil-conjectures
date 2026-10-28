## What changed

Proved `completed_adjunct_square` with its original signature. The proof constructs the
canonical completed unit adjunct, identifies its restriction using the existing
`diagonalTrace_finitePush_unit_seed`, and compares it with the normalized pair by full
faithfulness on complete objects. Naturality then gives the required realization square.

Added `completed_ordinary_unit` in `Sheaf.Paper.DiagonalCompletedOrdinaryUnit`, the ordinary unit
calculation used in that argument. Its proof uses the actual finite coefficient projections
to normalize coefficient one, then regular-module extensionality. It introduces no Chern
class, derived comparison, or adjunct-pair hypothesis. All supplementary helpers are proved.

The exact single-complex square is proved privately with independent localization universes;
the existing public single-square lemma fixes these universes equal. The public API of every
existing declaration and all public imports are preserved.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.completed_adjunct_square` (one of one).
Added zero holes and split off zero obligations. No `sorry` remains in either delivered module.
The new public theorem `completed_ordinary_unit` is proved as well.

The proof uses the existing stated finite-push unit seed and the existing completeness
results, as intended in stage 3. These existing obligations were not duplicated.

Validation: `lcompile.py --all` compiled both modules in import order, without warnings or
errors: `DiagonalCompletedOrdinaryUnit` in 48.0 seconds and
`DiagonalCompletedAdjunctSquare` in 45.6 seconds. The original theorem signature was
checked verbatim against the assigned source and is unchanged. Both modules have zero holes.

## No longer needed

None of the original six declared proof dependencies is removed. No existing module or node
is withdrawn. No public import is removed. No finite realization, quotient coefficient
comparison, Kummer comparison, or trace identity is added to this completed-square proof.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original proof plan omitted the explicit canonical
ordinary coefficient-unit calculation; the new proved theorem supplies it. The limit-unit
part is already stated as `diagonalTrace_finitePush_unit_seed`, so a new unit-limit obligation
is unnecessary. Equality of arbitrary derived-system arrows is not inferred from their
finite components: the final equality uses the full limit square and full faithfulness.

The source single-square lemma has one shared localization universe; this realization uses
independent completed and condensed localization universes, so the proof includes the same
single-complex coherence argument with those universes separated.

## New nodes

`lem-diagonal-completed-ordinary-unit`, realized by the proved theorem
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.completed_ordinary_unit` in
`Sheaf.Paper.DiagonalCompletedOrdinaryUnit`. Its statement is only the ordinary unital
coefficient calculation, and is strictly smaller than the assigned derived Chern square.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.DiagonalCompletedAdjunctSquare": "c19e0f39ec4ff357a4655a62190bd84828912415", "Sheaf.Paper.DiagonalCompletedOrdinaryUnit": "23465d58ab10004f5d6813d26f8f5ed62037492c"}, "results": {"Sheaf.Paper.DiagonalUniformizerAdjunctTransport": {"hash": "df41cc3ceaff2fb7b9fa22d1f055037911592030", "status": "OK"}}, "seconds": 165, "time": "2026-10-28T08:27:43+0800", "transitive": 0, "version": 1}
```

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
