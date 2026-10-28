## What changed

Marked `finite_exceptional_formula_scalar` as `STATEMENT-DISPUTED` and retained its
existing proof hole. The module and its import are otherwise unchanged.

## Proved and sorry left

No holes were closed. The existing hole
`WeilConjectures.CoefQbarVerdier.finite_exceptional_formula_scalar` remains.
No new declarations or holes were added.

## No longer needed

None. `Sheaf.SixFunctors.CoefQbarFiniteExceptionalCore` remains the required source of
`FiniteExceptionalFormulaCore`.

## Where the brief, the DAG or earlier work was wrong

The scalar conclusion is not determined by the stated core data. The structure
`FiniteExceptionalFormulaCore` contains an independent
`RationalOperations.ExceptionalIdentification` for every `E`; its `normalized` field
only determines `t.comparison E` from the chosen identification at that same stage.
There is no condition relating the choices at two stages.

An exceptional identification can be transported along an automorphism of its dual
formula while preserving its adjunction and the required unit and counit equations.
Changing the identification at one stage and leaving another unchanged changes the
normalized comparisons while leaving the scalar transition maps and duality data fixed.
The asserted equation would then force that automorphism to be the identity. The
constructible coefficient categories admit nontrivial scalar automorphisms, so this is
not a consequence of the current hypotheses.

The intended theorem needs an additional hypothesis tying `t.finite E` and
`t.finite L` by the rational exceptional scalar-mate identity, or a replacement of
`FiniteExceptionalFormulaCore` by the canonical family produced by that identity.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefQbarFiniteExceptionalScalar": "d28e1cf58a5052e7ca04dacc2dfd17fb705b4b8d"}, "results": {}, "time": "2026-10-28T09:51:26+0800", "transitive": 0, "version": 1}
```

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
