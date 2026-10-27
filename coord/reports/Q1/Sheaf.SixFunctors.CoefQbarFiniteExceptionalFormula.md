## What changed

Added the strictly smaller `FiniteExceptionalFormulaCore` module and its scalar-compatibility
module. The assigned module now imports the scalar module, obtains core comparison data, and
constructs `FiniteExceptionalFormula` from the core and scalar theorems.

## Proved and sorry left

The assigned `finite_exceptional_formula` theorem is reduced to the two component theorems.
The delivery adds these named split-off sorries:

- `finite_exceptional_formula_core` in `Sheaf.SixFunctors.CoefQbarFiniteExceptionalCore`
  (node `lem-coef-qbar-finite-exceptional-formula-core`);
- `finite_exceptional_formula_scalar` in `Sheaf.SixFunctors.CoefQbarFiniteExceptionalScalar`
  (node `lem-coef-qbar-finite-exceptional-formula-scalar`).

No definition contains a sorry.

## No longer needed

No proof-only imports are unused in the delivered modules. The direct attempted route through
`rationalExceptional_identifications` and an explicit global natural-isomorphism construction
is not imported; the two split modules expose exactly the comparison and scalar obligations
used by the assigned theorem.

## Where the brief, the DAG or earlier work was wrong

The original node compressed the finite comparison, normalization, and scalar square into one
large obligation. The decomposition separates the core comparison data from its scalar square;
each split statement is strictly smaller and the assigned structure is assembled by a real
Lean term. The prior decomposition commit was restored against the current source tree.

## New nodes

`lem-coef-qbar-finite-exceptional-formula-core` records existence of finite comparison data
with normalization, before scalar compatibility.

`lem-coef-qbar-finite-exceptional-formula-scalar` records the scalar square for that core data.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefQbarFiniteExceptionalCore": "724048b4ae623baa9438865b3c724a893af8a6da", "Sheaf.SixFunctors.CoefQbarFiniteExceptionalFormula": "a1e3b69d6893c46fff72dc3d50dcd5d46d7ef81e", "Sheaf.SixFunctors.CoefQbarFiniteExceptionalScalar": "66eb69004e780ee2eeec47a46633baaf4f8363f5"}, "results": {}, "time": "2026-10-28T06:44:25+0800", "transitive": 0, "version": 1}
```

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
