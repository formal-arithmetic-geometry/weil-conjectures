## What changed

Proved `properOpenLambdaReductionSquare` by transporting the ordinary proper/open
lambda square across the recursive completion maps and cancelling the source
completion isomorphism. Added three self-contained intermediate modules:
`ProperOpenLambdaOrdinarySquare`, `ProperOpenLambdaCompletionTransport`, and
`ProperOpenLambdaCompletionIso`.

## Proved and sorry left

The item theorem `properOpenLambdaReductionSquare` is proved. Three strictly
smaller intermediate theorems remain as named obligations:

- `properOpenLambdaOrdinarySquare`, node `lem-sf-proper-open-lambda-ordinary-square`;
- `properOpenLambdaCompletionTransport`, node `lem-sf-proper-open-lambda-completion-transport`;
- `properOpenLambdaCompletionIso`, node `lem-sf-proper-open-lambda-completion-isiso`.

No sorry occurs inside a definition.

## No longer needed

The original item proof plan's direct imports for mate-conjugate expansion,
composite-adjunction formulas, and open tensor normalization are not imported
by the delivered item. The proof uses the three split intermediate statements
instead, together with the public operation and reduction interfaces imported
by their modules.

## Where the brief, the DAG or earlier work was wrong

The earlier module was quarantined after an import collision and had no proof
route in Lean. The DAG proof text describes a long factor-by-factor calculation
but did not expose the ordinary square or endpoint completion transport as
Lean declarations; these are now explicit split nodes.

## New nodes

`lem-sf-proper-open-lambda-ordinary-square` is the pre-completion four-factor
ordinary square. `lem-sf-proper-open-lambda-completion-transport` is the recursive
completion-to-ordinary comparison. `lem-sf-proper-open-lambda-completion-isiso`
is endpoint completion invertibility on the short admissible domain.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.ProperOpenLambdaCompletionIso": "2829c260831c134f269dcef841c88b31a984192a", "Sheaf.SixFunctors.ProperOpenLambdaCompletionTransport": "99cd2303ea857270c57478bdca4038e935ed43aa", "Sheaf.SixFunctors.ProperOpenLambdaOrdinarySquare": "a25c0fe62d0ed16df8d97d8c9b7c9e13e72f6b44", "Sheaf.SixFunctors.ProperOpenLambdaReductionSquare": "f322e69491fd3f45c4e9dac73841eeb0b3d2034d"}, "results": {}, "time": "2026-10-28T01:14:10+0800", "transitive": 0, "version": 1}
```

## Second reading by Y9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
