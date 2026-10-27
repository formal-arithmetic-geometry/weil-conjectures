## What changed
Proved `smoothExchangeScalarCompatibility` by obtaining the geometric witness from
`TwistedPullbackScalars.twistedPullbackSquareScalars` and applying the existing typed
`assembleExchange` paste. Added the named `normalizedExchangeData` theorem as the
strictly smaller normalization step required by that paste; its proof remains a
single documented `sorry`. Added the endpoint data modules as public imports because
the new public normalization signature mentions their declarations.

## Proved and sorry left
Closed the original `smoothExchangeScalarCompatibility` hole. One sorry remains,
in `normalizedExchangeData`, which records the normalized endpoint families, canonical
purity identifications, middle comparison, scalar square, and shift square. This is
strictly below the original conclusion and has node
`lem-pur-smooth-exchange-normalized-data`.

## No longer needed
The parent proof no longer treats the endpoint and twisted-square theorems as an
untyped plan: it uses `twistedPullbackSquareScalars` for geometry and
`assembleExchange` for the final conclusion. No imported module was removed.

## Where the brief, the DAG or earlier work was wrong
The original theorem's proof plan required normalization data that was not exposed by
an existing theorem for arbitrary systems. That missing step is now isolated as a
named lower theorem rather than leaving a sorry in the target theorem. The original
`STATEMENT-DISPUTED` comment accurately records why this lower theorem remains open.

## New nodes
`lem-pur-smooth-exchange-normalized-data` records the normalization theorem and its
source proof plan. Its Lean declaration is `normalizedExchangeData` in the item module.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.SmoothExchangeScalarCompatibility": "16a1d704e33e2ff5dfc911308828582d30471344"}, "results": {}, "time": "2026-10-28T04:36:15+0800", "transitive": 0, "version": 1}
```

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
