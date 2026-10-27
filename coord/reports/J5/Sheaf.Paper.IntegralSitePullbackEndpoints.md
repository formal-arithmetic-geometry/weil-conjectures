## What changed

Added two proof-only endpoint modules, one for the integer square and one for the
units square, and imported them into `Sheaf.Paper.IntegralSitePullbackEndpoints`.
The parent theorem now assembles the two component lemmas. The component proofs
remain explicit named split-off statements with documented mate arguments.

## Proved and sorry left

The parent theorem `integral_site_pullback_endpoints` is proved by conjunction
introduction and application of the two component lemmas. The delivery adds the
strictly simpler split-off declarations
`integral_site_pullback_integer_endpoint` and
`integral_site_pullback_units_endpoint`; each remains `sorry` with its own DAG
node because the corresponding chartwise mate calculation is not available in
the current library.

## No longer needed

No existing dependency import was removed. The parent proof uses only the two new
component declarations; the original four proof dependencies remain needed by the
component statements and their documented proof routes.

## Where the brief, the DAG or earlier work was wrong

The original node presented both endpoint mate calculations as one indivisible
proof obligation, while the current library exposes no theorem implementing either
calculation. The conjunction is therefore reduced to two independent endpoint
statements, each strictly smaller than the assigned statement and retaining the
same unit route.

## New nodes

`lem-sp-integral-site-pullback-integer-endpoint` records the integer endpoint
identity and its chartwise constant-section mate proof.

`lem-sp-integral-site-pullback-units-endpoint` records the units endpoint identity,
including the chartwise hypothesis on `a`, and its pullback-of-units mate proof.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralSitePullbackEndpoints": "cd8e24e18454329c58c96bce6cb51627fea378b3", "Sheaf.Paper.IntegralSitePullbackIntegerEndpoint": "257ebf646c7961ae627b8bc075f480edc72cbdad", "Sheaf.Paper.IntegralSitePullbackUnitsEndpoint": "f5deba47cce005dae1f3f4cce17e5042f29af5ed"}, "results": {}, "time": "2026-10-28T03:27:36+0800", "transitive": 0, "version": 1}
```

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
