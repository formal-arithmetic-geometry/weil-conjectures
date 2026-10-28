## What changed

Added the strict-system compatibility proof assembly. The target theorem now assembles an
objectwise comparison and its naturality equation using `NatIso.ofComponents`. The two
missing mathematical steps were split into named public theorems in
`OpenQuotientScalarSystemsComponents` and `OpenQuotientScalarSystemsNaturality`.

## Proved and sorry left

Proved `openQuotientScalarSystemsCompatibility` by assembling the two split-off statements.
The split-off declarations `openQuotientScalarSystemsComponents` and
`openQuotientScalarSystemsNaturality` retain one `sorry` each.

## No longer needed

No imports or declared dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

The original plan treated the objectwise extension comparison and its naturality as one
step, but the current coefficient-system interfaces expose these as separate obligations.
The delivery records them as two strictly simpler intermediate statements.

## New nodes

- `lem-sf-open-quotient-scalar-system-components`
- `lem-sf-open-quotient-scalar-system-naturality`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.OpenQuotientScalarSystemsCompatibility": "bd2bcc29ef69713da5fbf1f384d8777af29a3056", "Sheaf.SixFunctors.OpenQuotientScalarSystemsComponents": "ffb209436a8ac033c7ef1baaec2cfe67487f0976", "Sheaf.SixFunctors.OpenQuotientScalarSystemsNaturality": "1cd4a76692fb949391392e94fef7f7f4642e6ca9"}, "results": {}, "time": "2026-10-28T10:02:11+0800", "transitive": 0, "version": 1}
```

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
