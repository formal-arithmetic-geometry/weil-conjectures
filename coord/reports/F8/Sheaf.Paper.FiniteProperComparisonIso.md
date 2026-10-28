## What changed

Marked `WeilConjectures.PurCompactSupport.finiteProperComparison_isIso` as
`STATEMENT-DISPUTED`. No proof was added because the statement quantifies over an
arbitrary `Change R S` while its stated finite-mate conclusion requires a
finite-free coefficient extension.

## Proved and sorry left

No holes were closed. The existing hole
`WeilConjectures.PurCompactSupport.finiteProperComparison_isIso` remains, attached
to node `lem-pur-compact-support-finite-proper-comparison-iso`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The node title says “finite coefficient change”, but the Lean `Change` structure
contains only ring maps and inverse-image compatibility. It does not assert finite
freeness (or any equivalent basis decomposition). The available theorem
`properComparison_isIso_of_finiteFree` therefore cannot be applied. In general,
the mate of an isomorphism between right-adjoint restriction/direct-image
functors need not be an isomorphism; finite freeness is the missing condition.
The parent call in `IntegralCompactSupportCoefficientComparison` likewise supplies
no such witness.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteProperComparisonIso": "77948319e5f91a47420a4a3add1eb3f6759ec06e"}, "results": {}, "time": "2026-10-28T07:58:42+0800", "transitive": 0, "version": 1}
```

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
