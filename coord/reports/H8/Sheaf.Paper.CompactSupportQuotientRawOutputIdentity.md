## What changed

Filled `WeilConjectures.compactSupportQuotient_raw_output_identity` in
`Sheaf.Paper.CompactSupportQuotientRawOutputIdentity`, preserving its statement.
Private proved helpers convert the mapped quotient arrow, coefficient comparison,
and identity restriction component to the existing native presentation. The final
proof applies `compactSupportQuotient_output_identity` at each level. Local
reducibility attributes follow the neighboring raw composition module and keep
conversion checks from expanding the coefficient constructions. Updated the own
DAG node to describe these component conversions.

Validation: the final module compiled cleanly through `lcompile.py` in 5.0 seconds.

## Proved and sorry left

Closed 1 of 1 holes:
`WeilConjectures.compactSupportQuotient_raw_output_identity`
(node `lem-coef-compact-support-quotient-raw-output-identity`).
No holes remain in the item and no holes were added or split off.
All four private helper theorems are proved.

## No longer needed

Removed the explicit `import all Sheaf.Paper.CompactSupportCoefficientPresentation`:
the public imports of `CompactSupportQuotientNative` already provide its API.
The coefficient-presentation node remains used for the proved intrinsic/ambient
functor equality. Removed `lem-coef-compact-support-restriction-identity` from
this node's direct proof dependencies: its normalization is already encapsulated
by the output identity theorem. Its module remains transitively needed by that
theorem. No module is withdrawn or claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is correct. A whole-expression rewrite of the functor
fails because the intervening comparison maps have dependent source and target
objects. Component equalities, including transport of a natural-transformation
component along the object equality, implement the stated plan without changing
any definitions, signatures, or public imports.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CompactSupportQuotientRawOutputIdentity": "fd1dd9b801277972fe8cb3373f7c47a5bb0edd1b"}, "results": {"Sheaf.Paper.CompactSupportQuotientCocycle": {"hash": "d968efa467527c3363d5eea4cc1e0a1110430787", "status": "OK"}}, "seconds": 283, "time": "2026-10-27T23:31:20+0800", "transitive": 0, "version": 1}
```

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
