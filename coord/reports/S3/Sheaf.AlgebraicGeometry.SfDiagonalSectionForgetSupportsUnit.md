## What changed

Proved `AlgebraicGeometry.Etale.SfP1Transport.diagonalSection_forgetSupports_unit`
in its assigned module, preserving its signature and public imports.
Added private proof imports of `ProperShriekCompSupports`,
`OrdinaryFiniteConstantUnitComp`, `DerivedSingleUnitExact`, and
`WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp`.

The proof applies the existing proper compositor compatibility and ordinary
constant-unit composition theorems. Private proved helpers normalize the constant
unit at the identity using the exact single-object unit comparison and the
factorization equations for derived functors. The two Boolean projections are
then handled uniformly, and naturality transports the normalization through
`constantUnit`. The node's proof and proof dependencies now record this argument.
The complete module compiles in 17.5 seconds through `lcompile.py`; the sole
formatting warning from that compile was removed before delivery. A private
congruence step keeps the canonical proper comparison folded while checking the
ordinary endpoint aliases. All profiler settings and scratch modules were removed.

The current server queue row is a stage-3 proof item with one hole. There is no
current rework row, return entry, or module build-error record for this item.
LeanFinder and Loogle locate the generic adjunction composition-unit lemmas;
local source search finds the more directly applicable existing project results.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.SfP1Transport.diagonalSection_forgetSupports_unit`
(node `lem-sf-diagonal-section-forget-supports-unit`).

Zero holes remain in the item. Zero holes were added or split off. Every private
helper is proved. The proof uses the existing stated proper compositor theorem;
its pre-existing downstream obligations remain with their assigned items.

## No longer needed

None. No original import or planned definition dependency was removed; no module
or node is withdrawn. No new public obligation is introduced.

## Where the brief, the DAG or earlier work was wrong

The original one-step plan omitted the identity normalization needed to match the
concrete ordinary derived identity comparison. This is now proved explicitly.
The existing proper compositor and ordinary constant-unit composition lemmas
supply the other steps, so another split of this obligation is unnecessary.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.SfDiagonalSectionForgetSupportsUnit": "8d0babee015cd384b13ab28f9560409305e65882"}, "results": {"Sheaf.AlgebraicGeometry.SfDiagonalSectionForgetSupports": {"hash": "fc837f993ee310e783948ddde98e1ab428fadf51", "status": "OK"}}, "seconds": 28, "time": "2026-10-28T11:41:01+0800", "transitive": 0, "version": 1}
```

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
