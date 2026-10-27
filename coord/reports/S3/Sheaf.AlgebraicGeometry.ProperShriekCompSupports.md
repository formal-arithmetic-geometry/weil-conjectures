## What changed

Proved `AlgebraicGeometry.Etale.properRouteCompIso_refl` by reducing the
specified compositor at reflexive equality to the canonical
`rightDerivedLowerShriekCompIso`. The existing private component simplification
lemma is retained and the public equality-case theorem now uses it directly.
The main transported compatibility theorem remains unchanged.

## Proved and sorry left

Closed `AlgebraicGeometry.Etale.properRouteCompIso_refl` (1 of 2 declarations
with `sorry` in the module). `AlgebraicGeometry.Etale.properShriekComp_comp_forgetSupports`
remains `sorry`; its node is `lem-sf-proper-shriek-compositor-supports`.
No new `sorry` declarations were added.

## No longer needed

None. The module imports and existing proof dependencies remain needed by the
remaining transported compatibility theorem and by the reflexive compositor.

## Where the brief, the DAG or earlier work was wrong

The DAG's reflexive substep was present as a separate node but the public
reflexive theorem still had an unfilled proof even though the module already
contained the complete private reduction `route_refl`. Reusing that reduction
closes the substep without changing its statement.

## New nodes

None.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProperShriekCompSupports": "50366151ca979b34c63da741d031522dde21eb31"}, "results": {}, "time": "2026-10-28T02:48:22+0800", "transitive": 0, "version": 1}
```

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
