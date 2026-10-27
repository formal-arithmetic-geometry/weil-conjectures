## What changed

Added `Sheaf.Paper.RefinementProperCounitIsIso` with the two intermediate statements used by the component proof. The component theorem now rewrites through the factorization, installs the isomorphism instance for the refinement pullback compositor, applies the proper-counit substatement, and closes by composition of isomorphisms. The auxiliary module imports the five geometric proof-dependency modules named by the DAG.

## Proved and sorry left

The target `refinementRestriction_component_isIso` is proved. Two strictly simpler geometric statements remain as named split-off theorems in `Sheaf.Paper.RefinementProperCounitIsIso`: `refinementProperCounit_isIso` and `refinementRestriction_factorization`. No sorry occurs inside a definition.

## No longer needed

None. The five geometric dependencies remain attached to the proper-counit substatement.

## Where the brief, the DAG or earlier work was wrong

The original component proof plan omitted a Lean-level factorization statement connecting `refinementRestriction` to `refinementPull` and the pulled proper counit. The delivery records that factorization explicitly and reduces the target to the proper-counit calculation.

## New nodes

`lem-sf-refinement-open-restriction-proper-counit-is-iso` records the clopen proper-counit calculation. `lem-sf-refinement-open-restriction-factorization` records the defining factorization of the specified component. Both declarations are in `lean/Sheaf/Paper/RefinementProperCounitIsIso.lean`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RefinementOpenRestrictionComponentIsIso": "232e5656c54ff849086d1cb59d942ebfdf8cc972", "Sheaf.Paper.RefinementProperCounitIsIso": "1a19570286f9b0cf29b55801bf52c3a3d715698e"}, "results": {"Sheaf.Paper.RefinementOpenRestrictionIsIso": {"hash": "3d4af1304cfd3b24625da66db79b7dc042dd2c57", "status": "OK"}}, "seconds": 13, "time": "2026-10-28T05:39:08+0800", "transitive": 0, "version": 1}
```

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
