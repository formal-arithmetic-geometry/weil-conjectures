## What changed

The item theorem now combines two named strict conjunct theorems:
`integralDualizing_mapping_limit_global` and
`integralDualizing_mapping_limit_hom`.  These are new modules with the exact
mapping-complex and degree-zero conclusions from the two conjuncts of the item.
The parent proof is complete and simply applies both declarations.  The two
new declarations retain the full proof plan in their docstrings and are the
remaining mathematical obligations.

## Proved and sorry left

The original `integralDualizing_mapping_limit` theorem is proved from the two
strict intermediate declarations.  Two sorries were added by decomposition:
`integralDualizing_mapping_limit_global` in node
`lem-coef-integral-dualizing-mapping-limit-global`, and
`integralDualizing_mapping_limit_hom` in node
`lem-coef-integral-dualizing-mapping-limit-hom`.
No definition contains a sorry.

## No longer needed

No imports or existing proof dependencies were pruned.  The Roos model remains
needed for all types in the statement, and the two split modules are imported
only to discharge the parent conjunction.

## Where the brief, the DAG or earlier work was wrong

The existing proof plan expands into a long project-specific mapping-tower
construction.  The repository declarations provide the component theories but
no single theorem that assembles them into the displayed global and degree-zero
conclusions.  I therefore split the two strict conjuncts into independently
named obligations, while keeping the original statement and its hypotheses
unchanged.  The recorded build failure was a stale/missing dependency artifact:
the exact item source and the restored Roos-model import compile cleanly through
`lcompile.py`.

## New nodes

`lem-coef-integral-dualizing-mapping-limit-global` records the global derived
mapping-complex comparison.  `lem-coef-integral-dualizing-mapping-limit-hom`
records the degree-zero Hom equivalence.  Each is strictly one conjunct of the
parent conclusion and has its own module and source proof description.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralDualizingMappingLimit": "9b4f50f6a14b1d4422739e604a1159fdea1d1595", "Sheaf.SixFunctors.IntegralDualizingMappingLimitGlobal": "97728eb4f2006420ac51b8b8801321c179c320e5", "Sheaf.SixFunctors.IntegralDualizingMappingLimitHom": "76de9ba4286c3b07503ce30c2f1fe3478ccfa2ad"}, "results": {}, "time": "2026-10-28T00:49:24+0800", "transitive": 0, "version": 1}
```

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
