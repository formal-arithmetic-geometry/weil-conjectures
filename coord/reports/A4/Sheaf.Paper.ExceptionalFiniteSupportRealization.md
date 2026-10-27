## What changed

Restored `Sheaf.Paper.ExceptionalFiniteSupportRealization` from its quarantined source and
added the local instance priorities for `strictEtaleLevelDerived` and
`strictEtaleSystemDerived`. These priorities make the derived-category instances used by
`integralExceptionalEtaleRealization.mapDerivedCategory` agree with the strict etale level
functors in the support-realization declarations. The module now compiles cleanly.

## Proved and sorry left

Closed the assigned repair for all nine declarations in the module:
`integralExceptionalEtaleOpen_existsUnique`, `integralExceptionalEtaleOpen`,
`IsIntegralExceptionalEtaleDerivedOpen`, `integralExceptionalEtaleDerivedOpen_existsUnique`,
`integralExceptionalEtaleDerivedOpen`, `integralExceptionalEtaleSupportComparison`,
`IsIntegralExceptionalEtaleRightAdjoint`, `integralExceptionalEtaleRightAdjoint_existsUnique`,
and `integralExceptionalEtaleRightAdjoint`.

No `sorry` remains in this module. Holes closed: 0 theorem sorries; the repair addresses the
module's build failure. Holes added: 0. No definition contains a `sorry`.

## No longer needed

None. No imports, nodes, or proof dependencies were removed.

## Where the brief, the DAG or earlier work was wrong

The quarantined source omitted the local derived-category instance priorities that are
required by the current `ExceptionalFiniteRealization` interface. Consequently Lean inferred
a different abelian-category instance and rejected each composition involving
`mapDerivedCategory`; later declarations were then reported as unknown. Adding the local
instance priorities repairs that interface mismatch without changing any declaration
statement or definition.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalFiniteSupportRealization": "d1c32f506463b770c8b2b08dcefad084d2734a3d"}, "results": {}, "time": "2026-10-28T06:23:38+0800", "transitive": 0, "version": 1}
```

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
