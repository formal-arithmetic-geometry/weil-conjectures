## What changed

Kept the local derived-category instance priorities for `strictEtaleLevelDerived` and
`strictEtaleSystemDerived`. Isolated the proper factor of the support comparison in the
new theorem `integralExceptionalEtaleProperDerivedRight_exists`, which provides the
strict-presentation comparison used by `integralExceptionalEtaleSupportComparison`.
The item imports that adapter publicly because its theorem occurs in a public definition
body. The item and adapter compile together.

## Proved and sorry left

The nine declarations already present in the item remain complete:
`integralExceptionalEtaleOpen_existsUnique`, `integralExceptionalEtaleOpen`,
`IsIntegralExceptionalEtaleDerivedOpen`, `integralExceptionalEtaleDerivedOpen_existsUnique`,
`integralExceptionalEtaleDerivedOpen`, `integralExceptionalEtaleSupportComparison`,
`IsIntegralExceptionalEtaleRightAdjoint`, `integralExceptionalEtaleRightAdjoint_existsUnique`,
and `integralExceptionalEtaleRightAdjoint`.

The one remaining `sorry` is the genuine lower-level split theorem
`integralExceptionalEtaleProperDerivedRight_exists` in node
`lem-pur-adic-support-proper-derived-adapter`. Its proof is to transport the published
proper comparison through the equivalence between the semilinear and strict coefficient
presentations, then compose the presentation isomorphisms. Holes closed: 0 of the item;
holes added: 1 split-off theorem. No definition contains a `sorry`.

## No longer needed

None. No imports, nodes, or proof dependencies were removed.

## Where the brief, the DAG or earlier work was wrong

The published `integralExceptionalEtaleDerivedRight` declaration records the proper
comparison using the semilinear coefficient and derived-category instances, while
`S.properDerived.level n` in the strict support record uses the strict
`SheafOfModules.instAbelian` and `strictEtaleLevelDerived` presentations. Local instance
priorities fix the support-side presentation, but cannot change the typeclass data baked
into that upstream declaration. The strict adapter theorem is therefore a necessary
intermediate statement rather than an instance-only application.

## New nodes

`lem-pur-adic-support-proper-derived-adapter` —
`Sheaf.Paper.ExceptionalFiniteSupportProperComparison`.

## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 3 OK, 1 UNCONFIRMED.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalFiniteSupportProperComparison": "49aed1c410d3ec300d86586777a55a2cc38d4adb", "Sheaf.Paper.ExceptionalFiniteSupportRealization": "c31e6cfbc757701b071e09c9abadc60e2c938e72"}, "results": {"Sheaf.Paper.AdicPurityObjects": {"hash": "7ae49c86edc75060fa694bac87576aac3bc3d7be", "status": "OK"}, "Sheaf.Paper.ClopenSystemRealizationData": {"hash": "5b68a62e6bf883c4b420078269a234e6ce5a902f", "status": "UNCONFIRMED"}, "Sheaf.Paper.FiniteExceptionalSiteNormalization": {"hash": "45a4008948aeb8b277eac484c15db3a7a001323f", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralReconstructionInterfaces": {"hash": "dfd7491b122f1402fa3e5e5f1ca4f2b05228ee34", "status": "OK"}}, "seconds": 125, "time": "2026-10-28T07:09:10+0800", "transitive": 0, "version": 1}
```

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
