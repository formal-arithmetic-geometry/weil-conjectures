## What changed

Reworked `Sheaf.Paper.SmoothExchangeScalarCompatibility` imports. Removed the
redundant direct imports of `Sheaf.Paper.TwistedPullbackSquareMaps` and
`Sheaf.Paper.RationalPurityLocalizedFamilyData`; both are already exposed by the
public endpoint and scalar-square imports used by the declarations here. The
existing assembly proof and its interfaces are unchanged. The module now compiles
against the repaired derived-category dependency chain.

## Proved and sorry left

The declaration `smoothExchangeScalarCompatibility` remains proved. The module
still has one existing split-off `sorry`, in `normalizedExchangeData`; it is the
node `lem-pur-smooth-exchange-normalized-data` and is unchanged by this repair.
No new sorries were added.

## No longer needed

The two removed direct imports are no longer needed:
`Sheaf.Paper.TwistedPullbackSquareMaps` and
`Sheaf.Paper.RationalPurityLocalizedFamilyData`. No DAG proof dependency is
pruned; the existing normalized-data split remains required by the parent.

## Where the brief, the DAG or earlier work was wrong

The recorded build failure listed bad imports while their modules were quarantined;
the current restored dependency chain compiles. The normalized-data theorem is
already explicitly documented as a split because the available purity theorem
constructs a particular coefficient system rather than proving normalization for
an arbitrary supplied system. This repair does not alter that statement.

## New nodes

None.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.SmoothExchangeScalarCompatibility": "11737d3617935a7e31d6a57bf6b5a73e7b30f177"}, "results": {}, "time": "2026-10-28T07:27:28+0800", "transitive": 0, "version": 1}
```

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
