## What changed

The item theorem `signed_shift_laws` is now proved by constructing the two fields of
`ShiftLaws`. The representative chain square is supplied by
`PodReindexingShiftChainPart.chain_shift_part_exists`, and the localized derived
square is supplied by `PodReindexingShiftDerivedPart.derived_shift_part`. The item
module imports these two proof-only modules. The two smaller theorem modules each
retain the original hypotheses and state one strictly smaller field obligation;
their proofs are the remaining named obligations for parallel proof work.

## Proved and sorry left

Closed the `signed_shift_laws` sorry (one hole). Added exactly two named split-off
sorries: `chain_shift_part_exists` in node
`lem-pod-reindexing-shift-chain-part`, and `derived_shift_part` in node
`lem-pod-reindexing-shift-derived-part`.

## No longer needed

The item proof does not import or use the former direct proof dependencies
`def-pur-hom-complex`, `lem-pod-reindexing-hom-resolution-model`,
`def-pur-kinjective-complex`, or
`lem-weil-pbc-ringed-internal-hom-exact-restriction`; their modules and nodes are
therefore no longer needed by this item's proof route. The required presentation
definitions remain available through `PodReindexingCoherenceData`.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan bundled the representative chain construction and the
derived localization argument into one theorem while listing lower declarations
that do not expose a finished public signed-shift construction. The route is valid
after splitting those two independent `ShiftLaws` fields into the two strictly
smaller obligations recorded below.

## New nodes

`lem-pod-reindexing-shift-chain-part` records existence of chain-shift
presentations together with only the representative chain square. Its Lean
statement is in `Sheaf.Paper.PodReindexingShiftChainPart`.

`lem-pod-reindexing-shift-derived-part` records only the derived localization
square for the displayed comparison. Its Lean statement is in
`Sheaf.Paper.PodReindexingShiftDerivedPart`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingShiftChainPart": "72f0e5e3afd72dfef8d93c33f7638118e48bc648", "Sheaf.Paper.PodReindexingShiftDerivedPart": "7ca596e6ce6f366afa984f2233947dffc6e1d16c", "Sheaf.Paper.PodReindexingSignedShifts": "ef8d3bb7d9fcbdaf0a5d070cbfdc56a8341000c2"}, "results": {}, "time": "2026-10-28T07:08:31+0800", "transitive": 0, "version": 1}
```

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
