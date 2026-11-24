# MDA Batch 0 tooling

This directory extends the [MOE snapshot contract](../moe/MOE-CONTRACT.md) and
READY4.2 Kernel instrumentation. It records a complete direct-cost partition
by `(gateway branch, nearest source head, API component)`, including separate
M1 calls/time, and keeps bounded
exact Expr pairs for the largest inclusive comparison subtrees. The selected
subtrees are intentionally nested; their inclusive times must not be added.

## Files

- `lean-v4.35.0-ready4.2-base.patch`: pristine Lean 4.35.0 to READY4.2.
- `lean-v4.35.0-mda-extension.patch`: READY4.2 to MDA, tested on EtaleHom.
- `lean-v4.33.1-ready4.2-base.patch`: pristine Lean 4.33.1 to READY4.2.
- `mda_analyze.py`: READY4.2 label and transition analysis with MDA rows.
- `mda_report.py`: checked section 4.1 and 4.2 tables for one root.
- `MDAFields.lean`, `mda_fields.py`: structure field index/name map.
- `EtaleHom-MDA-validation.md`, `etale-selected.jsonl.gz`: validation tables
  and exact selected pairs. Expand the gzip file with `gzip -dc`.

The tested instrumented binary and scratch build are recorded in the
separate worker handoff. No source case is edited by this tool.

## Run

In a pinned case checkout, set `LEAN_DEFEQ_ANATOMY=trace`,
`LEAN_DEFEQ_MPRWE_EVENTS=<scratch>/events.jsonl`,
`LEAN_DEFEQ_MPRWE_ROOT=<discovered-root>`,
`LEAN_DEFEQ_MPRWE_MAX_EVENTS=200`, `LEAN_DEFEQ_MDA_TOP=12`,
`LEAN_DEFEQ_MDA_SOURCE_PREFIX=<source-namespace>`, and
`LEAN_DEFEQ_MDA_FIELDS=<scratch>/fields.map`. Run the same Lean command used
for the READY4.2 probe with the MDA binary. Then run:

```sh
python3 mda_report.py events.jsonl --root ROOT --case CASE > validation.md
python3 mda_analyze.py events.jsonl --root ROOT > detail.txt
```

The `mda_report.py` assertions require label calls, transition edges, and
group direct times to reconcile with the root coverage. Root IDs are only
stable within one process run; select by call count and declaration context.
