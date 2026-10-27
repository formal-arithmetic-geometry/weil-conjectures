# Q17 identity-mate maintenance, 2026-10-23

The stage-1 C5/D1 return for `lem-pod-structure-identity-mate` at
`9da91422902` (coord/returns/Q17.md, 2026-10-22 06:26 UTC) requires dropping
both duplicate new nodes and using one proof step citing the already reviewed
`lem-sf-identification-coefficient-transport`. The old released repair note
still demanded new nodes. `tools/preflight_delivery.py` reads that note and
activated its minimum-new-node check; the retained worker dry-run
`durable-validation-20261023T143437Z.log` failed only on that check (4341
original proof characters, at least 1 new node required, 0 supplied).

The repair note now carries the later C5/D1 instruction: zero new nodes and
one application of the existing result. Its obsolete text is retained in
`superseded_instruction`; the original file is also saved beside it as
`lem-pod-structure-identity-mate.json.maint-Q17-1792766393.bak`.
`state=released`, `stage=1`, `keep_plan=true` and the original release
timestamp are retained: the corrected delivery is still owed and active.
No preflight, dispatcher, review, landing, admission or capacity code changed.
No DAG statement or Lean module changed.

The Q17 sandbox already contains the requested single-step proof and only
the item node. Rebase/package it against a server main containing this repair,
then use the normal stage-1 dry-run and delivery path. Do not recreate the two
duplicate proposals to satisfy the obsolete instruction. The repair still
needs ordinary independent review and landing; this record change does not
mark the mathematical delivery complete.
