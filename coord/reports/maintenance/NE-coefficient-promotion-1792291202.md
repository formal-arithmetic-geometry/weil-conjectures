# NE maintenance: omitted shared stage-1 promotion

The Q115 maintenance run merged the reviewed repair directly with `tools/merge_delivery.py` at `e097176c20`, but never ran the separate shared promotion. The dispatcher queue and claim tool read SHEAF_DAG in the live project; delivery preflight reads the side overlay. Thus the live parent remained unsplit while the side parent was already accepted, causing each NE retry to fail with "the item's node file is unchanged".

The three children were absent in live. Their later Q92/Q93/Q94 reviewed splits consequently failed promotion with one collision each, recorded in local/stage1-batch/collisions.tsv rows 403-405.

Replayed e097176c20, 8df00e1d52, 63211018c2 and 92cad7fe7b through the unchanged tools/nt_land_batch.py promote function, under the live merge lock, producing ec2f20f2cfbc17058154e19f1be489d58951f494 with the required Bin Wu identity. All four records now equal the committed side records. All promotion results had zero collisions. Cleared the obsolete NE claim and Q78 repair handoff, and regenerated the queue and blueprint index.

The current side review_split checks pass for the live parent and all three children. Their dependencies exist and introduce no cycle, and the parent is absent from stage 1. The older live review_split treats the already split children as new unsplit children; use the current side checker against the shared DAG when validating this history. No Lean file, mathematical statement or protected launcher/landing tool changed.

Every changed existing record has a .maint-NE-coefficient-1792291202.bak backup beside it; backups for new records document their prior absence.

Next worker: this parent and all three children have completed stage 1. Do not manufacture a changed delivery or restore the long steps. Later stages follow the ordinary dependency queue. Any manual stage-1 landing must also complete shared promotion; a side MERGED result alone does not mean the authoritative queue has accepted it. Protected landing and dispatcher hardening recommendations are in the local maintenance REPORT.md.
