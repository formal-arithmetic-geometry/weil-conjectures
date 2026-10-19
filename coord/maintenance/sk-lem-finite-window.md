# sk-lem-finite-window: duplicate stage-2 claim retired

Resolved 2026-10-18T07:45:40Z, group Q06, project newtargets-dag.

NR's delivery 6d6b705125 was reviewed PASS and promoted at
2026-10-18T05:27:19Z. Q06's claim was created 29 seconds later, at
05:27:48Z, from a stale stage-2 queue. The former claim.py completion
condition skipped every queued stage-2 item. Server commit
ec0ddc1ae72bf2edebfa2d98e138cfb1d420d401 fixed both claim paths at
05:58:12Z, but the older Q06 claim and return survived.

Six Q06 deliveries merely changed NR's lean.by and module Authors line.
The final head 9bb2c606b301d94a63d9733e2809509b7f2d64d1 was returned with no mathematical defect and an
explicit instruction to retire it. Workers restored NR's accepted files;
preflight then correctly rejected the unchanged node/module and NR
attribution in a Q06 packet. Retrying cannot satisfy that return.

This maintenance removes only Q06's obsolete claim and this item's return
entry. The reviewed head is retained at refs/superseded/Q06/sk-lem-finite-window/9bb2c606b301d94a63d9733e2809509b7f2d64d1; the existing
refs/stage2-returned/Q06/sk-lem-finite-window/9bb2c606b301d94a63d9733e2809509b7f2d64d1 is also retained. Other returns remain intact. This is neither
a new Q06 completion nor an abandonment. Existing .bak files preserve
the claim, return file, deliveries log and ledger before reconciliation.

The accepted node and module were checked byte for byte through the
transaction. Their SHA-256 values are:

- Node: 22433809688664fae687e8d179f7d49bd7ea2ae83cbd10d292d1120f7ed16709
- Module: 8e2c6ed98be74171a63cb5ee6bb91df89a7de5a312e52b3e58d31437427bbee6

Stage 2 is complete. Use Sheaf.Paper.FiniteWindow and
AlgebraicGeometry.ProEtale.finiteWindow / finiteWindow_padicAlgCl.
Preserve NR attribution and reviewed_lean. Further stage-2 work needs a
new explicit defect/repair handoff; the postponed proofs are later work.

Protected launcher follow-up: Group.work in dispatch_all.py should
reconcile already-held completed stage-2 claims and distinguish a
retirement-only return from a mathematical repair before relaunching.
Reconcile using authoritative completion and repair state; do not use
failure counts or introduce dispatch delays/limits. No protected launcher,
review or landing code was changed by this maintenance.
