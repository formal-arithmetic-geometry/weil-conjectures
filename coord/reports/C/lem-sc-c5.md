# Worker report: `lem-sc-c5`

Files written:

- `dag/nodes/sec-proper-base-change/lem-sc-c5.json`: split the C5 finiteness statement; no new nodes.

Attachments: none.

WANTED: none.

The imported node had no Mathlib search record and was not marked split. I checked the prime-to-characteristic and characteristic-`p` branches against the blueprint proof, recorded LeanSearch, LeanFinder, Loogle, and source grep searches, and retained the existing dependencies. No Lean declaration or hidden split was found.

## Review by C

I reviewed the statement, proof step, dependencies, source location, and recorded searches against the stage 1 DAG rules. The statement and proof follow the unit route through proper-curve cohomology, cohomological dimension, and the Artin-Schreier sequence. The node cites only existing nodes, has no new nodes or Lean attachments, and is marked `split`. `check_dag.py` and `review_split.py` pass for this delivery.
