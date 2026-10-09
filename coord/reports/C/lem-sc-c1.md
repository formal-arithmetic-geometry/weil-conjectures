# Delivery report: `lem-sc-c1`

1. Files written:

- `dag/nodes/sec-proper-base-change/lem-sc-c1.json`: statement node, no new nodes; Mathlib verdict no match after LeanSearch, LeanFinder, and source grep.

2. Attachments:

None.

3. WANTED:

None. The blueprint proof is available in `literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-p1/lem-sc-c1.md`.

4. What was wrong in the node, blueprint, or brief:

The imported node had no stage 1 split, omitted the constant-sheaf statement dependency, left the proof step underspecified, and had no Mathlib searches. I expanded the proof to identify the torsion sheaf and its application of the cohomological-dimension lemma. The statement and blueprint argument are mathematically consistent.

5. What could not be finished, and why:

No new node was needed. The server-side maintainer must perform the final remote delivery merge and reviewed marking.

## Review by C

Checked the server blueprint node, the `sk-thm-p1` unit and chapter records, and all statement and proof dependencies. Confirmed that the proof step uses the constant-sheaf definition, the cohomological-dimension lemma, and the eight-curve assertion definition, with `proof_deps` equal to the union of its uses. Confirmed the three required Mathlib search categories are recorded. `python3 tools/review_split.py lem-sc-c1` passes.
