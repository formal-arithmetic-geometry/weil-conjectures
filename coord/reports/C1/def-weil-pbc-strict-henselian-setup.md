# Stage 1 delivery: `def-weil-pbc-strict-henselian-setup`

## Files written

- `dag/nodes/sec-proper-base-change/def-weil-pbc-strict-henselian-setup.json` - existing definition node, now `status: split`; no new nodes.
- `coord/reports/C1/def-weil-pbc-strict-henselian-setup.md` - this delivery report.

## Attachments

None. The item has no Lean declaration on either branch. No reusable proof lemma was introduced.

## WANTED

None. This is a definition; its blueprint source is recorded in the node and no proof document is needed.

## What was checked or corrected

The definition statement and its three imported dependencies were checked against the neighboring setup and comparison nodes in `sk-thm-iff`. The setup introduces a strictly henselian local ring, its spectrum and residue-field closed fibre, the projective lines over both bases, an etale sheaf and its inverse image, and the restriction map on global sections. The projective-space construction is recorded as the direct dependency needed for the `P^1` objects. No Lean declaration exists on either audited branch.

LeanSearch, LeanFinder, Loogle, and a read-only grep of the Mathlib source were performed. They found only the ring-theoretic `HenselianLocalRing` primitive and unrelated projective-line declarations; Mathlib has no exact definition bundling this etale-sheaf closed-fibre setup or its restriction map. No source or statement error was found.

## What could not be finished

Nothing remains for this one-level Stage 1 split. No Lean was written or compiled.

## Review by C1

I independently checked that the node is a definition rather than a proposition, so it correctly has no proof steps or proof dependencies. Every concept used by the setup is represented by an existing DAG dependency, the node remains on unit `sk-thm-iff`, and no private helper declaration or reusable proof lemma was created. The Mathlib searches satisfy the three-search rule and justify `mathlib_match: null`. `python3 tools/review_split.py def-weil-pbc-strict-henselian-setup`, `python3 tools/check_dag.py`, and JSON validation pass; the six reachability messages from `check_dag.py` are pre-existing unrelated repository warnings.
