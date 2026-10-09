# Delivery report: `lem-sc-c2`

1. Files written:

- `dag/nodes/sec-proper-base-change/lem-sc-c2.json`: statement node, no new nodes; Mathlib verdict no match after LeanSearch, LeanFinder, Loogle, and source grep.

2. Attachments:

None.

3. WANTED:

None. The blueprint proof is available in `literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-p1/lem-sc-c2.md` on the server.

4. What was wrong in the node, blueprint, or brief:

The imported node had an empty `mathlib_searches` field and the first working copy recorded the grep as unavailable. I replaced this with actual search results: Mathlib exposes generic sheaf-cohomology infrastructure but no affine-curve etale cohomological-dimension theorem. The blueprint statement and its single proof paragraph are mathematically consistent. The proof uses `thm-sc-affine-cohomology` and `lem-sc-affine-cohomological-dimension`, whose units are outside `sk-thm-p1`; they are recorded as accepted generic tool uses for lead review, as required by the route checker.

5. What could not be finished, and why:

No new node was needed. The server-side maintainer must perform the final remote delivery merge and reviewed marking.

## Review by C

Checked the server blueprint node, the `sk-thm-p1` unit and chapter records, and the node dependencies. Confirmed that the prime-to-characteristic and characteristic-p cases cover every prime `n`, that the proof dependencies equal the step uses, and that the Mathlib searches are recorded in all three required categories. `python3 tools/review_split.py lem-sc-c2` passes.
