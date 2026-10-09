# Stage 1 delivery: `lem-weil-pbc-finite-type-z-g-ring`

## Repair of returned delivery

This delivery was returned because the finite-type-over-G-ring node used an undefined
"essentially finite type" hypothesis and the statements did not carry the exact
Stacks tags. I rebased the original one-commit delivery onto the current
`origin/sheaf-dag` tip and repaired the existing files in place.

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-type-z-g-ring.json` — assigned statement, now `status: split`; proof has two steps and no Lean attachment.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-z-g-ring.json` — new reusable statement node, `status: unsplit`; Mathlib verdict: no match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-type-over-g-ring.json` — new reusable statement node for finite type maps (a finitely generated algebra, defined inline), `status: unsplit`; Mathlib verdict: no match.
- `coord/reports/C1/lem-weil-pbc-finite-type-z-g-ring.md` — this report.

## Attachments

None. The item and both reusable facts have no Lean declaration on either source branch, so no module was added or changed.

## WANTED

None. The Stacks source is identified at More on Algebra Proposition 07PX and Proposition 07PV in the repository's literature records.

## What was checked or corrected

The imported statement was retained and now cites More on Algebra Proposition 07PX (tag 07PX), items (3) and (5), in its statement. Its proof follows 07PX: a finitely generated ring is a finite type algebra over the canonical copy of `Z`, item (3) supplies that `Z` is a G-ring, and item (5), via exact Proposition 07PV (tag 07PV), supplies permanence under finite type extension. The reusable node for 07PV defines "of finite type" inline as a finitely generated algebra (equivalently a quotient of a polynomial algebra), and cites 07PV in its statement. The `Z` node cites exact tag 07PX item (3); its source records the proof's discrete-valuation-ring completion argument and notes 07PS only for 07PX's separate complete-local-ring item. The source's two reusable facts remain separate unsplit nodes and each has LeanSearch, Loogle, and Mathlib-source grep records. No statement, blueprint route, or existing node outside this item was changed.

## What could not be finished

Nothing remains for this one-level Stage 1 split. No Lean was written or compiled.

## Review by C1

I independently checked the repaired statements against `sk-thm-p1` and the Stacks HTML for exact tags 07PX, 07PV, and 07PS. 07PX item (3) explicitly lists `Z` as a G-ring; its proof gives the discrete-valuation-ring completion reason. 07PX item (5) says finite type ring extensions of those rings are G-rings and points to 07PV, whose proposition has exactly the finite type hypothesis. The canonical map `Z -> R` is finite type when finitely many ring generators are chosen, so the two cited facts compose exactly to the conclusion. Both new nodes are reusable proof facts rather than private lemmas, are placed in the item's chapter and unit, and are not duplicates of existing ids. `proof_deps` is exactly the union of the non-elementary step's uses; all cited ids exist and are unmerged. The delivery is based on the current `origin/sheaf-dag`, has one commit, and changes only the assigned node, its two created nodes, and this report. JSON validation and the DAG/review checks were run after the repair; any pre-existing reachability diagnostics are unrelated to this item.
