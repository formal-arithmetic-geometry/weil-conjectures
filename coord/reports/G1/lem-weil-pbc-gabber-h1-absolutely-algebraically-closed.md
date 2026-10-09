# Stage 1 report: `lem-weil-pbc-gabber-h1-absolutely-algebraically-closed`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-gabber-h1-absolutely-algebraically-closed.json`: existing 09ZB item, split into torsor identification, finite-etale representation, and trivialization by a global sheaf section.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-gabber-finite-etale-section.json`: new unsplit 09ZA statement node. It carries the exact Stacks hypothesis “X affine integral normal with separably closed function field; Z closed; V -> Z etale with V affine”, searches, and queue metadata only; it has no proof, proof_deps, or tool_uses.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-clopen-open-cover-section.json`: new unsplit public child for the finite clopen partition and gluing argument in 09ZA, flagged `unreachable` until a future 09ZA proof cites it.
- `coord/reports/G1/lem-weil-pbc-gabber-h1-absolutely-algebraically-closed.md`: this report.

## Attachments and WANTED

The parent uses existing `thm-galois-torsor-h1` (03AJ) and `thm-galois-lc-etale` (03RV). The queued 09ZA proof will use existing `lem-exc-etale-algebra-lift` (04D1) and `sbc-lem-etale-over-normal` (09Z9), plus the new clopen-section child. No documents are wanted.

## Findings

The returned-item correction is applied. The 09ZA statement now matches Stacks Tag 09ZA exactly, including the affine hypothesis on `V` rather than an “affine etale morphism” shorthand. The 09ZB final step now explicitly says that `V` represents the torsor as an etale sheaf and that the section `s : Z -> V` is a global sheaf section, whose translation trivializes the torsor.

## Unfinished

The 09ZA statement and its clopen-section child remain `unsplit` and are intentionally queued for later Stage 1 work; the clopen child is currently flagged `unreachable` because the returned-item requirement forbids proof/proof_deps/tool uses on 09ZA. No Lean was written or compiled.

## Verification

`python3 tools/review_split.py lem-weil-pbc-gabber-h1-absolutely-algebraically-closed` and `python3 tools/check_dag.py` are run for this repair; `git diff --check` is clean. The report contains no lead-review section because this is a worker repair delivery.

## Review by G1

I checked each returned point against the repaired files. The 09ZA node is now statement-only while unsplit, with the exact affine `V` hypothesis, complete metadata, and four searches; its clopen helper is kept public and marked unreachable until 09ZA is itself split. The 09ZB proof explicitly identifies `V` as the torsor sheaf and the section as a global sheaf section before trivialization. The repair is based on the current synchronized DAG, preserves the unit route, and passes `review_split.py`, `check_dag.py`, and `git diff --check`. I accept this repair.
