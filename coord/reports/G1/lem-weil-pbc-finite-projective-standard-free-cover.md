# Stage 1 report: `lem-weil-pbc-finite-projective-standard-free-cover`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-projective-standard-free-cover.json` — existing statement node, now split into the local principal-open step and the finite-cover step; Mathlib verdict remains no exact match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-projective-prime-local-free.json` — new unsplit statement node; Mathlib verdict no exact match, with the finite-presentation localization theorem recorded as a piece.
- `coord/reports/G1/lem-weil-pbc-finite-projective-standard-free-cover.md` — this report.

## Attachments

None.

## WANTED

WANTED: `literature/stacks-project/algebra.tex`, Algebra Lemma Tag 00NX (lemma-finite-projective), implication (3)⇒(7), for the local finite-free standard-open construction. The source file is absent in this checkout; the proof is marked agent-written from the cited Tag 00NX route and the imported statement.

## Corrections and findings

- The statement is unchanged and correctly expresses Tag 00NX (3)⇒(7).
- The proof has two steps: obtain a principal open around every prime on which the finite projective module is finite free, then use the principal-open/unit-ideal criterion and quasi-compactness of `Spec A` to select finitely many opens.
- The first step is isolated as `lem-weil-pbc-finite-projective-prime-local-free`; Mathlib supplies only the component `Module.FinitePresentation.exists_free_localizedModule_powers`, together with projective finite-presentation and free-stalk results.
- The second step uses the existing Mathlib leaf `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`.

## Unfinished

The new local-freeness node remains unsplit and is intentionally queued for a later stage-1 worker. No Lean was written or compiled.

Validation: `python3 tools/check_dag.py` reports 0 cycles and only six pre-existing reachability warnings for unrelated nodes; `python3 tools/review_split.py lem-weil-pbc-finite-projective-standard-free-cover` passes with one new node.

## Review by G1

I checked the parent statement against Algebra Tag 00NX and the cited Definition 00NV. The two proof steps realize the imported implication: local finite freeness at each prime, followed by quasi-compactness of `Spec A` and the unit-ideal criterion. The new node is public, carries the same chapter and unit, introduces its own objects, and records LeanSearch, LeanFinder, Loogle, and grep searches; it is correctly left `unsplit`. The existing Mathlib leaf is cited without duplicating it. No target statement, unit route, or unrelated node was changed. The requested missing `algebra.tex` source is recorded as `WANTED`; the agent-written provenance is therefore appropriate. I accept this delivery.
