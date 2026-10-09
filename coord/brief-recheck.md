# Brief: re-check of the Mathlib searches with the Lean search tools (2026-10-09, evening)

Written by the lead, for the re-check decided by the human (SETUP.md, "Re-check of the Mathlib searches"). Read `AGENTS.md`, `SETUP.md` ("The machine", "The three levels", "The target"), `stages/1-dag.md` §2 (the Mathlib-leaf criterion and the search rule) and `coord/brief-stage1.md` §5 (the three kinds of search and how to record them) first. No Lean is written and nothing is built: use the lean-lsp server for searching and reading only (`lean_leansearch`, `lean_loogle`, `lean_leanfinder`, `lean_local_search`, `lean_declaration_file`, `lean_hover_info`), never `lean_build`, `lean_run_code`, `lean_multi_attempt`, `lean_verify`, and never open or change a file of the two source checkouts. Mathlib is `~/weil-conjectures-slopmaster2/.lake/packages/mathlib/Mathlib/` (read only); `rg` is installed.

## Your list

Your prompt names a file `coord/recheck-<X>.tsv`: one node per line (id, file, status, whether it is a Mathlib leaf, whether it was created today, whether it is reviewed, its unit). These nodes were searched by grep only, before the tools existed. You touch only the files of your list and nothing else: not another list's nodes, not the unit records, not `coord/`.

## For each node

1. Read the node: statement, dependencies, proof steps if any, `mathlib_searches`, `mathlib_match`.
2. Search again, with the three kinds of search of `coord/brief-stage1.md` §5 (LeanSearch; Loogle or LeanFinder; grep), for the node itself and, for a split node, for each step that could be one Mathlib lemma and each notion the node names that has no node of its own. Append every query to `mathlib_searches` with `"tool"`, `"query"`, `"results"`, `"date": "2026-10-09"`, `"verdict"`; keep the old entries.
3. Decide again against the leaf criterion of `stages/1-dag.md` §2: Mathlib states the same thing for the same kind of object, or a generalization that specializes in one line, including a few Mathlib lemmas applied one per clause; not when the agreement with Mathlib's definition is itself a theorem. Before calling a candidate a match, read its type and docstring with `lean_hover_info` or `lean_declaration_file` (or `sed -n` on the file) and compare hypothesis by hypothesis with the node's statement; write the comparison into `mathlib_match.how`.
4. For an existing leaf (`status` `mathlib`): confirm the recorded declaration exists in this Mathlib (`lean_local_search` or grep; the recorded `file` must exist under `Mathlib/`) and says what the node says. If it exists and matches, add one search entry with verdict `confirmed`. If it is close but not the statement, either replace the match by the right declaration (say so in `how`) or withdraw the leaf: set `status` to `unsplit`, keep the old match under `mathlib_match_withdrawn` with the reason, set `mathlib_match` to null, and remove the node's `reviewed` field (the lead re-reviews).
5. For a split node whose statement, or a whole step, turns out to be in Mathlib: do not rewrite the proof. Report it (which step, which declaration, how it matches), and if the node itself is a leaf, set `status` to `mathlib` with the match, keep the proof as it is, and remove `reviewed` (the lead re-reviews). Where a step's content is a Mathlib lemma that no node carries, you may create a Mathlib leaf node for it (the rules for new nodes of `coord/brief-stage1.md` §3, with the three searches) and add it to that step's `uses` and to `proof_deps`; say so in the report.
6. For an unsplit node created today: the search is the whole job; if it is a leaf, set `status` `mathlib` with the match.

Write each node file in one write (python3 json, `indent=1`, `ensure_ascii=False`, trailing newline), only the fields named here. Run `python3 tools/check_dag.py` from the project root at the end and fix what it reports about your files.

## Report

In this order: (1) nodes re-checked, as a count and the list of ids with one of `unchanged | leaf confirmed | leaf gained | leaf withdrawn | match corrected | step now in Mathlib | new leaf node created`; (2) for each change: the node, the declaration, the comparison of hypotheses and conclusion, and what you changed in the file; (3) candidates you rejected and why (one line each); (4) anything you could not decide, for the lead.
