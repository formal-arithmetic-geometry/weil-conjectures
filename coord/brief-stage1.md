# Standing brief for a stage-1 worker

Written by the lead. Your prompt names your item; this file says what to deliver. Read `AGENTS.md`, `roles/worker.md`, `SETUP.md` (its section "Requirements of the human" rules) and `stages/1-dag.md` first. No Lean is written and nothing is built or compiled. Use the Bash tool for reading and writing (cat, grep, python3 for JSON). Temporary scripts go into a subdirectory of the scratchpad named after your item (ten workers share the scratchpad; a script named like another worker's was once overwritten and run on the wrong files).

## 0. The unit and the chapter

Your node carries `chapter` and `unit`. Read `dag/chapters/<chapter>.json` and `dag/units/<unit>.json` (the chapter and unit files of the blueprint, verbatim) before the node. The chapter is fixed. The unit's statement and the steps of its proof are what your node and its neighbours realize: your proof keeps to the route the unit's steps give and to the units the unit cites; definitions and Mathlib leaves from anywhere are notions, not route. If a step of the unit is mathematically wrong, do not route around it silently: write in your node the step, what is wrong with it, and the counterexample or the failing inference, and report it; the lead confirms and reports to the human. Hard, long or not in Mathlib is not wrong. When your item is the unit's key node (its statement), fill the unit record's `realized` fields: `statement` with the node ids that state the unit, and `steps[k]` with the node ids that carry step k, and set `realized_by` to `{"date", "item"}`; the unit file is the only file outside `dag/nodes/` you may write, and only those two fields.

## 1. Your item

One node in `dag/nodes/<chapter>/<id>.json`. Split it by one level (`stages/1-dag.md` §3): afterwards its statement names every notion it is built from, and (for a statement) its proof is complete, in steps, each step naming the nodes it uses or judged elementary. The nodes you point to exist; the new ones you create are stated and searched in Mathlib but not split themselves.

What exists is material, not a finished split: the proof and dependency lists were imported from a blueprint written by agents, and the `import_flags` say what the import found doubtful. Check every step against its source. Read the node's `lean_audit.slopmaster2` and act by its state:

- `none`: no Lean exists. Work from the statement and the literature.
- `sorry_here`: the node's own declaration contains `sorry` (`decls`, with module and lines). Read the Lean statement and docstring in `~/weil-conjectures-slopmaster2/<module path>.lean` (module `A.B.C` is file `A/B/C.lean`); if the Lean statement differs from the node's statement, report it (do not change the statement unless the node's statement is wrong against its source; say so).
- `rests_on_sorry`: the node's Lean exists without `sorry`, but uses declarations that have one: the `open` list. Each entry with `nodes: []` is a statement the Lean split off and the DAG lacks. For each such declaration, read its Lean statement and docstring at the module and lines given, then either (a) find the existing node that states exactly it and report the attachment (`<declaration> belongs to <node id>`; you do not edit that node), or (b) create a node for it (§3) with `lean_audit.slopmaster2` = `{"state": "sorry_here", "decls": [that entry]}`, and make your item's proof use it in the step where that argument occurs. An `open` entry that already has a node is attached: point to that node where your proof uses it.
- `closed_part`: some named declarations exist and are closed, some names are missing. Treat as `none` for the missing part; say in the report which part the existing Lean covers.

Read also the slopmaster2 blueprint text for the node when it differs (`literature/blueprint/slopmaster2/`); the node's `source.document` is the master copy.

**Rule (decision of the human, 2026-10-10): A node that a sorry-free declaration of slopmaster2 (the done branch, now at 7d675a26; before 2026-10-12 at 71d63dcf) states exactly is finished and is not split. A worker who finds such a declaration for its item, or for a node it is about to create, attaches it (reports `<declaration> belongs to <node id>`, and for a new node records it in `lean_audit.slopmaster2.decls` with state `closed` left to `tools/lean_status.py`) instead of writing a proof; check the Lean statement against the node statement before attaching, and check for `sorry` with the sorry map. Look for it by the node id (`grep -rn "<id>" ~/weil-conjectures-slopmaster2/WeilConjectures ~/weil-conjectures-slopmaster2/Comparator`, the checkout of slopmaster2; a plain grep, no git), by the names in the node and in `dag/lean_names_upstream.json`, and by a grep of `~/weil-conjectures-slopmaster2/WeilConjectures` for the key words.**

## 2. What to write into your item

- `statement`: keep it unless it is wrong against its source; then correct it and say so in the report. A statement introduces its own objects: if it points at the objects another node constructed ("the map of [def-x]"), that is a statement dependency.
- `stmt_deps`: every node the statement needs. Remove ids the statement does not use; add those it does.
- `proof` (statements only): a list of steps `{"text", "uses": [ids], "elementary": true|false, "source": {"document", "place"}}`. Each step is a complete argument following the source document and place (`stages/1-dag.md` §4). `uses` names every node the step relies on; `elementary` is `true` only for a step that uses nothing beyond what any graduate student writes out in one line (an identity, a rearrangement, an instance of a definition already in `uses`); `null` is not allowed. An argument a step hides (a lemma the source calls standard, obvious, well known, "by the same argument") becomes a node of its own (§3) and the step uses it. **What is NOT a new node** (rule of 2026-10-10 17:10 UTC, from the audit of new nodes): an elementary fact, two or three lines from the cited statements and definitions (a Stacks tag quoted for such a fact included), is a STEP marked `elementary: true` that names the tag, not a node; the preflight accepts it and the reviewer judges whether it really is elementary. Likewise a special case or restatement of an existing node is a citation of that node, and a fact Mathlib states is a Mathlib leaf. Create a node only for a real lemma. Never cite a document as a step: the steps go into the node, the document is the source. Keep `proof_deps` equal to the union of all `uses`.
- `proof_origin`: `{"by": "document", "document": <path under literature/>, "place": <theorem/section/page>}` when the proof follows a document in `literature/`; `{"by": "agent", ...}` when you wrote it (§4). The blueprint itself is agent-written: a proof that follows only the blueprint is `"by": "agent"` with the blueprint file as document.
- `pointers`: leave as is.
- `status`: `"split"` when done. Do not write `reviewed`: the lead does.
- `split_report`: `{"date": "2026-10-09", "item": <your id>, "worker": "stage1", "summary": <one paragraph of what you checked and changed>, "blueprint": <which places of the blueprint node's proof (the blueprint node in your item's `blueprint.is` or `blueprint.from.node`) your steps realize>}`.
- `blueprint` (§7 below): if `from.place` is "unspecified", fill it; search the whole blueprint for your item's statement and write `same_as` (`[]` if none).

Delete nothing else; keep every `blueprint_*` field and `import_flags` untouched (the review reads them). Keep the JSON layout (`json.dump(..., indent=1, ensure_ascii=False)` and a final newline).

## 3. A new node

File `dag/nodes/<chapter of your item>/<id>.json`, id of the form `<def|lem|prop>-<chapter prefix>-<short-name>` like its neighbours, never an existing id (`ls dag/nodes/*/ | grep` it first). Before creating one, search the DAG for a node with the same statement, the same literature place or the same Lean declaration (`grep -rl` on `dag/nodes` for the key words, the tag, the declaration name) and point to it instead if it exists. Fields:

```
id, kind ("definition" | "statement"), title, statement (complete, introducing its own objects),
source {document, place}  (the document in literature/ and the place; for a Lean-split declaration also the module and lines),
stmt_deps [ids], proof [] , proof_deps [], proof_origin null,
mathlib_searches [ {tool, query, results, date, verdict} ... ]  (at least one search; see §5),
mathlib_match null | {"declaration": name, "file": path under Mathlib/, "how": "exact" | "specializes in one line: <how>"},
status "unsplit" | "mathlib",
merged_into null,
created {"by": "worker", "item": <your item id>, "date": "2026-10-09"},
blueprint {"is": null, "from": {"node": <tools/blueprint_refs.py ancestor <your item>>, "place": <the step, clause or sentence of that blueprint node's proof this node serves>, "via": <its via list, see §7>}, "same_as": [<blueprint nodes stating the same in another form>] or []}  (key placed right after "id")
lean_audit {"master": {"state": "none"}, "slopmaster2": {"state": "none"}}  (or sorry_here with decls, §1)
```

Before creating it, search the whole blueprint as well (§7): if a blueprint node states it, cite that node and create nothing.

A Mathlib leaf (`status` `mathlib`) has a `mathlib_match` and no proof. Any other new node is `unsplit` and joins the queue; do not split it.

## 4. The literature

A proof follows a document in `literature/` (`literature/LIST.md` lists what is obtained; `pdftotext` is installed; the Stacks project is `literature/stacks-project/` with `literature/stacks-tags-cited.tsv` and `stacks-project/tags/tags` mapping a tag to its label; EGA and SGA are PDFs, use `pdftotext` on the pages you need). Cite the document and the place for every step. When the document a step needs is not in `literature/`, do not download anything: write in your report `WANTED: <document>, <place>, for <node id>`; then write the proof yourself from what you know, with `proof_origin.by` = `agent`, so the node is marked as written by an agent.

## 5. Mathlib searches

Three kinds of search, each recorded, before a node is declared absent from Mathlib (rule of 2026-10-09, `stages/1-dag.md` §2):

1. **LeanSearch** (natural language): the tool `mcp__lean-lsp__lean_leansearch` (query in words, or a Lean term; `num_results` 5–10).
2. **Loogle or LeanFinder**: `mcp__lean-lsp__lean_loogle` (type pattern or name substring, e.g. `CategoryTheory.ShortComplex.isIso₂_of_shortExact_of_isIso₁₃`, `|- IsIso _ → _`) or `mcp__lean-lsp__lean_leanfinder` (semantic search by mathematical meaning; 10 requests per 30 s).
3. **grep of the Mathlib source**: `~/weil-conjectures-slopmaster2/.lake/packages/mathlib/Mathlib/` (read only): `grep -rn` (or `rg`) for the key words and the likely declaration names, and a look at the file where the notion would live. `mcp__lean-lsp__lean_local_search` (project root `~/weil-conjectures-slopmaster2`) checks that a name exists in Mathlib or in the source repository; an empty result from it is proof of absence only when its answer says `index: consulted`.

Search every new node by name and by concept with all three, and the item itself when its own Lean state is `none`. Record each query as `{"tool": "leansearch" | "loogle" | "leanfinder" | "local_search" | "grep", "query": "<the query, or the pattern and directory>", "results": "<the declarations that came up, with module, or none>", "date": "2026-10-09", "verdict": "<match | no match | generalization: ...>"}` in `mathlib_searches`; a node whose record lacks one of the three kinds is sent back. Mathlib has it when it states the same thing for the same kind of object, or a generalization that specializes in one line; check a candidate by reading its source (`mcp__lean-lsp__lean_declaration_file` or `sed -n` on the file) before recording a match. The lean-lsp server may be used only for searching and reading (`lean_leansearch`, `lean_loogle`, `lean_leanfinder`, `lean_local_search`, `lean_declaration_file`, `lean_hover_info`); never `lean_build`, `lean_run_code`, `lean_multi_attempt`, `lean_verify` or anything that compiles, and never open or change a file of the two source checkouts with it: nothing is built in this stage.

## 6. Delivering

Write your new nodes first and your item last, each file in one write, so that an interruption leaves no citation of a node that does not exist; then run `python3 tools/check_dag.py` and `python3 tools/review_split.py <your item>` from the project root and fix what they report about your files (every id you cite must exist and be unmerged; every step's `uses` must be in `proof_deps`). These two scripts only read (review_split.py reads the committed version with `git show`); apart from them, do not run `git`. Do not edit any file other than your item, the new nodes you created and, for a key node, the `realized` fields of your unit's record; never `coord/`, `literature/`, `tools/`, or another worker's node. End with a report, in this order:

1. files written (item, new nodes with one line each: id, kind, Mathlib verdict);
2. attachments: `<Lean declaration> belongs to <existing node id>` lines;
3. `WANTED:` lines;
4. what was wrong in the node, the blueprint, or the brief (statement errors, steps that were not proofs, dependencies the text cites without using, Lean that states something else);
5. what you could not finish, and why.

## 7. Blueprint references (rule of 2026-10-10, `stages/1-dag.md` §6)

Every node carries `"blueprint": {"is", "from", "same_as"}`: `is` = its own id for a node imported from the blueprint, else null; `from` = for a created node `{"node": <nearest blueprint ancestor through created.item>, "place": <the step, clause or sentence of that blueprint node's proof this node states or makes precise>, "via": [<created nodes in between, nearest first>]}`; `same_as` = blueprint nodes anywhere (all chapters, also outside the reach) stating the same thing in another form, `[]` if the search found none.

1. Before creating a node, search the whole blueprint: `python3 tools/blueprint_refs.py search <key words or tag>` (it reads every node with a blueprint id) and `grep -rl` on `dag/nodes`. If a blueprint node states it, cite it and create nothing.
2. A new node's `from.node` is what `python3 tools/blueprint_refs.py ancestor <your item>` prints; its `via` is the item's own `via` with the item in front when the item is not a blueprint node (`[]` when it is). Write the exact place in the blueprint node's proof text.
3. Your item: fill `from.place` if it says "unspecified", write `same_as`, and add `blueprint` to the `split_report`.
4. `tools/review_split.py` fails without these.


## Tool uses (decision of the human, 2026-10-10 14:08 UTC)

If a step uses the statement of a node of another unit as a generic tool (a black box that the unit's route does not replace; SETUP.md "Tool lemmas and the unit route"), declare it in the item's `split_report.tool_uses`: a list `[{"node": "<id>", "why": "<one line: what the step takes from its statement and why no node of your unit gives it>"}]`. `tools/review_split.py` and `tools/preflight_delivery.py` accept an off-unit citation declared there (the route line becomes "tool use declared"); the maintainer's reviewer judges it, and the merge copies the accepted ones into the node's `tool_uses`, which a delivery never sets itself. A declaration is not a licence to leave the unit's route: a step of the unit's proof is replaced only on an established error.
