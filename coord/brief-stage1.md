# Standing brief for a stage-1 worker

Written by the lead. Your prompt names your item; this file says what to deliver. Read `AGENTS.md`, `roles/worker.md`, `SETUP.md` (its section "Requirements of the human" rules) and `stages/1-dag.md` first. No Lean is written and nothing is built or compiled. Use the Bash tool for reading and writing (cat, grep, python3 for JSON).

## 1. Your item

One node in `dag/nodes/<chapter>/<id>.json`. Split it by one level (`stages/1-dag.md` §3): afterwards its statement names every notion it is built from, and (for a statement) its proof is complete, in steps, each step naming the nodes it uses or judged elementary. The nodes you point to exist; the new ones you create are stated and searched in Mathlib but not split themselves.

What exists is material, not a finished split: the proof and dependency lists were imported from a blueprint written by agents, and the `import_flags` say what the import found doubtful. Check every step against its source. Read the node's `lean_audit.slopmaster2` and act by its state:

- `none`: no Lean exists. Work from the statement and the literature.
- `sorry_here`: the node's own declaration contains `sorry` (`decls`, with module and lines). Read the Lean statement and docstring in `~/weil-conjectures-slopmaster2/<module path>.lean` (module `A.B.C` is file `A/B/C.lean`); if the Lean statement differs from the node's statement, report it (do not change the statement unless the node's statement is wrong against its source; say so).
- `rests_on_sorry`: the node's Lean exists without `sorry`, but uses declarations that have one: the `open` list. Each entry with `nodes: []` is a statement the Lean split off and the DAG lacks. For each such declaration, read its Lean statement and docstring at the module and lines given, then either (a) find the existing node that states exactly it and report the attachment (`<declaration> belongs to <node id>`; you do not edit that node), or (b) create a node for it (§3) with `lean_audit.slopmaster2` = `{"state": "sorry_here", "decls": [that entry]}`, and make your item's proof use it in the step where that argument occurs. An `open` entry that already has a node is attached: point to that node where your proof uses it.
- `closed_part`: some named declarations exist and are closed, some names are missing. Treat as `none` for the missing part; say in the report which part the existing Lean covers.

Read also the slopmaster2 blueprint text for the node when it differs (`literature/blueprint/slopmaster2/`); the node's `source.document` is the master copy.

## 2. What to write into your item

- `statement`: keep it unless it is wrong against its source; then correct it and say so in the report. A statement introduces its own objects: if it points at the objects another node constructed ("the map of [def-x]"), that is a statement dependency.
- `stmt_deps`: every node the statement needs. Remove ids the statement does not use; add those it does.
- `proof` (statements only): a list of steps `{"text", "uses": [ids], "elementary": true|false, "source": {"document", "place"}}`. Each step is a complete argument following the source document and place (`stages/1-dag.md` §4). `uses` names every node the step relies on; `elementary` is `true` only for a step that uses nothing beyond what any graduate student writes out in one line (an identity, a rearrangement, an instance of a definition already in `uses`); `null` is not allowed. An argument a step hides (a lemma the source calls standard, obvious, well known, "by the same argument", a Stacks tag used without a node) becomes a node of its own (§3) and the step uses it. Never cite a document as a step: the steps go into the node, the document is the source. Keep `proof_deps` equal to the union of all `uses`.
- `proof_origin`: `{"by": "document", "document": <path under literature/>, "place": <theorem/section/page>}` when the proof follows a document in `literature/`; `{"by": "agent", ...}` when you wrote it (§4). The blueprint itself is agent-written: a proof that follows only the blueprint is `"by": "agent"` with the blueprint file as document.
- `pointers`: leave as is.
- `status`: `"split"` when done. Do not write `reviewed`: the lead does.
- `split_report`: `{"date": "2026-10-09", "item": <your id>, "worker": "stage1", "summary": <one paragraph of what you checked and changed>}`.

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
lean_audit {"master": {"state": "none"}, "slopmaster2": {"state": "none"}}  (or sorry_here with decls, §1)
```

A Mathlib leaf (`status` `mathlib`) has a `mathlib_match` and no proof. Any other new node is `unsplit` and joins the queue; do not split it.

## 4. The literature

A proof follows a document in `literature/` (`literature/LIST.md` lists what is obtained; the Stacks project is `literature/stacks-project/` with `literature/stacks-tags-cited.tsv` and `stacks-project/tags/tags` mapping a tag to its label; EGA and SGA are PDFs, use `pdftotext` on the pages you need). Cite the document and the place for every step. When the document a step needs is not in `literature/`, do not download anything: write in your report `WANTED: <document>, <place>, for <node id>`; then write the proof yourself from what you know, with `proof_origin.by` = `agent`, so the node is marked as written by an agent.

## 5. Mathlib searches

Mathlib is at `~/weil-conjectures-slopmaster2/.lake/packages/mathlib/Mathlib/` (read only). Search every new node by name and by concept: `grep -rn` for the key words and the likely declaration names, and look at the file where the notion would live. Record each search as `{"tool": "grep", "query": "<the pattern and directory>", "results": "<what came up, or none>", "date": "2026-10-09", "verdict": "<match | no match | generalization: ...>"}`. Mathlib has it when it states the same thing for the same kind of object, or a generalization that specializes in one line.

## 6. Delivering

Write your item and your new nodes, then run `python3 tools/check_dag.py` from the project root and fix what it reports about your files (every id you cite must exist and be unmerged; every step's `uses` must be in `proof_deps`). Do not run `git`. Do not edit any file other than your item and the new nodes you created, and never `coord/`, `literature/`, `tools/`, or another worker's node. End with a report, in this order:

1. files written (item, new nodes with one line each: id, kind, Mathlib verdict);
2. attachments: `<Lean declaration> belongs to <existing node id>` lines;
3. `WANTED:` lines;
4. what was wrong in the node, the blueprint, or the brief (statement errors, steps that were not proofs, dependencies the text cites without using, Lean that states something else);
5. what you could not finish, and why.
