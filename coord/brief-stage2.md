# Standing brief for a stage-2 worker

Written by the lead (rules: decision of the human, 2026-10-11). Your prompt names your group `<G>` and your item; this page says what to deliver. Read `AGENTS.md` §3–5, `roles/worker.md`, `stages/2-statements.md` and `SETUP.md` ("Stages 1 and 2 are open") first, then `coord/delivery-errors.md` section H (stage 2). You write Lean statements and definitions; nothing is proved. Temporary files go into a scratchpad subdirectory named after your item.

## 0. What you read

- The node `dag/nodes/<chapter>/<id>.json`: `statement`, `kind`, `source`, `stmt_deps`, `proof` (statement nodes), `mathlib_searches`.
- Every node in `stmt_deps`, its statement and its `lean` record (`module`, `declaration`) or `mathlib_match`.
- The source module of each recorded declaration: `~/weil-conjectures-slopmaster2/<module path>.lean` (module `A.B.C` is file `A/B/C.lean`; compiled, read-only). Read the declaration and its docstring, not only its name.
- Mathlib: `~/weil-conjectures-slopmaster2/.lake/packages/mathlib/Mathlib/` (read-only).
- The node's source place: for Stacks, `literature/stacks-project/` (`stacks-project/tags/tags` maps a tag to its label).
- The example module `lean/Sheaf/CategoryTheory/CompactObject.lean` (node `def-pc-compact-object`, in git): header, docstrings, namespace as in §3.

## 1. Your item

One DAG node that a target reaches, split in stage 1, with no Lean declaration yet, whose `stmt_deps` all have a recorded `lean` or are Mathlib leaves. You write its module `lean/Sheaf/<Topic>/<Name>.lean`: the definition (definition node) or the statement with `sorry` as its proof (statement node). Nothing else is proved in it.

**One definition per notion.** Before writing, search whether Mathlib or the source repository (`~/weil-conjectures-slopmaster2/WeilConjectures/`) already defines the notion or states the statement: three kinds of search as in stage 1 (`coord/brief-stage1.md` §5: LeanSearch; Loogle or LeanFinder; grep of Mathlib and of `WeilConjectures/`), and the source's names in `dag/lean_names_upstream.json` (`tools/lean_names_upstream.py show`; `grep -rn "<id>" ~/weil-conjectures-slopmaster2/WeilConjectures`). If one exists and says exactly what the node says, record it as the node's `lean` with `"existing": true` and write no file. Likewise, when another node of this project already states your node's statement or defines its notion, record that declaration with `existing: true`, `branch: "sheaf-dag"`, `module: Sheaf.<…>` (no file; the declaration is read from `lean/Sheaf` on the base, nothing is compiled).

Claim with `tools/claim.py next <G> --stage 2` (nearest to Mathlib first).

**You add what is missing (STAGE 2 EXTRA NODES, decision of the human, 2026-10-11 05:55 UTC; `coord/STATE.md`).** You do not abandon for a missing or unusable dependency:

- **(A) A missing notion** (the statement needs a notion that no node, no Mathlib declaration and no source declaration gives): add a NEW DEFINITION NODE in the same delivery, `dag/nodes/<chapter of the item>/<id>.json` with the fields of §5, with its own module (or an `existing: true` record when Mathlib or the source has the notion and no DAG node carries it), and cite it from the item: the item's `stmt_deps` gains its id (the one other field of the item you may change). Search first (three kinds) that the notion is not already a node (`tools/blueprint_refs.py search`, grep of `dag/nodes`), not in Mathlib, not in the source.
- **(B) An unusable dependency** (a node in the item's `stmt_deps` whose recorded declaration or `mathlib_match` does not give the notion as the node states it, e.g. the general notion where the node means a specialization): write, in the same delivery, a module stating the dependency node's notion as the node says it, and set that dependency node's `lean` to its record with a `note` saying why the old record was unusable; nothing else of the dependency node changes (its `mathlib_match` stays).
- **(C) A wrong statement is CORRECTED, not abandoned (STAGE 2 STATEMENT CORRECTION, decision of the human, 2026-10-11; `coord/STATE.md`).** When the item's own statement is wrong or cannot be written (false, ill-typed, ambiguous, or leaving out what is needed to state it: an object not introduced, an action or a structure not specified, a hypothesis the source assumes throughout), correct the node in the delivery and write the Lean for the corrected statement. The correction makes the node say what the SOURCE says (the Stacks tag, the blueprint unit's intent), never something easier. The item may then change in `statement`, and only as far as the correction forces it in `stmt_deps`, `proof` and `proof_deps`; it gains `statement_change` (§5) and the report gets `## Statement corrected` (§6). Find the citers with `grep -rl '"<item>"' dag/nodes`: every node whose `stmt_deps` or `proof_deps` name the item; read each and write one line per citer (does its use of the item still hold?). A citer that breaks is named (`holds: false`), never edited. A correction that would change a UNIT's own statement is written up for `coord/HUMAN.md` and that item alone is still released: `tools/claim.py release <G> <item> "abandon: unit statement: <the precise reason>"`.

## 2. The statement says exactly what the node says

- Hypothesis by hypothesis, clause by clause, with the same objects (`stages/2-statements.md` §3). No hypothesis added or dropped; no weaker conclusion; no stronger one either.
- Write out the hypotheses the source assumes throughout (base field, Noetherian, separated, characteristic …) as binders; the node's statement or its source place says which.
- Check the edge cases before writing: empty index sets, zero objects, the empty scheme, `n = 0`, the characteristic. A universe or a `Type` choice must not exclude a case the node covers (as `I : Type w` in the example covers every set).
- Use the dependency nodes' recorded declarations (import their `lean.module`) and Mathlib's definitions whenever they exist; never a private copy of a notion.
- No hollow definition (`AGENTS.md` §5): a def's data is never `sorry`. A proof a definition needs (a well-definedness, an instance) is a named theorem with `sorry` of its own, in the same module, with its own docstring.
- A statement you find false or untypable: correct the node by (C) of §1, following the source, with `statement_change` and the report section. Never write it weaker, never change the statement silently (H7).
- A statement you only doubt (no counterexample, the source agrees with it): write it as the node says, mark `STATEMENT-DISPUTED: <reason>` in the report.

## 3. Conventions (upstreamable by renaming module paths `Sheaf.X -> WeilConjectures.X`)

- Directory by topic as in `WeilConjectures/`: `AlgebraicGeometry`, `CategoryTheory`, `RingTheory`, `FieldTheory`, `GroupTheory`, `Topology`, …; paper-specific under `Sheaf/Paper/`, targets under `Sheaf/Targets/`. File name: the main declaration in UpperCamelCase.
- Namespace: the one upstream would use, with NO `Sheaf.` prefix (only the module path starts with `Sheaf.`; upstreaming renames module paths, no declaration). Example: `open CategoryTheory CategoryTheory.Limits`, `namespace CategoryTheory`, `def IsCompactObject …`, `end CategoryTheory`. The full name must not already exist in Mathlib or the source repository: check with `mcp__lean-lsp__lean_local_search` (`index: consulted`) and grep of `dag/lean_names_upstream.json`, Mathlib and `WeilConjectures/`; the preflight checks it too. Names follow Mathlib's naming (`IsFoo` for a Prop-valued def, `foo_of_bar` for a theorem).
- Module docstring after the imports: `/-! # <title>` then `Source: <document, place> (blueprint: <node id>)`, and for several declarations a `## Main definitions` / `## Main statements` list as in `AlgebraicGeometry/Curve.lean`.
- Every declaration has a docstring naming the source place and carrying `(blueprint: <node id>)`. A statement's docstring also carries the node's proof in natural language, step by step (its `proof` steps, with the nodes they use), so that stage 3 can take it from there.
- Lines of at most 100 characters. Imports only `Mathlib.*`, `WeilConjectures.*`, `Sheaf.*`; no import the file does not use. Header as in the example module.
- The source's lakefile options hold: `relaxedAutoImplicit = false` (bind every variable, every universe); `warn.sorry = false`.
- Module pullback of O_X-modules = `Scheme.Modules.tensorPullback` (def-pc-module-pullback; adjunction `exists_tensorPullbackAdjunction`), never Mathlib's `Scheme.Modules.pullback`; a node's literal `Modules.pullback`/`g^*` names that node. Invertible = `Scheme.Modules.IsInvertible`, not `SheafOfModules.IsInvertible`. This binds the second reading too.
- "X a scheme over k" is `[X.Over (Spec (.of k))]` with properties as instances on `X ↘ Spec (.of k)` (def-weil-scheme-over-base); explicit `(f : X ⟶ Spec (.of k)) [P f]` only when the node names f, involves base change/several morphisms over the base, or a recorded declaration takes f (`Scheme.Hom.genus`, `f.picZero`, `f.picDegree`, `IsConnectedCurve f`). Both are the same notion: not H4, never convert one acceptable form to the other (STATE line SCHEMES OVER A FIELD). (08:29 UTC, L) Bundled `CategoryTheory.Over (Spec (.of k))` objects (`X Y : Over (Spec k)`, `f : X ⟶ Y`) are also acceptable when the node concerns morphisms between k-schemes or base change of a morphism (as landed K1 181333b23, C1 f5ae2762f, E1 6a5137809; the h_T form of def-pc-base-change).

## 4. Compiling

You have no compiled Lean. Compile on the server:
`ssh <server> 'cd ~/weil-conjectures-sheaf && tools/compile_remote.sh <G> <item>' < <file>.lean`
(120 s limit; prints the errors; compiled against the last green global build plus your group's landed modules). Compile until the file is clean: no error, no warning (fix unused variables). A declaration you can read in `lean/` but that does not compile for you has landed since the last green build: wait, do not write it again. A timeout is a fault of a definition, not of the limit.

## 5. The node records

The delivery changes the item's node file ONLY in the field `lean` (and in `stmt_deps`, only by adding the new definition nodes of (A) or a node that already exists on sheaf-dag with a `lean` record, e.g. a notion another group landed meanwhile that a return asks you to cite: STMT_DEPS MAY GAIN LANDED NODES, `coord/STATE.md`):

```
"lean": {"module": "Sheaf.<Topic>.<Name>", "declaration": "<full name>",
         "declarations": [...] (optional, when several), "file": "lean/Sheaf/<Topic>/<Name>.lean" (absent when existing),
         "statement": "<signature verbatim from the file, from the keyword to := or where>",
         "branch": "sheaf-dag" | "mathlib" | "slopmaster2", "by": "<G>", "date": "<date -u>", "existing": true|false,
         "note": "<free text>" (optional)}
```

`status` stays `split`; keep the JSON layout (`indent=1`, `ensure_ascii=False`, final newline).

**A corrected item (C)** changes also in `statement`, and only as far as the correction forces it in `stmt_deps`, `proof`, `proof_deps`, and gains

```
"statement_change": {"date": "<date -u, YYYY-MM-DD>", "by": "<G> stage 2",
  "old_statement": "<the old TeX, verbatim>",
  "what": "<what was wrong: the counterexample, or what could not be typed and why>",
  "source": {"document": "...", "place": "..."} <the source place the correction follows>,
  "citers": [{"id": "<node>", "holds": true|false, "note": "<one line: does its use of the item still hold>"}, ...],
  "old_stmt_deps": [...], "old_proof": [...], "old_proof_deps": [...]   <each present exactly when that field changed, verbatim from the base>,
  "previous": {...}   <exactly when the node already had a statement_change: the old record, whole>}
```

`citers` names exactly the nodes on `sheaf-dag` whose `stmt_deps` or `proof_deps` contain the item (`grep -rl '"<item>"' dag/nodes`, then keep those). The corrected statement cites every `[id]` it names in `stmt_deps`. Nothing else of the item changes (`status`, `source`, `kind` stay). The preflight checks every key (`tools/node_fields.py check_statement_change`).

**A dependency node of (B)** changes ONLY in `lean`: the record above for its module (`existing: false`, `by` = your group), with `note` required (why the recorded declaration or `mathlib_match` was unusable, what the module states). Its `mathlib_match` and every other field stay.

**A new definition node of (A)** is written whole, with exactly these fields (the preflight checks each):

- `id` = file name, `def-<chapter prefix>-<short-name>`, not existing on `sheaf-dag`; the file in the item's chapter directory;
- `kind`: `"definition"`; `title`; `status`: `"split"`;
- `statement`: self-contained TeX introducing its own objects and citing as `[id]` the definition node of every notion it is built from; `stmt_deps`: exactly the cited ids (existing nodes or other new nodes of the delivery);
- `source`: `{document, place}` (the Stacks tag and label, or the document in `literature/`);
- `proof`: `[]`, `proof_deps`: `[]`, `proof_origin`: `null`; `mathlib_match`: `null`;
- `mathlib_searches`: at least the three kinds (LeanSearch; Loogle or LeanFinder; grep of Mathlib, of the source repository and of `lean/Sheaf`), each `{tool, query, results, date, verdict}`;
- `created`: `{by: "worker", item: <the item>, date, group: <G>}`;
- `blueprint`: `{is: null, from: {node: <python3 tools/blueprint_refs.py ancestor <item>>, place: <the place in that blueprint proof the notion serves>, via: <the item's via with the item in front>}, same_as: [...]}`;
- `lean_audit`: `{"master": {"state": "none"}, "slopmaster2": {"state": "none"}}`; `chapter`, `unit`: the item's;
- `lean`: the record above for its module (`existing: false`), or an existing declaration (`existing: true`, no module); a declaration already landed in `lean/Sheaf` by another node is recorded with `existing: true`, `branch: "sheaf-dag"`, `module: Sheaf.<…>` (§1), also for a dependency node of (B).

No other field (`reviewed`, `reviewed_lean`, notes): the merge sets `reviewed` and `reviewed_lean`. The new node must be cited by the item (its `stmt_deps`), directly or through another new node.

## 6. Delivering

One commit on top of `sheaf-dag` with: the item's module and node file; for each new definition node (A) its node file and its module (none when `existing: true`); for each dependency module (B) the dependency node file and the module; the report `coord/reports/<G>/<item>.md` (for an item with `existing: true` and nothing else, only the node and the report). Every module is the `lean.file` of exactly one of these nodes, and its declarations carry `(blueprint: <that node's id>)`. The report has:

- `## Worker report`: what the module defines or states; for each hypothesis and each clause of the node's statement, the Lean that renders it; the dependency declarations used (module, name); the edge cases checked; the searches for an existing definition (tool, query, result); `STATEMENT-DISPUTED:` or node faults, if any.
- `## Second reading by <G>`: an independent reading by another worker of the group, with the node and the file open, answering above all: does the Lean say exactly what the node says? Name each mismatch found and what changed. It reads the new nodes and dependency modules too.
- `## New nodes` (when there are new nodes): one paragraph per new node, naming its id: its statement, its source, its searches and why it is not an existing node or declaration.
- `## Dependency modules` (when there are dependency modules): one paragraph per dependency node, naming its id: why its record was unusable, what the module states.
- `## Statement corrected` (when the item is corrected, (C)): the old statement, what was wrong, the source place the correction follows, and one line per citer naming its id (holds or not, why): the content of `statement_change`.

Before pushing: `python3 tools/preflight_delivery.py <G> <item> --stage 2` (shape, records, the new nodes' fields, the `statement_change` of a corrected item, docstrings, line width, sorry-only proofs) until it passes; for a corrected item it prints `item corrected: <n> citers, <k> marked holds:false` (n must be the number of citers you found), and a clean compile on the server of each module. A module that imports another module of the same delivery cannot compile on the server before that one has landed (the preflight and the packet print `compile: deferred`; the merge lands the modules in dependency order): compile it as one temporary file, the sibling's body followed by the module's body without the sibling import, under a scratch name (`tools/compile_remote.sh <G> <item>-check`). Push to `deliver/<G>/<item>` as in stage 1 (`coord/delivery-errors.md` A1: one commit, based on `sheaf-dag`, never on another delivery). The lead's reviewer checks the statements against the nodes, reads each new node against its source, compiles and lands the modules with `tools/land.sh`; returns go to `coord/returns/<G>.md`, and are repaired point by point (section G of that file).

merge_delivery.py, land.sh and landing.py take coord/.merge.lock themselves and are NEVER wrapped in `flock`; `flock coord/.merge.lock -c …` is only for a plain git add/commit.
