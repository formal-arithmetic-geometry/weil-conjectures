# Standing brief for a stage-2 worker

Written by the lead (rules: decision of the human, 2026-10-11). Your prompt names your group `<G>` and your item; this page says what to deliver. Read `AGENTS.md` §3–5, `roles/worker.md`, `stages/2-statements.md` and `SETUP.md` ("Stages 1 and 2 are open") first, then `coord/delivery-errors.md` section H (stage 2). You write Lean statements and definitions; nothing is proved. Temporary files go into a scratchpad subdirectory named after your item.

## 0. What you read

- The node `dag/nodes/<chapter>/<id>.json`: `statement`, `kind`, `source`, `stmt_deps`, `proof` (statement nodes), `mathlib_searches`.
- Every node in `stmt_deps`, its statement and its `lean` record (`module`, `declaration`) or `mathlib_match`.
- The source module of each recorded declaration: `~/weil-conjectures-slopmaster2/<module path>.lean` (module `A.B.C` is file `A/B/C.lean`; compiled, read-only). Read the declaration and its docstring, not only its name.
- Mathlib: `~/weil-conjectures-slopmaster2/.lake/packages/mathlib/Mathlib/` (read-only).
- The node's source place: for Stacks, `literature/stacks-project/` (`stacks-project/tags/tags` maps a tag to its label).
- The example module `lean/.sandbox/L/CompactObject.lean` (node `def-pc-compact-object`); its namespace is as in §3.

## 1. Your item

One DAG node that a target reaches, split in stage 1, with no Lean declaration yet, whose `stmt_deps` all have a recorded `lean` or are Mathlib leaves. You write ONE module `lean/Sheaf/<Topic>/<Name>.lean`: the definition (definition node) or the statement with `sorry` as its proof (statement node). Nothing else is proved in it.

**One definition per notion.** Before writing, search whether Mathlib or the source repository (`~/weil-conjectures-slopmaster2/WeilConjectures/`) already defines the notion or states the statement: three kinds of search as in stage 1 (`coord/brief-stage1.md` §5: LeanSearch; Loogle or LeanFinder; grep of Mathlib and of `WeilConjectures/`), and the source's names in `dag/lean_names_upstream.json` (`tools/lean_names_upstream.py show`; `grep -rn "<id>" ~/weil-conjectures-slopmaster2/WeilConjectures`). If one exists and says exactly what the node says, record it as the node's `lean` with `"existing": true` and write no file.

Claim with `tools/claim.py next <G> --stage 2` (nearest to Mathlib first). If a dependency's record is wrong (the recorded declaration does not exist, or does not say what the dependency node says), release: `tools/claim.py release <G> <item> "abandon: dependency <node>: <what is wrong>"`, and report it.

## 2. The statement says exactly what the node says

- Hypothesis by hypothesis, clause by clause, with the same objects (`stages/2-statements.md` §3). No hypothesis added or dropped; no weaker conclusion; no stronger one either.
- Write out the hypotheses the source assumes throughout (base field, Noetherian, separated, characteristic …) as binders; the node's statement or its source place says which.
- Check the edge cases before writing: empty index sets, zero objects, the empty scheme, `n = 0`, the characteristic. A universe or a `Type` choice must not exclude a case the node covers (as `I : Type w` in the example covers every set).
- Use the dependency nodes' recorded declarations (import their `lean.module`) and Mathlib's definitions whenever they exist; never a private copy of a notion.
- No hollow definition (`AGENTS.md` §5): a def's data is never `sorry`. A proof a definition needs (a well-definedness, an instance) is a named theorem with `sorry` of its own, in the same module, with its own docstring.
- A statement you believe false: write it as the node says, mark `STATEMENT-DISPUTED: <reason, counterexample>` in the report. Never write it weaker.
- If the node's statement is wrong or cannot be typed, do not change the node: report the fault; the lead decides.

## 3. Conventions (upstreamable by renaming module paths `Sheaf.X -> WeilConjectures.X`)

- Directory by topic as in `WeilConjectures/`: `AlgebraicGeometry`, `CategoryTheory`, `RingTheory`, `FieldTheory`, `GroupTheory`, `Topology`, …; paper-specific under `Sheaf/Paper/`, targets under `Sheaf/Targets/`. File name: the main declaration in UpperCamelCase.
- Namespace: the one upstream would use, with NO `Sheaf.` prefix (only the module path starts with `Sheaf.`; upstreaming renames module paths, no declaration). Example: `open CategoryTheory CategoryTheory.Limits`, `namespace CategoryTheory`, `def IsCompactObject …`, `end CategoryTheory`. The full name must not already exist in Mathlib or the source repository: check with `mcp__lean-lsp__lean_local_search` (`index: consulted`) and grep of `dag/lean_names_upstream.json`, Mathlib and `WeilConjectures/`; the preflight checks it too. Names follow Mathlib's naming (`IsFoo` for a Prop-valued def, `foo_of_bar` for a theorem).
- Module docstring after the imports: `/-! # <title>` then `Source: <document, place> (blueprint: <node id>)`, and for several declarations a `## Main definitions` / `## Main statements` list as in `AlgebraicGeometry/Curve.lean`.
- Every declaration has a docstring naming the source place and carrying `(blueprint: <node id>)`. A statement's docstring also carries the node's proof in natural language, step by step (its `proof` steps, with the nodes they use), so that stage 3 can take it from there.
- Lines of at most 100 characters. Imports only `Mathlib.*`, `WeilConjectures.*`, `Sheaf.*`; no import the file does not use. Header as in the example module.
- The source's lakefile options hold: `relaxedAutoImplicit = false` (bind every variable, every universe); `warn.sorry = false`.

## 4. Compiling

You have no compiled Lean. Compile on the server:
`ssh <server> 'cd ~/weil-conjectures-sheaf && tools/compile_remote.sh <G> <item>' < <file>.lean`
(120 s limit; prints the errors; compiled against the last green global build plus your group's landed modules). Compile until the file is clean: no error, no warning (fix unused variables). A declaration you can read in `lean/` but that does not compile for you has landed since the last green build: wait, do not write it again. A timeout is a fault of a definition, not of the limit.

## 5. The node record

The delivery changes the node file ONLY in the field `lean`:

```
"lean": {"module": "Sheaf.<Topic>.<Name>", "declaration": "<full name>",
         "declarations": [...] (optional, when several), "file": "lean/Sheaf/<Topic>/<Name>.lean" (absent when existing),
         "statement": "<signature verbatim from the file, from the keyword to := or where>",
         "branch": "sheaf-dag" | "mathlib" | "slopmaster2", "by": "<G>", "date": "<date -u>", "existing": true|false}
```

Nothing else changes: `status` stays `split`; no new nodes in stage 2; keep the JSON layout (`indent=1`, `ensure_ascii=False`, final newline).

## 6. Delivering

One commit on top of `sheaf-dag` with exactly three files: the module, the node file, the report `coord/reports/<G>/<item>.md` (for `existing: true` only the node and the report). The report has:

- `## Worker report`: what the module defines or states; for each hypothesis and each clause of the node's statement, the Lean that renders it; the dependency declarations used (module, name); the edge cases checked; the searches for an existing definition (tool, query, result); `STATEMENT-DISPUTED:` or node faults, if any.
- `## Second reading by <G>`: an independent reading by another worker of the group, with the node and the file open, answering above all: does the Lean say exactly what the node says? Name each mismatch found and what changed.

Before pushing: `python3 tools/preflight_delivery.py <G> <item> --stage 2` (shape, record, docstrings, line width, sorry-only proofs) until it passes, and a clean compile on the server. Push to `deliver/<G>/<item>` as in stage 1 (`coord/delivery-errors.md` A1: one commit, based on `sheaf-dag`, never on another delivery). The lead's reviewer checks the statement against the node, compiles and lands the file with `tools/land.sh`; returns go to `coord/returns/<G>.md`, and are repaired point by point (section G of that file).
