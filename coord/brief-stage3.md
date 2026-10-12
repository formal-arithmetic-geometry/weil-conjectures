# Standing brief for a stage-3 worker

In force from the line `STAGE 3 READY` (written by S3-C, 2026-10-12; adjusted to the human's decisions of 2026-10-12: the library is one Lake package, an item may be a module of the source root, no Claude reviewer). Your prompt names your group `<G>` and your item; this page says what to deliver. Read `AGENTS.md` §3–5, `roles/worker.md`, `stages/3-proving-and-pruning.md` and `SETUP.md` (the three levels of the blueprint; "Stages 1 and 2 are open" for the Lean project) first, then `coord/delivery-errors.md` section I (stage 3, to be written from the returns). You write proofs. Temporary files go into a scratchpad subdirectory named after your item.

## 0. What you read

- Your item is a MODULE of the library, `Sheaf.<…>` (file `lean/Sheaf/<…>.lean`) or `WeilConjectures.<…>` (file `lean/WeilConjectures/<…>.lean`, a module adopted from the source repository): a module that `lean/TargetsCheck.lean` reaches and that still contains `sorry` (`coord/queue.md`, stage 3). Read it whole. The library is one Lake package: a module of either root may import a module of the other, as long as no import cycle arises (`python3 tools/import_direction.py may <importing module> <imported module>`).
- The first principle of stage 3: prove from the targets downward and prune. Progress is counted in targets closed, modules proved, modules pruned, and sorries left in the targets' closure (`python3 tools/queue.py summary`).
- The imports of your module are the plan for its proof: it imports the modules of the stated proof dependencies of its node(s) (`stages/2-statements.md` §3, rule 7; the maintainer adds the missing ones after each build). The lemmas stated there are to be used first: before you state a new lemma, read what the imported modules state, and write a new one only for what none of them and nothing else in the library says (`roles/worker.md` §1.3).
- The node(s) whose `lean.module` is your module (`grep -rl '"module": "<your module>"' dag/nodes`): `statement`, `proof` (the steps and the nodes they use), `proof_deps`, `source`, `unit`, `chapter`. The proof in the DAG is a plan (stage 3 §2).
- For every node in `proof_deps`: its statement and its `lean` record (`module`, `declaration`), or its `mathlib_match`. A proof dependency without a Lean declaration means the module waits (the queue holds it back); do not state it yourself here.
- The unit record `dag/units/<unit>.json` (`realized`: which nodes carry the unit's statement and each step) and the unit file `sk-*/_section.md`: the unit's statement and steps stay (stage 3 §2; `SETUP.md` level 2).
- `coord/changes/`: every open or landed change record that names your module or a declaration you use (`roles/lead.md` §2.6). The library's version of a module adapted by another group is the one you work from.
- The source checkout and Mathlib, read-only, as in stage 2 (`~/weil-conjectures-slopmaster2`, its `.lake/packages/mathlib/Mathlib/`). A proof there of the same statement is used, not rewritten.

## 1. Your item

Prove every `sorry` of the module by the shortest route (stage 3 §2): a special case, a Mathlib lemma, a simpler argument, below the unit level. A route that would bypass a unit that the chapter's route passes through is not taken: a node that realizes a unit's statement or a step (`dag/units/<unit>.json` `realized`) is still used where the unit's proof uses it, and its module stays imported.

Claim with `tools/claim.py next <G> --stage 3` (repairs first, then statements marked `STATEMENT-DISPUTED`, then nearest to a target). Claim also every module you must change besides it (§4).

## 2. The proof

- Work in the sandbox; compile single files as often as you need (§5). A declaration you can read in `lean/` that your compile does not know has landed since the last green build: wait, do not write it again (`roles/worker.md` §2.2).
- Every module is a file of Lean's module system, written like the library's: `module` first, `public import …`, then `@[expose] public section` (a file of the source library cannot import any other kind of file; `python3 tools/to_module.py <file>` converts one). An import that only a proof needs is written `import X`, without `public`: no other module sees it, so it changes nothing for them and the delivery stays a proof-only one. `public import X` is for what the statements and definitions need. A `private` helper cannot appear in a public signature or in the body of a public definition.
- The module already imports the modules of its stated proof dependencies; add what else the proof needs. Once the proof compiles, remove every import it did not use (stage 3 §2), name each removed import under `## No longer needed`, and set the node's `proof_deps` to what the proof uses (§6), so that the import is not added again. A module that no target reaches any more is not proved: name it under `## No longer needed`; the maintainer's queue prunes it.
- What you cannot finish is split off into named theorems with `sorry`, each meeting `AGENTS.md` §5: a public `theorem` whose proof is exactly `:= by sorry`, with its source and a complete natural-language proof in its docstring, carrying `(blueprint: <node id>)`, and a DAG node matching it (§3). No `sorry` inside a partial proof, none in a `private` or anonymous declaration, none in a definition (a hollow definition).
- A result the proof needs and the DAG lacks becomes a node, under the rules of stage 1 (§3).
- An idea without a source that would leave `sorry`s goes into the report, not into the library (stage 3 §2).
- Data chosen from an unproved theorem is allowed only when its statement determines the object up to the equality used downstream; an arbitrary witness of mere existence is forbidden: construct the object and state its properties as theorems.
- No `axiom`, no `unsafe`, `extern`, `implemented_by`, `opaque`, no `sorryAx` written out, no `debug.skipKernelTC`. A target is proved when `#print axioms` shows nothing beyond `propext`, `Classical.choice`, `Quot.sound` (`AGENTS.md` §5); the preflight checks every declaration of the files you deliver.
- A file that exceeds the time limit is slow because of a definition it uses: find it and change it (§4); do not split the file or the proof to get under the limit (stage 3 §4).
- Conventions as in stage 2 (`coord/brief-stage2.md` §3): lines of at most 100 characters, imports only `Mathlib.*`, `WeilConjectures.*`, `Sheaf.*`, no auto-bound variables.

## 3. New nodes

A lemma the proof needs that the DAG lacks, and every theorem you leave with `sorry`, is a node: `dag/nodes/<chapter of the item's node>/<id>.json`, absent on `sheaf-dag`, written whole by the rules of stage 1 (`stages/1-dag.md` §3–§6, `coord/brief-stage1.md`): `id`, `kind`, `title`, a self-contained `statement` citing its `stmt_deps`, `source` {document, place}, `proof` in steps {text, uses, elementary} with `proof_deps` their union, `proof_origin`, three kinds of Mathlib search, `status` `split`, `created` {by: worker, item: <your module>, date, group: <G>}, `blueprint` {is: null, from: …}, the item's node's `chapter` and `unit`; and a `lean` record (`existing: false`, `module`, `file`, `declaration`, `statement` verbatim, `branch: "sheaf-dag"`, `by: <G>`, `date`) for the module that states it, which is a new module `lean/Sheaf/<Topic>/<Name>.lean` of your delivery or the item's own module.

## 4. Changing a definition or a statement (stage 3 §3)

When a definition or an intermediate statement turns out wrong or hard to use you may change it:

1. Claim the module and every module that must be adapted. A module another group has claimed stays with that group: change in it only what the adaptation requires, and name it and its group in the record.
2. List the modules that depend on it (`tools/downstream.py <module> --uses <name>`), and check for each that what it states does not become weaker, stronger or different.
3. Write `coord/changes/<name>.md` (§6).
4. Deliver the change with all adapted modules in the same delivery: they land together, as one set.

A target statement never changes (`AGENTS.md` §4). A target whose statement uses the changed definition is reviewed again (`stages/2-statements.md` §4): say so in the record. Of two definitions of one notion keep the better one and make the other an `abbrev` of it. A node whose statement changes gets `statement_change` as in stage 2 (`coord/brief-stage2.md` §5, citers included).

A statement you believe false: mark it `STATEMENT-DISPUTED: <reason>` in the module (a comment at the declaration) and in the report, with a counterexample if you find one; do not prove a weaker one in its place (`roles/worker.md` §2.7). Whoever takes it looks for a counterexample, finds the correct statement and changes it by the steps above.

## 5. Compiling

On the server: `SHEAF_GROUP=<G> tools/lean_file.sh lean/.sandbox/<G>/<item>/<File>.lean`. From another machine: `ssh <server> 'cd ~/weil-conjectures-sheaf && tools/compile_remote.sh <G> <name>' < <file>.lean`, where `<name>` is your module name, with its dots or with every `.` replaced by `_` (60 s; against the last green global build plus your group's landings). Compile until clean: no error, no warning.

## 6. Delivering

One commit on top of `sheaf-dag`, pushed to `deliver/<G>/<module>` (e.g. `deliver/C1/Sheaf.Paper.Foo`, `deliver/C1/WeilConjectures.AlgebraicGeometry.Curve.FieldExtension`), with only:

- the item's module;
- the adapted modules of a change (§4), and the new modules of new nodes (§3), which go under `lean/Sheaf/`;
- the new node files (§3); an existing node changed only in `lean`, `proof`, `proof_deps`, `proof_origin` (the route the Lean proof takes, so that the DAG agrees with the Lean code), and in `statement`/`stmt_deps`/`statement_change` only under §4;
- the change records `coord/changes/<name>.md`, each with `# <declaration>`, then `## Reason`, `## Old` (the old signature or definition, verbatim), `## New` (the new one), `## Users` (a table `| module | group holding it | effect |`, one row per module `tools/downstream.py --uses` lists, and per adapted module), `## Status` (`open`; the merge writes `landed <landing id> <date>`, the lead `closed <build commit>` once the global build has verified the set);
- the report `coord/reports/<G>/<module>.md` (`roles/worker.md` §3), with exactly these sections:
  - `## What changed`: the modules, declarations and imports changed, and why;
  - `## Proved and sorry left`: what is proved, by name; every `sorry` left in the item's module and every one the delivery adds elsewhere, by name, with its node;
  - `## No longer needed`: the imports removed and the nodes and modules the proof no longer needs;
  - `## Where the brief, the DAG or earlier work was wrong`;
  - `## Second reading by <G>`: another worker of the group, with the module and the nodes open: does the proof prove the node's statement unchanged; is every new statement true and exactly as strong as needed; is the unit's route kept;
  - `## New nodes` (when there are new nodes): one paragraph per id; and the path of each change record.

In `## Proved and sorry left`, report the holes closed and the holes added, by declaration name. Closing an upper hole only by adding as many lower ones is a decomposition: it is allowed when the lower statements are true, needed and strictly simpler, and is counted as a decomposition, not as a proof. Closing a hole by changing a holed statement it does not prove, or adding a hole inside a definition, is refused.

Before pushing: `python3 tools/preflight_delivery.py <G> <module> --stage 3` until it passes. It prints the review class of the delivery. `AUTO`: it changes only proofs of your module; a script lands it after the tools' own checks (it compiles, no new `sorry` without its node, no axiom, the statements of existing declarations unchanged). `CODEX: <reasons>`: it changes a statement, a definition, an import other modules see, or adds nodes; an independent Codex reviewer on another machine reads it, and a script executes its verdict (landing or return). Deliveries land in batches and the server does not compile a delivery again: the global build verifies the batch (compile, axioms, `sorry`, 60 s for each file alone), and a delivery it refuses is taken out of the library again and returned with the compiler's message. There is no Claude reviewer in stage 3. Returns go to `coord/returns/<G>.md` and are repaired point by point.

merge_delivery.py, land.sh, land_set.sh and landing.py take coord/.merge.lock themselves and are NEVER wrapped in `flock`.
