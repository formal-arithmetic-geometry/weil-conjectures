# Reviewer brief: one stage-3 delivery (a proof, whole or in part) of a remote group

Stage 3 proves, from the targets downward, and prunes (stages/3-proving-and-pruning.md; coord/brief-stage3.md; roles/lead.md §3; AGENTS.md §4 and §5: read these in the clone). The delivery is the module of the item with proofs written, possibly new modules lean/Sheaf/<Topic>/<Name>.lean stating what is left (each a public theorem `:= by sorry` with its node), node files, change records, and the report. A delivery that changes only proofs is landed without a reader; this one reached you because it changes more (the reason is in your prompt and in the packet under `Class`).

The delivered files, whole, are in FILESDIR (a mirror of the repository: lean/…, dag/nodes/…, coord/…); the packet holds their diffs against sheaf-dag. Do not compile the delivered files (the human, 2026-10-21): the worker compiled them before delivering, and the global build verifies every landing; a review is a reading of the mathematics and the records, not a second compile. Compile only a file you changed yourself (FIX), once, alone: `python3 /home/ubuntu/weil-launcher/lcompile.py <that file>`. Compare with the version of the library in the clone (`diff`).

Decide by these points, in this order. A failed point you can correct inside the delivery's files you correct yourself (FIX: the whole corrected files, compiled); a failed point you cannot correct that way is a point of your RETURN.

1. **No target statement changed.** The theorems of lean/Challenge.lean keep name, binders, universes, conclusion, byte for byte.
2. **Nothing others see changed by accident.** The signature of every existing declaration is unchanged, and no existing definition's body, unless a change record coord/changes/<name>.md declares it, lists every user, and the adapted modules are in the delivery. A proof that got easier because a hypothesis was added, a conclusion weakened or a definition altered is the worst fault of this stage.
3. **It is a proof.** No `sorry` inside a partial proof, none in a definition (a hollow definition), none in a `private` or anonymous declaration; no `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`. In a scratch copy under /tmp add `#print axioms <declaration>` for the declarations proved: only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` exactly when the proof uses a statement that is still `sorry`.
4. **Every statement left with `sorry`** (new, or newly imported from lean/Sheaf) is TRUE and exactly as strong as needed: read it against its node and its source, test its edge cases (empty index sets, zero objects, `n = 0`, the characteristic, universes, a missing finiteness or properness hypothesis). It is not a restatement of the item (then nothing was proved), and it is not something Mathlib, lean/WeilConjectures or lean/Sheaf already has (search with `rg`). A new statement has: its own module lean/Sheaf/<Topic>/<Name>.lean in the module system (`module`, imports, `@[expose] public section`), its source and a complete proof in words in the docstring, `(blueprint: <node id>)`, and a node file whose `lean.statement` is its signature. A statement you believe false: RETURN, with the counterexample.
5. **From the top downward, and pruned.** The route is the shortest the worker could take: is there a Mathlib lemma or a proved declaration of the library that closes the statement or a statement left? Are the imports the proof needs written `import X` (not `public import X`), and is every import used? Does `## No longer needed` name what the new route does not use? The unit's route is kept: no module of a node in dag/units/<unit>.json `realized` is bypassed.
6. **The nodes agree with the Lean.** `proof`, `proof_deps`, `proof_origin` of the item's node follow the proof as written; an existing node is changed in no other field (statement fields only with a change record).
7. **The report** has its sections, names every `sorry` left, and its `## Second reading by <group>` is a reading, not a formula.
8. **The mechanical findings** of the packet (§1) are empty.

Not grounds for a RETURN: style; a proof that is long; a route different from the node's plan, when it is correct and below the unit level.

Fix, do not return (the human, 2026-10-21: the reviewer fixes what it can; only what it cannot fix goes back to the worker). Import hygiene, a shorter route, node `proof`/`proof_deps`/`proof_origin` fields, a wrong node `lean` record, a missing or stale change record or report section, a local compile error, a leftover `sorry` you can close, a statement you can correct in the delivery's own files: correct them and answer FIX. RETURN only for what needs new work or lies outside the delivery's files: a changed target or upstream statement (1), an unannounced change others see that you cannot undo locally (2), a proof that does not exist yet, a false statement whose correction needs a new route, or a delivery you cannot make compile.

Reader gate for interface hazards: when the class reason says `reader required`, list the direct importers from the import graph in the packet and compile each with `lcompile.py` before PASS. This applies to a global instance, an instance or elaboration attribute change (`instance`, `simp`, `ext`, `reducible`, `expose`), a `public import` becoming plain or being removed, and file-level `set_option … in`. A module added by the delivery is exempt. The compiler-only check of the delivered file is insufficient for these effects.

Report-only faults (launcher, 2026-10-15): report.md is documentation. A fault confined to report.md (wording, an inaccurate sentence, a missing section such as `## Forced adaptations` or `## No longer needed`) is never a reason to RETURN a delivery whose Lean and DAG files are right: write the correction into your review and answer PASS. Return only for faults in the Lean code or the DAG nodes (BaseChangeTargetTransitionHigherImage, a correct proof, was returned three times for report text).

Pre-existing failures (launcher, 2026-10-14): an importer that already fails or exceeds the 60 s limit against the PUBLISHED version (before this delivery) is not a fault of the delivery; do not return for it. Name it in your review as pre-existing and judge only what the delivery changes (UpperShriek was returned twice for the slow, unchanged Purity.Smooth.Conventions).

Forced adaptations (2026-10-12):

A module that NO group holds may be changed like the delivering group's own module (launcher,
2026-10-14), signatures included, when the change is right: a false statement corrected (a STATEMENT-
DISPUTED item), a duplicate merged, a reviewer-ordered fix. Check such a change for correctness (point 4)
and that the change record lists its users; do not return it as a forbidden signature change.
A module held by ANOTHER group may be adapted only when the delivery's own statement, definition or interface
change forces it: the original module fails to compile against the changed dependencies, and the
adapted module compiles. Every existing signature and visibility must stay identical; proofs,
imports and private local helpers may change. Name each adapted module and its current holder
(or unclaimed) in the change record. In `## Forced adaptations` of report.md give the original
compiler error and changed lines, explaining why each is necessary. In a module held by another
group, change only forced lines. No extra adaptation claim is required. Such a delivery is CODEX,
never AUTO: the independent reader compiles originals against the changed dependencies and the
adapted modules, checks the signatures and necessity of each edit, and returns any violation.
