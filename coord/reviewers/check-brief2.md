# Brief for the second reader of a stage-2 statement (remote group GROUP, item ITEM)

Another worker wrote the Lean statement of the DAG node ITEM of weil-newtargets. You did not write it. You read it against the node, repair what is wrong, and deliver it. The maintainer's reviewers are the scarce resource: what you deliver should be landed after one reading. A statement that does not say what the node says is the worst fault of this stage, because everything above it is then stated and proved on the wrong thing.

## Where things are (this machine)

- The repository, read-only: /home/ubuntu/weil-newtargets-GROUP (dag/nodes/, literature/, lean/Sheaf/, the contract). No git command there.
- The Lean source (slopmaster2), read-only: /home/ubuntu/weil-src-slopmaster2 (WeilConjectures/, Mathlib under .lake/packages/mathlib/Mathlib/).
- The work, which you may change: /home/ubuntu/weil-newtargets-stage2-sandbox/GROUP/ITEM/ (the module under lean/Sheaf/, the node copy under dag/nodes/, report.md).

Read first, in the repository: coord/brief-stage2.md and coord/delivery-errors.md section H; then the report.md of the sandbox.

## The reading, with the node, the source place and the Lean open

1. Write down for yourself the node's statement as a list: each object introduced, each hypothesis, each clause of the conclusion. Read the node's source place (Stacks .tex) for the hypotheses the source assumes throughout.
2. Match the list with the Lean, item by item (H3). For each object: is it the same object as the node's, through the declarations of the dependency nodes (open them and read their signatures: a declaration with a similar name may be another notion, a special case, or need instances the node does not give)? For each hypothesis: is it there, and no stronger? Is anything assumed in the Lean that the node does not assume (an extra instance, a Noetherian or finiteness assumption, a universe restriction, a field where the node has a ring)? For the conclusion: every clause, not weaker and not stronger; quantifiers in the same order.
3. Edge cases: the empty index set, the zero object, the empty scheme, n = 0, the characteristic, universes. Does the Lean cover each case the node covers?
4. One definition per notion (H4): search Mathlib and the project's Lean yourself with other words than the first worker's (`python3 /home/ubuntu/weil-launcher-nt/msearch.py GROUP ITEM leanfinder|loogle|grep "<query>"`, `rg` on /home/ubuntu/weil-src-slopmaster2/WeilConjectures and on the repository's lean/Sheaf). If the notion or statement exists, the module is dropped and the node's `lean` is set with "existing": true. If the report says "existing", open that declaration and check that it says exactly what the node says; if it does not, the module has to be written.
4b. New definition nodes and dependency modules of the delivery (coord/brief-stage2.md §1 and §5; delivery-errors H12, H13): read each new node against its source place as a stage-1 new node (is the notion really absent from the DAG, Mathlib and the project? is the statement what the source says? are its fields as §5 lists them?), and each dependency module against the dependency node it serves. If the first worker left a hole, a private copy or a weaker statement because a notion was missing, add the missing definition node or dependency module yourself.
4c. If the item's statement was corrected (the node copy has `statement_change`, the report "## Statement corrected"): read the corrected statement against the source place FIRST (it must say what the source says, not something easier), then the Lean against the corrected statement; open two of the citers and check the `holds` verdicts. If instead the first worker bent the Lean away from the node because the node is wrong, make the correction yourself in the same way (coord/brief-stage2.md §1 (C), §5).
5. No hollow definition (H5), nothing proved (H6), docstrings with the source place and `(blueprint: ITEM)`, the statement's docstring carrying the node's proof step by step (H8), conventions (H9).
6. Repair what you found, in the sandbox, and compile: `python3 /home/ubuntu/weil-launcher-nt/scompile.py GROUP ITEM <the .lean file(s)>` (pass all sibling modules; each is compiled separately) until clean (no error; no warning except "declaration uses `sorry`"); check by eye that no variable or universe is left unbound. Keep the node's `lean.statement` verbatim equal to the signature in the file. Do not rewrite what is right. Correct an invalid internal node only under coord/brief-stage2.md §1(C); never change a target unit statement.

## Then

7. Append to report.md a section headed exactly "## Second reading by GROUP": the list of step 1 with, for each item, the Lean that renders it and your verdict; the edge cases; your searches; every mismatch you found and what you changed. Leave "## Worker report" in place.
8. Dry run: `python3 /home/ubuntu/weil-launcher-nt/deliver2.py GROUP ITEM --no-push` until it prints OK.
9. Deliver: `python3 /home/ubuntu/weil-launcher-nt/deliver2.py GROUP ITEM` .

## Your answer, one line, one of

- "DELIVERED ITEM at <commit>: <module path or 'existing: <declaration>'>; second reading changed <what, in ten words>" ;
- "ABANDON ITEM: unit statement: <what is wrong with the unit's own statement>" (the only abandonment) ;
- "BLOCKED ITEM: <the tool failure>".


## New-targets isolation (human, 2026-10-15)

Human update 2026-10-15, parallel landing: all compiles MUST use scompile.py, which now runs lcompile.py on the Codex machine with a local side-project overlay and server confirmation when needed. Local compilation through this wrapper is authorized and required where possible; the earlier server-only restriction is superseded. Each file still has nice 19, two threads and 60 seconds. No lake build or global build. The compiled live library is read-only. Statements land only in weil-newtargets/lean. Use branch newtargets-dag for project declarations. Read upstream sources on this machine; do not modify them. For pro-etale work, the 51-module framework is in the read-only group clone at /home/ubuntu/weil-newtargets-GROUP/lean/WeilConjectures/, not in the older slopmaster2 source tree. Read that exact declaration and coord/pefw-upstream-framework.md in the group clone; scompile.py compiles side-only imports into a private overlay against the live library. Compile every delivered file. Missing declarations are handled by §1(A)/(B), not by blanket BLOCKED. Supply a missing helper definition, canonical map, site transport or comparison in this delivery when it is part of the notion being stated. Helpers may be declarations in the owning node's module, listed in lean.declarations with source/blueprint docstrings, or a new definition node with its own module under §1(A). Every postponed theorem needs the matching DAG statement and proof docstring; definitions have real data. For an already recorded dependency with an unusable interface, §1(B) permits a dependency module and a lean-only repair, including an exact existing Mathlib/upstream declaration with lean.note. Do not replace a canonical construction by an arbitrary map, a mere Nonempty choice, or a stronger assumption.

If the needed object is a genuine DAG node with no usable recorded declaration or Mathlib match, state that node yourself in this delivery (its own module and node record, under §1(A)), cite it in stmt_deps, and state the item on top of it (the human, 2026-10-16: nothing waits). If another group has already landed or delivered it, use theirs. There is no WAITING answer. Reserve BLOCKED for an actual tool failure after the authorized repairs.

Use `python3 /home/ubuntu/weil-launcher-nt/scompile.py --source <Module.Name>` to read the current server source when a recorded module is missing or stale in the local checkouts. It uses the same live/side sources as server compilation. Preflight runs on the server too; a missing file in the older local checkout alone is not a blocker.

Universe failures require diagnosis and repair. Read the full site and coefficient universes; do not impose an extra equality merely to use an overly specialized API. Supply an equivalent transport or generalized dependency interface by §1(B) when the mathematical statement is unchanged. If the item's own statement really cannot be typed as written, §1(C) authorizes a source-based statement_change and full citer audit. In particular: def-weil-pbc-complete-coefficient-datum must retain the small pro-etale site (object universe t+1, morphism universe t); generalize/transport the derived-change-of-rings dependency rather than force those universes equal. For lem-weil-pbc-qcoherent-cohomology-comparison-pullback, the supplied Etale.cohomologyMap uses AddCommGrpCat.{u+1}: follow Stacks 03P2 and the size convention, either construct the canonical coefficient transport or record the common u+1 lift with its degree-zero down map as a §1(C) correction after checking all citers. Do not silently discard the identity/arbitrary-lift cases.


Dependency waits must be acyclic. Do not wait on a downstream theorem about the
very canonical map your definition introduces. The dispatcher rejects a wait
that closes a dependency cycle and gives the path in its next prompt. Repair the
already recorded dependency interface under §1(B) instead. Specifically,
def-weil-pbc-projection-formula-arrows must not wait for
lem-weil-pbc-ringed-projection-mate-exact: repair the recorded
lem-weil-pbc-ringed-topoi-derived-tensor-pullback in the same delivery, supplying
the canonical comparison characterized on K-flat representatives (and its
ordinary unit normalization), then define its counit mate and the specified
finite-total inverse. A bare Nonempty natural isomorphism is insufficient, but
an interface that forgets the representative characterization is an authorized
§1(B) repair. The projection-mate theorem can subsequently use these arrows.


Launcher-tool authorization (human parallel-landing update, 2026-10-15): the read-only clone rule prohibits your direct edits and Git mutations. It permits the prescribed scompile.py and deliver2.py wrappers to perform their normal local compilation, clone refresh and delivery bookkeeping. Their authorized local compiler and clone bookkeeping are not policy violations. Never edit live Lean files or run a global build.


## The shared repository (launcher, 2026-10-16)

The repository you read is shared by all groups and is read-only for you. The delivery tools (deliver.py, deliver2.py, deliver3.py, also with --no-push) build the delivery in their own temporary git worktree; running them is the required step, not a forbidden git command. If one reports that a delivery branch is checked out in another worktree, run it again once; report BLOCKED only if it persists.

## Derived form of complex isomorphisms (upstream decision, 2026-10-21)

Christian Merten (Zulip "per-degree statement for derived isomorphisms", 2026-10-21, relayed by Jiedong Jiang): a result identifying two complexes or derived objects is stated as an isomorphism in the derived category; a per-degree form `∀ q, H^q(…) ≅ H^q(…)` may accompany it as a second declaration deduced from the derived one, never replace it. A delivery whose only statement of such a result is per-degree is returned with this note (brief-stage2.md §3).
