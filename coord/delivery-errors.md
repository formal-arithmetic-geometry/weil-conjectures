# What deliveries were returned for, and how a lead checks for it

For the leads of the remote groups and their workers. It collects every reason for which a delivery was returned between 2026-10-09 14:40 and 2026-10-10 03:30 UTC (about 150 returns of groups C–G and C1–G1), grouped, each with real cases. The rules themselves are in `stages/1-dag.md`, `coord/brief-stage1.md` and `roles/remote-lead.md`; this file says where they were broken.

How to use it:

- **The worker** gets sections B–E in its brief and checks its split against them before it reports.
- **The lead** reviews each finished split against sections A–F, point by point, reading the node files and the sources, and sends back to the worker whatever fails, with the letter and number of the point. Nothing is pushed while a point fails.
- **The review** in the report (`## Review by <group>`) follows section F.
- **A return** from L names the points by letter and number where one applies (for example "C1: step 2 quotes 01KJ with no node"), then the specifics. A reason that fits no point is added to this file in the same commit as the return. Repair every point named, then check the whole delivery again against this file: a repair often breaks another point.
- **`tools/preflight_delivery.py`** finds all of section A and the parts of B it can read mechanically (B1, the doubled backslashes and "in the setting of" of B2/B4, every `[node]` cited exists (B3), a tag written in a step is carried by a cited node (C1)); run it before every push.

Counts are of the returns in which the reason appeared; a return often had several.

## A. The shape of the delivery (about 50 returns; none of these was read for its content)

`tools/preflight_delivery.py` finds all of these. Run it before every push.

1. **Several commits, or a branch built on another delivery** (31). "7 commits on the branch", "the branch is stacked on deliver/C1/…: its diff against sheaf-dag contains that item's report". One item is one commit on top of the current `sheaf-dag`: `git fetch`, `git reset --soft $(git merge-base origin/sheaf-dag HEAD)`, commit, rebase on `origin/sheaf-dag`, force-push. Each delivery branch starts from `sheaf-dag`, never from another delivery.
2. **No report, or no `## Review by <group>`** (13). The report `coord/reports/<group>/<item>.md` is part of the same commit.
3. **Files that are not the item's**: `coord/STATE.md`, a claim lock, another item's report, another item's node.
4. **A new node whose `created.item` is not the delivered item** (2), or **whose id already exists on `sheaf-dag`** with another statement (2): "the delivery creates lem-weil-pbc-chow-finite-type, but that id now exists". Search before creating (C4).
5. **The item has no `split_report`**; a branch that points at a commit of `sheaf-dag` itself and carries nothing.
6. **The same content pushed again** (5): "the branch is the returned head rebased on the current tip, the files are byte-identical". A rebase is not a repair. If the points of the return are not changed in the files, do not push.
7. **A push after the merge, or after an abandonment.** "The push that arrived after the merge is the same content rebased and is not merged; delete the branch." Once the ledger records the merge, the item is closed: a correction you still want goes into `coord/HUMAN.md` through your next report, not onto the branch. The branch of an abandoned item is deleted by the maintainer; nothing is pushed to it.

## B. The form of a new node (about 25 returns)

A new node is read later by someone who has only that node.

1. **A new node that is not split carries a statement only** (5 returns, 12 nodes). No proof steps, no `proof_deps`, no proof sketch inside the statement ("The proof uses the theorem on formal functions…"). The argument you have in mind goes into the report.
2. **Self-contained statement.** Returned: "In the setting of Grothendieck existence…", "the algebraization M", "finite-presentation O_X-modules" without saying what X is. Every object is introduced in the node itself, with all hypotheses.
3. **Every notion cites its definition node, and the cited node defines it.** Returned: "Dedekind domain" and "discrete valuation ring" with no node and no inline definition; `[def-weil-pbc-regular-sequence]` cited for "Artinian ring" and "module of finite length", which that node does not define; "essentially of finite type" with no node anywhere when the item only needs finite type.
4. **TeX, written once.** Returned: plain text (`F_2 -> F_1 -> F -> 0`, `P#`), and doubled backslashes in the JSON (`\\to`, `\\Lambda` render as literal backslashes).
5. **The source is the Stacks tag and the label in the `.tex` of `literature/stacks-project/`, not a section number** (15.44.9 changes between versions), and it is the right tag: a node "005H" was returned because the fact is Topology 09YJ and needs the hypothesis that the opens form a basis.
6. **A Mathlib leaf names the declaration, the file and the lines read.** Returned: a line number that was wrong, a `how` that named no lines.
7. **A statement does not refer to tags for its meaning** ("in the sense of Stacks Tags 034W and 034X"): write the meaning.
   A search that was not run is not recorded (finding of the launcher, 2026-10-10 16:51 UTC: of 259 nodes created by remote workers in two hours, 215 recorded three searches while the worker called no search tool, and LeanSearch's HTTP 500 was recorded as "no match"; Loogle gives `Polynomial.nodup_roots` for lem-pc-separable-polynomial-distinct-roots-alg-closed at once). Every entry of `mathlib_searches` is a query that ran, with its tool and its actual result; a service that is down is recorded with verdict `unavailable`, not "no match". Since 17:00 UTC the remote delivery tool refuses a new node whose recorded searches are not in the search log; the records of remote nodes created before 17:00 UTC are treated as not done (`coord/research-remote-nodes.txt`).
8. **A Mathlib leaf is an exact match or a one-line specialization**, or one declaration per clause with the line of each (`how` names them all). A hypothesis of the declaration that is an instance Lean infers (a `JacobsonSpace` instance for a scheme locally of finite type over a field, a `Noetherian` instance) is not a second step: name the instance and its line in `how` and the node is still a leaf (L, 2026-10-10 17:10 UTC). When the agreement of the Stacks notion with Mathlib's is itself a theorem (Stacks' quasi-finite at a prime against Mathlib's `QuasiFiniteAt`; Stacks' length against `Module.length` is fine, the remark that the two suprema agree is one line), the node is unsplit with the candidate recorded in `mathlib_candidate`, not a leaf. (L's own reviews of 2026-10-10; no return yet.)
9. **Blueprint references** (decision of the human, 2026-10-10; `stages/1-dag.md` §6, `coord/brief-stage1.md` §7). Every node carries `blueprint` = `{is, from, same_as}`. Before creating a node, search the whole imported blueprint (`tools/blueprint_refs.py search`, every chapter, also outside the reach); if a blueprint node states it, cite it and create nothing. Every new node has `from.node` = the item's nearest blueprint ancestor (`tools/blueprint_refs.py ancestor <item>`) and `from.place` = the exact step, clause or sentence of that blueprint node's proof it serves, and `same_as` = the search result (`[]` if none). The item gets its `from.place` filled where it was "unspecified" and its `same_as`, and its `split_report` has a `blueprint` entry naming the places of the blueprint proof the steps realize. `tools/preflight_delivery.py` (check 8) and `tools/review_split.py` fail without these.
10. **A node the Lean already states is not split** (decision of the human, 2026-10-10). A node that a sorry-free declaration of slopmaster2 (the done branch, now at 71d63dcf) states exactly is finished and is not split. A worker who finds such a declaration for its item, or for a node it is about to create, attaches it (reports `<declaration> belongs to <node id>`, and for a new node records it in `lean_audit.slopmaster2.decls` with state `closed` left to `tools/lean_status.py`) instead of writing a proof; check the Lean statement against the node statement before attaching, and check for `sorry` with the sorry map. Look for it by the node id (`grep -rn "<id>" ~/weil-conjectures-slopmaster2/WeilConjectures ~/weil-conjectures-slopmaster2/Comparator`, the checkout of slopmaster2; a plain grep, no git), by the names in the node and in `dag/lean_names_upstream.json`, and by a grep of `~/weil-conjectures-slopmaster2/WeilConjectures` for the key words.

## C. Citations in the proof steps (33 returns; the most frequent reason of content)

The rule: every fact a step uses that is not elementary is the statement of a node the step cites. A tag in the text is not a citation.

1. **A fact quoted by tag, or used "freely", with no node.** Returned: "the diagonal Δ is an immersion by Schemes Lemma 01KJ"; "immersions are stable under base change" and "a closed immersion followed by an immersion is an immersion"; "the étale locus is open"; "dim(W ∩ O) ≤ dim W"; "a product of injective objects is injective, from Mathlib's Pi instance". Each needs a node: an existing one, or a new unsplit node or Mathlib leaf. Exception (rule of 2026-10-10 17:10 UTC, after the audit of new nodes found 9 of 40 remote nodes to be two- or three-line facts): a fact that is two or three lines from the cited statements and definitions is a step marked `elementary: true` that names the tag, not a node; `tools/preflight_delivery.py` check 6 accepts it with a warning and the reviewer judges whether it really is elementary (a reviewer folds a few-line new node into a step itself and drops the node, FIX not RETURN).
2. **A step marked elementary that is not.** Returned: steps marked elementary that cite tags 0AUQ, 034W; a step marked elementary that "carries the whole conclusion". Elementary means a reader checks it from the cited statements and the definitions in a few lines.
3. **A step uses the proof of a node, not its statement.** Returned: "the presheaf G and the category of triples from the proof of lem-…-colimit-of-sites"; "the construction inside lemma-constructible-common-refinement gives the morphism X_i → W_{a,b}", which its statement does not give. Read the statement of every node you cite and check that it says what the step takes from it.
4. **A cited node that does not say it.** Returned: `[def-weil-pbc-sheafification]` cited for F^# = F^{++}, but that node defines sheafification by its universal property only; the plus construction is in no node. Returned: a node for normal rings applied to a ring that is not normal.
5. **Search before you write a new node.** `grep -rl "<tag>" dag/nodes` and a search for the key words on the current `sheaf-dag`: the fact is often there (the stalk of a closed pushforward, the existing 03S6/03S7/03RU nodes). Cite it, do not make a second one.
6. **No cycle.** A repair that cited a node depending on the item made a cycle of 8 nodes. `tools/check_dag.py` on the delivery tree shows it.
7. **Another unit's lemma for something the unit's own route gives.** Returned (first return of z-localizations-dvr): the DVR property through `lem-sc-normal-dim1-dvr` of another unit, which needs the normality the delivery had not proved, when the statement's own source (00PD (4)) gives it directly. A tool lemma of another unit may be used where the route genuinely needs it (the third return of the same item asked for exactly that node once normality was in place); the unit's route may not be replaced by it.
8. **A tool of another unit is recorded by L, not by you.** A node of another unit that is not a Mathlib leaf and not Lean-closed fails the route check of `review_split.py`; the maintainer records it in `tool_uses` at the merge (the spreading-out theorem 01ZM, the étale lifting 04D1 were recorded this way). Say in the report which node is used as a tool and why no node of the unit gives it; do not write `tool_uses` yourself, and do not avoid the tool by a weaker route.

## D. What a split is (about 10 returns)

1. **Relabelling.** "Each of the four steps cites a new node that is exactly the clause it is supposed to prove." "The two new nodes restate the item's own clauses." A split writes the proof of the item: the steps carry the argument, and a new node is a fact the argument uses, strictly smaller than the item.
2. **Everything moved into one new node.** "The whole content is moved into the new node …-torsion-injective-resolution." The same error.
3. **The source's proof restated loosely, citing only definitions.** "The proof is the construction of Stacks 05T6 restated in prose: all three steps cite only two definitions." If the source's proof uses lemmas, the steps cite nodes for them.
4. **Circular.** A new node whose statement step 2 derives and then cites. An induction that is not set up: "inductively … is regular after the identifications in the next steps". State the inductive claim, the base and the step.
5. **Where the source says "details omitted", the details are the split.** A return found the gap that Stacks 07QI hides behind those words. Write them, or make them a node.

## E. Mathematics (17 returns)

Found by reading each step against the hypotheses actually in force. The cases:

1. **A hypothesis used that is not there.** Step applies the lifting lemma with the ideal I^N, the pair is henselian for I. Intersections V_a ∩ V_b of affine opens taken to be affine: U is only quasi-separated. A base change lemma for finite type bases applied to a base that is not.
2. **A false statement in a new node.** "For every discrete valuation ring A the map A → Â is regular": false without excellence (or characteristic 0). Test a new statement on its small cases before writing it.
3. **A false step.** "The immersion X_i → X factors through W_{a,b} because its image is contained there": not in general; the stratum to take is X_i ×_X W_{a,b}.
4. **The wrong object.** The diagonal of f_0 written as X_0 → X_0 ×_{S_0} X_0 instead of X_0 ×_{Y_0} X_0. A/pA identified with the fibre ring. A lift r of an idempotent e treated as an idempotent.
5. **"Transports", "the same calculation commutes with the connecting maps", "clear denominators".** Each of these words stood where the argument was missing: a hypothesis stated for f, g in R used for f/h^n, g/h^m in R_h; a compatibility with connecting maps that is the substance of the clause; a substitution z ↦ sz, f ↦ s^p f that had to be written. When a step says one of these, write what it stands for.
6. **A notion with two meanings.** A proof route through "the formal-functions route exposed by the public interfaces": a step cites nodes for what their statements say, nothing else.
7. **The source is wrong.** It happens (2026-10-10: 07EV's first assertion K ⊗ C ≅ J/J² is false, 09AX's proof identifies ε⁻¹ε_*F with F, 0884 states an equality that is only a surjection, 07PM cites the descent lemma 07EH for a base change, 07E5 cites 00OM where 00ON is needed). Then: state what is true and what the citers use, with a counterexample for the false part tested on a small case; say so in the report under its own heading (`## Source error`), and the maintainer records it in `coord/HUMAN.md`. Do not reproduce the source's statement because it is the source's, and do not weaken a statement silently: a changed statement is always named in the report.

## F. The lead's review (16 returns for the review alone)

Returned: "Pending lead review"; "Reviewed by C worker"; the worker's report under a new heading; a list of mechanical checks ("statement against the unit, steps name dependencies, searches recorded").

The review is written by the lead, after the worker has returned, with the node files and the sources open, and it says:

1. which source was read (tag, label), and that the statement of the item and of each new node agrees with it, hypothesis by hypothesis;
2. for each step: which cited statements it uses and that they say it (C3, C4), and what is elementary in it;
3. for each new node: B1–B7, and where the search for an existing node was made (C5);
4. section E: which hypotheses were checked at which step, and the small cases a new statement was tested on;
5. what the lead sent back to the worker and what changed.

A review that could have been written without opening the files will be returned.

## G. Repairs

1. Read the whole entry of the return. Repair every numbered point. "Three points of the first return are still open" and "Not repaired: the branch still cites …" were written several times each; one item went to its fourth return this way.
2. Do not answer an uncited fact by moving it into a new node that restates the item (D1): cite the fact, or write its argument in the step.
3. After the repair, check the delivery again from A to F, and say in the review, point by point, what was done for each point of the return.
4. An item returned three times is abandoned with the reason (`roles/remote-lead.md`), not pushed a fourth time.

## H. Stage 2 (statements)

The rules are in `coord/brief-stage2.md` (decision of the human, 2026-10-11). A stage-2 delivery is returned for the points below, by letter and number (`H3: the hypothesis "X proper" is missing`). The list grows as returns come in; each new reason is added here in the same commit as the return. `tools/preflight_delivery.py <G> <item> --stage 2` finds H1, H2, H8 (in part), H9, H10 and the field part of H12.

1. **Shape.** Not one commit on top of `sheaf-dag`; files other than the modules `lean/Sheaf/<Topic>/<Name>.lean`, the item's node file, new definition node files in the item's chapter directory, dependency node files and `coord/reports/<G>/<item>.md`; a module that is not the `lean.file` of exactly one node of the delivery (the item, a new node, a dependency node), or a node with `existing: false` without its module; no `## Worker report` or no `## Second reading by <G>`; no `## New nodes` (resp. `## Dependency modules`) naming each new node (resp. dependency node) when the delivery has any.
2. **A node changed outside its fields.** The item changed in any field but `lean` and `stmt_deps`, or its `stmt_deps` changed otherwise than by adding new definition nodes of the delivery; a dependency node (one in the item's `stmt_deps` on the base) changed in any field but `lean`, or its record without `lean.note`; a node changed that is neither the item, a new node nor a dependency node; a `lean` record incomplete (`module`, `declaration`, `statement`, `branch`, `by`, `date`, `existing`; `file` when not existing) or its `statement` not verbatim from the file.
3. **Not the node's statement.** A hypothesis added or dropped, a conclusion weakened or strengthened, a clause missing, other objects than the node's (another category, another ring, a special case), a hypothesis the source assumes throughout left out, an edge case excluded (empty index set, zero object, a characteristic, a universe too small).
4. **A second definition of a notion.** The notion or statement exists in Mathlib or in the source repository and was written again; (under the EXTRA NODES rule of 05:55 a dependency whose record is unusable gets a dependency module in the same delivery, H13, not an abandonment) a dependency's recorded declaration not used (a private copy instead); no record of the three kinds of search in the report.
5. **Hollow definition.** A def whose data is `sorry`, or a proof a def needs left as `sorry` inside it instead of a named theorem.
6. **Something proved, or a statement weakened to be provable.** Stage 2 states; every theorem's proof is `sorry`. A statement believed false is written as the node says and marked `STATEMENT-DISPUTED:`.
7. **Node faults handled silently.** The node's statement wrong or ill-typed and the worker changed it, or rendered something else without reporting; a wrong dependency record not released with `abandon: dependency <node>: …`.
8. **Docstrings.** No module docstring `/-! # … Source: … (blueprint: <id>) -/`; a declaration without a docstring naming the source place and `(blueprint: <id>)`; a statement whose docstring lacks the node's proof step by step.
9. **Conventions.** A line over 100 characters; an import outside `Mathlib.*`, `WeilConjectures.*`, `Sheaf.*` or unused; an unbound variable (auto-implicit); the wrong topic directory; a declaration carrying a `Sheaf.` prefix, or a full name that already exists in Mathlib or the source repository.
10. **Does not compile clean** on the server (`tools/compile_remote.sh`): an error, a timeout, or a warning left (unused variables).
11. **Second reading not a reading.** It could have been written without opening the node and the file: it must match each hypothesis and clause of the node with its Lean and say what it found and what changed.
12. **A new definition node that should not be one, or breaks the field rule** (`coord/STATE.md`, STAGE 2 EXTRA NODES). The notion exists in Mathlib or the source repository (then the item cites it through an `existing: true` record, on a new node only when no DAG node carries it), or a DAG node already carries it (cite that node), or it is not what the source place says; or its fields break the rule: id not `def-<chapter prefix>-<name>` or already on `sheaf-dag`, not in the item's chapter directory, `kind` not `definition`, `status` not `split`, the statement not self-contained TeX or not citing (in `stmt_deps`) the definition nodes it is built from, `source` without document and place, fewer than the three kinds of search (LeanSearch; Loogle or LeanFinder; grep), `mathlib_match` not null, `proof`/`proof_deps` not empty, `created` not {by worker, item, date, group}, `blueprint.from` not the item's ancestor and via, `lean_audit` not none, `chapter`/`unit` not the item's, no `lean` record, a maintainer's field; or the item does not cite it.
13. **A dependency module that does not state the dependency node's notion.** The module for a dependency node (B) states something else than the node says (another object, a special case, a hypothesis added or dropped), duplicates a declaration that was usable after all, or `lean.note` does not say why the recorded declaration or `mathlib_match` was unusable and what the module states.
