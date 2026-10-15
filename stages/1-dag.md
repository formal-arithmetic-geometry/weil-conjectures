# Stage 1: the natural-language DAG

**Produces:** `dag/nodes/`, a DAG of definitions and statements with complete natural-language proofs, from the targets down to results in Mathlib. No Lean is written.

## 1. Nodes

A node is one definition or one statement, in one JSON file, in any layout. It records:

- an id, never reused;
- whether it is a definition, a statement or a target;
- the statement in words and where it comes from;
- the nodes needed to state it (statement dependencies);
- for a statement that is not in Mathlib, a complete proof in steps, each step naming the nodes it uses (proof dependencies) or marked elementary;
- whether the proof follows a document, with the document and the place, or was written by an agent;
- the Mathlib searches made, with tool, query, results and date, and the Mathlib match if there is one;

A node has no history field: the file's git history is the node's history. A change that needs a reason is one line in `coord/ledger.md` (date, id, what changed, why); nothing is copied into the node for the record.

A statement is a proposition that can be judged true or false, or the definition of one mathematical object. It introduces its own objects rather than pointing at the objects another node constructed, and its source is a document and a place in it.

Nodes are never deleted. Two nodes that state the same thing are merged: one is marked as merged into the other, and its users point to the other. A node that no target reaches stays in the graph and is not an item of any stage: when a parent's proof stops using a node, nothing else is done to it.

## 2. Who does what

An item of this stage is a node that a target reaches and that is not split yet. This stage goes from the targets downward. A node is split when what it is built from is written as nodes: the notions its statement uses and the steps of its proof, each step naming the nodes it uses (§3). A definition is as far from Mathlib as the notions it is built from. A Mathlib leaf is not split further. The stage is finished with a node in two cases only: every branch below it ends in a Mathlib leaf; or the node's own Lean is written and compiles, its declaration with a body of at most ten lines, a definition's body or a statement's proof, that uses nothing but Mathlib and says exactly what the node's statement says (§6). Such a node is not split further. Stage 2 may state a node as soon as it is split, while the nodes below it are still being split (`roles/maintainer.md` §6).

- The **maintainer** keeps the queue: the nodes that are neither Mathlib leaves nor split, nearest to a target first. If `SETUP.md` asks for an early review of the target statements, the nodes needed to state the targets come before all others. It starts with the targets. There is no Lean to build in this stage; in each cycle the maintainer brings the queue up to date, checks the new nodes against §6, and commits.
- A **lead** claims nodes and gives each to a worker.
- A **worker** splits its node by one level (§3) and writes the nodes directly into `dag/nodes/`. It changes no node that is not its own; what it finds wrong in another node goes into its report.
- The lead reviews the node: the proof follows its source, every step names what it uses, every new node was searched in Mathlib, and no new node repeats an existing one. A node counts as split only when its `status` is `split` and the lead has written `reviewed` (date, lead, result) on it after that review; `tools/review_split.py` does the mechanical part first. An item that turns out to be in Mathlib gets `status` `mathlib` with its match and `reviewed` as well.

Conventions settled on review (2026-10-09):

- **Mathlib leaf.** A node is a leaf when Mathlib states the same thing for the same kind of object, or a generalization that specializes in one line, including a conjunction of two Mathlib classes (finite type = `LocallyOfFiniteType` and `QuasiCompact`) or a few Mathlib lemmas applied one per clause; not when the agreement with Mathlib's definition is itself a theorem (smooth morphisms: Mathlib's smooth ring maps against the formally-smooth definition, Stacks 02H6, stays a split node with the match recorded). A `mathlib_match` is `{"declaration", "file", "how"}` with the file under `Mathlib/`.
- **Mathlib searches (rule of 2026-10-09).** A node is declared absent from Mathlib only after three kinds of search have been tried and recorded in `mathlib_searches` (tool, query, results, date, verdict): LeanSearch (natural language), Loogle or LeanFinder (type pattern or semantic search), and a grep of the Mathlib source. A search of one kind only is not a verdict. The search services are reached through the lean-lsp tools or their HTTP endpoints (`SETUP.md`, "The machine"; `tools/README.md`); nothing is built for a search. Nodes reviewed before this rule were searched by grep only; the lead re-searches the unsplit new nodes among them when the queue is quiet, since a missed leaf costs an item.
- **New nodes.** A new node is named `<def|lem|prop>-<prefix of its chapter>-<short name>`, placed in the directory of the item that created it, carries `created` (`by`, `item`, `date`), a complete statement introducing its own objects, a source with the place, at least one recorded Mathlib search with a verdict, and is `unsplit` (it joins the queue) or `mathlib`. A node that nothing cites yet (a claim moved out of a definition) is flagged `unreachable` in `import_flags` until a user cites it; the ledger records it.
- **Claims inside definitions** become statement nodes; the definition keeps the data and takes its well-definedness from the theorem by name. A definition does not cite a lemma about itself (that is a pointer, kept in `pointers`, since it would close a cycle).
- **Lean in slopmaster2 finishes a node (2026-10-10).** A node that a sorry-free declaration of slopmaster2 (the done branch, now at 7d675a26; before 2026-10-12 at 71d63dcf) states exactly is finished and is not split. A worker who finds such a declaration for its item, or for a node it is about to create, attaches it (reports `<declaration> belongs to <node id>`, and for a new node records it in `lean_audit.slopmaster2.decls` with state `closed` left to `tools/lean_status.py`) instead of writing a proof; check the Lean statement against the node statement before attaching, and check for `sorry` with the sorry map. Look for it by the node id (`grep -rn "<id>" ~/weil-conjectures-slopmaster2/WeilConjectures ~/weil-conjectures-slopmaster2/Comparator`, the checkout of slopmaster2; a plain grep, no git), by the names in the node and in `dag/lean_names_upstream.json`, and by a grep of `~/weil-conjectures-slopmaster2/WeilConjectures` for the key words.
- **Lean found by a worker.** A sorry-free declaration of slopmaster2 that states a node exactly is attached by the lead at review (`lean_audit`, with the sorry map as the proof that nothing below it has `sorry`); the node is then closed. `tools/lean_status.py` keeps such hand-attached names.
- **Duplicates.** Two nodes created the same day for one notion: the later one is merged into the earlier (`status` `merged`, `merged_into`) or, if never committed, dropped, and the citers repointed.

## 3. Splitting

1. For a target, start from the statement and proof in the paper.
2. For a definition, name the notions it is built from as its statement dependencies; one that Mathlib does not have becomes a definition node of its own.
3. For a statement, write its proof in steps (§4), and name for every step the definitions and results it uses.
4. For each of these, look for an existing node with the same statement, the same place in the literature or the same Mathlib match, and point to it. If there is none, create a node.
5. Search Mathlib for every new node. If Mathlib has it for the same kind of object, or has a generalization that specializes in one line, record the match: the node is a leaf. Otherwise record the search, and the node joins the queue.

The stage goes on until every branch ends in a Mathlib leaf or in a node whose Lean is written (§2). The graph stays acyclic.

## 4. Proofs and the literature

- Download every document a proof relies on into `literature/` and list it in `literature/LIST.md`: the paper, what it cites for a step, and the references for the textbook results the DAG splits.
- A proof follows its source exactly and cites the document and the place. It is not written from memory.
- A reference is not a proof: the steps go into the node. Where the source omits a step or calls it obvious or standard, write the step out.
- A proof written by a human is preferred to one written by an agent. When you cannot obtain a document, add it to the wanted documents in `literature/LIST.md`, so that the human is asked for it. Until it arrives, write the proof yourself and mark the node as written by an agent. When it arrives, rewrite the proof from it and remove the mark.

## 5. The three levels of the blueprint

`SETUP.md` fixes what an agent may change at each level of the blueprint. In this stage:

- A node's proof realizes the steps of its unit's `sk-*/_section.md`: the unit's statement and each step of its proof are carried by nodes of the DAG, and the units the unit cites are the ones the DAG passes through. A split keeps to that route. A step the unit calls obvious is still written out, below the unit, in nodes the worker is free to choose.
- A departure from a unit's route needs an established mathematical error in the unit: the step, what is wrong with it, and the counterexample or the inference that fails, written in the node that meets it, confirmed by the lead on review, and reported in `coord/HUMAN.md` with the replacement route, as `SETUP.md` says. A step that is hard, long, or absent from Mathlib is not an error.
- The chapter level is never touched: not the key theorem, not the reference route, not which chapters a chapter uses.

## 6. Units and chapters in the DAG

The 16 chapter files and the 389 unit files of the blueprint are records beside the nodes, written by `tools/units.py build`:

- `dag/chapters/<sec>.json`: the chapter's key theorem, reference and the chapters it uses, verbatim.
- `dag/units/<sk>.json`: the unit's statement and the paragraphs of its proof as `steps`, the units it cites (`uses`), its Lean names, and the binding fields `realized` (`statement`: the node ids that state the unit; `steps`: for each step, the node ids that carry it) and `realized_by`. The worker of the unit's key node fills `realized` as part of its split, and the lead confirms it on review.
- Every node carries `chapter` and `unit`, from its blueprint path; a node a worker created inherits them from the item it was created for.

A node's route is its unit and the units its unit cites, transitively. The route is about proofs: a step of a statement may use a statement of another unit only if the node's unit cites that unit; definitions, Mathlib leaves and nodes whose Lean is finished (`closed`) are notions or tools, not route. `tools/check_dag.py` reports a unit whose `realized` fields leave a step with no node or a cited unit unreached, and a reviewed statement whose proof uses a statement outside its route; `tools/review_split.py` reports the same for one item, and the lead rejects the split (§5) unless the departure is an established error or the cited statement is a generic tool lemma used as a black box (`SETUP.md`), which the lead records in the node's `tool_uses`.

### Blueprint references (decision of the human, 2026-10-10)

The DAG refers to the existing blueprint node by node, so that the two can be read against each other. Every node carries one field:

```
"blueprint": {
  "is":      the blueprint node this node is: for a node imported from the blueprint (it carries `blueprint_kind`) its own id; else null.
  "from":    null for an imported node; for a node created in a split:
             {"node":  the blueprint node whose proof it serves: the item it was created for if that is a blueprint node, else the
                       nearest blueprint ancestor found by following `created.item`;
              "place": the step, clause or sentence of that blueprint node's proof text which this node states or makes precise
                       (name the place in the blueprint proof, e.g. "proof, second paragraph: 'by Lemma 01YE ...'"; the backfill wrote
                       the step of the ancestor's split, or "unspecified" where it could not read it off);
              "via":   the created nodes between this node and that blueprint node, nearest first ([] when created for it)},
  "same_as": the blueprint nodes anywhere in the blueprint (every chapter, also outside the targets' reach) that state the same thing
             in another form, found by search; [] when the search found none; null only on a node nobody has searched for yet.
}
```

- **Before creating a node**, search the whole imported blueprint (every node with a blueprint id, every chapter, not only the reach) for a node with that statement: `tools/blueprint_refs.py search <words or tag>`, and `grep -rl` on `dag/nodes`. If one exists, cite it and create nothing. Record a blueprint node under `same_as` only when it states the same thing in a different form and the new node is still needed.
- **Every new node** gets `from` with the exact place and `same_as` with the result of the search. `tools/blueprint_refs.py ancestor <item>` prints the `from.node` it must carry.
- **The item** of a split gets its `from.place` filled if it was "unspecified" and its `same_as` searched, and the `split_report` has an entry `blueprint`: which places of the blueprint node's proof the item's steps realize.
- The field was backfilled mechanically on 2026-10-10 by `tools/blueprint_refs.py backfill` (`is` for the imported nodes; `from` through `created.item`, with the place read off the ancestor's split). The reverse index `coord/blueprint-index.tsv` (blueprint node id → the DAG nodes that are it, come from its proof, or state the same) is regenerated with the queue (`tools/queue.py write`). `tools/check_dag.py` requires the field on every node; `tools/review_split.py` and `tools/preflight_delivery.py` check the item and the new nodes strictly.

## 7. After this stage

The DAG keeps changing while statements and proofs are formalized. Nodes are added and revised under the same rules. A node is updated from Lean twice: when its statement is formalized, with the module, the declaration and the Lean statement; when its proof is done, with the proof dependencies the Lean proof uses.

## 8. Finished when

- every target has a node, and every branch of statement and proof dependencies ends in a Mathlib leaf or in a node whose Lean is written (§2);
- every other statement has a complete proof, and every step of it names the nodes it uses or is marked elementary, unless its Lean is written (§2);
- the graph is acyclic, and no node points to a missing or merged node;
- every unit the targets' route passes through has its statement and every step realized by nodes (§6), and no reviewed statement leaves its unit's route without an established error (§5).
