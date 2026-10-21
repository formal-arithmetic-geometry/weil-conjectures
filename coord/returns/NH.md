

## lem-weil-pbc-ringed-projection-mate-exact (2026-10-15 12:16 UTC, branch head e5561d1610)

L: independent stage-2 immutable head e5561d1610ee: the dependency node def-pc-kflat-complex: its `lean` changed on newtargets-dag since the delivery's base ({"module": "Sheaf.Algebra.Homology.KFlat", "declaration": "CochainComplex.IsKFlat", "file": "lean/Sheaf/Algebra/Homology/KFlat.lean", "statement": "def IsKFlat (K : CochainComplex (SheafOfModules.{w} ); the reviewer decides and the group re-pushes

Launcher: Sheaf.Algebra.Homology.KFlat now provides IsKFlat, IsKFlatResolution, and the independent-coefficient predicates; import it instead of changing it.

## lem-exc-proetale-cartesian-open-injective-acyclic (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 2 (3129 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 2 (3129 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## det-lem-int-ext-formula (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 3 (2316 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 3 (2316 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are; the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## det-prop-sfb-qlbar-colimit-x-pullback (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 2 (2335 characters); step 6 (2086 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 2 (2335 characters); step 6 (2086 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are; the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.

## lem-zl-bertini-independent-functions (2026-10-17 19:35 UTC, branch head e6ce72aa48)

L: independent stage-2 immutable head e6ce72aa48b7: Head e6ce72aa48b7 is a stage-1 split (commit 'Split lem-zl-bertini-independent-functions'; base node was unsplit with no proof), not a stage-2 statement delivery. H1: no .lean module, no lean record on the item, no '## Worker report' (stage-1 '# Worker report' heading) and no '## Second reading by NH'; the report says no Lean file was written or compiled. H2: item changed in status/proof/proof_deps/proof_origin/created/split_report, and stmt_deps grew by two statement nodes. H12: the new nodes lem-zl-bertini-fibre-dimension-bound and lem-zl-bertini-closed-point-component are unsplit statement nodes with no module. H11: no second reading. A: the report lists citations.json, which is not in the commit. The split's mathematics matches Stacks 0G4E (statement and steps 1-5; dropping 'in no other component' is harmless), but it belongs in stage-1 review. Nothing to compile. Correction: route the split through stage 1; then deliver stage 2 as one commit with a lean/Sheaf module stating 0G4E with sorry, source/blueprint/proof-step docstrings, a lean record with verbatim statement, '## Worker report' and '## Second reading by NH', and a clean per-file compile.







## lem-weil-pbc-formal-exact-projection-mate (dedicated repair handoff; head d17261b201a63e9843bb11669006577f9c7ee34c)

The previous worker ended with: re-split (decision of the human, 2026-10-21): the proof in words is 4869 characters, far too much work for one node. The purpose of this re-split is to SPREAD THE WORK so that many workers can start on it at once: cut the proof into new nodes, each a separate argument with its own self-contained statement, delivered statement-only (status unsplit, source, three kinds of Mathlib search, no proof steps: other workers write their proofs in parallel), cited by the step that uses it. This node keeps its statement; its proof becomes the short assembly of the new nodes, at most 3000 characters, and the delivery adds at least 1 new node(s), of comparable size, not one node that restates the whole. Do NOT shorten, summarise or blur the existing argument: every argument the old proof carries must reappear as a new node. A shorter text without the new nodes is the worst answer and is returned. Lean module: Sheaf.CategoryTheory.FormalExactProjectionMate

Compiler messages and attribution:
re-split (decision of the human, 2026-10-21): the proof in words is 4869 characters, far too much work for one node. The purpose of this re-split is to SPREAD THE WORK so that many workers can start on it at once: cut the proof into new nodes, each a separate argument with its own self-contained statement, delivered statement-only (status unsplit, source, three kinds of Mathlib search, no proof steps: other workers write their proofs in parallel), cited by the step that uses it. This node keeps its statement; its proof becomes the short assembly of the new nodes, at most 3000 characters, and the delivery adds at least 1 new node(s), of comparable size, not one node that restates the whole. Do NOT shorten, summarise or blur the existing argument: every argument the old proof carries must reappear as a new node. A shorter text without the new nodes is the worst answer and is returned. Lean module: Sheaf.CategoryTheory.FormalExactProjectionMate
