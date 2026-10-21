

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

## lem-sfb-bounded-bifunctor-devissage (2026-10-21 11:20 UTC, branch head d4ae18616d6)

Superseded (A7/B10), and C5/D1 on the new node. The live item lem-sfb-bounded-bifunctor-devissage already has reviewed (NF 58701bbdc PASS), reviewed_lean (Q34 PASS) and reviewed_proof (H2 COMPILER pass, landing 20261021T061203, 06:12Z). Its module lean/Sheaf/CategoryTheory/DerivedCategory/BoundedBifunctorDevissage.lean has 0 sorry. The repair note this delivery answers is the generic batch re-split text in weil-conjectures-sheaf/coord/repair-notes, mtime 13:04:49 +0800 (05:04Z). That is before the stage-3 landing, and no later human decision for this item exists. Q20 90d757505 delivered the same re-split earlier and was RETURNED as superseded (A7/B10/C5; svc.log 15:17, landing recorded the RETURN at 16:21 +0800). This NH head is the second push on the same stale note. Merging would overwrite the proof that matches the Lean and would put closed work back in the queue. Mathematics, read in full against Stacks derived.tex Tag 08J5 (lines 4075-4107): the statement is unchanged. Step 1 handles zero objects through strict fullness. Steps 2 and 3 apply the one-variable criterion correctly to B(F[0],-) with M and to B(-,M) with K, with the zero and A0/B0 case splits. Nothing from the base proof is lost, there is no cycle and there is no SGA citation. The new node lem-sfb-bounded-functor-cohomology-devissage is true: the truncation-triangle induction works, H^q[-q]=(H^q[0])[-q] goes through the shift comparison and shift closure, and I checked acyclic L, single-degree and gapped cases. However, it is a one-line specialization of the existing split node lem-sfb-degreewise-bounded-devissage. Take Q(X) := G(X) in S, which is iso-invariant, contains 0 and is extension-closed, and P_q(M) := G(M[0]) in S. Then Q(M[0][-q]) holds by shift closure. The report itself concedes this (C5/D1). No fixes. Maintainer: retire the stale 05:04Z repair note, which the H2 landing at 06:12Z resolved.
