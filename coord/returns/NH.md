

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

## lem-sfb-continuous-algcl-tame-boundary-comparison (2026-10-21 13:35 UTC, branch head 39dbfc86c5c)

L: independent stage-2 immutable head 39dbfc86c5c1: H1/H2/H11 + superseded. The S2-lane delivery 39dbfc86 is NH's stage-1 5-step split (status split, new proof/proof_deps/split_report, 2 new statement-only children) with no .lean file, no lean record, and a report without '## Worker report' or '## Second reading by NH'. H1: no Lean module, stage-1 node files instead. H2: item changed in proof/proof_deps/status/proof_origin/split_report/blueprint. H11: no stage-2 reading possible. NF 26a608e08's 8-step split passed review and landed live (LAND FIX MERGED 21:31:15, live node reviewed by NT-cc-NF-26a608e08) before this review began (21:32:40); a FIX would overwrite that reviewed split and add duplicate children. Correction: no re-delivery of the split; once the item is open for stage 2, deliver a Lean statement on the live base with a verbatim lean record, unchanged proof fields, and both report sections.

## lem-a1-finite-pullback-strict-tower-comparison (2026-10-21 19:20 UTC, branch head da39d42ea06)

L: independent stage-2 immutable head da39d42ea06e: H13 (F1): delivery da39d42e keeps the item Lean byte-identical to the returned head 7de42038, whose statement was checked clause by clause and is correct. Prior F1/F3 are fixed: lem-pur-integral-operations-well-defined is dropped from stmt_deps; def-a1-flat-term-kflat-complex, def-pur-integral-finite-pullback and def-a1-principal-completed-koszul-towers are cited; the new existing:true def-a1-integral-finite-pullback-tower is sound (canonical ∃!-characterized transition, fields follow H12). But both §1(B) records still rebind reviewed, sorry-free, general dependency nodes to an O_E-only special case on new sorry'd modules: def-weil-pbc-adic-coefficient-datum (Q44, AdicCoefficientDatum, general Noetherian A/I^n, 73 importers) → AdicCoefficientDatumIndependent.reductionPair (Classical.choice of sorry'd reduction_exists), with supporting_modules [AdicCoefficientDatumCompleted] dropped (the stage2 validator rejects the key on any rewritten record; the report wrongly says it is retained) and Q44's note replaced; def-weil-pbc-completed-pullback (Q99, PbcQbarCompletedPullback, 32 importers, node includes Rlim completion) → CompletedTowerPullbackIndependent.derivedPull (tower part only, 4 sorries, statement field 'def derivedPull'). A stage-2 fix cannot revert dependency records. Correction: deliver both dependency records byte-identical to live; put the CompletedTowerIndependent helpers in the item module (listed in its lean.declarations) or in a new §1(A) def node in sec-deligne-laumon-a1 cited from stmt_deps (appending to AdicCoefficientDatum is impossible: the helpers import the downstream IntegralOperationsWellDefined); correct the report. Advisory: the second reading is again a same-worker pass; list integralOperationsPullbackTransition_existsUnique in the new node's declarations; give derivedPull/reductionPair explicit types. No compile run (no file changed).
