

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

## lem-sfb-gabber-global-snc-alteration (2026-10-21 21:20 UTC, branch head 8182e6dc88a)

This is the 12th push of lem-sfb-gabber-global-snc-alteration; the 11 earlier pushes (NV, NF×3, NL×2, NB, NH, NC, NI×2) were all RETURNed. The drop list (side-live coord/route-pivot-dropped.txt, mtime 2026-10-19 21:37) is unchanged, and no repair note exists for this item or for the dropped chain. I checked ILO X Thm 2.1, Lemma 2.2 and proof 2.3 Steps 1-3 (pp.148-152). Steps 1-6 follow that proof faithfully, and the maths is sound, including the componentwise good-orbit Sylow selection, the H=D/I compatibility, the union-of-components SNC argument and the disjoint-union projectivity. Edge cases checked: empty X or Z, dim 0, disconnected X, nonfaithful action, imperfect k. Faults: (C1/F) Step 4 cites dropped lem-per-very-tame-boundary-quotient-cartier (drop list line 1982, artin-gabber section) for the essential Q-Cartier/union-of-components claim, and no live node replaces it. (C5/B9) All four new sfb nodes re-create dropped nodes under new ids, which works around the drop: equivariant-field-alteration-presentation is X 2.2 plus Y/G existence (1518/1815/1814); sylow-alteration-good-components asserts that Y_0/L exists and is projective (1814); field-log-smooth-equivariant-modification is X 1.1 plus the log-smooth quotient (1604/1946); field-log-smooth-snc-resolution is VIII 3.4.9 plus 4.1 (1699/1734/1603). (G4) The report calls 1982 'existing' and lists dropped ids as 'Not duplicates', with no mention of the drop or of the previous RETURNs. Batch-5 flags: the trf/per log definitions (SNC boundary, log regular pair, fs log blowup, fs-log-smooth-etale, fs-log-group-action) and lem-trf-h-projective-composition are generic and are not steps of the trace formula or of Poincaré duality, so I accept them. No SGA source is used. Maintainer: this is a dispatch loop. Either un-drop the ILO X/VIII alteration chain (1518, 1598, 1603, 1604, 1699, 1734, 1814, 1815, 1946, 1982) or withdraw this item and its citer nested-open-regular-alteration.
