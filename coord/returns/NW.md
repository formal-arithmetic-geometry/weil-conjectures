

## lem-sbc-composite-fibre-local-models (2026-10-14 17:39 UTC, branch head 934fa789b6)

L: approved by the reader, but the landing refused it: NOT MERGED lem-sbc-composite-fibre-local-models: lem-sbc-composite-fibre-local-models: no longer stage-1-open; live completion takes priority Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-weil-proetale-surjective-tower-derived-limit (2026-10-15 23:04 UTC, branch head 4c7df00d82)

L: the delivery could not be prepared for review: NOT MERGED lem-weil-proetale-surjective-tower-derived-limit: the report lacks the heading '## Review by NW' (the group's own review) Repair what this says (the report needs the sections the brief lists) and push again.

## cor-pur-vector-bundle-purity (2026-10-17 19:35 UTC, branch head e6d4950c3d)

L: independent stage-2 immutable head e6d4950c3d99: H3: vector_bundle_purity only asserts that some iso pi^!K ≅ Lpi^*K(r)[2r] exists; the extra clause 'beta K = alpha' is vacuous. The canonical alpha = gamma^{-1} (mate via PurityFiniteSetting.counit of (1⊗t_pi)∘PF^{-1}, t_pi = Etale.vectorBundleIntegration) is not defined. The base-change, direct-sum, adjunction, omega_pi ≅ Lambda_E(r)[2r] and finite-reduction clauses are all missing. The hypothesis K ∈ D^b_ctf is dropped and the claim is made for every unbounded K. Correction: define alpha as real data, prove it is an iso natural in K for K in D^b_ctf, and add each compatibility clause, adding any missing mate or projection helper under §1(A)/(B). H8: theorem docstring lacks the 8 proof steps; 'source' abbrev docstring lacks source place and blueprint tag. H1/H11: '## Second reading by NW' is empty boilerplate. Checked fine: only the lean field changed and its statement is verbatim; recorded PurityFiniteSetting and VectorBundleZeroSection used directly; no hollow defs; sorry-only proofs; pro-etale site, no substitute; universes u/u+1; r=0 and empty base covered; nt_compile.py per-file compile clean (8.4 s, no diagnostics).

## lem-pur-derived-complete-koszul-reconstruction (2026-10-17 20:53 UTC, branch head c4e59e9784)

L: independent stage-2 immutable head c4e59e9784bf: --apply-fixes: coord/reports/NW/lem-pur-derived-complete-koszul-reconstruction.md: a stage-2 fix is only DIR/<basename of a module>.lean (DerivedCompleteKoszulReconstruction.lean), DIR/lem-pur-derived-complete-koszul-reconstruction.lean-record.json, DIR/lem-pur-derived-complete-koszul-reconstruction.statement-change.json, DIR/<new node id>.json (no new node), DIR/lem-pur-derived-complete-koszul-reconstruction.report.md or a new module DIR/lean/Sheaf/<Topic>/<Name>.lean

## lem-per-algebraic-field-dualizing-shift (2026-10-19 01:49 UTC, branch head 63aebf34d27)

Route-pivot RETURN; the maths is not at fault. The mechanical finding holds: Steps 1 and 4 and the statement (as a stmt_dep) cite def-per-algebraic-normalized-dualizing. That node is in coord/route-pivot-dropped.txt, 2026-10-19 artin-gabber section, at line 1368, and no step justifies using it. More decisively, the item itself is dropped (line 1413). So is its only citer, lem-per-algebraic-local-dualizing-normalization (1415). Its whole blueprint via chain is dropped too: local-cohomology-top-nonvanishing 1680, normal-top-residue-class 1753, potential-dualizing-uniqueness 1779, qbar-generic-duality-model 1839, qbar-middle-tstructure 1840. That chain is the Q144 Qbar_l duality and middle t-structure route, which coord/repair-notes/lem-per-artin-gabber-affine-curve.json forbids ('the Q144 split (5ea9835359) that did so is dropped ... the review rejects citations of it'). The finite-coefficient 5-step plan does not reach this node. The report does not mention the route pivot. I read all 5 steps in full and they are correct: the 08JA one-object-site End = k step, the field splitting with its Hom bijection, the degree projection, the basis projection and s = -n. I checked K = 0, two nonzero degrees and k^2 over F_2. Both tool_uses are generic and acceptable, there are no new nodes, and no SGA source is cited. None of this can be landed, and a FIX cannot repair a dropped item. Maintainer: withdraw the item from dispatch.

## lemma-nagata-strict-chart-map-kernel (2026-10-21 08:00 UTC, branch head 6418af0b72b)

L: approved by the reader, but the landing refused it: NOT MERGED lemma-nagata-strict-chart-map-kernel: lemma-nagata-strict-chart-map-kernel: completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it) Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.
