

## lem-weil-pbc-normal-algebra-separable-scalar-extension (2026-10-14 17:40 UTC, branch head 4f6b801bdf)

L: approved by the reader, but the landing refused it: NOT MERGED lem-weil-pbc-normal-algebra-separable-scalar-extension: lem-weil-pbc-normal-algebra-separable-scalar-extension: no longer stage-1-open; live completion takes priority Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## def-weil-pbc-four-arrows (2026-10-16 02:37 UTC, branch head 6e57613ce8)

L: independent stage-2 immutable head 6e57613ce829: Review written to review.md. All three modules compile cleanly and the arrow formulas match. H13/§1 dependency gap: state the full unattached lemma-weil-pbc-perfect-projection-formula in the same delivery; the finite-level invertibility helper does not cover its remaining clauses.

## lem-kun-geometric-reduced-perfect (2026-10-16 08:03 UTC, branch head e791a88d80)

L: approved by the reader, but the landing refused it: NOT MERGED lem-kun-geometric-reduced-perfect: lem-kun-geometric-reduced-perfect: no longer stage-1-open; live completion takes priority Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.



## lem-cbc-rational-compact-support-coefficient-coherence (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 4 (3073 characters); step 6 (3595 characters); step 9 (3143 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 4 (3073 characters); step 6 (3595 characters); step 9 (3143 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are; the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.

## lem-pur-site-comparison-edge-section (2026-10-17 18:20 UTC, branch head e53ceadaec)

L: independent stage-2 immutable head e53ceadaec0f: file-only compilation failed: sandbox Sheaf/Stage2/Sandbox0.lean
timeout after 60 s: the fault is usually a definition that is expensive to unfold, not the limit

## lem-zl-bertini-field-extension (2026-10-17 19:35 UTC, branch head 01fd606bf5)

L: independent stage-2 immutable head 01fd606bf525: Commit 01fd606 is a stage-1 split (message 'Split lem-zl-bertini-field-extension') delivered in the stage-2 lane: it fills the item's proof, proof_deps, proof_origin, mathlib_searches and split_report, and adds six lem-zl-bertini-* statement nodes with no lean record. H1: no lean/Sheaf module, no lean record on the item, and no '## Worker report', '## Second reading by NG' or '## New nodes' in the report (only the stage-1 '## Review by NG'). H2: the item is changed in fields other than lean and stmt_deps. H12: the new nodes are lemma nodes used only by the proof, not definition nodes. No Lean declaration exists, so H3-H10 and the compile cannot be checked; nt_compile.py was not run (no .lean file). Minor stage-1 points: citations.json is claimed in the report but absent from the commit; stray '$' in step 1's source place; doubled '$$' in step 2; step 2's source place calls 037J and 030N Algebra tags and omits 037N. Correction: re-deliver the split through the stage-1 lane, or deliver the actual stage-2 Lean statement of Tag 0G4D (lean-only change to the item, sorry proof, docstrings, verbatim lean.statement, clean per-file compile, Worker report and Second reading) on top of an accepted split.

## lem-wf-curve-kummer-jacobian-tate-module (2026-10-17 22:24 UTC, branch head 04978822af)

L: independent stage-2 immutable head 04978822afb4: --apply-fixes: coord/reports/NG/lem-wf-curve-kummer-jacobian-tate-module.md: a stage-2 fix is only DIR/<basename of a module>.lean (CurveKummerJacobianTateModule.lean), DIR/lem-wf-curve-kummer-jacobian-tate-module.lean-record.json, DIR/lem-wf-curve-kummer-jacobian-tate-module.statement-change.json, DIR/<new node id>.json (no new node), DIR/lem-wf-curve-kummer-jacobian-tate-module.report.md or a new module DIR/lean/Sheaf/<Topic>/<Name>.lean

## lem-trf-elementary-semistable-chart-globalization (2026-10-19 04:02 UTC, branch head 3668b7bcb7)

L: approved by the reader, but the landing refused it: NOT MERGED lem-trf-elementary-semistable-chart-globalization: lem-trf-elementary-semistable-chart-globalization: completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it) Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-weil-pbc-pulled-reduction-strict-tower-comparison (2026-10-21 09:02 UTC, branch head da9b673d70a)

L: independent stage-2 immutable head da9b673d70a6: H3 / arbitrary-map rule: `insertion` uses (proEtaleModuleInverseImage_canonicalUnitComparison g _).choose.unit. That theorem is a bare ∃ adjunction with an iso abelian adjunct, which is non-unique: any natural automorphism φ of the inverse image (e.g. -1) gives another. IsOrdinaryNormalized (s) and IsStrictNormalized (e) are stated through insertion, so s, e, δ and τ are pinned only up to φ; a consistently twisted family satisfies every clause, so τ_n is not asserted to be the node's canonical composite. Repair: use a canonical unit, either (a) §1(B) make the private ProEtaleOperations.proEtaleModuleInverseImageAdjunction public, (b) rebuild it in the item module (model equivalences + SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit g R), then ofNatIsoRight), or (c) pin insertion by an ∃! section formula; then recompile. Mechanical finding: the stmt_dep on lem-weil-pbc-ordered-exchange-coefficient-comparison is genuine (OrderedExchange.lambda = .choose of lambda_existsUnique, used in ρ), PASS on that point; def-sp-constant-reduction-models is an existing def node owning reduction, augmentation and unit, accepted. All other clauses match the node (N, H_•, R(N), τ pinned via an invertible targetCounit on K-flat P, augmentation, ρ = λ then inverse Rlim τ, Res(p_n^H) = τ_n p_n ρ, η), as do the edge cases and the records; the statement is verbatim and the dep records are unchanged. Advisories: the p_n η = u_n clause is a naturality tautology; completedRlim owner def-pur-completed-rlim-functor not cited; proof-only imports; overlap with NZ re-split / NO roos nodes. No compile run (no file changed); worker reports a clean 44.7 s server compile.
