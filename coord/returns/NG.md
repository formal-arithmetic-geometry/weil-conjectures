

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

## lem-sfb-finite-etale-trace-image (2026-10-21 04:13 UTC, branch head 0e8accd4a5)

L: independent stage-2 immutable head 0e8accd4a547: H2: stmt_dep lem-weil-pbc-continuous-coefficient-pullback-composition (added by this delivery) supplies only the plain defs continuousCoefficientDirectMap, continuousCoefficientMap and integralRationalCoefficientMap of Sheaf.AlgebraicGeometry.ContinuousCoefficientPullback (no .choose, the theorem's proof is not needed, no def node owns them). Correction: a definition node owning that module's definitions (e.g. def-sfb-continuous-coefficient-pullback-maps, existing:true record listing them), cited by the item instead of the theorem, or inline the two maps; lem-weil-pbc-continuous-ring-functions-sheaf is a genuine dependency (continuousCoefficientSheaf packs continuousMapPresheafCommRing_isSheaf), PASS on that point. H3: `∃! τ, TraceImageLocalSums τ ∧ ∃ N, …` restricts uniqueness to maps that also satisfy the image clause; restate as `(∃! τ, TraceImageLocalSums τ) ∧ ∀ τ, TraceImageLocalSums τ → ∃ N, …`. Advisory: TraceImageSplitting restates def-weil-pbc-finite-etale-trace-splitting-data (FiniteEtaleTraceSplitting): reuse it or justify; the Paper.ContinuousIntegralCoefficients import is unused in the statement. Otherwise every clause matches (continuous A/E sheaves, canonical pullback via the unit, sheaf image and sheaf sum by covering sieves, all splittings over the whole slice, J empty allowed); statement verbatim, one sorry, docstrings complete, only the item node changed. Compile not reproducible: the published build /home/ubuntu/weil-conjectures-sheaf/lean/.lake/build is missing (nt_compile: 'Live published library is unavailable', twice).
