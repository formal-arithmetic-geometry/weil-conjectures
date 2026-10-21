

## cor-weil-pbc-constructible-complete (2026-10-14 17:36 UTC, branch head 40b0c1885a)

Returned for C4/E1 and E5: step 3 does not establish the exactness hypotheses required by lem-pur-left-derived-exact-when-defined, so the ordinary triangulated restriction is unproved; the new shift node is an additional unproved compatibility theorem. Both new nodes also fail B7 search completeness (no LeanSearch record) and required created metadata. The custom integral uniform-tower coefficient category is not identified with the exact master target's condensed E coefficient category and bounded-constructible functor.

## lem-weil-absolute-frobenius-well-defined (2026-10-15 21:41 UTC, branch head d57601cf80)

L: approved by the reader, but the landing refused it: NOT MERGED lem-weil-absolute-frobenius-well-defined: coord/.merge.lock held for 120 s by pid 2178981: /usr/bin/python3 tools/merge_delivery.py return NF def-weil-ambient-exceptional-adjoint L: approved by the reader, but the landing refused it: NOT MERGED def-weil-ambient-exceptional-adjoint: coord/.merge.lock held for 120 s by pid 2157422: /usr/bin/python3 tools/merge_delivery.py N5 lem-weil-compact-support-representative-independence --stage 1 --reviewer NT-Codex-N5-c51ccab3c --head c51ccab3c4892dbaed876d402eef0c6af0e64211 --spot-checked Read the item, new node, cited statements and source p Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## cor-sf-direct-image-ctf-etale-origin (2026-10-16 01:38 UTC, branch head f72d5a2bb5)

L: approved by the reader, but the landing refused it: NOT MERGED cor-sf-direct-image-ctf-etale-origin: cor-sf-direct-image-ctf-etale-origin: no longer stage-1-open; live completion takes priority Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## def-amb-vector-integration (2026-10-16 07:38 UTC, branch head 85348b87c8)

L: the delivery could not be prepared for review: NOT MERGED def-amb-vector-integration: the report lacks the heading '## Review by NE' (the group's own review) Repair what this says (the report needs the sections the brief lists) and push again.


## lem-pur-finite-kummer-level (dedicated repair handoff)

The previous worker ended with: The literature re-review (2026-10-16) returned this split. Keep the route; fix exactly the finding below and re-deliver.

Compiler messages and attribution:
C4/E4: Step 6 claims that lem-pur-twist-sheaf-locally-free(4), specialized to E=Q_l, identifies L_T tensor^L_{(Z_l)_T} (Z/l^N)_T with its ordinary reduction. Clause (4) explicitly concerns derived reduction over the completed sheaf widehat{Z_l}_T, whereas Step 6 explicitly works over the constant sheaf (Z_l)_T. These are different rings; the cited statement supplies no such change-of-rings comparison. Prove the constant-coefficient assertion and canonical augmentation separately, for example with the two-term free resolution of (Z/l^N)_T over (Z_l)_T and injectivity of l^N on the inverse-limit Tate sheaf, or cite an applicable comparison node. Then justify the finite-direct-sum passage to A. The ordinary finite Kummer comparison and its base-change calculation are otherwise correct.

## def-coefficient-twists-detailed (2026-10-17 04:15 UTC, branch head c1430181ea)

L: independent stage-2 immutable head c1430181ead3: H4/H3: the new rational and common-stage twist functors (rationalComplexTwistFunctor, algebraicClosureComplexTwistFunctor), their scalar comparisons, and the integral constructibility theorems use the old finite-field categories (boundedConstructibleDerivedCompleteIntegral D, rationalConstructibleCategory D, rationalScalarExtension, AlgebraicallyClosedCoefficients.*). These records were invalidated by maintenance Q22/N7 and are not the recorded declarations of def-weil-derived-complete-integral-detailed (sfIntegralConstructible), def-weil-rationalization-karoubi (sfRationalConstructibleCategory) or def-weil-algebraically-closed-coefficients (generalAlgebraicallyClosedConstructibleCategory). No published identification between the old and new categories exists (grep over the side tree), so consumers citing those nodes cannot use the functors. Correction: build the integral, rational and common-stage functors and CoefficientTateTwistData on the recorded sf/General categories, normalize comparisons against sfRationalScalarExtension and its unit/associator and the General stage system (old helpers may stay as extra declarations), and redo the consumer validation. Otherwise checked: hypotheses D/ℓ/hℓ/E/S and invertibility, n-1 indexing, purTwist reuse, rank instances, signed powers m=0/>0/<0, finite and integral derived twist, no hollow definitions (every choice is pinned by an exists-unique formula), docstrings, report sections. nt_compile (local overlay): exit 0, 18.7 s, only sorry warnings, no line over 100 characters.


## lem-amb-relative-torsor-cohomology (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 10 (4817 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 10 (4817 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## thm-pur-affine-line-orientation (2026-10-17 20:36 UTC, branch head 3e743f7ff3)

L: independent stage-2 immutable head 3e743f7ff3fb: --apply-fixes: coord/reports/NE/thm-pur-affine-line-orientation.md: a stage-2 fix is only DIR/<basename of a module>.lean (no module), DIR/thm-pur-affine-line-orientation.lean-record.json, DIR/thm-pur-affine-line-orientation.statement-change.json, DIR/<new node id>.json (lem-pur-supported-hom-pullback-natural), DIR/thm-pur-affine-line-orientation.report.md or a new module DIR/lean/Sheaf/<Topic>/<Name>.lean

## lem-zl-shriek-composition (2026-10-17 22:08 UTC, branch head 3f6b4c67b9)

L: independent stage-2 immutable head 3f6b4c67b95c: H3/H13: replace the derived Weil-sheaf interface with the node's fixed-pair/common-stage category and re-deliver.




## lem-pur-finite-smooth-gamma-normalization (2026-10-17 23:35 UTC, branch head b3cbc5b38a)

L: independent stage-2 immutable head b3cbc5b38afc: This is a stale duplicate of an item already landed at stage 2: Q17's statement merged 2026-10-17 23:22 with reviewer PASS, and NE's claim was retired 2026-10-18 07:24:49, before this 07:29:18 commit. Against the commit before it, the delivery only adds one docstring line ('rechecked by group NE') to Q17's module and changes the node's lean.by from Q17 to NE, plus a report. H2: the lean record would falsely credit NE with Q17's declaration (the file header still says Authors: Q17; reviewed_lean is Q17's). H11: the 'Second reading by NE' section is the worker rereading its own delivery, with no clause match. Substance checked independently and correct: the N normalization copies the etaleSupportMapCompatibility equations (minus one conjunct, which only weakens the hypothesis); Coeff is Z/l^n lifted to u+1; G is unique via existsUnique_normalized and the Prop class HasCompactification; factor (i) is the dualizing base-change mate pulled back along the diagonal; hypotheses are no stronger than the node's and edge cases are not excluded. nt_compile --json rc=0, 10.6 s, no warnings. Correction: withdraw the delivery; nothing needs to be re-delivered, and any future touch must keep lean.by Q17 and add no authorship docstring.

## lem-sf-compact-support-proper-image-tower (2026-10-21 04:10 UTC, branch head 1c88d63d9d)

L: approved by the reader, but the landing refused it: NOT MERGED lem-sf-compact-support-proper-image-tower: local changes on the delivery's files, resolve first: M dag/nodes/sec-smooth-purity/lem-sf-compact-support-proper-image-tower.json Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-weil-pbc-finite-field-stratified-perfect-models (2026-10-21 08:46 UTC, branch head a2f52894c00)

L: approved by the reader, but the landing refused it: NOT MERGED lem-weil-pbc-finite-field-stratified-perfect-models: lem-weil-pbc-finite-field-stratified-perfect-models: completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it) Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-sfb-etale-stalk-constant-complex-exactness (2026-10-21 08:53 UTC, branch head 3da47abf31b)

L: independent stage-2 immutable head 3da47abf31bc: H2/H12: stmt_deps add theorem node lem-cbc-constant-ring-module-sheaves, but the Lean statement uses only the plain def CategoryTheory.constantRingModuleRestriction (lines 66, 171, 181; not a .choose) from its module Sheaf.CategoryTheory.ConstantRingModuleSheaves. The DAG already has definition node def-sfb-constant-ring-module-restriction (existing:true, same module, declarations constantRingModuleRestrictionPresheaf/constantRingModuleRestriction, universes match). Correction: replace lem-cbc-constant-ring-module-sheaves with def-sfb-constant-ring-module-restriction in the item's stmt_deps and in the report; Lean module unchanged. Everything else checked and correct: S = restriction ⋙ pointSmallEtale.sheafFiber, which is literally the pointedEtaleStalkDiagram colimit; c = recorded siteConstantModuleFunctorGeneral; additivity; finite-limit/colimit exactness; natural H^n isos for all n in ℤ; acyclicity and QuasiIso preservation; η pinned by pointedEtaleGerm of the sheafification unit at (𝟙 T, t); ε normalized on SheafOfModules.unit; no finiteness or bounds; A : Type (u+1) is the recorded size convention; edge cases A=0, empty T, T=Spec Ω, unbounded complexes; docstrings carry the source place, blueprint id and steps 1-6; all theorem proofs sorry, no hollow defs, both report sections present. No compile: no file changed (2026-10-21 instruction); the worker reports a clean scompile.
