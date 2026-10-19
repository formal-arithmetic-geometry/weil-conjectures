

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

## lem-pur-vector-integration-site-comparison (2026-10-18 10:30 UTC, branch head b4a72165a0)

L: independent stage-2 immutable head b4a72165a0ea: H5/H3: VectorIntegrationSiteComparisonSpec is defined as `P = P ∧ hr = hr`, a tautology that states none of the node's clauses (tau_T and its naturality; beta_q C_S(b_q^e)=b_q^p, t_q^p beta_q=C_S(t_q^e), t_q^p h_q^p=1; j_! counit comparison; beta_pi and t_pi^p beta_pi=C_S(t_pi^e); for all K in D^b_ctf the projection-map and a_K comparisons and eta^p_{C_S K}=C_V(eta^e_K); purity inverse; r-independence). H4/H13: only PurityFiniteSetting and the VectorBundleZeroSection module are imported; VectorBundleZeroSection.scheme is never formed (the bundle is a bare locally free F), and no other recorded stmt_dep declaration is used (siteComparisonDerivedPullbackPlus, cartier_kummer_map, projectiveLineTrace, fixedComparisonDirectImageMatePlus, vectorBundleIntegration, sfIntrinsicCompactSupport, openImmersionLowerShriekComparison_coherence, vectorBundlePurity, finiteTorConstructible, ...). H11: the second reading did not notice the tautology. Binders are otherwise fine (finite type over Spec k, no separatedness, d>=0, l^r=0, universes bound, lean.statement verbatim). Compiles clean via nt_compile --json (4.6 s, exit 0). Correction: state every clause over the recorded dependency declarations, using the recorded vector-bundle object; build missing pro-etale maps (t_q^p, t_pi^p, beta_pi, eta^p) in this delivery as helpers, §1(A) def nodes or §1(B) dependency repairs, with no arbitrary map or Nonempty; redo the second reading clause by clause.

## prop-pur-rational-purity-trace-coherence (2026-10-18 21:40 UTC, branch head b41005e365)

L: independent stage-2 immutable head b41005e365c4: H3 F1: trace/composition/baseChange fields universally quantify arbitrary G, γ, adj, γQ (not the canonical family) and are false: rescaling γ_L by 2 for E<L on a nonzero object breaks PbcPurityTransitivity and pbcPurityTraceEquation; a non-identity automorphism of γQ breaks PbcPurityDescent. H3 F2: 'composition' is coefficient-tower transitivity for one f (no g, no c_{g,f}); 'baseChange' is coefficient descent (no Cartesian square, no Ex^{!,sm}); thm-pur-composition-coherence and thm-pur-smooth-base-change-coherence are unused. H5/H12 F3: new def node def-pur-pbc-rational-purity-data is the theorem statement PbcRationalPurityConclusion of prop-pur-rational-purity-transitivity-summands under a new name, and rationalPurity re-asserts it; it is existential and pins nothing. Correction: drop the def node; state the item existentially over the canonical (G, γ, adj, γQ) with the trace equation; add rational and Qbar composition coherence (f, g, rational c_{g,f}) and base-change coherence (arbitrary Cartesian square, rational Ex^{!,sm}), supplying those comparisons in the same delivery if they have no declaration. Both files compile (nt_compile --json, 4.2 s and 6.7 s, no errors).
