

## lem-sf-proetale-flat-model (2026-10-14 18:18 UTC, branch head 37e0e2def1)

Errors E1, E4, and E7: the node changes the exact master theorem from arbitrary coefficient category Sheaf(X.ProEt) A to Mod(A_X), drops a ≤ b and bounded-constructibility hypotheses, and claims a stronger theorem. See review.md.

## def-amb-vector-integration (2026-10-16 00:14 UTC, branch head 300268e2e9)

The overlap proof relies on lem-amb-linear-trace-invariance, but the immutable baseline statement leaves A, N, the ordinary finite-etale twist, Noetherian base, and coefficient action unbound; it still points to the pro-etale coefficient definition. Thus the cited theorem does not license the finite ordinary-etale application (delivery-errors C4/E4). review.md records all source, route, dependency, edge-case, and construction checks.



## def-sf-datum (2026-10-16 04:53 UTC, branch head 8f8c601a85)

L (re-issued by the launcher; the entry had been lost): ge 1 --reviewer NT-Codex-NF-feff4537f --head feff4537f2e04d616a84a30efe5bba6921490df0 --spot-checked Read both nodes and all seven proof steps in full. Verified canonical exchange, double-evaluation signs, hypotheses, and unbounded torsion-coefficient scope against Stacks 0F7B/0F7H–0F7J and 08J9–08JA. No duplicate or delivery-introduced cycle found. Accepted eight declared tool uses. Concrete checks and unrelated baseline graph issues are recorded in review.md; no repairs needed. --verdict PASS

## lem-coef-finite-direct-image (2026-10-16 05:08 UTC, branch head d3b156aca3)

L: independent stage-2 immutable head d3b156aca378: Sheaf.Paper.ConstantCoefficientTensorPullback declares names that other modules already declare:
  AlgebraicGeometry.ProEtale.coefficientPullbackIso: also in WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
Import and reuse the existing declaration. Renaming yours only hides the collision and leaves the same fact proved twice; rename only when the two declarations say different things.

## lem-pur-finite-kummer-level (dedicated repair handoff)

The previous worker ended with: The literature re-review (2026-10-16) returned this split. Keep the route; fix exactly the finding below and re-deliver.

Compiler messages and attribution:
C4/E4: Step 6 claims that lem-pur-twist-sheaf-locally-free(4), specialized to E=Q_l, identifies L_T tensor^L_{(Z_l)_T} (Z/l^N)_T with its ordinary reduction. Clause (4) explicitly concerns derived reduction over the completed sheaf widehat{Z_l}_T, whereas Step 6 explicitly works over the constant sheaf (Z_l)_T. These are different rings; the cited statement supplies no such change-of-rings comparison. Prove the constant-coefficient assertion and canonical augmentation separately, for example with the two-term free resolution of (Z/l^N)_T over (Z_l)_T and injectivity of l^N on the inverse-limit Tate sheaf, or cite an applicable comparison node. Then justify the finite-direct-sum passage to A. The ordinary finite Kummer comparison and its base-change calculation are otherwise correct.

## def-weil-exceptional-adjoint-admissibility (dedicated repair handoff)

The previous worker ended with: The literature re-review (2026-10-16) returned this split. Keep the route; fix exactly the finding below and re-deliver.

Compiler messages and attribution:
E4/C4: The displayed restriction comparison U_{phi,X}F_A ≅ F_BU_{phi,Y} is not composable for U_phi:D(B)→D(A), and is not the statement of lem-sf-compact-support-restriction-of-scalars. Replace it by F_A U_{phi,X} ≅ U_{phi,Y}F_B (or its inverse), and form alpha and its mate from that typed comparison. B3: remove unused statement dependencies def-weil-integral-derived-reduction, lem-weil-integral-scalar-extension-well-defined and def-weil-ambient-exceptional-adjoint unless the definition actually invokes their additional data.



## prop-asd-smooth-base-change (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 1 (4395 characters); step 2 (4109 characters); step 4 (3769 characters); step 5 (2034 characters); step 7 (2683 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 1 (4395 characters); step 2 (4109 characters); step 4 (3769 characters); step 5 (2034 characters); step 7 (2683 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## lem-sfb-wcontractible-constant-reductions-ml (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 1 (2366 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 1 (2366 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.

## thm-coef-integral-verdier (2026-10-17 23:32 UTC, branch head de5fb5ad3e)

L: independent stage-2 immutable head de5fb5ad3e80: A7/A6: re-push after the Q145 merge (deliveries.log 2026-10-17T23:15Z, PASS) and after NA's claim was retired (ledger 36466). Lean byte-identical to the landed file except one added module-docstring sentence; nt_compile --json of the delivered IntegralVerdier.lean: rc 0, 27.1 s, no errors or warnings. H11/H1: the report is Q145's report with the group name replaced; the 'Second reading by NA' is Q145's self-reading, and it claims a DeltaRestriction repair and compile runs that are not in NA's commit. H2: lean.by/date rewritten from Q145/2026-10-17 to NA/2026-10-18 while Q145's reviewed_lean is kept. No mathematical fault (statement = landed Q145 version). Correction: withdraw the delivery and delete the branch; keep the landed record; nothing to re-deliver.

## lem-per-finite-quotient-cochain-colimit (2026-10-19 01:50 UTC, branch head c24a1f6ddcf)

Off-route: the human's route decision of 2026-10-19 dropped this item. /home/ubuntu/weil-newtargets/coord/route-pivot-dropped.txt, section '2026-10-19 artin-gabber', lists the item itself at line 1572 and its only citer lem-per-procyclic-torsor-tower-descent at line 1811. Its blueprint via chain is dropped too: semistable-coordinate-divisor-purity (1901), monomial-trait-punctual-purity (1718), log-smooth-trait-punctual-purity (1706) and gabber-regular-pair-purity (1609). The chain ends in lem-per-qbar-middle-tstructure, which coord/repair-notes/lem-per-artin-gabber-affine-curve.json removes by name. No target reaches the node and no repair can put it back on a route, so I return it as with the other dropped items (Q159, Q110, Q26, Q86, Q35); the maintainer should withdraw it from dispatch. No split fault is claimed. I read the mathematics in full and it is sound. The differential and d^0 match Stacks 0DVG (etale-cohomology.tex section-continuous-group-cohomology, l.9008) and lem-exc-cochains-derived-invariants. Step 1: the module structure on the filtered set colimit over N is elementary, and the action is well defined without injective transitions. Step 2: Q_r is finite and G^a is profinite (Tychonoff 08ZU, basis W^a). Step 3: the stabilizer lemma on G^a, then W = the intersection of the e_i^{-1}(V), with W^a in V, U_t in W and h = g(g^{-1}h). Steps 4-6: the cocone, surjectivity by finitely many representatives, and injectivity by eventual zero over the finite domain Q_r^a. Step 7: the term-by-term differential check uses equivariance. Step 8: naturality. Small cases checked: trivial G, zero transitions, Z_l with constant A, infinite N_r, a=0. It is not a duplicate: det-base-field-cd-cochains (3) has fixed coefficients and lem-sc-group-cohomology-filtered-union is about inclusions. No SGA citations. No fixes written.

## lem-weil-pbc-residue-perfect-finite-quotient-models (2026-10-20 20:11 UTC, branch head 1edabf9b81)

L: independent stage-2 immutable head 1edabf9b815b: H3 R1: the predicate ResidueFiniteQuotientModel asks for a single constant finite-projective model on the whole chart V, with no étale cover, while the node, its proof steps 1/4 and Stacks 09C2 ask only for étale-local models. The conclusion is then false: X=V=Spec Q, A=Z_p, n=0, [0,0], M the rank-one sheaf of a character trivial mod p but not mod p^2; M_0 is constant Z/p but M_1=Z/p^2(chi) has H^0=pZ/p^2, so it is not constant on V. Correction: quantify over an étale/pro-étale covering of (toProEt X).obj V, with a complex in [a,b] and an iso per piece (cf. HasEtaleLocalConstantProjectiveModel in the PASSed 5464e50d). H3 R2: the uniform-propagation clause of the node's statement and title (residue cover => one interval per chart for every level, by induction) is missing; add it as a second sorry'd declaration with a docstring. Otherwise: no hollow defs, sorry-only, docstrings, universes and edge cases ok, report sections present, lean.statement verbatim. Live record is null (module withdrawn), so no H4 collision. Advisory: residueLisseConstantComparison's owner lem-weil-pbc-residue-lisse-perfect-lift is not in stmt_deps. Maintainer: citer finite-perfect-adic-realization refers to removed declarations and lacks this stmt_dep. No compile run (substance RETURN).
