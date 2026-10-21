



## thm-amb-p1-decomposition (2026-10-16 04:53 UTC, branch head 11be63537e)

L (re-issued by the launcher; the entry had been lost): Major exact-target mismatch: the master source uses pro-etale A_{E,n}/completed coefficient objects, while delivery changes to ordinary-etale finite A with added N hypotheses. Resolve and record this target correction upstream before resubmission (B9, E7).

## det-pe-topos-functoriality-inverse-image (2026-10-16 17:57 UTC, branch head 95970f33a2)

L: independent stage-2 immutable head 95970f33a2a1: H1/H2/H11: the item has already landed at 6e45d0d0f5 (Q14, reviewed_lean pass, present in the delivery's base fe31ddf7a2). Delivery 95970f33a2 changes nothing in substance: the module differs only in 'Authors: Q14 -> ND', the node only in lean.by Q14 -> ND and lean.note, plus an ND report that presents Q14's landed module as ND's work without saying it had landed. Correction: do not land and do not re-deliver the same content; release the claim. Any real defect must be delivered as a change on top of 6e45d0d0f5, keeping Q14's attribution. Content verified anyway: clauses 1-5 match the node (base change Over.pullback @WeaklyEtale, lowerStar/sheafPullbackConstruction adjunction, colimits/finite limits, abelian underlying-set iso plus exactness, conjugate of lowerStarComp with a correctly typed unit equation); defs carry no sorryAx; statement verbatim; nt_compile clean. Existing H4 overlap of setPullback/setPullbackComp with Scheme.proEtaleSheafInverseImage/profinitePointSetComp is already in the landed version.



## det-sf-comparison-affine-continuity (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 1 (2349 characters); step 5 (2269 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 1 (2349 characters); step 5 (2269 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## det-lem-int-ext-continuity (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 2 (2342 characters); step 3 (2512 characters); step 4 (2169 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 2 (2342 characters); step 3 (2512 characters); step 4 (2169 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are; the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.



## lem-sfb-continuous-algcl-proper-scalar-comparison (2026-10-21 13:31 UTC, branch head 52a0b9d579b)

E2/E1/D (false inputs, major gap): steps 1-6 never use any property of B and prove pi_M invertible for EVERY degree-zero condensed A-module M (step 1 says so). That is false. Counterexample: k = F_p-bar, T = Spec k, Z an ordinary elliptic curve, K = A_E constant, M = A tensor_Z C(-,Q_p) (underived condensed tensor). H^1(F(M)) = M^2 comes from l-adic characters. The Artin-Schreier-Witt character chi: pi_1 -> Z_p, pushed out along z -> 1 tensor z (continuous because p^n -> 0 in the Q_p factor), gives a nontrivial M-torsor: an invariant section over the connected cover would force 1 tensor z = 0 in E tensor_Z Q_p. Its class is not in the image of M^2, since l-adic characters vanish on the pro-p part of pi_1. So lem-sfb-proper-free-profinite-projection and lem-sfb-proper-constant-twist-upper-bound, with lem-sfb-adic-proper-bounded-below-coproducts, are jointly false, most likely the free-profinite projection node. Both geometric nodes are also unsourced (the report marks them WANTED). The item itself may still hold, because |p| = 1 in Omega, but a proof must use the l-adic nature of B. Checked as correct given the inputs: step-5 cone S_n[n+1] and the window n > max(c,d) - i; second-variable exactness of lem-weil-pbc-ringed-projection-mate-exact; lem-sfb-bounded-above-flat-kflat for step 3; the step-7 adjunct identification via lem-weil-pbc-ring-sheaf-change-adjunction. The free-resolution node is standard. Batch-5 check: det-thm-sfb-proper-base-change-rational is used only for clause (2), proper D^b_c finiteness. Its route to the sec-poincare-duality node lem-pd-module-ringed-topos-derived-comparison is a generic module/ringed identification, not a step of duality or of the trace formula, so the citation alone would be acceptable. Source read: main-20261015 sk-thm-sf-ctf-stability-direct-images.proof.md paragraph (3), which gives no all-continuous comparison. No fixes written.

## lem-coef-enriched-sequence-projection-formula (2026-10-21 14:00 UTC, branch head 3e255f21b94)

L: independent stage-2 immutable head 3e255f21b94a: H3/H5: the repaired degree-zero conjunct uses (rhom_global_sectionsOfUniverses J A).choose and (… J (B n)).choose. That existential fixes only naturality, so the witness is unique only up to a natural automorphism of the identity (−e is also a witness). The two choices are independent, so the clause is unprovable and is not the node's class(g)↦Q(g) map. Mechanical finding: the theorem stmt_dep lem-pur-rhom-global-sections must be replaced by the existing def node def-coef-hom-zero-cycle-class. Correction: use WeilConjectures.coefficientHomZeroEquiv J A P (L.obj N) and J (B n) ((σ n).T.obj P) ((e n).obj N), the ∃!-normalized 08JA (ringedSiteZerothHypercohomologyOfUniverses = coefficientGlobalSections ⋙ H0 by definition); publicly import Sheaf.Paper.CoefficientHomZeroClass; swap the stmt_dep; update the step-6 docstring and report. A reviewer FIX cannot change stmt_deps. Clauses 1-4, helpers (ordinarySectionsIso and sectionsH0Comparison pinned by ∃!), the verbatim statement, docstrings and sorry-only proofs were checked and are correct. Advisory: the second reading is a self-reading and missed this; μ is universally quantified.
