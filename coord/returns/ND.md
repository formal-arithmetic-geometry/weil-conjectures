



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

## def-per-support-condition (2026-10-22 01:36 UTC, branch head 0a51279c19c)

C1/F (dropped route node). The delivery has no new nodes and changes only the item. It takes D_X from lem-per-qbar-arbitrary-field-duality, which is dropped (side-live coord/route-pivot-dropped.txt line 1836, 2026-10-19 artin-gabber section). It also cites lem-per-adic-heart-pullback-fibres. coord/repair-notes/lem-per-artin-gabber-affine-curve.json lists both under removed_deps and forbids arbitrary-field Qbar_l duality. The live lem-per-artin-gabber-affine-curve cites this item, so the forbidden duality would come back into its closure. No step justifies it: the item is a definition with no steps. A FIX is not possible because no live node gives Verdier duality on Qbar_l over an arbitrary field: thm-coef-qbar-verdier, lem-a1-qbar-curve-duality and thm-sf-biduality-class are F̄_q only, and def-trf-dualizing-complex covers a finite field with finite A. Source check: main-20261015 order 3082 and master order 2738 have the same body. The worker is right that the base text is ill-typed (Qbar_l over any k with the finite-field def-trf dual). The SuppCon/CosuppCon formulas, the −i index and dim ∅ = −∞ are kept. Small cases checked: a point in degree 0, the shift [1] passing Supp but failing Cosupp, a curve local system failing at i = 0, and O_E/ϖ dying after rationalization. Batch-5 flags, each acceptable alone: heart-pullback-fibres reaches sec-poincare-duality only through the definition def-pod-lisse-l-adic-sheaves, and qbar-arbitrary-field-duality reaches sec-trace-formula only through the pure-algebra trf catenary lemma; the drop ground decides. No SGA is cited. The stmt_deps are identical to the RETURNed O3 66540e08 and NJ 80b963a5; this is about the 19th delivery of this item. It is a dispatch loop: the maintainer must decide the scope of D_X (finite-field datum, a coefficient-parametric definition at finite Λ, or ω as the object representing Hom(Ra_!−, unit)) or withdraw the item. No fixes were written.

