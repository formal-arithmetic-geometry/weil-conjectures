

## def-weil-constructible-heart (2026-10-16 01:30 UTC, branch head 1d3ffc72f8)

L: independent stage-2 immutable head 1d3ffc72f8ef: file-only compilation failed: preliminary Sheaf/Paper/IntegralOperationsWellDefined.lean

(with the modules compiled into /tmp/nt-local-compile-te9zabir/.lbuild) [16.6 s]
preliminary Sheaf/Paper/SfIntegralReductionTower.lean

(with the modules compiled into /tmp/nt-local-compile-te9zabir/.lbuild) [9.9 s]
sandbox Sheaf/Stage2/Sandbox0.lean

(with the modules compiled into /tmp/nt-local-compile-te9zabir/.lbuild) [16.6 s]
library Sheaf/Paper/IntegralOperationsWellDefined.lean

[22.0 s]
sandbox Sheaf/Stage2/Sandbox1.lean

(with the modules compiled into /tmp/nt-local-compile-te9zabir/.lbuild) [10.1 s]
library Sheaf/Paper/SfIntegralReductionTower.lean

[10.3 s]
sandbox Sheaf/Stage2/Sandbox2.lean

(with the modules compiled into /tmp/nt-local-compile-te9zabir/.lbuild) [3.2 s]
library Sheaf/Paper/SfIntegralConstructibleTriangulated.lean

[5.2 s]
sandbox Sheaf/Stage2/Sandbox3.lean

(with the modules compiled into /tmp/nt-local-compile-te9zabir/.lbuild) [4.9 s]
library Sheaf/Paper/IntegralConstructibleLinear.lean

[8.4 s]
sandbox Sheaf/Stage2/Sandbox4.lean

(with the modules compiled into /tmp/nt-local-compile-te9zabir/.lbuild) [6.6 s]
library Sheaf/Paper/IntegralScalarExtension.lean

[7.3 s]
sandbox Sheaf/Stage2/Sandbox5.lean

(with the modules compiled into /tmp/nt-local-compile-te9zabir/.lbuild) [7.7 s]
library Sheaf/Paper/IntegralScalarExtensionConstructible.lean

[9.4 s]
sandbox Sheaf/Stage2/Sandbox6.lean

(with the modules compiled into /tmp/nt-local-compile-te9zabir/.lbuild) [15.8 s]
library Sheaf/Paper/RationalConstructibleCoefficients.lean
/tmp/nt-local-compile-te9zabir/lean/Sheaf/Paper/RationalConstructibleCoefficients.lean:6:0: error: object file '/home/ubuntu/weil-lean/.lake/build/lib/lean/Sheaf/Paper/IntegralScalarExtensionWellDefined.olean' of module Sheaf.Paper.IntegralScalarExtensionWellDefined does not exist

[0.4 s]

## cor-coef-finite-verdier (2026-10-16 02:30 UTC, branch head 4c0488cecf)

L: independent stage-2 immutable head 4c0488cecf20: Wrote review.md. All three snapshot modules compile through scompile.py. H3/H13: arbitrary categories and predicates replace the geometric constructions; cocycle quantifiers are incorrect; evaluation compatibility omits the comparison component; dependency modules omit required clauses. Also found H2 signature-record mismatch and H8 incomplete proof docstrings. Requires substantive re-delivery.

## lem-coef-finite-dualizing (2026-10-16 02:44 UTC, branch head 17030bd826)

L: independent stage-2 immutable head 17030bd826e5: Review explicitly requires re-delivery: H13/H3 missing geometric projection/counit compatibility; H13 incomplete exceptional-inverse-image restrictions and integral/rational/common-stage coefficient regimes; H13/H3 missing transported double-dual invertibility and restricted Verdier duality. Also H6 completed local naturality proof violates the sorry-only gate, and H2 all five owning-node statement strings lack verbatim formatting. Independent compiler reproduction has no final result recorded, so the review is incomplete. No files changed.

## thm-coef-finite-hom (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 3 (2938 characters); step 7 (5783 characters); step 8 (3355 characters); step 14 (2525 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 3 (2938 characters); step 7 (5783 characters); step 8 (3355 characters); step 14 (2525 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are; the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.

## lem-a1-integral-pullback-completed-comparison (2026-10-17 23:04 UTC, branch head 0e473be282)

L: independent stage-2 immutable head 0e473be282bd: Errors H3/§1(C): the statement correction replaces the integral derived pullback (def-pur-integral-derived-operations, Lean integralDerivedPullback; Stacks 099N(5) RHS R lim Lf*(M⊗Λ/I^n)) with ordinary d.pull. Unfolding completedPullReduction, the Lean claims ordinary pullback of every intrinsically complete object is complete with invertible completion unit. Stacks 099N(2) defines Lf*_comp as Lf* followed by completion and does not say this, so the claim is unsourced and stronger, about a different functor. H8: proof steps 6-10 build gamma from the integral cone C(B_•) and do not prove the new statement. The shift clause was dropped because the subcategory lacks HasShift (not a source reason; it can be stated objectwise), while the docstrings still claim shift compatibility. Citer audit: all three citers marked holds:false with no repair. Correction: restore integral pullback vs completed pullback, with the coefficient identification integralTowerModules ↔ d.derived for (O_E,ϖ) as a §1(B) helper in this delivery (or Rlim of finite pullbacks identified with integralDerivedPullback); keep the old-direction projection clause and an objectwise shift clause; fix the docstrings. Checked fine: binders/universes, no extra assumptions, ℕ indexing, statement verbatim, source/blueprint docstrings, report sections, sorry only. Per-file nt_compile on the side overlay finished with no errors (6.7 s).

## lem-per-henselian-valuation-coarsenings (2026-10-19 01:46 UTC, branch head 770249ea4cb)

L: approved by the reader, but the landing refused it: NOT MERGED lem-per-henselian-valuation-coarsenings: lem-per-henselian-valuation-coarsenings: completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it) Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-sfb-lisse-lattice-potential-kummer-tameness (2026-10-21 16:59 UTC, branch head 8589c9f98c5)

C5/B9: the new node is a duplicate that gets around the 2026-10-19 drop. This is the fifth delivery of the item, after NL 1f51eeaf, N5 68c9bff0, NX af5315f6 and NN b8613865, all returned because the multi-parameter Abhyankar step had no live node. The new lem-sfb-strict-local-prime-to-p-root-splitting is the dropped lem-per-snc-root-punctured-torsor-splitting (side-live route-pivot-dropped.txt line 1918) under a fresh id. Both take a strictly henselian regular Noetherian local R, t_i part of a regular system of parameters, and a finite étale torsor of invertible order over Spec R[1/t], possibly disconnected, split over the punctured Kummer root algebra. The new node only replaces the exponent n=|G| with some m prime to p, and its source is the same, ILO IX 2.1 pp.133-134. The dropped node is already split (25 deps via Stacks 0BRM/0BMB). The report does not mention it, the drop or the earlier returns. I found no maintainer note in side-live coord authorizing a fresh node. The new node is true: I tested r=0 with m=1, r=1, r=2, a disconnected P and Q=1. But it cannot be fixed here: no live node gives the step, since every live lem-sbc Abhyankar node is one-divisor (0EYG), and lem-per-snc-parameter-root-quotient and prime-to-order-snc-kummer-charts are dropped too (lines 1916 and 1806). Repair: the maintainer un-drops line 1918 (preferred, as it is already split) and Step 5 cites it with m=|Q_n|, which is prime to p because Q_n is an ℓ-group; or the maintainer authorizes a fresh sfb node in a repair note. Otherwise this item will keep looping. Second fault, C4 in Step 1: it applies lem-per-lisse-completed-system-comparison, which is stated over B_S = lim (A/ϖ^n)_S, to modules over the continuous-function ring C(−,O_E). Nothing in the step identifies the two rings. The coefficient isomorphisms of lem-sfb-integral-lisse-reduction-equivalence give this, as lem-a1-normal-completed-integral-model does. Everything else is correct. New node lem-sfb-congruence-kernel-ell-group is true and not a duplicate: the kernel 1+ϖM_d(A_n) has order |κ|^{d²(n−1)}; checked d=0, n=1, n=2. Step 2: the frame torsor from cor-galois (1) and the finite-set monodromy torsor is correct. Step 3: the strict-local clause of the residual-charts node makes V and T connected. Step 4: the ℓ-group monodromy and the regular torsor via thm-galois-fundamental are correct. Steps 6-8: the compatible bases (geometric-series inverse), reconstruction on the non-Noetherian T by the any-scheme reduction equivalence, and scalar extension are correct, as are r=0 and d=0. There is no SGA citation. Batch-5: cor-galois-lisse-representations (clause 1 only; its closure has only pod lisse/Galois definitions and lattice lemmas), lem-per-lisse-completed-system-comparison (reaches def-pod-lisse, a definition) and lem-sfb-snc-universal-residual-charts (reaches def-trf-SNC and generic trf geometry) are all generic and outside both assumptions, so accepted. The ten tool_uses are generic and acceptable. No fixes were written.
