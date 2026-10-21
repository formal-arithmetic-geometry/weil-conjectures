

## lemma-weil-pbc-projection-formula-open-piece (2026-10-15 19:22 UTC, branch head d461fd6596)

L: independent stage-2 immutable head d461fd65967a: file-only compilation failed: preliminary Sheaf/Algebra/Homology/KFlat.lean

(with the modules compiled into /tmp/nt-local-compile-ab4e9kpu/.lbuild) [6.9 s]
preliminary Sheaf/Paper/StrictPerfectCoefficientPackage.lean

(with the modules compiled into /tmp/nt-local-compile-ab4e9kpu/.lbuild) [26.5 s]
sandbox Sheaf/Stage2/Sandbox0.lean

(with the modules compiled into /tmp/nt-local-compile-ab4e9kpu/.lbuild) [6.5 s]
library Sheaf/Algebra/Homology/KFlat.lean

[6.6 s]
sandbox Sheaf/Stage2/Sandbox1.lean

(with the modules compiled into /tmp/nt-local-compile-ab4e9kpu/.lbuild) [28.2 s]
library Sheaf/Paper/StrictPerfectCoefficientPackage.lean

[21.8 s]
sandbox Sheaf/Stage2/Sandbox2.lean

(with the modules compiled into /tmp/nt-local-compile-ab4e9kpu/.lbuild) [3.2 s]
library Sheaf/CategoryTheory/LocalizedModuleAdjunctionUniverses.lean

[3.3 s]
sandbox Sheaf/Stage2/Sandbox3.lean

(with the modules compiled into /tmp/nt-local-compile-ab4e9kpu/.lbuild) [59.0 s]
library Sheaf/Paper/RingedTopoiCanonicalTensorPullback.lean
timeout after 60 s: the fault is usually a definition that is expensive to unfold, not the limit

Launcher: Sheaf.Algebra.Homology.KFlat now provides IsKFlat, IsKFlatResolution, and the independent-coefficient predicates; import it instead of changing it.
## lemma-weil-pbc-projection-formula-proper-piece (2026-10-15 22:37 UTC, branch head 0fed1b5ce5)

L: independent stage-2 immutable head 0fed1b5ce5a7: file-only compilation failed: preliminary Sheaf/Paper/ProjectionCompactification.lean

(with the modules compiled into /tmp/nt-local-compile-7x42funq/.lbuild) [16.2 s]
sandbox Sheaf/Stage2/Sandbox0.lean

(with the modules compiled into /tmp/nt-local-compile-7x42funq/.lbuild) [12.2 s]
library Sheaf/Paper/ProjectionCompactification.lean

[9.9 s]
sandbox Sheaf/Stage2/Sandbox1.lean
/tmp/nt-local-compile-7x42funq/lean/Sheaf/Stage2/Sandbox1.lean:199:49: error: incorrect number of universe levels CochainComplex.IsKFlat
/tmp/nt-local-compile-7x42funq/lean/Sheaf/Stage2/Sandbox1.lean:199:53: error: incorrect number of universe levels CochainComplex.IsKFlat
/tmp/nt-local-compile-7x42funq/lean/Sheaf/Stage2/Sandbox1.lean:200:17: error: incorrect number of universe levels CochainComplex.IsKFlat
/tmp/nt-local-compile-7x42funq/lean/Sheaf/Stage2/Sandbox1.lean:200:17: error: incorrect number of universe levels CochainComplex.IsKFlat

(with the modules compiled into /tmp/nt-local-compile-7x42funq/.lbuild) [10.5 s]

Launcher: Sheaf.Algebra.Homology.KFlat now provides IsKFlat, IsKFlatResolution, and the independent-coefficient predicates; import it instead of changing it.
## def-pur-affine-line-purity-comparison (2026-10-15 23:03 UTC, branch head 89140e09a0)

L: approved by the reader, but the landing refused it: NOT MERGED def-pur-affine-line-purity-comparison: cited node def-exchange-projection: statement changed since the reviewed delivery; rebase and revalidate the citation Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.



## def-weil-exceptional-adjoint-admissibility (dedicated repair handoff)

The previous worker ended with: The literature re-review (2026-10-16) returned this split. Keep the route; fix exactly the finding below and re-deliver.

Compiler messages and attribution:
E4/C4: The displayed restriction comparison U_{phi,X}F_A ≅ F_BU_{phi,Y} is not composable for U_phi:D(B)→D(A), and is not the statement of lem-sf-compact-support-restriction-of-scalars. Replace it by F_A U_{phi,X} ≅ U_{phi,Y}F_B (or its inverse), and form alpha and its mate from that typed comparison. B3: remove unused statement dependencies def-weil-integral-derived-reduction, lem-weil-integral-scalar-extension-well-defined and def-weil-ambient-exceptional-adjoint unless the definition actually invokes their additional data.

## lem-sp-filtered-homology-tower-forward-representatives (2026-10-17 06:30 UTC, branch head bb15e00d79)

L: independent stage-2 immutable head bb15e00d793b: incremental DAG validation: blueprint: lem-sp-filtered-homology-tower-forward-representatives: blueprint.from.node lem-sp-filtered-homology-tower-differential is not a blueprint node



## lem-weil-pbc-etale-lisse-open-relative-line-constructibility (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 4 (2226 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 4 (2226 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## thm-exc-curve-open-dimension-general (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 7 (2067 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 7 (2067 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## lem-fin-normalization-extends-cover (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 5 (2252 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 5 (2252 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## det-proper-heart-bound-reduction (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 2 (2804 characters); step 3 (2646 characters); step 4 (2116 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 2 (2804 characters); step 3 (2646 characters); step 4 (2116 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are; the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.

## lem-fd-convolution-kernel (2026-10-18 01:09 UTC, branch head b648c9e43b)

L: independent stage-2 immutable head b648c9e43b8e: Sheaf.Paper.FourierConvolutionKernel declares names that other modules already declare:
  WeilConjectures.fourierConvolutionGeometry: also in Sheaf.Paper.FourierKernelConvolution
  WeilConjectures.fourierKernelConvolutionIso: also in Sheaf.Paper.FourierKernelConvolution
Import and reuse the existing declaration. Renaming yours only hides the collision and leaves the same fact proved twice; rename only when the two declarations say different things.

## lem-sbc-ambient-operations-scalar-linearity (2026-10-21 10:12 UTC, branch head 30919d5cb8f)

Superseded again (A6/A7/B10/G4). This is the 6th NN push of this item, after c27a08bf, 53cc9686, ea00ef15, c2b1251b and 7ffdcfe4, each returned as superseded (ledger l.20772/21124/21621/21857; svc.log 17:48 +0800). Both new nodes are sha-identical to 7ffdcfe4: lem-sbc-underived-ringed-operations-linear 66260d34 and lem-sbc-linear-right-adjoint 19ffc367. The item differs from 7ffdcfe4 only in split_report.summary, which now cites the 'current user brief'. That is the launcher's generic hand-off text, not a human decision on file. The live item is status split, with J3 reviewed_proof from stage-3 landing 20261021T061336-L-1761747 and sorry_after [] (ledger l.20365, 06:13Z). The repair note's mtime is 14:08:38 +0800 (06:08:38Z), which predates that landing, and coord/HUMAN.md was last modified 10-19. brief-stage1 l.103 says live finished or split-and-reviewed nodes win and must never be split. The maths is sound and unchanged: the sectionwise underived linearity (Stacks 03D3/03D6/04TT), the generic right-adjoint node (right_adjoint_linear/right_adjoint_additive) and the 3-step assembly via lem-cbc-exact-linear-derived-functor. No SGA source is used. Maintainer: retire or refresh the pre-landing repair note, or record an explicit post-landing human decision, to stop the re-dispatch loop.
