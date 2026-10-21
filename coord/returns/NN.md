

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

## lem-sbc-ambient-operations-scalar-linearity (2026-10-21 09:02 UTC, branch head ea00ef151ab)

Superseded again (A7/B10). brief-stage1 l.103 says live finished or split-and-reviewed nodes win and must never be split. Live status: the node is split with reviewed_proof from J3's stage-3 landing 20261021T061336-L-1761747 (06:13:36Z). The live ProEtaleAmbientOperationsScalarLinearity.lean has 0 sorry, and I read proEtaleRingDerivedOperations_scalarLinearity in full. Its hc `have` makes u_* linear, left_adjoint_linear gives u^*, an inferInstance gives Lu^*, and right_adjoint_linear gives Ru_*. That is the old 4-step route, already closed. Timing and instructions: the only re-split note (coord/repair-notes) has mtime 06:08:38Z, before that landing. coord/HUMAN.md was last changed 2026-10-19 and does not mention the item. The 'explicit human instruction' the report cites is the launcher's handoff boilerplate. History: this is the 3rd NN push, after c27a08bf and 53cc9686 were both RETURNed as superseded. Both new nodes are sha256-identical to both earlier pushes (lem-sbc-linear-right-adjoint 03b33a10, lem-sbc-underived-ringed-operations-linear 66260d34), and the item differs only in split_report. The report says it 'additionally seeds lean_audit.slopmaster2.decls'; that is false, because the node has no such entry and did not change. Mathematics: I read it in full and it is sound. The statement is unchanged. The underived node is true: its rho condition is the A-compatibility of c (= hc), and G and P are linear by the sectionwise and unit-bijection arguments (Stacks 03D6/03D3/04TT). Step 2 is correct: exact termwise P plus lem-cbc-exact-linear-derived-functor and lem-weil-linear-abelian-derived-category. The generic right-adjoint node is true by the counit argument (09MK) and is already proved by right_adjoint_linear and right_adjoint_additive. Edge cases u=id with nontrivial c, A=0, a=0/1 and non-injective a_T all hold, and no SGA is used. Maintainer: retire the stale 06:08Z re-split note for this item.
