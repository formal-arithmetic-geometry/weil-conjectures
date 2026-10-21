

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

## lem-weil-pbc-affine-cohomology-etale-module-realization (2026-10-21 09:17 UTC, branch head f860f10ce33)

L: independent stage-2 immutable head f860f10ce33d: Item maths correct (H3 clauses, action pinned on local classes, uniquely normalized comparison, q=0/non-affine covered). RETURN H13: dep records rebound, dropping live decls used by landed citers: def-weil-pbc-etale-cohomology (existing Etale.cohomology, 436 citers -> sheafHDerivedEquiv), def-sc-etale-qcoherent-module (etaleTensorSectionsSheaf -> coherentEtaleRestrictionIso), lem-weil-pbc-module-pullback-quasi-coherent (isQuasicoherent_pullback -> sorry isQuasicoherent_tensorPullback); keep records byte-identical, move helpers into new def node(s) and cite them. Mechanical theorem stmt_deps: lem-sbc-abelian-higher-direct-image-class-compatibility supplies only the plain def abelianHigherDirectImageClass -> RETURN: add a def node owning it (e.g. existing:true on the unchanged module) and cite that; lem-sbc-raw-restricted-cohomology-comparison-is-iso is unused by the item statement -> drop (belongs to the new def node); lem-weil-pbc-module-pullback-quasi-coherent is genuinely needed for the instance (PASS on that point). H2: add owners def-pbc-canonical-coherent-etale-comparison (liftedCoherentEtaleSheaf, coherentEtaleMap), def-sc-ringed-space-module-cohomology (moduleCohomology), lem-weil-pbc-qcoherent-normalized-comparison-exists (exists_unique choose); etaleTensorSectionsRestriction is a plain def of theorem node lem-sc-etale-qcoherent-presheaf-functorial and needs a def-node owner.

## lem-sbc-ambient-operations-scalar-linearity (2026-10-21 09:18 UTC, branch head c2b1251b98f)

Superseded again (A6/A7/B10/G4). This is the 4th NN push, after c27a08bf, 53cc9686 and ea00ef15, each RETURNed as superseded. lem-sbc-underived-ringed-operations-linear has sha256 66260d34, identical in all four pushes. lem-sbc-linear-right-adjoint differs from 03b33a10 only by a new lean_candidates field (right_adjoint_linear at LinearFunctor.lean:34, right_adjoint_additive at Mathlib Adjunction/Additive.lean:38). The item differs from ea00ef15 only in the wording of proof_origin.place and split_report, and from clones/live only in proof, proof_deps, proof_origin and split_report; its statement is byte-identical. Live is split with J3's stage-3 reviewed_proof (landing 20261021T061336-L-1761747, sorry_after []). The live ProEtaleAmbientOperationsScalarLinearity.lean contains no sorry. I read proEtaleRingDerivedOperations_scalarLinearity (l.77-137): an hc `have` makes u_* linear, left_adjoint_linear gives u^*, inferInstance gives Lu^*, and right_adjoint_linear gives Ru_*. So brief-stage1 l.103 ('live ... split-and-reviewed nodes win; never split one') and B10 apply. The only repair note has mtime 06:08:38Z in live (06:08:48Z in side-live), earlier than the 06:13:36Z landing. HUMAN.md was last changed 2026-10-19 and does not mention the item. The 'direct user route note' is launcher handoff boilerplate. The report again falsely says both names are seeded in lean_audit.slopmaster2.decls: the new node has no lean_audit key. The mathematics is sound and I read it in full. The underived node's rho condition is the A-compatibility of c (= hc); G is linear sectionwise (Stacks 03D6/04TT) and P by unit-bijection injectivity (03D3). Step 2 applies lem-cbc-exact-linear-derived-functor to the exact P with the structures of lem-weil-linear-abelian-derived-category. The generic right-adjoint node is true and is exactly right_adjoint_linear plus right_adjoint_additive. Edge cases u=id with nontrivial c, A=0, a=0/1 and non-injective a_T all hold; no SGA is used. Maintainer: retire the stale 06:08Z note or get a human re-split dated after the landing; G4 says abandon after three returns, do not push a 5th time.
