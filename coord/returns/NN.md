

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







## lem-cbc-derived-finite-quotient-coherence (2026-10-21 07:40 UTC, branch head e76276c9418)

L: independent stage-2 immutable head e76276c9418d: H2: delivery adds theorem node lemma-weil-pbc-completed-pullback-reduction to stmt_deps only for completedReductionFiniteTarget/FiniteModules/FiniteEvaluation/FiniteGenerator/FiniteModelMap/OrdinaryTransition/TargetTransition/TargetNormalization/QuotientAssoc/Unit in Sheaf/Paper/CompletedPullbackReduction.lean, all plain defs or .choose of module-local _exists helpers, none of completedPullback_reduction; def-a1-integral-completed-pullback-interfaces is O_E-only and names only 4 of them. Required: add an existing:true definition node on that module listing these declarations (general adic datum; stmt_deps adic-coefficient-datum, completed-pullback, constant-completion) and cite it instead of the theorem (theorem to proof_deps if used); Lean file unchanged. Substance otherwise correct: six conjuncts match the node's square for all K and b>=a>=1, normalization iso, (x⊗r)⊗s↦x⊗q(r)s section formula with derived-model link, cocycle and unit for arbitrary K; new decls have real data; statement verbatim; nt_compile --json clean 35.0 s.

## lem-sbc-ambient-operations-scalar-linearity (2026-10-21 07:42 UTC, branch head c27a08bf36c)

Superseded (A7/B10, brief 'live finished nodes win; never split one'). This re-split was committed 05:52 UTC on base 7ffa57a. At 06:13 UTC the live ledger merged deliver/J3/Sheaf.AlgebraicGeometry.ProEtaleAmbientOperationsScalarLinearity (stage 3). The live node's reviewed_proof shows sorry_after [], and the live ProEtaleAmbientOperationsScalarLinearity.lean has 0 sorry. That Lean proof proves the exact item along the old 4-step route: u_* linearity sectionwise via hc, u^* by left_adjoint_linear, Lu^* by the mapDerivedCategory instance, Ru_* by right_adjoint_linear. Merging would replace the live proof that matches the Lean code with an assembly. That assembly cites the new unsplit node lem-sbc-underived-ringed-operations-linear, whose content is already a `have` block of the closed proof, so it would create spurious open work. The mathematics is sound and I read it in full. The statement is byte-identical to the base. The underived node is true: rho_W(a_V|_W)=a_U|_{W_U} is the sectionwise form of A-compatibility of c, the Hom action is def-pur-sheaf-modules-hom-module restricted along a_T, and G and P are linear by the old steps 1-2. Step 2 is the same as old step 3 (lem-cbc-exact-linear-derived-functor with the derived structures of lem-weil-linear-abelian-derived-category). lem-sbc-linear-right-adjoint is true and generic, with no existing duplicate found by rg -L. The sources are Stacks 03D3/04TT/09MK, with no SGA. The re-split-note shape is satisfied (2 new nodes, assembly 1236 chars). Edge cases u=id with nontrivial c, A=0, a=0 and a=1 all hold. This matches the same 06:10-06:14 UTC stage-3 batch that superseded the Q34, NP, N0, Q32 and Q27 re-splits.
