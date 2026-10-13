## What changed

Proved AlgebraicGeometry.Scheme.affine_restriction_source_depth_comparison in
Sheaf.AlgebraicGeometry.Morphisms.DepthTwoAffineRestrictionSourceDepth, without changing
its signature or any public import. Added only proof imports and fully proved private helpers.
Finiteness uses the Noetherian affine chart and the finite submodule S. Constructed the actual
linear equivalence from N(V) to the comapped range K and localized it. Proved semilinear
invariance of depth and used affine germ localization to transfer the boundary stalk depth.
For interior points, used qcqs quasi-coherent pushforward, naturality of the restriction/stalk
isomorphism, and the module stalk functor to prove localized-unit surjectivity. Factoring through
S and applying localization exactness then makes the localized quotient zero.

Updated the node's proof, proof_deps and proof_origin to this route. Only the item's module and
its node are changed. The unit's depth-two extension route is preserved.

## Proved and sorry left

Closed 1 hole: AlgebraicGeometry.Scheme.affine_restriction_source_depth_comparison
(node lem-sbc-affine-restriction-source-depth). Added 0 holes; split off 0 statements.
No sorry remains in the delivered module, including its five private helpers.
The proof uses existing library declarations as allowed by stage 3; their own dependencies
remain separate items. No definition or target statement was changed.

## No longer needed

No existing import was removed. The planned tensor-product presentation node
lem-pc-intrinsic-flat-module-stalk-tensor-presentation and its module
Sheaf.AlgebraicGeometry.IntrinsicFlatModuleStalkTensorPresentation are no longer needed by
this proof: the existing lem-sbc-affine-module-germ-localization directly gives the needed
localization universal property. The tensor-product module was never imported here.
All other planned proof dependencies are retained. The two temporary scratch theorem modules
were removed from the delivered lean tree; there are no new public helper modules.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the statement or the unit route was found. The DAG's first step can
be shortened: finiteness follows already from K being a submodule of finite S over the
Noetherian affine section ring, independently of injectivity or the M-to-K equivalence.
The old tensor-product presentation is a longer interface for the needed germ localization;
the newer, proved affine-module-germ-localization declaration fits directly.

The affine-germ module was initially absent from the local compiled snapshot; it became
available from the refreshed green library before use. No missing declaration was duplicated.

## Second reading by T4

1. Compared the delivered module and node with the repository versions. The public theorem signature and existing declarations are unchanged; the node records only the proof route and dependencies. Verdict: pass.
2. Compiled the module with lcompile.py successfully and checked that the delivered source contains no sorry, axiom, unsafe, opaque, extern, or implemented_by. An explicit scratch-copy #print axioms check of affine_restriction_source_depth_comparison returned exactly propext, Classical.choice, and Quot.sound, with no sorryAx. The proof is substantive and uses only permitted library declarations. Verdict: pass.
3. Reviewed the private helper arguments and the node proof steps. No split-off statements were added; the target statement is unchanged and no duplicate public theorem was introduced. Verdict: pass.
4. Checked the proof from the target downward. The route uses affine germ localization, qcqs pushforward, localized exactness, and semilinear depth transport; the planned unit route is preserved. The tensor-product presentation is correctly pruned because it is not used. An import-removal compile confirms Modules.Tilde supplies the restriction quasi-coherence instance and must remain. Searched the depth library for equivalence/congruence lemmas; none directly replaces the semilinear helper. Verdict: pass.
5. Checked that the node proof, proof_deps, and proof_origin match the Lean proof, and that the report's pruning account names the removed planned dependency. Verdict: pass.

Changed only this report section; no Lean or DAG repairs were needed.
