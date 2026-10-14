## What changed

Replaced the proof of `AlgebraicGeometry.affine_isomorphic_source_normalized_models`.
Its existing signature, docstring, public imports, and visibility are unchanged.
Added the proof-only import `Sheaf.AlgebraicGeometry.AffineTopTensorSections`.
The proof uses `Scheme.exists_affineTopTensorSections`, transports its tensor-pullback
comparison to standard pullback by the adjunction unit equation, and constructs
all changes of coefficient ring and starting chart. Private helpers construct the
section map, its tensor extension, and prove its bijectivity. The starting inverses
are inverses of the proved bijective pullback units, not arbitrary existence witnesses.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.affine_isomorphic_source_normalized_models`.
Added no holes. No `sorry` remains in the delivered module.
The previously proposed
`AlgebraicGeometry.affine_isomorphic_source_normalized_model_single` and its new
module/node were removed from this delivery. This closes one hole with zero holes
added; it is a proof, not a decomposition.

A scratch copy with `#print axioms` reports exactly `propext`, `Classical.choice`,
and `Quot.sound` for the target declaration. The delivered file compiles cleanly.

## No longer needed

No existing public import was removed: they supply the unchanged public statement.
The proposed proof-only import
`Sheaf.AlgebraicGeometry.AffineIsomorphicSourceNormalizedModelSingle` was removed,
and its proposed module and node
`new-affine-isomorphic-source-normalized-model-single` are not delivered.

The original target node's direct proof dependencies
`lem-weil-pbc-affine-tilde-gamma-adjunction` and
`lem-weil-pbc-tilde-pullback-base-change` are replaced by the existing
`lem-sc-affine-top-tensor-sections`. Their reconstruction content is already in
that proved affine comparison; no claim is made that their modules leave the
whole targets' import closure. The original direct dependency
`lem-pc-module-pullback-adjunction` remains. No library module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The first proposed single-module split was equivalent to the paired target by
specializing the pair to M=M, so it moved the main hole rather than reducing the
argument. The earlier search missed
`AlgebraicGeometry.Scheme.exists_affineTopTensorSections` and its upstream
`tensorPullback_affine_sections_bijective`, which already provide the needed
canonical affine comparison. The replacement proof constructs the isomorphic
starting-chart transport rather than hiding it in another statement.

## Second reading by J3

1. Compared the delivered module with the repository version. Extracted the existing
   target's signature through `:= by` and checked byte-for-byte equality. Its
   public imports, visibility, and docstring are unchanged. Only proofs, one
   proof-only import, and private helpers change. No change record is required.
2. Compiled the delivered module and a scratch axiom-check copy through lcompile.py.
   Both compile cleanly. There is no sorry, axiom, unsafe, opaque, implemented_by,
   extern, or holed definition. The target uses only propext, Classical.choice,
   and Quot.sound. Private definitions are explicit adjunction maps; the starting
   inverses use independently proved bijectivity, and the chosen affine map is
   determined on every pure tensor by its theorem's formula.
3. Refused and removed the equivalent single-module split. No split-off statements
   remain. Repeated searches with different terminology through leanfinder,
   loogle, and grep, and read PullbackTilde, ModulePullbackAffineSectionsBijective,
   ModulePullbackAffineSections, and AffineTopTensorSections. The latter's existing
   theorem supplies the comparison. Read Stacks Tags 01I9 and 01IB against the
   affine/quasi-coherent hypotheses. No finite presentation or nonempty hypothesis
   is needed; empty affine schemes/zero rings and zero modules are included.
4. The route is from the target to an existing proved affine comparison. Scalar
   extension and adjunction unit formulas prove the starting-chart transport,
   semilinearity, and normalization locally. The shorter existing-library route
   eliminates the added hole. The only added import is proof-only and used.
   Both replaced original proof dependencies are listed above. Read
   dag/units/sk-thm-picard-semicon.json: this node is not a realized unit statement
   or step (the realized arrays are empty), and no unit record or route changes.
5. Updated the existing node's proof, proof_deps, and proof_origin to record the
   actual affine-comparison and scalar-extension argument. The dependencies are
   the union of the cited steps. No new nodes or interfaces are delivered.

Second reading changed the equivalent split into a complete proof using the
existing affine tensor-sections theorem, removed its proposed module/node,
constructed the canonical maps and inverse-unit coordinate transport, and
corrected the DAG and hole accounting.
