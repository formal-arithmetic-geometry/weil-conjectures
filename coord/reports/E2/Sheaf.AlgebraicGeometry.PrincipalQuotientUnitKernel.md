## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.Modules.principal_quotient_unit_kernel` with a complete Lean
reduction along the existing proof plan. Its signature, visibility and definitions are unchanged.

The proved private helper `mono_baseScalar_of_flat` applies
`injective_smul_sections_of_flat` to each open subscheme and its restricted line bundle.
It transfers invertibility through `restrictFunctorIsoPullback`, identifies the scalar actions
through `restrictAppIso`, and cancels sections to prove the scalar endomorphism is mono.

The main proof makes the quotient map and its base change closed immersions, identifies L
with the ideal-action image using the new image-comparison theorem and `imageMonoIsoSource`,
and applies `closedImmersion_unit_kernel`. It explicitly compares the adjunction chosen there
with the adjunction of the original statement using `leftAdjointUniq`. Each map killed by the
stated unit lifts through the existing image kernel and the inverse image isomorphism;
monicity proves uniqueness. No data definition chooses a witness from the new existence theorem.

Added the proof-only import
`Sheaf.AlgebraicGeometry.PrincipalQuotientMultiplicationImage` and its new module/node.
The image comparison is strictly a part of the argument: it does not mention adjunctions,
restriction units, scalar monomorphisms, or kernel universal properties. It holds for any
commutative base ring, any scalar, any morphism and any module. Its docstring records the
full affine/stalk/gluing proof and checks zero scalars, unit scalars, and empty schemes.
The parent's proof steps now follow the delivered Lean reduction.

Both modules compile individually with the launcher compiler. The main theorem needs a local
heartbeat limit of 800000 for definitional comparison of the tensor adjunctions; its compile
completed in approximately eight seconds, well within the file timeout. An explicit
closed-immersion instance for the quotient is necessary for pullback instance synthesis.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.principal_quotient_unit_kernel`
(node `lem-sc-principal-quotient-unit-kernel`). The main module has no sorry remaining.
The private helper `mono_baseScalar_of_flat` is fully proved.

Added one hole, exactly a public theorem with proof `:= by sorry`:
`AlgebraicGeometry.Scheme.Modules.principal_quotient_multiplication_image`
(node `lem-sc-principal-quotient-multiplication-image`), in
`Sheaf.AlgebraicGeometry.PrincipalQuotientMultiplicationImage`.

This is a decomposition: one original hole closed, one lower hole added, net zero holes.
The remaining work is the geometric identification of the two multiplication images.
The scalar monomorphism and the kernel/adjunction combination are complete Lean proofs.
The existing kernel theorem is used with its existing dependencies; this delivery does not
claim that all axioms in its transitive dependency closure have been eliminated.

## No longer needed

Removed the redundant direct public import
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` from the new image-comparison
module; its statement prerequisites are available through the retained ideal-sheaf module.
The `Invertible` import is needed even for an arbitrary F: it installs the scheme-module
monoidal instance used in the statement.

None of the original imports, nodes, or modules can be pruned: the proof uses both
`Sheaf.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree` and
`Sheaf.AlgebraicGeometry.ClosedImmersionUnitKernel`, and retains the statement imports.
A temporary explicit `Mathlib.CategoryTheory.Adjunction.Unique` import was removed and the
module recompiled successfully; those declarations are already available through the retained
imports. No blueprint unit or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The planned image identification is not
supplied by either of the two original theorem dependencies: their conclusions give
section injectivity and an ideal-action image kernel, respectively. The missing bridge is
now isolated as the new, strictly intermediate image-comparison theorem. Section injectivity
on the whole scheme alone is insufficient for monicity, so the proof applies the section
result on every open restriction and transports the scalar action explicitly.

The local copy has no Stacks source directory at the node's historical path; the cited
Tags 0EX8 and 08KS were read from their official Stacks pages. The LeanSearch service returned
Internal Server Error; LeanFinder, Loogle, and source searches were used as well.

## New nodes

`lem-sc-principal-quotient-multiplication-image` states the isomorphism over F between
the categorical image of the principal scalar endomorphism and that of the base-changed
quotient ideal acting on F. Its proof computes the principal ideal on affine charts,
uses the tensor-multiplication stalk range and exactness of module stalks, and glues the
unique local comparison maps. It inherits the parent's chapter and unit and carries
its own source, complete proof in words, searches, and verbatim Lean signature.
There are no statement-change records or forced adaptations.


## Second reading by E2

1. Compared the existing module and node against the repository with `diff`.
   The sole existing public theorem signature is byte for byte unchanged; no
   definition or existing docstring changed. The extra declaration is a private
   proved helper. Existing node edits are confined to proof, proof_deps and
   proof_origin. There are no interface changes or forced adaptations. Pass.
2. Compiled both delivered modules in import order, then compiled a scratch copy
   with explicit `#print axioms` for the private helper, original theorem and new
   theorem. The helper uses only propext, Classical.choice and Quot.sound; both
   public theorems additionally use sorryAx, as expected from the documented open
   image comparison. Only the new named public theorem contains sorry; there are
   no definitions choosing data, forbidden declarations or hidden proof holes.
   Read the sectionwise cancellation, image-source isomorphism and adjunction-unit
   comparison: each factorization has the stated source and target, and Mono mu
   supplies the uniqueness in ofι'. Pass as a decomposition, not a completed proof.
3. Read the entire image-comparison statement, docstring and node, together with
   the ideal-sheaf construction and the cited stalk/tensor declarations. On every
   affine chart the base-changed ideal is (pi), so its product with an arbitrary
   stalk module is pi times that module. The statement therefore needs no flatness
   or invertibility. Tested pi = 0, a unit, a zero-divisor in a ring such as Z/4,
   arbitrary modules with pi-torsion, and empty X: the two images still coincide.
   The local lifts glue uniquely because their image inclusions are mono. Read
   [Tag 0EX8](https://stacks.math.columbia.edu/tag/0EX8) and
   [Tag 08KS](https://stacks.math.columbia.edu/tag/08KS); the latter supplies the
   quotient/stalk viewpoint, while the image equality is the explicitly recorded
   agent expansion. Independent LeanFinder search for the ideal action of a
   base-changed principal subscheme returned ideal-map/comap and algebraic tensor
   results, not this theorem. Independent Loogle search `image, smul` returned an
   unknown-identifier diagnostic, not evidence of absence. Source searches with
   scalar/image and principal/image, and reading ModulePullbackIdealProductImage
   and ClosedImmersionDisjointIdealTwistImage, found related but distinct results.
   The new lemma omits the scalar monomorphism and kernel universal property, so
   it is strictly an intermediate step rather than a relabelled target. Pass.
4. Read from the target down through both original proof dependencies. The scalar
   helper genuinely applies the existing flat-section theorem on every open;
   the kernel transport genuinely applies the existing closed-immersion theorem.
   No short ready-made image equality was found. Formalizing the affine-to-stalk
   bridge and gluing would be substantial additional work, not a few-minute
   closure. Both original proof dependency nodes remain used: No longer needed
   is complete for the original plan. The cube unit statement and its sole step
   stay unchanged; its pre-existing realized arrays are empty, and this non-key
   node delivery neither changes them nor bypasses that route. Pass.
5. Checked both node proof-step uses against proof_deps, the new node's required
   metadata, verbatim Lean signature, chapter/unit, source and blueprint origin.
   They describe precisely the delivered reduction and the still-open image
   calculation. The report correctly counts one original hole closed and one
   lower hole added, net zero. Pass.

Second-reading changes: removed the redundant ClosedImmersion import from the
new module and recorded why Invertible remains necessary for its tensor instance.
No proof or statement repair was needed. Recompiled both modules after this edit.
