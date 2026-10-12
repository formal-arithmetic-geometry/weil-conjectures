## What changed

Proved `AlgebraicGeometry.Scheme.nonempty_idealAdditiveImageRelativeKernelIso` in
`Sheaf.AlgebraicGeometry.Curve.IdealAdditiveImageRelativeKernel`, with its signature and
visibility unchanged. Added three proved private helpers: `additive_restriction_epi`,
`additive_restriction_comp`, and `image_kernel_factor`. The second reading removed the redundant proof-only import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` and the first worker's redundant
`Mathlib.CategoryTheory.Sites.LocallySurjective` import. Updated the theorem docstring and the
existing node's proof and proof_origin to describe the compiled argument.

The geometric step uses Mathlib's surjectivity of global functions for a closed immersion
with affine target. An affine open cover of every etale test object makes restriction
locally surjective. The remaining proof uses the canonical composition isomorphism,
the pullback universal property, stability of epimorphisms under pullback in an abelian
category, uniqueness of strong epi-mono images, and preservation of kernels by direct image.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.nonempty_idealAdditiveImageRelativeKernelIso`
(node `lem-sc-ideal-additive-image-relative-kernel`). No holes remain in the item;
no holes were added. All three private helpers are completely proved. This is a proof,
not a decomposition into new sorried statements.

The file compiles cleanly with `lcompile.py` (about 3 seconds).
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`,
with no `sorryAx`. The universal hypotheses include zero/equal ideals
and the empty scheme; the local cover argument permits an empty cover, and the categorical
argument requires only the proved epimorphism and composition identity.

## No longer needed

Removed the original proof-only import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` and discarded the newly added
`Mathlib.CategoryTheory.Sites.LocallySurjective` import. Their declarations and instances
are already available through the public statement imports. Both were removed together
and the file still compiled cleanly. No existing dependency nodes or modules pruned: the proof
still uses the ideal-sheaf definitions, additive structure restriction, direct image,
and its preservation of kernels. The explicit sectionwise ideal-kernel computation and
sheafification of its image are unnecessary; the categorical pullback argument replaces
those portions of the plan, without importing a new comparison theorem.

Searches: leanfinder for the image of the kernel of a composite under an epimorphism found
image-to-kernel infrastructure, not this geometric theorem; loogle's query with unqualified
`kernel` was rejected as an unknown identifier; grep `kernel.*comp|image.*kernel` found
generic kernel/image infrastructure. Local source searches found
`IsClosedImmersion.isAffine_surjective_of_isAffine`,
`MorphismProperty.Over.pullbackComp_left_fst_fst`, `Abelian.epi_snd_of_isLimit`, and
`image.isoStrongEpiMono`, which supply the full proof.

## Where the brief, the DAG or earlier work was wrong

No statement or interface error found. The DAG's dependencies did not contain a theorem
for its affine representative step, but Mathlib's affine closed-immersion surjectivity
suffices after passing to affine covers. The planned explicit kernel calculation and
sheafification are avoidable. No definition or existing statement changed, no forced
adaptations, and no new nodes.


## Second reading by P4

1. **Existing interface: pass.** Compared the sole delivered Lean module with the
   repository using `diff -u`. The existing theorem signature, including universes,
   hypotheses, conclusion and public visibility, is byte for byte unchanged. No
   definitions, target files or other modules changed. The only additions are three
   fully proved private helpers and proof documentation; no change record is needed.
2. **Proof and axioms: pass.** Independently compiled the delivered module locally
   through `lcompile.py`, without errors or warnings. A scratch copy with
   `#print axioms AlgebraicGeometry.Scheme.nonempty_idealAdditiveImageRelativeKernelIso`
   reports exactly `propext`, `Classical.choice`, `Quot.sound`. There is no `sorry`,
   forbidden declaration or hollow definition in the delivered module. Read all three
   helper proofs: affine closed-immersion surjectivity supplies the local lifts;
   pullback projection compatibility supplies the composition equation; the explicit
   pullback universal property and epi stability supply the image comparison.
3. **Split statements: pass, none.** No new public statements, nodes or holes are
   split off. The proved private helpers are strictly intermediate arguments. Checked
   the edge cases: equal ideals give the zero relative kernel; J=0 makes restriction
   to J an isomorphism; I=top gives the entire additive sheaf on the J subscheme;
   the empty scheme is allowed by the covering argument. No properness, nilpotence,
   nonemptiness or square-zero premise was introduced, and no data is selected from
   an unproved existence statement.
4. **Shortest route and pruning: pass after import repair.** Independently searched
   local Mathlib kernel/composite and abelian exactness infrastructure, and searched
   lean/Sheaf and lean/WeilConjectures for this comparison. No direct geometric
   theorem replacing the argument was found. Mathlib's imageToKernel_epi_comp is
   about precomposing the first map of a complex, not the kernel-of-composite
   pullback used here. Kept the correct proof. Removed both redundant proof-only
   imports, testing each removal and both together. The public imports supply the
   statement's additive sheaf and ideal-subscheme notions. All four old proof_deps
   remain used, so no dependency node is pruned. Read dag/units/sk-prop-h2.json:
   this extracted node realizes no unit statement or step there, and the Kummer
   unit route is unchanged. The referenced literature text is not installed on
   this machine; the supplied node statement and the cited Mathlib source were read.
5. **DAG agreement: pass.** Compared the delivered node with the repository node.
   Only proof and proof_origin changed. The four proof steps describe the compiled
   local-cover, composition, categorical pullback and preserved-kernel argument;
   their uses have exactly the recorded proof_deps as their union. The lean
   statement record is unchanged and matches the theorem. No new node is required
   for an unclosed obligation, since there are none.

Second-reading changes: removed the two redundant proof-only imports; corrected
What changed and No longer needed accordingly; added this independent review.
Closed one original hole, added zero holes, pruned no dependency nodes or modules.
