## What changed

Replaced the sole sorry in `AlgebraicGeometry.modulePullbackIdealQuotient` with a complete
Lean reduction to `AlgebraicGeometry.modulePullbackIdealProductImage`. The latter is a new,
strictly smaller statement about the image of the pulled-back product inclusion only.
It has no quotient, epimorphism, kernel fork, comparison isomorphism or naturality clause.
The main proof derives all those clauses by cokernel universal properties. The affine ideal
formula uses the existing closed source theorem `Scheme.IdealSheafData.ideal_comap_appLE`;
the power formula is proved on the affine cover with `Ideal.map_pow`.

Added proof imports of the source affine ideal module, the new image module, and Mathlib's
abelian-category and cokernel-preservation modules. All existing public imports and the
entire theorem signature are unchanged. Both delivered Lean modules compile cleanly through
lcompile.py. No existing definition, statement or visibility changes.

Updated the main DAG proof to match the Lean reduction. Also updated only the proof fields
of `lem-pc-ideal-sheaf-comap-affine-extension`: its attached sorry-free source implementation
is independent of this item, but its obsolete natural-language sketch cited this item.
Recording the actual independent implementation prevents a spurious dependency cycle.

## Proved and sorry left

Closed: `AlgebraicGeometry.modulePullbackIdealQuotient`
(node `lem-weil-pbc-module-pullback-ideal-quotient`), the sole original hole.

Added: `AlgebraicGeometry.modulePullbackIdealProductImage`
(node `lem-weil-pbc-module-pullback-ideal-product-image`), exactly `:= by sorry` in its own
module with a complete affine tensor-generator and sheaf-gluing argument in its docstring.

This is a decomposition: one hole closed, one strictly smaller hole added, net zero holes.
The ideal formula, power compatibility, categorical quotient construction, epi assertion,
kernel limit proof and naturality are checked Lean proofs. No sorry remains in the item.
The remaining theorem was checked conceptually on J=0, J=O, G=0, the identity morphism,
empty affine opens, and nonflat ring maps: only an image is asserted, so no injectivity of
the pulled-back inclusion is assumed. No arbitrary data is chosen from an existence sorry.

## No longer needed

Removed direct proof imports from the main module:

- `Sheaf.AlgebraicGeometry.Coherent` (already publicly supplied by CoherentFormalModule).
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections` (needed only in the image lemma).
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`
  (needed only in the image lemma).
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
  (needed only in the image lemma).
- `Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`
  (needed only in the image lemma).

The first, affine-section, affine-product, quasi-coherent-image and Tilde nodes are not
claimed globally pruned: their notions or arguments remain needed below the image lemma.
The structure-sheaf comparison node `lem-weil-pbc-module-pullback-structure-sheaf` and its
module `Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf` are no longer needed by this
route. Neither are the old proof's `lem-weil-pbc-spec-module-tilde-sections`,
`lem-weil-pbc-sheaf-morphism-on-basis` or `lem-weil-pbc-tensor-right-exact` as separate
steps of this item: the ideal formula is already proved, and the quotient construction uses
preservation of cokernels by the proved pullback adjunction. The image calculation retains
affine tensor sections and computes the image directly by generators. Other users may still
need all these nodes; no global unreachability is asserted. No unit-realizing node is bypassed.

## Where the brief, the DAG or earlier work was wrong

The old search missed the source library's exact affine ideal formula (Affine.lean:95) and
its independent comap power proof (Functorial.lean:379). The delivery uses the former and
proves powers directly, so no new ideal-extension theorem is introduced.

The closed affine-extension node still carried an obsolete plan citing this item's clause
(1). Its actual attached source proof uses ideal-sheaf Galois connections and restriction
of affine charts, not this item. Its proof fields are updated to describe that implementation.

The local literature/stacks-project/coherent.tex is absent. Read the source at
https://stacks.math.columbia.edu/tag/0887 instead; its displayed quotient calculation is the
source of the reduction. LeanSearch was unavailable (HTTP Internal Server Error), recorded
as unavailable. LeanFinder and Mathlib grep completed; local source and Sheaf searches found
no declaration of the new image equality. Blueprint searches for ideal module pullback,
ideal product and 0887 returned no matching imported blueprint node.

## New nodes

`lem-weil-pbc-module-pullback-ideal-product-image`, in its own module
`Sheaf.AlgebraicGeometry.ModulePullbackIdealProductImage`, states equality of two images
inside the pulled-back module. It is strictly the image-identification part of the argument,
not a repackaging of the main quotient theorem. Its node records the affine comparison,
image-on-affines, ideal-product and gluing steps, their sources and completed searches.
No change record is required: no existing interface changes or forced adaptations.

## Second reading by J2

1. **Signatures:** Compared the delivered main module with the repository version. Existing
   declaration signatures are unchanged byte for byte; the added image theorem is a new
   split-off declaration with its own node.
2. **Proof:** Compiled both delivered modules with `lcompile.py`; the main theorem has no
   `sorry`, and the only remaining `sorry` is the named image theorem. No forbidden
   declarations or hollow definitions occur.
3. **Statements:** Checked the image statement on zero and unit ideals, zero modules,
   identity maps, empty affine opens, and non-flat maps. It asserts only equality of images,
   so it does not assume injectivity; it is strictly weaker than the quotient theorem and
   exactly supports the kernel argument.
4. **Pruning:** Confirmed the removed imports are unnecessary in the main proof and that
   the retained image-module imports are used. The main proof follows the cokernel and
   pullback route recorded in the DAG; no unit-realizing step is bypassed.
5. **DAG/report agreement:** Checked the main and image nodes against the Lean declarations,
   including proof dependencies and the decomposition accounting. The updated affine
   extension node records its independent source proof and removes the obsolete cycle.

Changed only this second-reading record; no Lean declarations or DAG statements were altered
by this review.
