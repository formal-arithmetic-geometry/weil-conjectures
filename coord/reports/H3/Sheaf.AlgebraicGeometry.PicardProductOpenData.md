## What changed

Replaced the whole proof of `AlgebraicGeometry.Scheme.picard_product_open_data`, preserving
its signature and public imports. The proof now constructs the two-factor family indexed by
`Fin 2`, obtains local descent from the universal Picard locus and the existing H¹
multiple-locus theorem, and trivializes the descended module by pulling back along the
section `σ ≫ iX`. It then supplies the explicit auxiliary module as the actual structure
module, the constructed trivialization, and the identity isomorphism. No arbitrary object
is defined by selecting an unproved existence witness.

Added three modules, each with one public theorem and a matching node:
`Sheaf.AlgebraicGeometry.PicardH1LocalDescent`,
`Sheaf.AlgebraicGeometry.ProductUniversalStructurePushforward`, and
`Sheaf.AlgebraicGeometry.ProductResidueH1Injective`.
The first two have complete Lean proofs; only the third has a whole-proof `sorry`.
The product pushforward proof compares the chosen tensor-adjunction unit with the canonical
map on modules, checks it on every open, and uses explicit pullback-pasting isomorphisms.
The section trivialization is proved in a private helper in the original module.
All new imports in the original module are proof-only imports.

A declaration-local `linter.unusedVariables` setting suppresses warnings about the original
existential binder names `eL` and `eN`, which intentionally do not occur in `True`.
Their names and the statement were preserved. No existing interface was changed.

The entire sandbox compiles through `lcompile.py --all` with no warnings. The delivery dry
run checks the same files and the axiom probe. No push is requested or performed.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.picard_product_open_data`
(node `lem-sc-picard-product-open-data`). This is a decomposition: one original hole is
replaced by one strictly smaller geometric input, so the direct-hole net is zero.
The main module contains no `sorry`.

Proved the new public theorems:

- `AlgebraicGeometry.Scheme.picard_h1_local_descent`
  (`lem-sc-picard-h1-local-descent`), from the existing named Picard-locus declarations.
- `AlgebraicGeometry.Scheme.product_universal_structure_pushforward`
  (`lem-sc-product-universal-structure-pushforward`), by the section-map criterion and pasting.

Exactly one added hole remains:
`AlgebraicGeometry.Scheme.product_residue_h1_injective`
(`lem-sc-product-residue-h1-injective`), in
`lean/Sheaf/AlgebraicGeometry/ProductResidueH1Injective.lean`.
It has no line bundle and no neighbourhood or trivialization conclusion: its conclusion is
only injectivity of the pair of H¹ slice maps after residue-field base change. Its docstring
and node explain how to specialize the existing field-product injectivity theorem and
transport it through the fibre-product comparison. The hypothesis-to-scalar-global-sections
comparison and naturality of the explicit cohomology map are the remaining formal glue.

The existing holes in `picard_diagonal_locally_closed`, `picard_h1_multiple_locus`, and
`picard_h1_product_injective` are used as intended by stage 3; they were not edited or copied.
Thus the completed assembly is not a claim that the full transitive proof is sorry-free.

## No longer needed

Removed the original module's direct imports:

- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar` and its planned dependency
  `lem-pc-flat-base-change-cohom`: this argument does not use flat cohomology base change.
  Universal structure pushforward follows directly from the two universal hypotheses.
- `Sheaf.AlgebraicGeometry.PicardH1MultipleLocus`: still needed through the proved local
  descent module, so this is a removed direct import, not global pruning of its node.
- `Sheaf.AlgebraicGeometry.PicardH1ProductInjective`: still planned below the residue-field
  input, so this is a removed direct import, not global pruning of its node.

An import-closure comparison found no library modules pruned from this item: `EulerChar`
is still reachable through other dependencies. Its explicit planned proof edge is removed;
this is not global pruning of that module. The unit statement and
route remain unchanged: the general theorem of the cube still uses product Picard openness,
which still uses the multiple-locus theorem and the product H¹ input. No closed-image or
further-shrinking lemma is needed in the final assembly, because the given section slice
already trivializes the descended base module on the obtained open.

## Where the brief, the DAG or earlier work was wrong

The recorded `finrankH_pullback` in `EulerChar` is a field-extension specialization, not a
universal structure-pushforward theorem for the product. The delivery eliminates that
unnecessary planned input instead of trying to apply it to an incompatible conclusion.

`picard_product_open_core` and `picard_product_open` depend on this item, and cannot be
used as shortcuts without a cycle. The original one-step plan omitted the fibre-product
transport, universal-locus evaluation, and the trivialization of the descended base module.
These are now either explicit Lean proofs or the one precisely stated remaining input.

The Stacks TeX source is absent from this read-only clone. The source statements and proofs
were read from https://stacks.math.columbia.edu/tag/0BF3 and
https://stacks.math.columbia.edu/tag/0BF2. LeanSearch was unavailable (Internal Server Error);
LeanFinder, Loogle, and repository/Mathlib grep were also run and their actual results recorded.
Blueprint searches found no identical existing unit statement for the new lemmas.
The ancestor script returns `None` for the original data node because its earlier
`created.item` is a module name. New nodes use the already recorded ancestor
`thm-sc-theorem-of-cube` of product openness, with the intervening nodes named explicitly.

Edge cases checked: the local descent construction also works when `n = 0`; the injectivity
hypothesis then supplies the necessary vanishing, while factorization through every identity
locus is vacuous. The product pushforward proof does not require a point of the base or any
flatness or finiteness hypothesis. The residue H¹ assertion works over arbitrary residue
fields; properness and rational-point sections suffice and no reducedness is added.
The final trivialization works for the zero-size open scheme as well; the given `s ∈ U`
ensures the neighbourhood in this application is nonempty.

## New nodes

`lem-sc-picard-h1-local-descent`: the universal-locus application for an arbitrary finite
family with trivial restrictions. Its proof is complete in
`lean/Sheaf/AlgebraicGeometry/PicardH1LocalDescent.lean`.

`lem-sc-product-universal-structure-pushforward`: stability of universal structure
pushforward under products, with no finiteness assumptions. Its proof is complete in
`lean/Sheaf/AlgebraicGeometry/ProductUniversalStructurePushforward.lean`.

`lem-sc-product-residue-h1-injective`: the residue-field specialization and transport of
the existing Kunneth slice-injectivity result. It is the only added hole, in
`lean/Sheaf/AlgebraicGeometry/ProductResidueH1Injective.lean`.

No change record is needed: all existing signatures and public imports are identical.

## Second reading by H3

1. Compared the delivered `PicardProductOpenData.lean` against the repository version. The
   existing theorem signature is byte-for-byte unchanged; the proof-only imports and the
   three new modules are the only interface additions.
2. Compiled all four delivered modules with `lcompile.py --all`. They compile cleanly; the
   only remaining `sorry` is the named theorem
   `AlgebraicGeometry.Scheme.product_residue_h1_injective`, and no forbidden declarations or
   hollow definitions occur. The completed declarations use only the permitted foundations
   (the split theorem necessarily carries `sorryAx`).
3. Checked the three split-off statements against their docstrings and DAG nodes. The two
   proved auxiliary statements are true and have the advertised strength; the residue-field
   injectivity statement is a strictly smaller, precise input and its remaining proof is
   documented. No duplicate declaration was found in the repository or Mathlib searches.
4. Checked the proof route and imports against the unit record. The route retains the
   product universal-locus, residue H¹, and local-descent steps, and removes only the unused
   Euler-characteristic dependency. The node proof, proof dependencies, and proof origins
   agree with the Lean proof; no additional pruning was identified.
5. Checked edge cases and statement stability: the Fin 2 indexing, section pullback
   trivialization, and residue-field formulation do not add hypotheses or weaken the target.
   The unit's realized route remains unchanged.

I changed only this second-reading report section; no Lean declaration or DAG statement was
altered during review.
