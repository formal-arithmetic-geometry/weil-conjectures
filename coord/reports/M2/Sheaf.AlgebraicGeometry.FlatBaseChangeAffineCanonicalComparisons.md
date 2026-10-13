## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.FlatBaseChangeAffineCanonicalComparisons`
with a reduction that constructs the source B-linear tensor equivalence and its unit formula.
It uses `AffineCohomologySectionEquiv`, `OrdinaryHigherImageQuasiCoherent`, and
`ModulePullbackAffineSections`. The source natural comparison and target chart/Leray
compatibility are chosen simultaneously by one new intermediate theorem in
`Sheaf.AlgebraicGeometry.FlatBaseChangeTargetLerayComparison`. The existing statement and
public imports are unchanged. The item's node now records the implemented reduction.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.exists_flatBaseChange_affine_canonical_comparisons`
(node `new-flat-base-change-affine-canonical-comparisons`), from existing declarations and
the target comparison below. No sorry remains in the item.

Added: `AlgebraicGeometry.Scheme.Modules.exists_flatBaseChange_target_leray_comparison`
(node `new-flat-base-change-target-leray-comparison`), whose entire proof is `by sorry`.
This is a decomposition (one upper hole closed, one strictly partial lower hole added),
not a net hole reduction or a claim that the canonical comparisons are axiom-free.
The new theorem constructs only the target comparison with a natural source Ext family;
it contains neither the source tensor equivalence nor its normalization. The parent
constructs these using affine Leray and tensor sections, then combines the two sides.

The unchanged imported lemmas retain their existing dependencies. No definition, existing
signature, axiom, or arbitrary data witness is added or changed. Existential comparisons
are eliminated only inside theorem proofs. Empty opens and zero coefficients yield zero
complexes; degree zero uses the augmentations, and the new argument assumes no flatness.

## No longer needed

Removed direct proof imports from the item:
- `Sheaf.AlgebraicGeometry.LerayDegenerateSections`
  (`lem-pc-leray-degenerate-sections`);
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`
  (`lem-pc-affine-vanishing`);
- `Sheaf.Paper.HigherDirectImagePresheaf`
  (`lem-weil-pbc-higher-direct-image-presheaf`);
- `Sheaf.AlgebraicGeometry.ModuleCohomologySourceComparison`
  (`lem-sc-module-cohomology-source-comparison`);
- `Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural`
  (`lem-sc-module-abelian-zariski-cohomology`).

These are not globally pruned: the new target comparison still needs their mathematical
results, and several remain reachable through the existing source affine lemma.
Also removed from the parent proof-dependency list (their definitions remain in statement
imports or the target construction): `def-pc-fibre-product`,
`def-pc-flat-cohomology-comparison`, `def-pc-module-pullback`, and
`def-weil-pbc-module-cohomology-fmap`. The restriction/pullback comparison remains used.
The second reader restored plain proof imports in the new open theorem for every
stated proof dependency, including the Mathlib open-immersion comparison. These
imports record its proof plan; the five imports removed from the parent are retained
there. No module is globally pruned. No unit statement or realized proof step is
bypassed, and no downstream module is asserted to leave the target closure.

## Where the brief, the DAG or earlier work was wrong

The DAG describes the correct mathematical route but its listed generic natural comparison
alone does not pin the degreewise comparison against cohomological inverse image. Arbitrary
natural additive families may differ by degreewise automorphisms. The new theorem chooses
one compatible family and the target edge together, rather than claiming that an arbitrary
family commutes with base change. The existing affine source theorem assumes flatness even
though its proof construction does not use it; its underlying normalized affine Leray lemma
is available without flatness and is reused here.

LeanSearch was unavailable (Internal Server Error); LeanFinder, Loogle, source searches,
and blueprint searches were performed and recorded. The main compilation needed explicit
intermediate comparison terms and reduction of categorical hom-type wrappers in the
compatibility hypothesis. This avoids expensive conversion through module homology data.

## New nodes

`new-flat-base-change-target-leray-comparison` states the target affine chart/Leray comparison
and its common-section-complex pullback compatibility for a natural source family. Its
module contains one public named theorem with a source and complete proof in words; its
node records the chart, affine vanishing and augmented-resolution steps. It is strictly
the target half of the argument. No change record is needed: existing interfaces remain
identical and there are no forced adaptations.


## Second reading by M2

1. Compared the delivered parent module with the repository by diff and extracted its
   declaration header through `:= by`: byte-for-byte identical. Existing public
   imports, definitions, visibility and docstring are unchanged. The only new declaration
   is the reported target comparison. No change record or forced adaptation is needed.
2. Compiled both modules in import order with `lcompile.py`: clean. Inspected every
   declaration and scanned for forbidden constructs. Only the new public theorem has
   `sorry`, as reported; it has its source, full mathematical argument and DAG node.
   Scratch-copy `#print axioms` for both the parent and new theorem reports exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The parent remains
   conditional on open imported results; there is no claim of an axiom-free target.
   The existential families are eliminated inside proofs, never used to define data.
3. Read the new statement against D's augmentation, components and unit-square fields
   and the definitions of the two cohomology maps. Checked degree zero (the coefficient
   unit and augmentations), empty opens and zero coefficients (zero groups), and an
   identity base change (the same normalized comparison). The chart equivalence and
   target Leray edge exist without flatness; no base-change isomorphism is asserted.
   The natural source family is chosen compatibly, rather than universally quantified.
   This is strictly the target part: the parent still constructs and normalizes the
   source B-linear tensor equivalence from affine sections. It is a valid one-for-one
   decomposition, net zero holes. Fresh LeanFinder, Loogle and grep searches used
   Leray naturality, inverse image, Ext functoriality and resolution-class terminology.
   Loogle found the standard LinearEquiv.ofBijective construction; two geometric
   identifiers were unavailable, and no absence claim follows from those errors.
   Direct source review found H.globalFreeExtComparison and affine-open section
   isomorphisms, but neither states the required chart/resolution compatibility;
   FlatBaseChangeAffineTarget imports the parent, so is not reusable here.
4. Read the source comparison, affine cohomology section equivalence, tensor section
   construction and the original node plan. The source proof takes the existing
   normalized affine equivalence and extends scalars, using tensor commutation and
   bijectivity; its equations are checked by Lean. The remaining chart/Ext comparison
   is substantial and cannot be closed in a few minutes from the located results.
   Checked sk-thm-p1.json `realized`: no realized node or unit step is bypassed or
   changed. Completed the report's old proof-dependency removal list. Restored the
   new open node's planned dependencies as plain imports, preserving their reachability.
5. Checked both nodes' Lean declarations and verbatim signatures, the union of each
   proof's uses against proof_deps, source references, new-node creation and blueprint
   records. Only proof, proof_deps and proof_origin differ for the existing node.
   The implemented parent proof agrees with those steps. The new node describes its
   remaining target chart comparison and contains all required metadata.

Second-reading changes: restored the new theorem's plain proof-plan imports; completed
`No longer needed`; recorded this independent review and the additional searches.
No proof, existing signature, definition or public import was changed by the second reader.
