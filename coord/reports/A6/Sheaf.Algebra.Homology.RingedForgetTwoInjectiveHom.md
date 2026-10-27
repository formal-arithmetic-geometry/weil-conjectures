## What changed

Proved the general `CategoryTheory.RingedForgetTwoInjective.ringed_forget_two_injective_hom`
by constructing the required projection-normalized chain comparison and descending it through
the localization of K-injective complexes. The existing signatures, representative normalization,
public imports and native structures are preserved. The delivery adds four proved helper
modules and relocates the existing definitions and representative construction into a models
module. The item publicly re-exports that module and privately imports the two sheaf
specializations. The moved declaration names, signatures, visibility and bodies are identical.

`RingedHomComplexComparison` constructs the degreewise product-cone isomorphism, checks the
standard differential and both-variable naturality on projections, and assembles the chain
natural isomorphism. Its abstract projection hypotheses avoid unfolding the large chosen
Hom-complex construction. `RingedSheafHomComplexComparison` specializes them using
`HomComplexComponents`. `KInjectiveHomComparisonDescent` combines representative isomorphisms with
the chain comparison and the exact-functor localization factors. Full faithfulness of
precomposition by the opposite product of K-injective localizations descends this isomorphism,
with the required representative equality.

Validation: all six delivered Lean files passed `lcompile.py --all`, along with the unchanged
direct importers `Sheaf.Algebra.Homology.RingedForgetTensorTransposition` and
`Sheaf.Paper.NativeWeilRowHomComparison`. Their temporary sandbox copies were removed after
the check. The models module uses default respectTransparency settings. Both original theorem
signatures and all original public imports were checked against the shared source.

## Proved and sorry left

Closed one of the item's two original holes:
`CategoryTheory.RingedForgetTwoInjective.ringed_forget_two_injective_hom`
(node `lem-sf-ringed-forget-two-injective-hom`).

The remaining hole, unchanged, is
`AlgebraicGeometry.ProEtaleWeilSheaf.native_two_injective_hom_model`
(the same node). No new holes are added or split off. The previously proved
`CategoryTheory.RingedForgetTwoInjective.ringedRepresentatives` is preserved.

The new results `CategoryTheory.ringedHomComplexComparison`,
`CategoryTheory.sheafHomComplexComparison`,
`CategoryTheory.kInjectiveHomComparisonDescent`, and
`CategoryTheory.sheafHomComparisonDescent` have complete proofs. Their statements are
strict parts of the existing argument: the first pair only compares complexes; the descent
results assume a chain comparison and natural representative models and only handle descent.

## No longer needed

No existing module is withdrawn. All original public imports are retained verbatim.
The private `QuasiIsoHomComplexMapOfUniverses` import moves from the item to the models module
with its only user, the already proved `ringedRepresentatives` construction. It remains needed.
The closed tensor structures and coherence binders of the general theorem are retained, although
the normalized forgetting argument needs only the internal-Hom models, exactness, preservation
of products and K-injectives. The original native-specialization dependencies remain needed
by its unfinished proof. The DAG's component and descent steps are now realized by the new
proved lemmas. No unit statement or unit proof step is bypassed. The general comparison does
not use the original explicit source- and target-homotopy formulas: the localization descent theorem
replaces that calculation. The generic node `lem-pur-rhom-well-defined` is replaced by its
already proved universe companion `lem-pur-rhom-well-defined-universes` in the representative
argument. No module is thereby withdrawn: the retained imports and native specialization
still carry their existing interfaces.

## Where the brief, the DAG or earlier work was wrong

The rework table contains a quarantine record, but the current item source is present. Its
original version compiled successfully in 35.9 seconds; restoration or deletion was therefore
unnecessary. The item remains present with its original theorem attachment. Its moved declarations have
an explicit models-node attachment and are publicly re-exported.

The chain comparison and descent were described together in the original node. They can be
implemented independently: product-cone uniqueness handles the former, and the existing
K-injective localization API handles the latter. The native sign-normalization and coefficient
specialization remain unfinished; this delivery makes no claim to prove them.

## New nodes

`lem-sf-ringed-hom-complex-comparison` realizes the original steps 4–5 for abstract product-total
Hom complexes. Its source is Stacks Section 0A8X and the parent's explicit
component calculation. Its edge cases include zero complexes, identity forgetting, and every
integer degree; no boundedness or injectivity is used in this result.

`lem-sf-kinjective-hom-comparison-descent` realizes the localization part of the original step 5.
It works for arbitrary abelian categories with K-injective resolutions in the source, with
natural representative models and a given chain isomorphism. Its source is Stacks 0A95 and
08J7, formalized through the existing K-injective and localization APIs. No K-flatness, boundedness
or source-site identification is added. LeanSearch, LeanFinder/Loogle, and source searches
found the product and localization ingredients, but no duplicate complete theorem.

`lem-sf-ringed-sheaf-hom-complex-comparison` specializes the abstract product-total
comparison to `homComplexFunctor`, using `homComplexIsLimit`, `homComplex_d_π`, and
`homComplexFunctor_map_f_π`. The source is the same Stacks component calculation.
This separates the specialization from the representative construction after profiling showed
that checking their combined proof term exceeded the per-file limit. The abstract construction
first removed repeated unfolding of the chosen Hom-complex definitions; this further
separation keeps each application small. No shared definition or interface is changed.

`lem-sf-ringed-sheaf-hom-comparison-descent` specializes the abstract descent theorem to the
actual ringed sheaf-Hom models. It assumes the representative isomorphisms, their naturality,
and the chain comparison. The only conclusion is their derived descent and representative
equation. Its source is Stacks 0A95 and 08J7 and the parent's localization step. This isolates
the expensive specialization of the large chosen model definitions. It adds no hole and changes
no shared definition or interface.

`def-sf-ringed-two-injective-models` records the relocation of the existing representative,
comparison, standard-model and native-model definitions, plus the already proved representative
construction. The final theorems remain in the original module. No definition changes.
The reason is the measured cumulative compile cost after proof abstraction and specialization.
The change record is `coord/changes/A6-ringed-two-injective-module-split.md`.
The change record lists both direct importers tested and the indirect users reported by
preflight. The first preflight found one metadata error: the models node included the structure
body in lean.statement; this now contains only the signature before where. No Lean code
changed for that repair.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
