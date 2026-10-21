## What changed

Implemented `CochainComplex.filteredTensor_localization` from the existing replacement
and graded-comparison declarations. The proof constructs the filtered homotopy congruence,
forms the convolution bifunctor on the good homotopy category, proves that it inverts the
specified denominators, applies the two-variable localization, and transports along the
replacement equivalence. Forgetting and each grading are constructed using the homotopy
quotient and single-variable localization, with the required representative map formulas.

The signed tensor homotopy is proved separately, including its factorization through every
image defining a convolution filtration step. The underlying comparison is obtained from
the quotient's lax monoidal comparison and `Localization.lift₂NatIso`, with its prescribed
representative normalization. The graded argument uses natural coproduct legs, descent by
`Localization.lift₂NatTrans`, transport of colimits by isomorphisms, and reduction to any
finite support. The finite-support proof includes existence, naturality, enlargement and
the normalization on representatives; empty supports and unbounded cochain degrees are
included.

Moved the ten existing representative definitions into the publicly reexported
`FilteredTensorLocalizationSetup` to avoid an import cycle. The first seven structural
wrappers are transparent abbreviations of the same terms. The other three constructions
are unchanged. The change record lists all consumers; no consumer adaptation or source-tree
edit is required. The final `lcompile.py --all` passes all six delivered modules with no
errors or warnings; the longest file takes 24.1 seconds and the parent takes 18.8 seconds.

## Proved and sorry left

Closed the original hole in `CochainComplex.filteredTensor_localization`
(`lem-kun-filtered-tensor-localization`). The delivery introduces no new `sorry`.
The new public theorems are
`CochainComplex.kunnethConvolution_filtered_homotopy`,
`CochainComplex.filteredTensor_localized_graded_cocone`,
`CochainComplex.filteredTensor_localized_graded_comparison`, and
`CochainComplex.filteredTensor_localized_comparisons`.

Thus this is one original hole closed, zero holes added, and zero unfinished split-offs.
The existing holes in the supplied replacement and graded-comparison declarations are
unchanged; the proof uses those stated dependencies as this stage requires.

## No longer needed

The parent proof no longer needs separate applications of
`lem-weil-pbc-complex-ses-homology-long-exact` or
`lem-weil-pbc-complex-ses-long-exact-naturality`: the proved
`CochainComplex.finiteFilteredModule_graded_comparison` supplies the needed underlying
quasi-isomorphism directly. The signed tensor construction moves to the proved homotopy
lemma, rather than remaining an unformalized step of the parent.

Removed redundant direct imports from the parent: `FiniteFilteredKFlatReplacement`,
`FilteredTensorGradedComparison`, `DerivedTensorSecondFactorFunctor`,
`Mathlib.CategoryTheory.Localization.Bifunctor`, `FiniteFilteredModuleHomotopy`, and
`Mathlib.CategoryTheory.Whiskering`. The shared interface publicly reexports the first
five dependencies. In the interface, removed direct imports of
`FilteredTensorGradedComparison`, `DerivedTensorSecondFactorFunctor`, and
`FiniteFilteredModuleHomotopy`, already publicly reexported by
`FiniteFilteredKFlatReplacement`. Removed redundant `Mathlib.CategoryTheory.Whiskering`
imports from both comparison descent and graded cocone descent. These are import
simplifications, not claims that their declarations are unused globally.

No module is withdrawn. In particular, the second-factor derived tensor declaration remains
needed through the graded-comparison interface, and its maintainer approval is retained.
There is no claim that a source declaration or a module in another dependency closure is
unused.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The existing plan needs explicit homotopy/image
factorizations and normalized graded coproduct legs; the new proved lemmas provide these
steps. The finite graded-comparison theorem already available in the library shortens the
forgetful-localization step. The quarantined item's attachment and original mathematical
statement are preserved; absence during synchronization was not treated as withdrawal.

The representative wrappers and inferred coproduct families required care during
elaboration: explicit intermediate object types and named coproduct families avoid
expanding the tensor total complex when matching the canonical comparisons.

## New nodes

`def-kun-filtered-tensor-representative-interface` attaches the ten existing representative
constructions to their common interface module. The names, types and mathematical terms
are preserved. The transparency change and complete consumer list are recorded in
`coord/changes/Q4-filtered-tensor-localization-interface.md`.

`lem-kun-convolution-filtered-homotopy` states and proves preservation of the filtered
homotopy relation by the signed convolution tensor. It uses degreewise coproduct
universality and epimorphisms onto the convolution images.

`lem-kun-filtered-tensor-graded-cocone` supplies the natural, normalized, colimiting graded
cocone after localization. It transports the existing representative cocone and descends
its legs; it does not choose a finite support.

`lem-kun-filtered-tensor-graded-descent` proves the finite-support graded comparison from
that cocone. Its remaining arguments are finite-filtration vanishing and explicit
biproduct universal-property calculations.

`lem-kun-filtered-tensor-comparison-descent` pairs the proved underlying comparison with
the proved graded comparison. All functors and their lifting witnesses are inputs; this
lemma does not replace any construction made by the parent proof.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
