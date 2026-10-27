## What changed

Reduced `WeilConjectures.CompletedOpenTensor.completedOpenTensorRepresentatives` to
compatible context construction and ordinary derived descent. The original theorem's
signature is unchanged. Its proof now establishes the remaining strict normalization
and system comparison from existing declarations:

- K-flatness and flatness of the two total tensors follow from the proved
  `SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model`.
- `ordinaryReductionAugmentedComputation` supplies computations natural on good complexes.
  A private lemma proves uniqueness of their morphisms using their strict scalar-unit
  augmentations and injectivity of the adjunction hom-equivalence.
- The strict chain's evaluated component follows from `strictOpen.components` and
  naturality of ordinary evaluation. Applying it to scalar-unit sections proves the
  exact local augmentation equation in every degree and coefficient level.
- A private categorical pasting lemma combines ordinary descent, the strict open model
  square and naturality of the augmented computation. It cancels the interior tensor
  presentation and proves the whole-system square, before any total limit.

Moved the 21 existing interface declarations verbatim to
`Sheaf.Paper.CompletedOpenTensorRepresentativeData` to avoid an import cycle between
the item and its two construction lemmas. Their signatures and bodies, and the item
signature, were compared mechanically to the original source. The original module
retains its public imports and publicly reexports the interface. The change record is
`coord/changes/J9-completed-open-tensor-representative-data.md`.

No definition chooses data from the unproved context theorem.
The local proof helpers are private and proved. The natural tensor presentations and
their comparison on good complexes are separate proved theorems, to keep each module
within the compile-time limit. The unit route and upstream source declarations
are preserved. Zero objects, identity and empty open immersions introduce no new
hypotheses: the normalization proof uses naturality and inverse laws uniformly.

## Proved and sorry left

Closed the original one hole:
`WeilConjectures.CompletedOpenTensor.completedOpenTensorRepresentatives`.

Proved the natural good-complex presentations
`WeilConjectures.CompletedOpenTensor.openTensorGoodPresentations`, their comparison
`WeilConjectures.CompletedOpenTensor.openTensorGoodComparison` and the ordinary descent theorem
`WeilConjectures.CompletedOpenTensor.openTensorOrdinaryDescent` using the product of the
two good-complex localizations, natural K-flat tensor models and the given natural chain
comparison. Its representative equation follows by counit and inverse cancellation.
Restriction goodness is supplied by the existing proved `restriction_preservesGood`.

Verification: all six packet modules compile without profiler options. All four unchanged
direct importers compile against this overlay: `CompletedOpenTensorSystemRealization`,
`OpenTensorQuotientAugmentation`, `OpenTensorQuotientCochains`, and
`OpenTensorQuotientGeometry`. Each passed the server's 60-second Lean limit. The unchanged
consumer copies were removed from the sandbox after verification. No consumer adaptation
was necessary.

Added one strictly smaller hole:
`WeilConjectures.CompletedOpenTensor.completedOpenTensorContext`, which only constructs
compatible coefficient/completion models. It asserts no ordinary tensor comparison,
scalar-unit tensor equation or whole-system representative square.

This remains a decomposition rather than a proof from axioms alone: one original hole
closed, one smaller hole added, net zero. The original module, the three ordinary-comparison
modules and data module contain zero `sorry`; the context module contains one. No other holes
are introduced.

## No longer needed

No module is withdrawn or claimed globally prunable. The original public imports remain
available for downstream compatibility. The old direct proof dependencies for context
construction and ordinary descent now belong to the corresponding smaller nodes rather
than the item's glue proof. They remain needed transitively and are not counted as pruned.
The old summand-by-summand reconstruction of the scalar-unit and system squares is
unnecessary in this item: `Comparison.components`, `Comparison.model`, augmented
computation uniqueness and naturality prove those squares directly.

The former direct dependency `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
(module `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`) is not needed for
the ordinary descent or restriction step here: `lem-sf-open-restriction-good-complex`
and product localization replace that route. This is a local proof-dependency removal,
not a request to delete that theorem or module. The former `lem-pc-kflat-resolution`
is used through the existing good-complex localization API rather than separately.
The other original dependencies remain in the compatible-context construction or the
unchanged interface dependencies: `lem-coef-derived-system-evaluation-calculus`,
`lem-sf-immersion-completed-pullback-comparison`,
`lem-sf-integral-open-reduction-comparison`, `lem-sf-open-quotient-koszul-completeness`,
`lem-sf-open-semilinear-tensor-model`, `lem-sf-open-tensor-normalization`,
`lem-weil-pbc-constant-completion-equivalence`, and `def-pur-integral-derived-operations`.
None of those is claimed unnecessary globally.

The proof-only imports are the two new construction modules,
`Sheaf.Paper.OpenRestrictionGoodComplex`,
`Sheaf.SixFunctors.OrdinaryReductionAugmentedComputation`, and
`Sheaf.Algebra.Homology.KFlatTotalTensorModel`; each is used.

## Where the brief, the DAG or earlier work was wrong

The rework record quarantined this item because of a transitive false-tail import.
Its current source and archive preserve the full representative interface. The baseline
source compiled successfully against the compiler's current overlay; no declaration,
archive, attachment or parent dependency was withdrawn on the basis of quarantine.

The previous plan did not mention the already proved natural augmented-computation
API. Using it avoids a fresh construction of quotient computations and permits a direct
proof of the whole-system square. The revised item node records this shorter argument.
The scheme clauses of `OpenQuotientKoszulCompleteness` specialize site and coefficient
universes together. The new context plan uses its coefficient-only adic datum and the
independent-universe `canonicalModels`, `normalizedCompletionRealization`, and open
Roos descent APIs for the completion and unit fields. No universe is identified in the
item or any new theorem.

The difficult simultaneous choice of compatible closed structures and actual completion
units remains explicit in the context lemma, rather than being assumed by independently
choosing existential witnesses.

Dependency checking also encountered an existing cycle outside this packet:
`lem-pc-ring-hom-extension-differential` has the adjacent-case node as a proof dependency,
while `lem-pc-ring-hom-extension-differential-adjacent` has the former as a statement
dependency. Neither node is changed here. No node in this packet has a dependency path
back to itself.

## New nodes

- `def-pur-completed-open-tensor-representative-data`: owns the 21 unchanged relocated
  interface declarations, including Context and RepresentativeLaws.
- `lem-pur-completed-open-tensor-context`: the compatible coefficient/completion model
  construction, original proof step 1.
- `lem-pur-open-tensor-good-presentations`: the proved natural source and open tensor
  presentations, with their exact component identifications.
- `lem-pur-open-tensor-good-comparison`: the proved natural comparison on good complexes,
  before localization; separated to keep the compile time bounded.
- `lem-pur-open-tensor-ordinary-descent`: the ordinary localization and representative
  part of original proof step 4.

Each node records three kinds of Mathlib search and its source in the current unit route.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
