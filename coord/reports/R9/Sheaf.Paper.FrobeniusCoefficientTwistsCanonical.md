## What changed

Reduced the augmentation-isomorphism obligation in
`Sheaf.Paper.FrobeniusCoefficientTwistsCanonical`. The proved private lemma
`WeilConjectures.FrobeniusCoefficientTwists.pullbackAugmentation_eq` identifies the
specified augmentation with the adjunction-normalized ordinary completion chain.
The augmentation construction proves its product projections on adjunction-unit
generators and its vanishing shifted cone coordinates once. Uniqueness identifies
the chosen map with that explicit canonical augmentation. A generic mapping-cocone
precomposition identity then gives the comparison with ordinaryCompletionChain.

The proof of `pullbackAugmentation_isIso` then uses the intrinsic/legacy
completeness comparison, the proved `CompletedCoefficientPushforward.complete_roosUnit` lemma on the
given K-flat representative, and preservation of quasi-isomorphisms by
exact ordinary pullback, implemented by its derived functor and naturality of
`mapDerivedCategoryFactors`. It composes these with a strict chain isomorphism. That
last structural assertion is extracted into the new module
`Sheaf.Paper.IsomorphismOrdinaryCompletionChain`. Its statement concerns arbitrary
complexes, and its docstring supplies the reindexing, quotient, transition,
product and mapping-cocone argument. Existing public mathematical statements and definitions are
definitionally preserved. The private handwritten complex comparison is replaced by the hom of
Mathlib's mapped natural isomorphism; its degree components are identical. The
change record is `coord/changes/r9-augmentation-complex-comparison.md`. No consumer
adaptation is needed.

The existing normalization formula is factored into the public definition
`pullbackAugmentationNormalization`; the property in
`existsUnique_pullbackAugmentation` now names that formula, with exactly the same
binders and equations by unfolding. Its sole direct external consumer is
`IntegralPullbackAugmentationAmbient` (unclaimed). The change is recorded in
`coord/changes/r9-augmentation-normalization-predicate.md`. No Challenge statement
is edited. The new predicate belongs to the existing definition node.
The cone projections and the standard localization and
complex-extension functors stay folded locally, with their existing API lemmas
used in the proofs.

The local transparency settings are enabled throughout. Thin model aliases remain
available for instance checking while large pullback and derived-functor data stay
folded. The two tensor-naturality proofs now instantiate one proved generic
category-theoretic calculation. Coefficient-line maps and the resulting Weil
constructors also stay folded locally; the heart proofs unfold only their carrier.
The four Weil-line constructors explicitly supply
the existing `Iso.isIso_hom` proof for geometric Frobenius; these proof-only local
instances preserve their definitions by proof irrelevance. This is recorded in
`coord/changes/r9-rationalWeilLine-proof-instance.md`,
`coord/changes/r9-rationalWeilTwistingFunctor-proof-instance.md`,
`coord/changes/r9-commonWeilLine-proof-instance.md`,
`coord/changes/r9-commonWeilTwistingFunctor-proof-instance.md`.

The existing proof of `existsUnique_completedToOrdinary` is also tightened:
the entire normalized localization argument is proved once for arbitrary
categories, then instantiated with the good-complex localization. Its normalization
uses the inverse law of the single forward composite. The representative
comparison is written as that composite's symmetry, definitionally the same
isomorphism by `Iso.trans_symm`; see
`coord/changes/r9-completed-good-inverse-composite.md`. Its other direct consumer,
`CanonicalTateComparisons` (P7), needs no adaptation. The augmentation identification uses the generic mapping-cocone
precomposition identity and the shared canonical normalization theorem. The exact-functor localization calculation is also proved once in a generic
private helper. Hom extensionality on adjunction-unit generators is also proved
once for arbitrary coefficient rings, and the two concrete coordinate proofs
instantiate it. The auxiliary finite-field existence argument is isolated in a
proved lemma and used only inside the completeness proof. The adjunction comparison is kept
irreducible before constructing subsequent chain maps, and the large pullback
definitions are kept irreducible locally during the descent proof. These changes
avoid repeated unfolding of the large pullback construction; they change proof
elaboration only. After the coordinate comparison, the strict augmentation,
raw pullback functor, Roos unit and ordinary completion chain also stay
folded. Subsequent proofs use the normalized comparison as their interface.

The existing native preadditive instance is named once as
`coefficientPreadditive` and registered locally. Its body is the unchanged native
instance, so the additive structure is definitionally identical; see
`coord/changes/r9-coefficient-preadditive-presentation.md`. This real data
presentation has no hole and belongs to the existing definition node.

The new proof imports are `CompletedReductionAugmentationIso`,
`SfDerivedCompleteLegacyComparison`, and `IsomorphismOrdinaryCompletionChain`.
The choice calculation keeps the normalization predicate abstract; the explicit
canonical augmentation stays folded after its normalization is proved. The
assigned node's proof and dependencies have been updated to describe the
actual argument.

Validation: `lcompile.py --all` accepted the assigned module and the new
structural module, with no errors or warnings and within the server's per-file
compilation limit. The same run also compiled the unchanged external consumer
`Sheaf.Paper.IntegralPullbackAugmentationAmbient` against the revised module.
Its temporary unchanged copy is excluded from the delivery. The other consumer
checks are the definitional-equality and proof-irrelevance checks in the change
records; their statements retain the same meaning and require no source edits.
All source lines satisfy the 100-character limit, all dependency node ids exist,
and debugging options have been removed.

## Proved and sorry left

Original module: three holes before, two afterwards. One original hole is closed
by a complete Lean combining proof:
`WeilConjectures.FrobeniusCoefficientTwists.pullbackAugmentation_isIso`.
One lower hole is added, so this is a decomposition, with net hole reduction zero,
not an unconditional proof of the augmented completion comparison.

The remaining holes are:

- `WeilConjectures.FrobeniusCoefficientTwists.existsUnique_positiveLineMaps`,
  unchanged; node `def-weil-frobenius-coefficient-twists`.
- `WeilConjectures.FrobeniusCoefficientTwists.existsUnique_finitePositiveLineMaps`,
  unchanged; node `def-weil-frobenius-coefficient-twists`.
- `WeilConjectures.IntegralOnSlice.isomorphismOrdinaryCompletionChain`, added in
  its own module; node `lem-pur-isomorphism-ordinary-completion-chain`.

The new statement is strictly a structural part of the argument. It neither
mentions the assigned augmentation nor asserts its derived invertibility on
complete constructible objects. The combining proof separately establishes the
normalization equality, invertibility of the completion unit, and preservation
of its quasi-isomorphism before using the structural chain comparison.

## No longer needed

Removed proof import `Sheaf.Paper.QcqsCompletionUnitLocality` and the corresponding
proof dependency `lem-fix-qcqs-completion-unit-locality`. The augmentation
construction uses ordinary-model definitions, while the invertibility proof uses
the proved complete-Roos-unit comparison. Neither proof uses the finite open/closed
locality tree or the leaf-restriction comparison. No public import is removed.
The following modules, with their nodes, leave this module's transitive import
closure through that removal:

| Module under `Sheaf.Paper` | Node |
| --- | --- |
| `QcqsCompletionUnitLocality` | `lem-fix-qcqs-completion-unit-locality` |
| `QcqsCompletionComparisonDescent` | `lem-fix-qcqs-completion-comparison-unit` |
| `QcqsCompletionUnitCriterion` | `lem-fix-qcqs-completion-unit-criterion` |
| `QcqsCompletionUnitRestriction` | `lem-fix-qcqs-completion-unit-restriction` |
| `QcqsCompletionUnitTree` | `lem-fix-qcqs-completion-unit-tree` |
| `QcqsOrdinaryLocalDetection` | `lem-fix-qcqs-ordinary-local-detection` |
| `QcqsOrdinaryRestrictionModels` | `lem-fix-qcqs-ordinary-restriction-models` |

No module is withdrawn: other consumers and unit routes may still need this
machinery, so no global pruning count is claimed. A comparison of the current
Challenge import closure finds no module removed there. The assigned module's DAG
parents still require this item; an unfinished parent need not yet import its
planned proof dependency in Lean. Other existing imports and planned dependencies are
retained for the declarations and proofs already in the module.

## Where the brief, the DAG or earlier work was wrong

The ordinary locality machinery is stronger than this proof needs and carries
finiteness hypotheses absent from the assigned theorem. The proved complete-Roos-unit comparison applies on the given K-flat representative
for arbitrary schemes. The existing
`isomorphismIntegralDerivedPullback_termwise` also assumes invertibility of ell
on both schemes and does not give this chain's augmentation normalization; it
cannot directly fill the assigned hole. No statement is changed or disputed.

Generic tools from other units are used as black boxes: the complete-Roos-unit comparison
(`sk-lem-sf-mate`), intrinsic/legacy completeness comparison
(`sk-def-sf-operations`), pro-etale isomorphism inverse image
(`sk-def-sf-admissible`), and generic exact-product Roos chain comparison
(`sk-prop-sf-cbc`). They supply general completeness/reindexing infrastructure
rather than a replacement for the purity-convention unit. No `tool_uses`
approvals have been added by this worker. The assigned unit's realized route
is preserved.

Searches used LeanFinder, Loogle, LeanSearch and Mathlib grep through `msearch`,
local library searches, and the imported-blueprint reference search. Their actual
results are recorded in the new node. They found cone and exactness infrastructure,
but no theorem identifying these specified strict quotient towers and normalized
augmentation. The source checks include Stacks `sites-modules.tex`,
`lemma-tensor-product-pullback` (03EL), and `derived.tex`,
`definition-derived-limit` (08TC). The extracted step is a refinement of the
expanded assigned DAG clause 4 and the existing augmentation-isomorphism
proof-in-words; it is not claimed to be verbatim text of the shorter current
blueprint definition.

## New nodes

`lem-pur-isomorphism-ordinary-completion-chain` states the strict chain comparison
for ordinary pullback along a scheme isomorphism, with the equation on the
quotient-map/zero augmentation. Its source, full proof steps, searches, Lean
attachment and blueprint ancestry are in the new node. The argument applies to
zero complexes, the empty scheme and the identity isomorphism, and uses products
rather than boundedness, so it imposes no extra hypothesis on unbounded inputs.
The coefficient-action comparison and every finite quotient transition must be
retained by its eventual proof. No data is defined by choosing its existential
witness; the combining theorem eliminates that witness only in a proof of a
proposition.

The private-comparison implementation change is recorded in
`coord/changes/r9-augmentation-complex-comparison.md`.

The explicit Frobenius proof instances are recorded in
`coord/changes/r9-rationalWeilLine-proof-instance.md`,
`coord/changes/r9-rationalWeilTwistingFunctor-proof-instance.md`,
`coord/changes/r9-commonWeilLine-proof-instance.md`,
`coord/changes/r9-commonWeilTwistingFunctor-proof-instance.md`.

The inverse-composite presentation is recorded in
`coord/changes/r9-completed-good-inverse-composite.md`.

The native additive-instance presentation is recorded in
`coord/changes/r9-coefficient-preadditive-presentation.md`.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
