## What changed

Proved `AlgebraicGeometry.ProEtale.internal_first_residue_ordinary_comparison` from the existing exact-map flatness theorem and one new ring-level first-residue pushout lemma. The original public signature and public imports are unchanged.

The private `ordinarySmallExtensionIso` constructs the scalar-extension transport by mates from the existing restriction square and section-module/AsSmall equivalences. `ordinaryScalarFlat` uses `IntegralModelsStacks.integralModels_flat_residue` and `ConstantCompletion.change_exact`, then reflects finite limits through that equivalence. `ordinarySmallPushoutIso` applies the already proved ordinary pushout comparison, identifies the auxiliary ordinary extension functors by their object and map equations, and cancels the fully faithful smallModules functor. The final proof factors extension along the residue-ring isomorphism and identifies it with inverse restriction using `e.hom_inv_id`.

Only proof imports were added, including the scalar-change API in `WeilConjectures.CategoryTheory.ModuleObjects.MapMod`. No definition, existing statement, source-library declaration, or consumer was changed. The standard cochain-model existence theorem is used solely to access its ordinary extension functors; the resulting assertion remains on ordinary modules.

Verification: the complete two-module packet compiled. A subsequent profiler run of the main module compiled in 7.4 seconds, with no expensive declaration identified; the development profiling options were removed before delivery. The theorem signature and node attachments were checked verbatim, and the dependency lists equal the unions of the proof-step uses.

## Proved and sorry left

Closed the item's one hole: `AlgebraicGeometry.ProEtale.internal_first_residue_ordinary_comparison`, node `lem-sfb-internal-first-residue-ordinary-comparison`. The item's module has zero remaining sorries.

Added one hole: `AlgebraicGeometry.ProEtale.internal_first_residue_ring_pushout`, in `Sheaf.SixFunctors.ProEtale.InternalFirstResidueRingPushout`, node `lem-sfb-internal-first-residue-ring-pushout`. It states only the normalized residue coefficient-ring pushout and the residue-ring isomorphism. It contains no module tensor comparison or flatness conclusion. This is a decomposition (one hole closed, one added), not a net hole reduction. The existing `integralModels_flat_residue` declaration is used as stated. It was filled independently in the shared library during this session; this delivery neither changes it nor counts that proof as its own work.

The new ring-level statement was checked against finite residue fields, empty profinite objects, empty schemes and the zero section ring. It uses sheaf pushouts and does not falsely require sectionwise surjectivity on the original pro-etale site. Its docstring and node give the complete argument from the projection-normalized coefficient comparison and Stacks 093M/099L.

## No longer needed

No original imports or modules were removed and no modules are withdrawn. No whole module is claimed globally pruned.

The main proof no longer directly uses the following original planned dependencies: `lem-sf-finite-discrete-normalized-encoding` (`Sheaf.Paper.FiniteDiscreteOrdinaryEncoding`), `det-pe-derived-nakayama-resolution` (`Sheaf.Paper.DerivedNakayamaResolution`), `def-weil-l-adic-coefficient-extension`, `lem-sfb-integers-coset-basis` (`Sheaf.NumberTheory.Padics.IntegersCosetBasis`), `det-prop-integral-criterion-constant-coefficients` (`Sheaf.AlgebraicGeometry.IntegralConstantCompletion`), and `lem-pe-fixed-integral-section-squares` (`Sheaf.SixFunctors.ProEtale.IntegralNormalizedSectionSquares`). Ring normalizations are isolated in the new ring-pushout node, which retains the finite-discrete, coset-basis, completion and fixed-section-square inputs; those inputs are not claimed globally unnecessary. The derived Nakayama resolution theorem itself is not needed for the ordinary categorical assembly; only its coefficient definitions already in the public signature are retained.

The exact scalarMap flatness declaration avoids duplicating the ordinary constant-abelian/ring-sheaf comparison and topology transport. Generic pushout comparison replaces a second proof of tensor balancing.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The earlier plan omitted a named interface for the actual residue ring pushout and mixed this ring-normalization task with the ordinary categorical tensor argument. The delivery separates that strictly smaller coefficient-ring task and completes the categorical argument. Stacks 093M is the completion-flat lemma; Stacks 099L invokes it in the constant Noetherian derived-completion discussion.

The generic helpers reused from `IntegralModelsEmbeddedCompletion` are independent of its specialized embedded-field theorem and Noetherian-scheme assumptions. Likewise only the ordinary pushout helper from `OrdinaryCommonQuotientTower` is used; no tower hypothesis or flatness hypothesis is imposed on that helper. Both modules were checked for import cycles before use.

## New nodes

`lem-sfb-internal-first-residue-ring-pushout`: the first constant-to-continuous residue square is a pushout after section-ring reconstruction and the coefficient-sized small-site equivalence. It is exactly the ring-level portion of the original first-quotient argument. Three Mathlib searches and a whole-blueprint concept search found no existing statement of this normalized square. Its public theorem has one sorry with its source and full natural-language proof in the docstring. The original node's proof and proof dependencies now follow the Lean assembly. No change record is needed because no existing definition or statement changed.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
