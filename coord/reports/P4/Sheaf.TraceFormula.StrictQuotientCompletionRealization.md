## What changed

Repaired TrfCompletionRoosNormalized to require the existing whole-system predicate
IsIntegralComparisonPresentationCoherent. The old finite-evaluation hypothesis does
not fix a morphism in the derived system; its universal normalization clause is
false. The actual tower, finite comparisons, Roos map and theorem signatures are
unchanged. The semantic correction is explicit in the node and change record.

Implemented strictQuotientCompletionRealization by constructing a derived comparison
on good complexes, passing through the natural Roos bridge, and applying an ordinary
tower comparison. Naturality and cancellation prove its universal coherent-presentation
formula. CompletionUnit.fixedCalculusModels constructs the ordinary/derived adjunction
models for an arbitrary fixed calculus, using existing proved private constructions
without the unused residue-characteristic restriction of canonicalModels.

Adapted strictQuotientCompletionUnit to prove that its canonical presentation is
coherent, using derivedTranspose on the identity and ordinary_unit_section.
(Reviewer: the proposed proof-only edit of IntegralReductionTowerCanonical was withdrawn.
The delivered modules compile against its published version, so it was not forced.) No source-library module
under WeilConjectures is edited.

## Proved and sorry left

Closed the body of WeilConjectures.strictQuotientCompletionRealization for the
explicitly corrected auxiliary predicate. The old, false predicate is not proved.
The item's original one hole becomes zero holes in that module.

Added one hole: WeilConjectures.ordinaryQuotientTowerComparison, node
lem-trf-ordinary-quotient-tower-comparison. It asserts only the ordinary natural strict
tower isomorphism and its section formula. It has no derived calculus, good/K-flat
hypothesis, derived-category comparison, limit or Roos normalization. The main
module proves the derived/naturality part from it, so this is a decomposition,
with one upper hole removed and one strictly smaller lower hole added (net zero).

WeilConjectures.CompletionUnit.fixedCalculusModels has no hole of its own. Its new
module has zero holes. Its axioms include sorryAx only through holes that already exist
upstream (ordinaryModel_exists, finiteComparison_of_unit, tensor_derived_exists). The existing completion-unit proof and canonical transition
proof retain zero holes. No hole occurs in a definition or a private declaration.

## No longer needed

No existing module is withdrawn and no public import is removed. No source-library
declaration is removed. The original seven direct proof-plan dependencies are
replaced in the item's proof_deps by the fixed-calculus model, ordinary tower
comparison, coherentQuotientModelComparison and the realization-model interface.
K-flat resolution, countable-product exactness, well-definedness of integral
operations, and strict Roos comparison are provided through the already constructed
models or the supplied r, rather than reproved by this item. Inverse-image
comparison is irrelevant to the completion-only assembly. These statements may
remain transitive imports or dependencies of other items; no global pruning is
claimed. The blueprint unit's own statement and realized route are preserved.

The replaced direct plan dependencies are `lem-pc-kflat-resolution`, `lem-coef-derived-system-evaluation-calculus`, `def-pur-integral-derived-operations`, `lem-weil-strict-roos-comparison`, `lem-weil-proetale-countable-products-exact`, `lem-pur-integral-operations-well-defined`, `def-weil-inverse-image-pullback-comparison`.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (old interface): CoefficientReductionPresentation only records
finite derived evaluations. Evaluations are conservative on objects but do not
jointly detect morphisms. The invisible-twist example already documented in
coord/reports/T6/Sheaf.Paper.PrimitiveQuotientRealizationComparisons.md also contradicts
the old completion normalization clause. The related pullback interface already
uses IsIntegralComparisonPresentationCoherent; this delivery applies that correction
to completion, and proves the additional coherence for its actual unit consumer.
No Challenge target statement is changed.

canonicalModels has an unused invertibility-of-l-on-residue-fields argument. Its
private constructions and derived comparison proof require no such argument.
The new theorem exposes the same construction without adding that hypothesis to
this item's theorem.

(Reviewer: the duplicate transition-equation claim did not reproduce against the
published build. The IntegralReductionTowerCanonical edit was withdrawn; see
coord/changes/P4-canonical-transition-equation-import.md.)

Validation: the main theorem, the corrected strict-model module, both new modules,
and the canonical transition proof compile. All four direct importers of the
corrected model interface compile. The additional pullback-normalization consumer
also compiled with development profiling enabled (52.6 seconds reported); that
unchanged checking copy was removed. The completed unit-consumer check is recorded
by the delivery tool. No debugging options remain in the packet.

## New nodes

lem-trf-completion-unit-fixed-calculus-models: fully proved existence of ordinary
and derived models for the specified calculus, without a geometric restriction.

lem-trf-ordinary-quotient-tower-comparison: remaining ordinary strict quotient
tower comparison, separated from the completed derived naturality argument.

Change records: coord/changes/P4-strict-completion-presentation-coherence.md and
coord/changes/P4-canonical-transition-equation-import.md. The existing strict-model,
realization and completion-unit node records describe the corrected interface and
implemented route. No archived or quarantined attachment is deleted.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
