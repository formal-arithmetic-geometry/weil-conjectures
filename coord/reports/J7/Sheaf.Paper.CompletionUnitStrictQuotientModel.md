## What changed

The original theorem statement is unchanged. Its proof now establishes the local tensor
section formula, zero shifted cone coordinate, whole-morphism completion-unit formula,
all comparison equations for arbitrary pairs of K-injective resolutions, and naturality.
The proof uses private, proved helpers for adjunction transposes, cone naturality,
comparison cancellation and invertibility of the two resolution identifications.

The model definitions were extracted verbatim to `Sheaf.Paper.CompletionUnitModels`
and are publicly re-exported. This allows the separate construction lemma
`Sheaf.Paper.CompletionUnitCanonicalModels` without an import cycle. The definition
extraction is documented in `coord/changes/completion-unit-models-extraction.md`.

## Proved and sorry left

One original hole is closed in
`WeilConjectures.CompletionUnit.completionUnitStrictQuotientModel`. There are zero
sorries in that module and zero in the extracted definitions. One hole is added:
`WeilConjectures.CompletionUnit.canonicalModels`, node
`lem-trf-completion-unit-canonical-models`. Its proof is exactly `by sorry`.

This is a decomposition, not a net proof: one hole closed minus one added is zero.
The remaining lemma is the construction/normalization portion (old steps 1--4),
not the original cone or unit theorem under another name. The complete Lean argument
combining it with adjunction normalization and strict Roos naturality is in the item.
No data are chosen in a definition from this existence theorem.

The construction lemma has a full proof in words, including the necessary comparison
of the generic derived adjunction with the already chosen coherent calculus by
uniqueness of left adjoints and equality of projected counit mates. Its zero-object,
identity-resolution and unbounded-complex edge cases require no extra hypothesis.
The existing dependencies remain available to prove it. At a point with a rational
coefficient object the finite quotient system is zero; this statement does not assert
that the completion unit is invertible, so that edge case is consistent as well.

## No longer needed

The item now has just its public model import and private construction import.
The following original public imports remain public through the model module:
`Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`,
`Sheaf.Paper.IntegralReductionTowerCanonical`, and
`Sheaf.CategoryTheory.StrictRoosModel`.

These original proof imports are removed from the item and retained as mathematical
dependencies of the construction node, not claimed as globally pruned:
`Sheaf.AlgebraicGeometry.ProEtaleProductsExact`,
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`,
`Sheaf.CategoryTheory.SequenceProjectionDerivedAdjunction`,
`Sheaf.SixFunctors.ResolvingDerivedAdjunction`,
`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`,
`Sheaf.CategoryTheory.SequencePushforwardLimitProjections`,
`Sheaf.CategoryTheory.SystemRingedSequenceSite`, and
`Sheaf.CategoryTheory.StrictRoosComparison`. The last was formerly a public import.
The construction module imports only the model signatures while its theorem remains
sorry; it adds no unused proof imports.

`Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` is also removed and is not
needed by these statements or proofs. No global module or node is withdrawn.

The original item's eight direct tool-use approvals are withdrawn from that node:
`det-pe-products-exact`, `lem-weil-strict-roos-comparison`,
`prop-pur-kinjective-resolutions-exist`,
`lem-coef-sequence-projection-derived-adjunction`,
`lem-sfb-resolving-derived-adjunction-normalization`,
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`,
`lem-coef-sequence-pushforward-limit-projections`, and
`lem-coef-derived-system-evaluation-calculus`. Their actual construction uses move
to the new canonical-model node. They supply generic module/sequence-site machinery
for which this trace-formula unit has no alternative theorem. The same applications
were already approved for the original steps; any approvals on the new node are left
to the maintainer. The item now only uses the construction and model definitions.

## Where the brief, the DAG or earlier work was wrong

The seven-step argument is mathematically sound, but applying the generic sequence theorem
is not a direct type-level instantiation. It returns strict-system functors and a newly
constructed derived adjunction. The coefficient calculus fixes its own reduction
functor and adjunction. The bridge must transport the ordinary functors through the
strict-system/sequence-site equivalence and compare the derived left adjoints
compatibly with the actual counits. The original node's reviewer advisory already
identified this normalization issue. The initial generic-evaluation equality test
failed to reduce: its structural ring map is written as an identity on sections,
while the coefficient evaluation uses eqToHom. The correct bridge is
SheafOfModules.pushforwardCongr after identifying those ring maps. The coefficient
cone uses NatTrans.ofOpSequence and the completed-limit projection equation on
successor arrows. These tests were kept outside the delivery Lean files. It cannot be discharged by identifying object
values or testing equality on finite derived projections alone. The remaining lemma
states this construction explicitly and its proof plan gives the adjunction-mate
argument. No source-library declarations or target statements were changed, and the
unit route is preserved. Tag 07A6 states the derived adjunction; the ordinary
module adjunction used in the construction is Tag 03D7, sites-modules.tex
lemma-adjoint-pullback-pushforward-modules. The new source records distinguish them.

## New nodes

`def-trf-completion-unit-models` records the nine existing, unchanged definitions now
in the extracted module. It introduces no existence assertion and has no sorry.

`lem-trf-completion-unit-canonical-models` records the compatible ordinary and derived
model construction from the original first four steps. Its conclusion omits every
strict-cone augmentation, whole-unit, arbitrary-resolution and naturality formula
proved by the item. Its dependencies are the existing declared generic construction
theorems. Both nodes stay in `sec-trace-formula`, unit `sk-thm-trace-transport`.

Change record: `coord/changes/completion-unit-models-extraction.md`.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
