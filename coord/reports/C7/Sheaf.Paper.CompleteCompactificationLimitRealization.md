## What changed

Replaced the one proof hole of
`AlgebraicGeometry.ProEtale.CompleteCompactificationLimit.complete_compactification_limit_realization`
with the actual categorical assembly in the existing module. The statement and all five existing
support declarations are unchanged. The proof constructs `ScalarComparison` from the ordinary and
derived scalar squares, expands the specified `comparison` into its four factors, proves their
invertibility on the specified complete inputs, and takes `asIso` of that exact map. Projection
naturality, followed by the push and open projection equations, yields the actual quotient
augmentation equation. It does not use evaluation to detect equality of arbitrary derived maps.

Three new modules isolate the scalar-system construction and the two fixed-ring mate normalization
obligations. Each is strictly part of the parent's original proof (steps 1–3); none asserts the
compactification-image isomorphism or its final augmentation identity. Each has one public theorem,
a source, a proof in words, and a matching new node. They add no definitions or choices of data.
Private proof imports in the main module now name those three obligations. Their statements use
only the existing public CompleteCompactificationLimitSupport interface, avoiding import cycles.
The parent node's proof, proof_deps and proof_origin now follow the Lean assembly.
Local irreducibility during the theorem proof keeps the scalar and mate constructions behind
their existing interfaces; the comparison words are expanded explicitly only where needed.

## Proved and sorry left

Original holes: 1. The body of
`AlgebraicGeometry.ProEtale.CompleteCompactificationLimit.complete_compactification_limit_realization`
is closed by a complete proof from the three explicitly named intermediate results. This is a
**decomposition**, not a net hole reduction and not a claim of a sorry-free axiom closure.

Holes added: 3; every remaining hole in this delivery is the entire proof of one of:

- `AlgebraicGeometry.ProEtale.CompleteCompactificationLimit.compactificationScalarData`
  (`lem-sp-compactification-scalar-data`): normalized reduction/limit presentations and strict
  ordinary/derived scalar squares, before taking a compactification limit.
- `AlgebraicGeometry.ProEtale.CompleteCompactificationLimit.compactificationOpenLimit`
  (`lem-sp-compactification-open-limit`): invertibility and the projection formula for the specified
  constant-diagram open mate on fixed completed-coefficient towers.
- `AlgebraicGeometry.ProEtale.CompleteCompactificationLimit.compactificationPushLimit`
  (`lem-sp-compactification-push-limit`): K-injective-normalized evaluation and the projection
  formula for the specified direct-image limit mate on fixed completed-coefficient towers.

The main item has zero remaining textual holes. None was added inside a definition.
Net textual change for this packet: one upper hole closed and three lower holes added.

## No longer needed

The main proof no longer directly imports ExactProductFunctorStrictLimit,
ProEtaleRingedOpenExtensionProducts, RingedOpenScalarAdjunction,
SequencePushforwardLimitProjections, DiagramRingRestrictionPushforward,
LocalizedModuleExactForSystems, RingedToposDerivedPushforwardComposition,
ProEtaleCountableProductsExact, ProEtaleWeaklyEtaleLocalization, or
RingedTowerPushforwardLimitComparison. These are the same general tool declarations needed in the
new obligations' documented proof plans; their nodes are retained there. No existing declaration,
node or module is withdrawn, and no claim is made that these tools leave the target import closure.
No mathematical dependency of the original construction is pruned; its obligations are reorganized.
The new theorem-only statement modules have no unused proof imports.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction is made. The existing general lemmas return normalized
constructions in their own section or ringed-site coordinates; they do not give the exact
LimitPresentation, scalar comparisons, fixedOpenEvaluation or adjunction-conjugate pushLimit
identities by one application. Those transport/normalization steps are substantial and are now
explicitly stated. The elementary final assembly and augmentation calculation are written in Lean.
The unit route stays unchanged. The extra D+ input hypothesis is retained verbatim, although the
assembly only needs invertibility of its specified completion unit.

Small-case checks: open-limit specializes to the identity and the empty open using the same
constant-diagram mate and product formulas. Push-limit applies to arbitrary morphisms, including
identity and empty schemes; properness is unnecessary for the ringed adjunction theorem. The scalar
lemma retains all schemes, coefficient exponents starting at one, and all semilinear transitions;
it assumes no constructibility, output normalization or scalar preservation of K-injectives.

Searches were actually run through msearch.py (LeanSearch, LeanFinder/Loogle, and Mathlib grep),
plus local source and blueprint searches. Existing cbcRealizationLimitMap_isIso only proves
invertibility, and does not supply the projection normalization needed here. The general strict
limit and ringed-tower theorems are recorded as dependencies, rather than duplicated as purported
new general theorems.

## New nodes

`lem-sp-compactification-scalar-data`, module Sheaf.Paper.CompactificationScalarData, carries the
original proof's steps 1–2 with the existing normalization fields written out, so its module does
not depend on the main module's ScalarComparison structure.

`lem-sp-compactification-open-limit`, module Sheaf.Paper.CompactificationOpenLimit, carries the
open part of step 3, including identification with the already specified mate and its projections.

`lem-sp-compactification-push-limit`, module Sheaf.Paper.CompactificationPushLimit, carries the
direct-image part of step 3, with the actual K-injective equation written out to avoid an import
cycle through IsFixedPushEvaluation. All three use the current blueprint's direct-image proof,
paragraph (2), and the existing general tool lemmas in the parent's accepted route. No change
record is needed: no existing signature, definition, public import, or consumer interface changes.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
