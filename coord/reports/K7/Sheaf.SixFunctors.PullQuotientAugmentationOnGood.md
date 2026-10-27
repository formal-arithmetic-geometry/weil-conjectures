## What changed

Replaced the hole in `WeilConjectures.GeneratorReduction.pullQuotientTranspose_onGood`
by a proof that expands the full reference pullback model, uses
`RealizationModel.model`, and transports the actual reconstruction unit through the
ordinary-pullback localization factor. The reduction-model Hom normalization supplies
the derived transpose. Private proved helpers extend the specified K-injective Roos
normalization to arbitrary tower complexes, prove naturality of the ordinary-limit
unit, and identify the two explicit mapping-cocone coordinates.

Added `Sheaf.SixFunctors.PullQuotientOrdinaryProjection`, stating the ordinary finite
projection calculation before products, cones, or derived localization. The main
proof combines these finite identities by product extensionality, identifies both
Roos coordinates (the shifted coordinates vanish), and applies localization.
No existing declaration signature, definition, attribute, or public import changed.
The item node now records this exact proof route.

Validation: both delivered modules were checked with lcompile.py. The final item
module compiles without warnings in 25.8 seconds. The original theorem signature
was checked against the shared source, and only the allowed proof fields of its
existing node differ. The new node signature matches its Lean declaration.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.GeneratorReduction.pullQuotientTranspose_onGood`
(node `lem-sf-pull-quotient-augmentation-on-good`). No holes remain in the item module.

Added one hole:
`WeilConjectures.GeneratorReduction.pullQuotientOrdinaryProjection`
(node `lem-sf-pull-quotient-ordinary-projection`). It states the ordinary cochain-map
identity after a single finite projection, for arbitrary complexes. It requires
neither the system Operations/RealizationModel nor any derived reconstruction unit,
reference Roos isomorphism, completeness, or good-complex hypothesis. Its docstring
specifies the unit-conjugate and finite adjunction calculation still to prove.

This is a decomposition: one original hole closed, one strictly simpler hole added;
net hole reduction is zero. Every private helper is fully proved.

## No longer needed

No existing Lean import was removed and no existing library module is withdrawn.

The original direct proof dependency
`lem-coef-sequence-adjunction-cochain-transposes`
(`Sheaf.CategoryTheory.SequenceAdjunctionCochainTransposes`) is unnecessary here:
`pullbackTensorReductionModel_existsUnique` already specifies the Hom normalization
for the actual calculus and actual ordinary quotient model, avoiding transport from
the existential sequence-adjunction package. The original direct dependency
`lem-coef-derived-system-evaluation-calculus` is unnecessary as a separately applied
proof theorem; its constructions remain in the public statement context through the
canonical bridge. The old dependency
`def-pur-completed-pullback-tensor-comparison` is replaced in the proof record by
`def-pur-completed-pullback-tower-realizations`, which now owns the actual reference
model definitions. None of these observations claims that the corresponding modules
are globally unreachable from other consumers.

## Where the brief, the DAG or earlier work was wrong

The published reference pullback, reduction, and Roos models now live in
`Sheaf.Paper.CompletedPullbackTowerRealizations`, extracted after the original node
was written. The proof record has been adjusted to that ownership. The mathematical
route and the statement are unchanged. The reduction-model Hom normalization can
be used directly instead of the more general existential cochain-transpose theorem.

## New nodes

`lem-sf-pull-quotient-ordinary-projection` isolates the finite projected-section part
of the original second proof step. The ordinary adjunction unit-conjugate identity,
`OrdinaryLimitModel.projections`, the two normalized evaluation comparisons, and
`Pull.generators` prove its assertion degreewise. It applies to arbitrary complexes;
zero complexes, empty schemes, identity maps and exponent one require no exceptions.
The already proved underived scalar adjunction supplies the section normalization
of its finite scalar unit; this is recorded explicitly in the new node. The source,
complete proof in words, Lean signature, and Mathlib searches are in its node and module. No change record is needed because no existing interface changes.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
