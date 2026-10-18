## What changed

Repair: removed the redundant exported declaration
`CategoryTheory.embeddingUpNat_extend_preservesFiniteLimits` from
`MappedSmartTruncationTower`.  Its proof is now supplied locally at each use site
as an instance value, while the existing `CategoryTheory.extend_preserves_finite_limits`
declaration from `CartanEilenbergGoodCutDecalage` remains the library's sole named
statement of this fact.  The module's public declarations and theorem holes are
unchanged.

Replaced the hole in
`CategoryTheory.cartanEilenberg_decalage_spectralObject_iso_exists` by the composite
of three specified comparisons. The existing theorem's signature is unchanged. All seven delivered modules
compile on the project server; the final main-module check took 8.9 seconds
and produced no warning.

The source comparison is constructed in Lean: extended smart truncation towers
include zero and the full complex, left exactness commutes the mapped functor
with all their steps, total smart cuts identify with decalage steps, and monic
inclusion equations prove naturality for every prescribed filtered lift. Mapping
the entire tower isomorphism through the existing spectral-object functor also
transports its interval connecting maps.

The target comparison is constructed in Lean: the derived image of a single
object is computed using the presentation's supplied injective resolution,
with naturality for every resolution lift. This generalizes the proved
`PlusSingle` formulas instead of choosing a new resolution.

The remaining CE interval-cone comparison stops at `Q(F(P.J))`. It is stated in
its own module and does not require a filtration, decalage, left exactness of F
or G, or a derived category of A. The main theorem combines it with the proved
source and target comparisons, proves bottom-interval invertibility by
composition, and proves presentation naturality by conjugating the two proved
squares and composing the remaining comparison's square.

## Proved and sorry left

Original holes closed: one,
`CategoryTheory.cartanEilenberg_decalage_spectralObject_iso_exists`.
New holes added: one,
`CategoryTheory.cartanEilenberg_smartTruncation_spectralObject_comparison`
(node `lem-sp-ce-smart-truncation-spectral-object`).
This is a decomposition, with net hole reduction zero, not a completed proof
of the original theorem without `sorryAx`.

The remaining theorem needs the interval comparison after using CE injective
total resolutions: commute G with finite total diagonals, assemble normalized
augmentations for cutoffs and presentation maps, compute their interval cones
through the inverse derived unit, and compare these cones with canonical
truncation intervals, including the connecting-arrow signs. Its docstring and
node give the argument and name the existing declarations to use.

The six supporting modules add zero holes except for the one named comparison
above. No other delivered declaration contains `sorry`. The new tower constructions,
left-exact tower comparison, decalage tower comparison, and specified-resolution
comparison and their naturality proofs contain no holes.

## No longer needed

Removed the original module's direct proof imports of
`CartanEilenbergTruncationResolution`, `CartanEilenbergMappedTotal`,
`LeftExactTruncationIso`, `DerivedInjectiveResolutionNaturality`,
`DoubleComplexTruncationDecalage`, and `DerivedUpperTruncationComparison`.
They are replaced by the new comparison module and the smaller proved APIs
below it. The resolution and derived-comparison declarations remain necessary
for the remaining interval-cone theorem; this does not prune them from the
transitive proof route.

For the step moving G through smart truncations, the proof now uses the explicit
`mapTruncLEComparison` API and its proved extended-tower comparison rather than
choosing an isomorphism from `leftExact_truncation_iso`. The latter remains
upstream of the CE truncation-resolution theorem. No existing module is
withdrawn and no existing DAG obligation is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

No statement was disputed or changed. The plan's parent-module augmentation
lemmas cannot be imported into this child module without a cycle; their role is
recorded in the remaining interval-comparison proof plan rather than introducing
that import. The source tower identifications and specified-resolution target
identification can be separated from that interval argument and proved directly.

The assigned node's inherited unit is `sk-prop-av-pqf-finite`, whose realized
statement and proof-step arrays are empty; its text concerns proper quasi-finite
maps rather than CE spectral objects. No unit record or unit route was changed.
The blueprint provenance of the new nodes follows the existing CE comparison
parent's `thm-sp-grothendieck` ancestry.

## New nodes

`def-sp-extended-smart-truncation-tower`: constructs extended smart truncations,
cutoff arrows, inclusions, and maps induced by complex maps, with their equations.

`lem-sp-extended-smart-truncation-map-iso`: proves a left exact additive functor
commutes with this whole tower, naturally in cutoffs and complex maps.

`lem-sp-smart-truncation-decalage-tower`: proves the natural total-smart-cut and
decalage tower isomorphism and transports it to cohomology spectral objects.

`lem-sp-mapped-smart-truncation-tower`: proves extension by zero preserves finite
limits and moves the mapped functor through the smart-cut tower before totalization.

`lem-sp-specified-resolution-derived-single`: computes the derived image of a
single object using any specified injective resolution and proves lift naturality.

`lem-sp-ce-smart-truncation-spectral-object`: the one remaining hole, confined to
CE resolved interval cones and their comparison with the canonical truncation
spectral object of `Q(F(P.J))`.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
