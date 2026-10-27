## What changed

Preserved every existing public signature and definition in
`Sheaf.Paper.SfQbarLocalizationCommonStage`. The assembly proof descends the finite
unit and counit families with the existing StageSystem API, verifies their triangle
identities at each object stage, proves shift compatibility through the stage
inclusions, identifies the pullback functors by their unique representative
specification, and includes the finite distinguished triangles.

The cross-stage Hom argument uses finite-stage orthogonality first: conjugation
makes every raw representative group zero; any two common-stage arrows then agree
by the existing Hom coordinate equivalence. Every direct-limit element is
represented and hence zero.
The unique additive equivalence between these zero groups satisfies the required
formula on every representative.

Added finite-data, finite-coherence, shift-descent, and exact-descent modules. The exact-descent proof
identifies the preadditive structures using uniqueness in a category with binary
biproducts, then uses the existing additive pair-functor instance. Its triangulated
part is the actual image of an included finite distinguished triangle, transported
through the inclusion comparison. Shift descent applies the proved generic
framework pair-shift construction and its restriction theorem to the actual
general coefficient categories. Finite coherence remains a separate mathematical
subresult; it contains no descended localization conclusion.

## Proved and sorry left

Original holes: 1. Holes closed in the item: 1, `WeilConjectures.sfQbarLocalizationCommonStage`.
The assembly reduces this original hole to the named finite-coherence theorem, using the
proved shift-descent, exact-descent, adjunction, triangle and Hom arguments.

Added holes: 1. This is a decomposition, not a net proof of the whole item:

- `WeilConjectures.sfQbarLocalizationFiniteCoherence`
  (`lem-sf-qbar-localization-finite-coherence`): finite normalized coefficient
  functor families, shifts, and compatible finite adjunction maps only.

`WeilConjectures.sfLocalizationShiftDescent` is proved without a placeholder.
It reuses `pairCommShift` and `pairRestrictionShift` from
`SfFrameworkCommonStageDescent`; these construct the natural shift isomorphism
on common-field representatives and verify zero, addition, and restriction coherence.

`WeilConjectures.sfLocalizationExactDescent` is proved from shift descent. No
placeholder occurs in a definition or private helper. The finite records are
explicit structures, and no data definition chooses an arbitrary existence witness.
The assembly is a private helper with the inherited geometry as parameters, so
the public proof does not repeatedly unfold its geometry lets through the record.
The assembly supplies explicit finite-functor and adjunction arguments, uses
the existing adjunction constructor, and keeps the finite
triangulation, intrinsic predicate, and Frobenius models locally
irreducible to avoid inference through their expanded constructions.
Its adjunction constructor reuses the proved `descendStageAdjunction` from
`SfCommonStageDirectImage`, with component equations proved for the private wrapper.
The raw Hom subsingleton proof uses `Iso.homCongr` and requires no unfolding
of the additive conversion maps. The finite triangulation package stays locally
irreducible during assembly checking.
The geometry transport needed for orthogonality is proved using equality of the
structure morphisms forced by j.IsOver and proof irrelevance for their properties.

## No longer needed

Removed proof imports from the item:
`Sheaf.Paper.BasicOperationsCoefficientReduction`,
`Sheaf.Paper.ScalarExtensionExactIntrinsic`,
`Sheaf.Paper.SfScalarExtensionComposition`, and
`Sheaf.CategoryTheory.StageSystemFunctorDescent`.
The first three belong to the finite-coherence proof plan and are not imported
by its currently unproved theorem. The abstract pair-descent wrapper
is unnecessary because the proved upstream StageSystem functor and compatible
natural-transformation constructors give the required operations directly.

The generic nonzero Hom-system equivalence and its transition conjugation proof
are unnecessary: each component is already a subsingleton, so the directed-system
laws and the specified additive comparison are unique. The representative formula
is still proved for every common field. No existing module is withdrawn. The
original unit statement and its localization route are preserved.

The duplicate explicit shift construction is also unnecessary: the existing
framework helpers provide precisely its generic shift and inclusion conclusions.
The finite-stage Hom zero proof uses the existing `Iso.homCongr` bijection instead
of unfolding the additive composition maps.

## Where the brief, the DAG or earlier work was wrong

The upstream `StageSystem` exact-descent helper uses its explicitly constructed
pair shift, while the general coefficient category supplies its own normalized
shift. The generic helpers in `SfFrameworkCommonStageDescent` already work with
the actual general shifts and their inclusions. Reusing them removes the earlier
duplicate 400-line shift construction and its associated definitional comparisons.

The operation-reduction theorem quantifies its algebraic closure in the scheme
universe, whereas this item allows an independent universe. The finite-coherence
interface retains the item's independent universe; no universe restriction was
added to the target. Its proof must use the underlying coefficient comparisons
with small finite coefficient models, rather than blindly apply that bundled
theorem at mismatched universes.

The finite-coherence proof plan additionally identifies the existing normalized
compact-support action, rational pullback/direct-image coefficient-mate theorem,
and ringed/compact-support scalar shift normalization lemmas. They supply the
finite comparison steps; no unit route provides their general scalar assertions.
These tool dependencies are recorded in the new finite-coherence node for review.

Finite-stage edge cases were checked in the argument: repeated coefficient
fields use multiplication units, zero objects use the same additive equations,
empty open or closed subschemes give zero functors, and negative shifts use the
same coherent integer-shift comparison. The finite coherence claim retains
canonical comparisons and both adjunction normalizations; none was dropped.

The current blueprint localization proof no longer prints the historical
algebraically closed-stage paragraph named by the old node source. The new nodes
make explicit the finite coherence and shift descent steps retained in the
existing node's reviewed eight-step argument.

## New nodes

`def-sf-qbar-localization-finite-data` owns the explicit finite exact-family and
localization records. It adds no construction chosen from unproved existence.

`lem-sf-qbar-localization-finite-coherence` states only the finite coefficient
compatibility part of the reviewed localization argument. It contains no
common-stage exactness, adjunction, triangle, or Hom conclusion. The remaining
finite-coherence theorem is in `SfQbarLocalizationFiniteCoherence`; the explicit
records themselves are in `SfQbarLocalizationFiniteData`.

`lem-sf-qbar-localization-shift-descent` isolates the compatible integer shifts of
a single general pair functor. It has no localization or orthogonality assertion
and is proved by the existing framework pair-shift and inclusion-comparison lemmas.

`lem-sf-qbar-localization-exact-descent` proves additivity and triangulatedness
from that shift result, the finite exact structures, and the recorded
finite-stage distinguished-triangle criterion. No existing statement or
definition changed. The conservative command-change advisory is documented in
`coord/changes/T1-localization-proof-elaboration.md`; no forced adaptation is needed.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
