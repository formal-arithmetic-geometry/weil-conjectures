## What changed

Completed the categorical assembly in
`Sheaf.Paper.RationalContinuousComparisonCoherence` without changing its statement.
The three private lifting constructions recover raw composition, identity and mixed
natural isomorphisms from their ambient counterparts using the full faithfulness of
postcomposition by realization. The map-preimage equations prove their compatibility.
The mixed normalization is recovered by faithfulness from the specified integral
component, rather than by choosing a raw identification arbitrarily.

The coefficient associator equality is proved sectionwise from the three recorded
field-map normalizations. Raw objects retain their underlying integral objects, so
an integral scalar tower equation supplies the full field composition compatibility.

Four new modules isolate the ambient geometric calculation, integral scalar tower,
ambient mixed calculation, and specified mixed integral component. The integral scalar
tower is proved by the integral normalization equations, naturality and associativity
of the published reduction comparisons. The other three calculations remain named
statements with sources, complete proof plans and matching nodes. This is a
decomposition of the original obligation, not a claim that its mathematics is closed.
No public interface of an existing module changes. All changed imports are private
proof imports.

Validation: the four supporting modules compiled in import order. The final item
then compiled cleanly against those objects (8.9 seconds), without warnings.
The original theorem signature was compared textually and is unchanged. All new
node references exist, and each proof dependency list equals the union of its
proof steps' references. The unchanged direct importer
`Sheaf.Paper.ContinuousRationalDerivedRealization` also compiled against the revised
item; its temporary source copy was removed. No importer adaptations are needed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.ContinuousRational.rationalContinuousComparisonCoherence`
(node `lem-per-rational-continuous-comparison-coherence`) by a complete assembly proof.

Proved
`AlgebraicGeometry.Scheme.ContinuousRational.continuousIntegralScalarTower`
(node `lem-per-continuous-integral-scalar-tower`).

Three new holes remain, each the entire proof of its public theorem:

- `AlgebraicGeometry.Scheme.ContinuousRational.continuousAmbientGeometricCoherence`
  (`lem-per-continuous-ambient-geometric-coherence`).
- `AlgebraicGeometry.Scheme.ContinuousRational.continuousAmbientMixedCoherence`
  (`lem-per-continuous-ambient-mixed-coherence`).
- `AlgebraicGeometry.Scheme.ContinuousRational.continuousMixedIntegralComponent`
  (`lem-per-continuous-mixed-integral-component`).

The item has zero direct holes after the change. One original hole was closed and
three lower holes were added; this is counted as a decomposition. All private helper
definitions contain complete proofs and choose only inverses of established bijections.

## No longer needed

Removed the item's private proof imports
`Sheaf.Paper.RationalPullbackCompositionCoherence` and
`Sheaf.Paper.RationalRealizationScalarCoherence`. They are no longer direct inputs to
the assembly proof. Their nodes
`lem-per-rational-pullback-composition-coherence` and
`lem-per-rational-realization-scalar-coherence` remain needed by the lower ambient
and integral normalization calculations. Their declarations and files remain intact. No global
module withdrawal or global pruning is claimed.

The raw composition, raw identity and raw mixed-existence conclusions of those older
strict-tower records are not needed by the assembly. Full faithfulness constructs
those raw isomorphisms directly in the reflector presentation. In particular there
is no need to transport all raw fraction morphisms across the strict/reflector
presentation solely to obtain these isomorphisms.

## Where the brief, the DAG or earlier work was wrong

The original declared dependencies use strict quotient-tower completion and
realizations with literal object equalities. The item uses reflector completion,
identity-scalar-free ordinary inverse image and natural integral comparison
isomorphisms. Their conclusions cannot simply be applied to the item's supplied
records. `RationalAmbientPullComposition` was also checked: the import-direction
tool refuses it here because it already reaches this item through
`ContinuousRationalDerivedRealization`, so importing it would close a cycle. The new lower statements isolate exactly the remaining normalization
calculations; the assembly itself needs only full faithfulness.

The item was listed in `coord/rework.tsv` with its preserved quarantine path.
Its source reappeared in the shared tree during inspection. The delivered source
preserves its complete theorem signature, Lean attachment and mathematical content.
No quarantined archive is deleted or treated as an unused module.

Edge cases checked in the statements: empty schemes, zero complexes, identity scheme
maps, repeated coefficient fields and identity embeddings are all permitted. The
lift uses bijectivity on every Hom, not nonemptiness of the scheme or torsion-free
integral Homs. The mixed component statement fixes the published completed scalar
comparison, not an arbitrary isomorphism. All work remains below the unit route.

## New nodes

`lem-per-continuous-ambient-geometric-coherence` supplies ordinary/cochain/derived
composition and identity with their specified tensor units and counits. It contains
no raw isomorphism and no raw realization compatibility. The two auxiliary records
state precisely those fields and have no postponed definition data.

`lem-per-continuous-integral-scalar-tower` is the scalar associator equation on an
integral representative, using the actual integral normalization maps and reduction
associators. Its proof reduces the diagram to three associativity equations.

`lem-per-continuous-ambient-mixed-coherence` supplies only the ordinary, cochain and
ambient derived mixed tensor comparison. Its all-scalar section equation and K-flat
computation equation fix its normalization, independently of completed raw objects.

`lem-per-continuous-mixed-integral-component` identifies a single arrow on each
integral representative with the actual rationalized completed scalar/pullback
component and gives its realized square. It asserts neither naturality nor
invertibility of a raw transformation. The assembly proves those properties by
fully faithful lifting and uses this component equation only for normalization.

Searches: LeanSearch returned ordinary sheaf pullback composition, module scalar
associators and ordinary tensor base change. Their source signatures were checked:
they do not state the normalized derived/completed equations here. LeanFinder
returned scheme-normalization and general Tor/derived-functor
results, not these coefficient normalizations; Loogle found leftDerivedUnique and
FullyFaithful.whiskeringRight (the latter is used in the assembly); Mathlib grep
for the concrete normalization predicates found no hits. Searches in the current
blueprint and the existing project modules found no directly applicable adapter.
Change record:
`coord/changes/h8-rational-continuous-proof-options.md` documents the static
preflight's file-command advisory. The changed settings are local to elaborating
this proof; all existing public signatures, definitions and imports remain unchanged.
The only direct importer is checked unchanged and is not part of the delivery.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
