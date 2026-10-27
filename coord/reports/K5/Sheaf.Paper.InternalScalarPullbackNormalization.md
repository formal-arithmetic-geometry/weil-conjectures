## What changed

Prove `internal_scalar_pullback_normalization` by combining independent scalar,
internal tensor and pullback constructions with the section transport theorems.
The scalar section construction is proved from `internal_section_scalar_adjunction`
and cochain/homotopy universal derived uniqueness. The internal pullback construction
uses the K-flat left-derivability criterion and `leftDerivedNatIso`; its defining counit
identity is precisely `PullNormalized`. The existing canonical coefficient tensor theorem
supplies the two tensor normalizations. The existing section pull transport supplies the
last clause. The independent section tensor transport is stated as a new sourced lemma.

Move the eight comparison definitions verbatim to
`Sheaf.Paper.InternalScalarPullbackNormalizationData`, publicly re-exported by the
original item. This permits using the comparison lemmas without an import cycle.
No definition data, declaration signature or public visibility changes. The source-library
boundary is respected: no `WeilConjectures` source file is changed.

Adapt the public import in `SectionPullNormalizationTransport`. Extract the two
constructed regular pullback definitions verbatim into
`RestrictedCoefficientPullbackData`, publicly re-exported by
`RestrictedCoefficientMateProjection`; the canonical tensor module imports this data
module instead of the mate theorem. Add the required private proof import of the mate
theorem in its consumer `CoefficientPushFilteredLegs`. Preserve the newly landed complete mate theorem
proof and its current node proof route. This module is now unclaimed. The blueprint
proper-base-change unit and all of its realized steps remain unchanged.

Change record: `coord/changes/K5-internal-scalar-normalization-data.md`, including the
consumer audit for all eight moved names and all 22 downstream modules.

## Proved and sorry left

Original item: one hole, in
`AlgebraicGeometry.ProEtale.QuotientChange.internal_scalar_pullback_normalization`.
That declaration now has a complete Lean combination proof and no `sorry`.

New fully proved results (zero holes):

- `AlgebraicGeometry.ProEtale.QuotientChange.internal_section_scalar_normalization_exists`
  (`lem-sfb-internal-section-scalar-normalization-existence`).
- `AlgebraicGeometry.ProEtale.QuotientChange.internal_pull_normalization_exists`
  (`lem-sfb-internal-pull-normalization-existence`).

One new hole, a strictly smaller independent result:
`AlgebraicGeometry.ProEtale.QuotientChange.section_tensor_normalized_of_normalized`
(`lem-sfb-section-tensor-normalization-transport`). It only transports supplied scalar
and tensor normalizations at one scheme; it constructs neither of them and says nothing
about geometric pullback. Its exact normalization statement and complete proof in words
are in its own module and node. Thus closing the upper hole and adding this lower hole
is a decomposition (one closed minus one added), not a net sorry-count proof gain.

Unchanged holes in existing modules included in the packet:
`section_pull_normalized_of_normalized` (existing transport theorem),
`canonicalCoefficientTensorNormalization_normalized` (only its public import changed).
The current `restricted_coefficient_mate_projection` is fully proved and remains so.
No definition has a hole; no new axiom is introduced.

Validation: the original eight-module packet compiled cleanly through
`lcompile.py --all`. During the delivery-capacity wait, the shared library gained the
completed mate proof. All ten modules of the revised packet then compiled cleanly,
including the preserved mate proof and the downstream consumer with its explicit proof
import. The delivery tool records the final preflight.

## No longer needed

The original item's direct proof imports are removed:

- `Sheaf.Paper.SectionDerivedTensorNormalization`.
- `Sheaf.CategoryTheory.SheafTensor`.
- `Sheaf.CategoryTheory.InternalSectionTensorComparison`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison`.
- `Sheaf.Algebra.Homology.RingedDerivedTensorNative`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.CategoryTheory.InternalModuleInverseImageComparison`.
- `Sheaf.Paper.KFlatScalarComparisonNormalization`.
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`.
- `Sheaf.Paper.KFlatRingedToposPullback`.

The combination proof no longer directly follows these original proof dependencies:

- `sk-def-sfb-sheaf-tensor`.
- `lem-pe-internal-section-tensor-comparison`.
- `lem-sfb-internal-section-scalar-adjunction`.
- `lem-pd-section-derived-pushpull-normalization`.
- `lem-pd-section-derived-tensor-normalization`.
- `lem-weil-pbc-extension-tensor-comparison`.
- `def-sfb-internal-derived-scalar-comparisons`.
- `lem-pur-derived-change-of-rings`.
- `lem-sf-ringed-derived-native-tensor`.
- `lem-weil-pbc-site-derived-tensor-descent`.
- `lem-pc-kflat-resolution`.
- `sk-def-sfb-coefficient-morphisms`.
- `lem-sfb-internal-module-inverse-image-comparison`.
- `lem-sfb-kflat-scalar-comparison-normalization`.
- `lem-sfb-internal-module-operations-transport`.
- `def-sfb-comap-lower-star-iso`.
- `lem-weil-pbc-conjugate-iso-unit-equation`.
- `lem-weil-pbc-ringed-pullback-preserves-kflat`.

These are route-level removals, not declarations or modules withdrawn from the library.
Some remain dependencies of the reused scalar, tensor or section transport results;
no claim is made that their whole modules leave the targets' import closure.
In particular the internal tensor construction reuses the canonical coefficient tensor
normalization instead of duplicating its balanced tensor descent argument.
All original public imports remain available through the publicly re-exported data
module, together with the retained `SectionDerivedPushpullNormalization` public import.
No source-library declaration is removed and `deleted.txt` is not used.

## Where the brief, the DAG or earlier work was wrong

The original item bundled definition ownership and the existence theorem in one module.
This made the already stated section transport theorem impossible to import back into
its parent proof. Its DAG also listed the parent's existence theorem as a dependency
although the transport argument uses a supplied `PullNormalized` hypothesis. That obsolete
proof dependency is removed.

Likewise the canonical coefficient tensor statement used the restricted coefficient mate
theorem's node solely to name `regularPullback`. The mate theorem itself depends on this
item, whereas the definition is constructed independently. A definition-only owner repairs
that citation without changing the canonical theorem's statement in Lean.

The smaller K-flat proof imports avoid an unrelated unpublished `Derived.Localizing`
dependency which timed out when importing the broad projection/shift module. No timeout
limit or launcher code was changed.

## New nodes

`lem-sfb-internal-section-scalar-normalization-existence` records the proved universal
scalar comparison at one scheme; its construction identifies counits and preserves the
ordinary normalized generators.

`lem-sfb-internal-pull-normalization-existence` records the proved internal scalar/pullback
comparison from the two composite K-flat universal counits.

`lem-sfb-section-tensor-normalization-transport` records the independent remaining
section tensor transport theorem, with its ordinary generator and flat-term K-flat
computation argument.

`def-sfb-restricted-regular-pullback-data` owns the already constructed ordinary and
derived regular pullback definitions in `RestrictedCoefficientPullbackData`, extracted
verbatim from the current `RestrictedCoefficientMateProjection`. No Lean object is
chosen from an existence statement.

## Forced adaptations

None in the revised packet. `RestrictedCoefficientMateProjection` is now unclaimed;
its completed proof and private helpers are preserved verbatim. Only its two regular
pullback definitions move, with a public re-export from the new data module.
`CanonicalCoefficientTensorNormalization` and `SectionPullNormalizationTransport`
and `CoefficientPushFilteredLegs` are also unclaimed and receive the import adaptations
described above. The latter uses the mate theorem only in its proof (lines 262 and 279
of the original); the new explicit private import replaces its former transitive access.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
