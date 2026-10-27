## What changed

Filled `ContinuousRational.continuousAmbientGeometricCoherence` without changing its
statement or the two public records. Added private proof imports of
`Sheaf.Paper.RationalRealizationScalarCoherence` and
`Sheaf.AlgebraicGeometry.ProEtaleCanonicalAdjunctionUnit`, and private transport helpers.
The existing proved composition/identity wrappers supply the old comparisons.
Normalized coefficient uniqueness identifies their maps with the supplied `Along`
maps. The scalar cancellation and its degreewise counit equation are extracted
from `Along.normalized_counit`. Conjugating the ordinary comparisons gives the
new unit formulas; degreewise cancellation and counit naturality give the derived
normalizations. The argument uses no additional assumptions, including for empty
schemes and identity morphisms.

Updated the item's DAG proof, dependencies and origin to match this transport.
No existing interface, shared definition, instance or public import changed.
The scalar tensor object-equality cancellation is factored into a proved private
lemma to keep the proof term small; local irreducibility keeps large geometric and
derived-category definitions folded. The complete proof compiled remotely in
53.0 seconds; the sole whitespace warning was then removed for delivery.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Scheme.ContinuousRational.continuousAmbientGeometricCoherence`
(node `lem-per-continuous-ambient-geometric-coherence`). Added 0 holes and split off
0 statements. No `sorry` remains in this module. This proof uses existing declared
rational coherence dependencies; it does not claim those dependencies are all closed.

## No longer needed

No modules are globally pruned and no existing imports are removed.
The planned direct dependency `lem-pur-inverse-image-scalar-unit-normalization`
(`Sheaf.AlgebraicGeometry.ProEtaleInverseImageScalarUnitNormalization`) need not be
imported: the required scalar cancellation is already part of each supplied
`IsNormalizedPullCounit`. The old composition theorem
`lem-per-rational-pullback-composition-coherence` is used through the already proved
`rationalScalarPullComposition` and `rationalScalarPullIdentity` wrappers in
`lem-per-rational-realization-scalar-coherence`; it is still needed transitively.
The realization and pullback-comparison existence dependencies remain needed.
No unit-level statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The proof plan's scalar cancellation is already explicitly available in the
normalization data, so constructing it anew is unnecessary. The existing rational
scalar coherence module also already proves the required reversal of the old
composition equation and its unit formula, including the identity site projection.
`RationalAmbientPullComposition` has a closely matching statement but cannot be
imported: it reaches this item through the continuous-realization existence theorem.
The import-direction tool confirmed this cycle; the delivered route avoids it.

Searches were run with Lean Finder (derived inverse-image composition and identity),
Loogle (`CategoryTheory.Functor.leftDerivedUnique`), the search service grep
(`pullbackComp|extendScalarsId`), and repository `rg`. Generic Mathlib uniqueness and
ordinary pullback lemmas do not directly provide the specified tensor-unit equations;
the existing project coherence wrappers are the shorter usable route.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
