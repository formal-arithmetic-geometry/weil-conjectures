## What changed

Proved `AlgebraicGeometry.ProEtale.IntegralFiniteScalar.finiteFreeScalarDerivedComparison_beta_construction`
without changing its signature or the meaning of `AugmentationNormalized`.

The proof constructs the ordinary linear comparison from the existing coequalizer
isomorphism in `InternalKFlatScalarTowerRealization`. It identifies the augmented
target with the degree-zero restricted regular module, forms the natural total
complex comparison, and checks its prescribed `(0,n)` summands. The derived scalar
counit, exact restriction localization factor, and the lax tensorator of `Q` give
two natural comparisons to the same complex functor. Both are invertible on native
K-flat inputs. Fully faithful precomposition with the localization of K-flat
complexes descends their ratio; its map-preimage equation is precisely the required
augmentation normalization. The quasi-isomorphism of the finite-free augmentation
comes from `finiteFreeScalarDerivedComparison_augmentation`.

Added two private proof imports: `Sheaf.Algebra.Homology.InternalKFlatScalarTowerRealization`
(with its proved private coequalizer comparison and cochain counit visible) and
`Sheaf.Paper.FiniteFreeScalarDerivedComparisonAugmentation`. All new helpers are
private and proved; no existing public declaration or public import changes.
The item's node records this native-module proof route.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.IntegralFiniteScalar.finiteFreeScalarDerivedComparison_beta_construction`
(node `new-sfb-finite-free-scalar-derived-comparison-beta-construction`).
No holes added, no split-off statements, and no `sorry` left in the delivered module.

## No longer needed

The original module had only its definition import, which is retained. No import
was removed. The planned direct proof dependencies are replaced as follows:

- `lem-pc-kflat-resolution` / `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  the proof uses the existing native K-flat localization of internal modules.
- `lem-pe-restricted-kflat-tensor-identification` /
  `Sheaf.Algebra.Homology.RestrictedKFlatTensorIdentification`: the native module
  coequalizer comparison directly supplies the ordinary linear identification.
- `lem-weil-pbc-site-derived-tensor-descent` /
  `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`: native
  derived tensor and fully faithful K-flat localization suffice.
- `lem-sfb-kflat-scalar-comparison-normalization` /
  `Sheaf.Paper.KFlatScalarComparisonNormalization`: this construction is schemewise;
  it needs no comparison between geometric inverse images.

These nodes remain available for other consumers. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned sheaf-level comparisons are unnecessary for this substep. Native
module-object APIs already provide the ordinary comparison and the needed
localization. Naturality of the lax tensorator transfers invertibility across the
augmentation, so the construction itself only needs the augmentation to be a
quasi-isomorphism; it does not require a separate proof that the two-term model is
K-flat. The fixed coefficient isomorphism and all normalization equations are
preserved. The proof works equally for rank zero, the zero complex, and zero
coefficient rings; no cancellation by ring elements or nonzero assumptions occurs.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteFreeScalarDerivedComparisonBetaConstruction": "f9577273170a4abfcf5dae4134a67b954c5962fd"}, "results": {"Sheaf.Paper.FiniteFreeScalarDerivedComparisonBetaNormalization": {"hash": "6b03055e38a3adaf4d1af04b3a070afeb4eab17f", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T12:14:59+0800", "transitive": 0, "version": 1}
```

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
