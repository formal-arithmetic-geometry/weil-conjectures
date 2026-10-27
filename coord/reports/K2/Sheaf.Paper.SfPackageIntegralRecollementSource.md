## What changed

Replaced the hole in `sfPackageIntegralRecollementSource` by an explicit boundary
construction. The proof obtains integral normalized triangles and cross-object
shifted Hom vanishing, carries both through the full exact inclusion, and uses
`triangle_morphism_extension` to prove naturality and uniqueness in the ambient
completed derived category. The actual statement and existing docstring are unchanged.
The new statement compiled through `lcompile.py --all`; the final source module
compiled cleanly through `lcompile.py` in 9.8 seconds.

Added `SfPackageIntegralRecollementNormalization`, isolating the comparison of the
supplied counit/unit with the exact completed sheaf sequence. Its conclusion is
only two natural outer isomorphisms and their representative-complex map equations.
It assumes no distinguished triangle or connecting transformation and makes no
uniqueness or Hom-vanishing claim. It is the map-identification part of the original
argument, strictly before the triangle and boundary argument implemented here.

## Proved and sorry left

Closed the original hole in `WeilConjectures.sfPackageIntegralRecollementSource`
(node `lem-sf-package-integral-recollement-source`).

Added one hole, `WeilConjectures.sfPackageIntegralRecollementNormalization`
(node `lem-sf-package-integral-recollement-normalization`). No other hole remains
in either delivered file. This is a decomposition: one upper hole closed, one
strictly smaller normalization obligation added; net hole reduction is zero.

## No longer needed

No existing imports were removed. The original direct dependency on
`prop-sf-open-closed-triangle-all-stages` is replaced by its already proved
normalized integral triangle argument, `integral_normalized` in
`SfNormalizedRecollementTriangles`, imported privately with `import all`.
This avoids the unrelated rational, common-stage and Weil assembly.
The source theorem no longer directly uses
`lem-sf-integral-support-functor-normalization` or
`lem-sf-integral-immersion-pullback-normalization`; the new normalization node
retains both. No module is withdrawn and no unit-level step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original single proof step combines a comparison of the supplied adjunctions
with the exact sheaf sequence and a separate triangle argument. The existing
normalization declarations do not themselves state that the actual datum's
counit and unit satisfy `SfIntegralRecollementNormalization`. That interface
comparison is now explicit. The original statement is unchanged and is not disputed.

The new normalization statement was checked on zero inputs and empty strata:
its comparisons are adjunction identifications and the sheaf exact sequence,
which specialize without requiring either stratum to be nonempty. Arbitrary
supplied adjunctions are handled by adjunction-compatible uniqueness isomorphisms,
not by assuming that any preselected functor isomorphism carries their maps.

## New nodes

`lem-sf-package-integral-recollement-normalization`: the two actual adjunction maps
have the exact sheaf-kernel normalization. It retains the support and immersion
comparisons, full-subcategory adjunction restriction, ringed exact sequence and
termwise derived localization as its argument. Its docstring gives that argument
and its source. No definition or existing signature is changed.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
