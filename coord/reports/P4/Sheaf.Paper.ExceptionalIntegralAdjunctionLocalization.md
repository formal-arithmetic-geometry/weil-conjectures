## What changed

Proved `WeilConjectures.ConstructibleExceptionalCoefficients.exists_raw_localized_adjunction_core`
in `Sheaf.Paper.ExceptionalIntegralAdjunctionLocalization`.

The proof constructs the equivalences that change only the integral membership proofs,
composes their adjunctions with the supplied integral adjunction, and proves exactness
of the full integral left functor by reflection through the fully faithful ambient
inclusions. It reuses the already proved private `sfLocalizedAdjunction`,
`sfLocalization_factor`, and `sfRationalizedExact` helpers from
`Sheaf.Paper.SfRationalLocalizationOrthogonality` through a proof-only `import all`.
Mathlib supplies the right-adjoint shift, shift compatibility of the adjunction,
and exactness of the right adjoint. The tensor functors themselves stay literal.
The core node now records this route, and the main node records its existing
combination of the core and comparison theorems.

Repeated instance inference is controlled with local irreducibility of
`sfIntegralConstructible` and `sfRationalTriangulationDatum`, and explicit local
additive/linear instances. No public signature, definition, instance, attribute,
or public import was changed.
The identity-comparison declaration is marked disputed; its proof remains unfinished.

Validation: the final item module compiled without errors or warnings through
`lcompile.py` in 53.1 seconds, within the 60-second limit.

## Proved and sorry left

Closed one of the two original holes:
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_raw_localized_adjunction_core`
(node `lem-sf-integral-adjunction-raw-localization-core`).

The one remaining hole is
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_raw_localized_identity_comparison`
(node `lem-sf-integral-adjunction-raw-localization-identity`).
No holes or axioms were added. No decomposition was introduced.
The already existing main theorem still uses the remaining comparison hole.

## No longer needed

No modules or nodes were withdrawn, and no existing imports were removed.
For the core, explicit tensor-extension of the Hom adjunction equivalence and the
natural-bijection constructor are unnecessary: the proved localization helper
uses Mathlib's `Adjunction.localization` instead. Consequently
`lem-weil-pbc-adjunction-of-natural-bijection` is removed from the main node's
direct proof dependencies. The scalar-localization and triangulated-localization
dependencies are retained transitively through the core node. The parent normalization argument
is still unfinished, so its dependencies are not claimed as globally pruned.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED:
`exists_raw_localized_identity_comparison` quantifies over an arbitrary
`RawLocalizedAdjunction`, but that structure contains no compatibility of its
adjunction with the supplied integral unit or counit and no normalization of
its shift comparisons. Exactness and compatibility of its own unit and counit
with its own shifts do not imply that missing normalization.

For example, start with an identity adjunction on a nonzero rational coefficient
category. Multiply its unit by -1 and its counit by -1. The triangle identities,
exactness and shift compatibility still hold. The integral adjunction can remain
the original one. If both comparison maps are identity components, the
`CounitComparison.counit` field forces the rational counit to equal the image of
the original integral counit. On a nonzero object in characteristic zero this
would assert `-id = id`. Thus the arbitrary-R statement is too strong; the
normalization must be part of the construction of a particular R or an explicit
hypothesis. This is a mathematical counterexample pattern, not a formalized
counterexample in this delivery. The existential main localization statement
can still be true. Its signature has not been changed.

The existing identity-comparison docstring also pointed to a nonexistent
`...-comparison` node instead of its attached `...-identity` node; this tag was
corrected.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
