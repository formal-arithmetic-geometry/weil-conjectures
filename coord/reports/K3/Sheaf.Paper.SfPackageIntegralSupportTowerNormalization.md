## What changed

Proved `WeilConjectures.sfPackageIntegralSupportTowerNormalization` with its statement
unchanged. The proof constructs the designated strict tower datum with the canonical
coefficient total derived limit. A proved private lemma derives the unit-projection
identity on every complex from right-derived descent and the K-injective normalization.
The existing `constructibleIntegralSupport_eq` identifies the supplied action with the
published action; `compactSupportNormalizedTowerLimit` supplies the natural comparison
and every Roos projection equation. Added three private proof imports and updated the
item node to record this route. No definitions, target statements, or consumer APIs change.
The compositor-data theorem serves only as a generic equality of normalized actions;
it does not replace the six-functor package unit by a Verdier-exchange unit conclusion.
The revised dependency graph has no path from any new dependency back to the item.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.sfPackageIntegralSupportTowerNormalization`
(`lem-sf-package-integral-support-tower-normalization`).
Added zero holes. No `sorry` remains in the delivered module. The new private helper
`unitProjection` is proved. This is a proof from existing library declarations, including
their already recorded dependencies, rather than a decomposition into new obligations.

## No longer needed

No existing imports were removed: the original module imported only its statement API.
The item proof no longer directly needs `lem-sf-compact-support-total-limit-realization`
(`Sheaf.Paper.CompactSupportTotalLimitRealization`),
`lem-sf-integral-compact-support-constructible`
(`Sheaf.Paper.SfIntegralCompactSupportConstructible`), or
`lem-weil-integral-constructible-triangulated`
(`Sheaf.Paper.SfIntegralConstructibleTriangulated`). Existing normalized action/comparison
APIs already retain the constructible domain and supply the comparison. These modules
are not withdrawn and may remain needed transitively or by other parents. The reduction
tower dependency is retained. No unit-level statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG plan did not name two existing reusable results:
`constructibleIntegralSupport_eq` and `compactSupportNormalizedTowerLimit`.
The datum's bare `supportConstruction` does not state that its existential tower equals
the designated tower, so projecting that field alone would leave the equality unproved.
The existing equality with the published action resolves this without changing the datum.
The canonical projection API states its normalization on K-injectives; the construction
record asks for the derived-unit equation on all complexes. The private descent argument
bridges these exact statements.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
