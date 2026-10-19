## What changed

Proved `AlgebraicGeometry.Etale.supportedProductLocalization_naturality` from naturality
of the derived supported-coefficient tensor comparison and the two evaluation counits,
then applied the supported-coefficient adjunction's naturality square. Three proved
private helpers express tensor bifunctor composition and evaluation naturality.
Replaced the interrupted attempt's unrestricted simplification with explicit identity
transport rules; the complete module compiled in 30.3 seconds.

## Proved and sorry left

Closed 1 of the original 6 holes:
`AlgebraicGeometry.Etale.supportedProductLocalization_naturality`.
Added zero holes and split off zero statements.

Five original holes remain, all attached to `lem-pur-supported-product-localization`:

- `AlgebraicGeometry.Etale.supportedProductLocalizationFirst`
- `AlgebraicGeometry.Etale.supportedProductLocalizationSecond`
- `AlgebraicGeometry.Etale.supportedProductLocalization_openFirst`
- `AlgebraicGeometry.Etale.supportedProductLocalization_openSecond`
- `AlgebraicGeometry.Etale.supportedProductLocalization_openRows`

## No longer needed

None. The original localization and open-restriction proof plans remain necessary.
No DAG dependencies have been removed. Retired Sheaf imports were replaced with
the current source module header after the upstream namespace migration; this removes
only obsolete and duplicate import paths, without pruning mathematical dependencies.

## Where the brief, the DAG or earlier work was wrong

The interrupted attempt's final unrestricted `simp` exceeded the compile limit when
simplifying the external-product equality transports. Explicitly simplifying
`eqToHom_refl`, identities and associativity avoids the expensive unfolding. No
statement, public definition, signature or visibility has changed. During the provider
interruptions, five imported Sheaf modules migrated to WeilConjectures; the sandbox
header now matches the current item module header.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
