## What changed

Completed `WeilConjectures.finite_constructible_derivedHom_proEtale` in
`Sheaf.Paper.FiniteConstructibleHom`, preserving both public theorem signatures and
all existing public imports. A local priority for `CommRing.toRing` aligns generic
coefficient specializations with the canonical ring hierarchy. Added private proof imports of
`Sheaf.Paper.ComparisonTorAmplitude`, `Sheaf.SixFunctors.FiniteDualitySiteComparison`,
`Sheaf.Paper.IntrinsicSiteHomTransport`, and the exact-derived-functor API.

The finite-duality comparison already supplies an equivalence between the etale
and fixed-scalar pro-etale finite-Tor constructible subcategories. Pull the intrinsic
inputs back along the exact coefficient-realization equivalence, then use that
subcategory equivalence to choose etale origins. Reflect their exact Tor intervals,
apply the existing etale theorem, and preserve the resulting interval under comparison.
Compose the invertible evaluation-defined site Hom comparison, the coefficient-presentation
Hom comparison, and functoriality in the two inputs. Private proved helpers transport
Tor amplitude and finite-Tor constructibility across isomorphisms.

Updated `cor-weil-finite-constructible-hom`'s proof, proof dependencies, and proof origin
to describe these actual steps. No new declarations with postponed proofs or definitions
were introduced. The complete candidate compiled in 49.3 seconds after aligning
`CommRing.toRing`; profiling options were removed for the delivery verification.
Empty schemes, zero inputs, and degenerate ordered intervals are covered:
all equivalences and isomorphism transports are unconditional in these cases, and
`c - b - 2*d <= e - a + 2*d` follows from the original ordered intervals and `d >= 0`.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.finite_constructible_derivedHom_proEtale`
(node `cor-weil-finite-constructible-hom`). Added zero holes and split off zero statements.
The item now contains zero `sorry`s. The already proved
`WeilConjectures.finite_constructible_derivedHom_etale` is retained unchanged.
The proof uses existing stated comparison theorems; their own remaining holes are
unchanged and are not claimed as closed by this delivery.

## No longer needed

Removed the direct proof dependency on `lem-sf-proetale-constructible-origin`
(`Sheaf.Paper.ProEtaleConstructibleOrigin`): the finite-duality site's already stated
finite-Tor subcategory equivalence supplies the needed origins directly. It remains
a dependency of that comparison theorem, so no global retirement is claimed.
No existing import was removed and no module was withdrawn. Added the existing
`lem-sf-intrinsic-site-hom-transport` dependency for the actual intrinsic Hom conversion.
No other node or module is claimed unnecessary.

## Where the brief, the DAG or earlier work was wrong

The previous pro-etale plan suppressed the change between fixed-scalar module sheaves
and the intrinsic constant-ring module presentation. The existing
`AlgebraicGeometry.ProEtale.intrinsicSiteHom_transport` states exactly the needed
ambient Hom conversion. The finite-duality theorem also already gives finite-Tor
origins, making a separate origin theorem invocation redundant.
The theorem statements and unit route were not changed.

Searches: LeanFinder returned only generic derived-category boundedness facts;
Loogle found the canonical `mapDerivedCategoryCompIso` composition API. Source searches
located the adopted etale Hom bound, the interval equivalence API, and the existing
intrinsic Hom transport. No duplicate theorem was introduced.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
