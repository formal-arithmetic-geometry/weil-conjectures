## What changed

Proved `AlgebraicGeometry.Etale.exists_clopen_normal_integral_components` in
`Sheaf.AlgebraicGeometry.EtaleNormalComponents`, with its signature and public imports unchanged.
All new helpers are private and completely proved. Affine stalk-localization isomorphisms
transfer target normality to the hypotheses of `RingHom.Etale.isNormalRing`, then transfer
its conclusion to the source stalks. For disjointness, the image of the spectrum of a local
domain is irreducible and contains every generization of the point; generic points and
maximality force all components containing that point to coincide. Finiteness makes each
component open as well as closed. Restricted stalk isomorphisms supply normality, while
reducedness and irreducibility supply integrality. Enumerating the components by their
cardinality handles the empty source without any extra hypothesis.

Updated the existing node's proof text and origin to describe this implementation of the
same blueprint argument. No new modules or statements were required. The unchanged current
blueprint statement and proof were read in `main-20261015`, under
`sec-six-functors-basics/sk-prop-sf-cbc/`.

Searches: LeanFinder returned the existing finite-component theorem and basic scheme
properties; Loogle returned localization/domain results but no decomposition theorem;
launcher grep returned no hits. Direct source searches located Mathlib's stalk localization
API, `Scheme.range_fromSpecStalk`, generic points, and reduced/irreducible integrality.
The module compiled cleanly through `lcompile.py` (about three seconds).

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.exists_clopen_normal_integral_components`
(node `lem-fin-etale-normal-components`). Proved 1 of 1; zero holes remain in the item;
zero holes added; zero statements split off. The proof uses the existing declared dependency
`RingHom.Etale.isNormalRing`; its underlying normality-ascent dependencies remain separate
items, as intended by stage 3.

## No longer needed

None of the original imports, nodes, or declared dependencies was pruned. The proof still
uses normal-scheme conventions, affine etale maps, etale normality ascent, and finiteness of
Noetherian irreducible components. An experimental direct import of
`Mathlib.AlgebraicGeometry.Stalk` was removed: the required API is already available through
the existing imports. No new import remains in the delivered file.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG's local-ring/minimal-prime argument is implemented
using the equivalent generization-spectrum argument, avoiding additional minimal-prime
comparison infrastructure. The theorem's statement, hypotheses, definitions, and unit route
are unchanged. No consumer adaptation or change record is needed.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
